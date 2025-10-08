#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

#include <vector>
#include <algorithm>
#include <unordered_map>
#include <string>
#include <set>

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintMoCut(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocut", Lsv_CommandPrintMoCut, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

void Lsv_NtkPrintNodes(Abc_Ntk_t* pNtk) {
  printf("Printing nodes...\n");
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i) {
    printf("Object Id = %d, name = %s\n", Abc_ObjId(pObj), Abc_ObjName(pObj));
    Abc_Obj_t* pFanin;
    int j;
    Abc_ObjForEachFanin(pObj, pFanin, j) {
      printf("  Fanin-%d: Id = %d, name = %s\n", j, Abc_ObjId(pFanin),
             Abc_ObjName(pFanin));
    }
    if (Abc_NtkHasSop(pNtk)) {
      printf("The SOP of this node:\n%s", (char*)pObj->pData);
    }
  }
}

int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
      case 'h':
        goto usage;
      default:
        goto usage;
    }
  }
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  Lsv_NtkPrintNodes(pNtk);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_print_nodes [-h]\n");
  Abc_Print(-2, "\t        prints the nodes in the network\n");
  Abc_Print(-2, "\t-h    : print the command usage\n"); 
  return 1;
}

// Utilities for k-l multi-output cuts
static std::string Lsv_KeyFromCut(const std::vector<int>& cut) {
  std::string key;
  for (size_t i = 0; i < cut.size(); ++i) {
    if (i) key.push_back(' ');
    char buf[32];
    int n = snprintf(buf, sizeof(buf), "%d", cut[i]);
    key.append(buf, (size_t)n);
  }
  return key;
}

static std::vector<int> Lsv_MergeCutsLimited(const std::vector<int>& a,
                                             const std::vector<int>& b,
                                             int k,
                                             bool* ok) {
  std::vector<int> out;
  out.reserve(a.size() + b.size());
  size_t i = 0, j = 0;
  while (i < a.size() || j < b.size()) {
    int va = (i < a.size()) ? a[i] : 0x7fffffff;
    int vb = (j < b.size()) ? b[j] : 0x7fffffff;
    int v = va < vb ? va : vb;
    out.push_back(v);
    if (va == v) ++i;
    if (vb == v) ++j;
    if ((int)out.size() > k) { *ok = false; return {}; }
  }
  *ok = true;
  return out;
}

static bool Lsv_IsSuperset(const std::vector<int>& a, const std::vector<int>& b) {
  // return true if a is a strict superset of b (all b in a, and sizes differ)
  if (a.size() <= b.size()) return false;
  size_t i = 0, j = 0;
  while (i < a.size() && j < b.size()) {
    if (a[i] == b[j]) { ++i; ++j; }
    else if (a[i] < b[j]) { ++i; }
    else { return false; }
  }
  return j == b.size();
}

static int Lsv_CommandPrintMoCut(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  if (!pNtk) { Abc_Print(-1, "Empty network.\n"); return 1; }
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "Please run 'strash' before lsv_printmocut.\n");
    return 1;
  }

  if (argc != 3) {
    Abc_Print(-2, "usage: lsv_printmocut <k> <l>\n");
    Abc_Print(-2, "\t  3 <= k <= 6, 1 <= l <= 4\n");
    return 1;
  }
  int k = atoi(argv[1]);
  int l = atoi(argv[2]);
  if (k < 3 || k > 6 || l < 1 || l > 4) {
    Abc_Print(-1, "Argument out of range.\n");
    return 1;
  }

  // Topological order of internal nodes
  Vec_Ptr_t* vDfs = Abc_AigDfs(pNtk, 0, 0);
  int nDfs = vDfs ? Vec_PtrSize(vDfs) : 0;

  // Map from object id to list of cuts (each cut is sorted vector<int>)
  std::vector< std::vector< std::vector<int> > > idToCuts(Abc_NtkObjNumMax(pNtk) + 1);

  // Initialize PI cuts and treat them as outputs
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachPi(pNtk, pObj, i) {
    int id = Abc_ObjId(pObj);
    idToCuts[id].push_back(std::vector<int>(1, id));
  }

  // For AND nodes in DFS order, build cuts from fanin cuts and the trivial {node}
  for (i = 0; i < nDfs; ++i) {
    Abc_Obj_t* pNode = (Abc_Obj_t*)Vec_PtrEntry(vDfs, i);
    int id = Abc_ObjId(pNode);
    if (!Abc_ObjIsNode(pNode)) continue;

    // trivial cut {node}
    idToCuts[id].push_back(std::vector<int>(1, id));

    Abc_Obj_t* pF0 = Abc_ObjFanin0(pNode);
    Abc_Obj_t* pF1 = Abc_ObjFanin1(pNode);
    int id0 = Abc_ObjId(pF0);
    int id1 = Abc_ObjId(pF1);
    const auto& cuts0 = idToCuts[id0];
    const auto& cuts1 = idToCuts[id1];

    std::set<std::string> seen;
    // keep already inserted trivial {node}
    seen.insert(Lsv_KeyFromCut(idToCuts[id][0]));

    for (size_t a = 0; a < cuts0.size(); ++a) {
      for (size_t b = 0; b < cuts1.size(); ++b) {
        bool ok = false;
        std::vector<int> merged = Lsv_MergeCutsLimited(cuts0[a], cuts1[b], k, &ok);
        if (!ok) continue;
        std::string key = Lsv_KeyFromCut(merged);
        if (seen.insert(key).second) {
          idToCuts[id].push_back(std::move(merged));
        }
      }
    }

    // Filter non-irrelevant: remove any cut that is a strict superset of another
    auto& cutsN = idToCuts[id];
    std::vector<char> drop(cutsN.size(), 0);
    for (size_t a = 0; a < cutsN.size(); ++a) {
      if (drop[a]) continue;
      for (size_t b = 0; b < cutsN.size(); ++b) {
        if (a == b || drop[b]) continue;
        if (Lsv_IsSuperset(cutsN[a], cutsN[b])) { drop[a] = 1; break; }
      }
    }
    std::vector< std::vector<int> > filtered;
    filtered.reserve(cutsN.size());
    for (size_t a = 0; a < cutsN.size(); ++a) if (!drop[a]) filtered.push_back(std::move(cutsN[a]));
    idToCuts[id].swap(filtered);
  }

  if (vDfs) Vec_PtrFree(vDfs);

  // Group multi-output cuts across all outputs (PIs and AND nodes)
  std::unordered_map<std::string, std::vector<int> > cutToOutputs;
  std::unordered_map<std::string, std::vector<int> > keyToInputs;

  // Add PIs
  Abc_NtkForEachPi(pNtk, pObj, i) {
    int id = Abc_ObjId(pObj);
    for (const auto& cut : idToCuts[id]) {
      std::string key = Lsv_KeyFromCut(cut);
      cutToOutputs[key].push_back(id);
      if (!keyToInputs.count(key)) keyToInputs[key] = cut;
    }
  }
  // Add AND nodes
  Abc_NtkForEachNode(pNtk, pObj, i) {
    int id = Abc_ObjId(pObj);
    for (const auto& cut : idToCuts[id]) {
      std::string key = Lsv_KeyFromCut(cut);
      cutToOutputs[key].push_back(id);
      if (!keyToInputs.count(key)) keyToInputs[key] = cut;
    }
  }

  // Collect and sort results before printing
  std::vector<std::pair<std::vector<int>, std::vector<int>>> results;
  for (const auto& kv : cutToOutputs) {
    const std::string& key = kv.first;
    const auto& outs = kv.second;
    if ((int)outs.size() < l) continue;
    const auto& ins = keyToInputs[key];
    
    // Sort inputs and outputs
    std::vector<int> sortedIns = ins;
    std::sort(sortedIns.begin(), sortedIns.end());
    std::vector<int> sortedOuts = outs;
    std::sort(sortedOuts.begin(), sortedOuts.end());
    
    results.push_back({sortedIns, sortedOuts});
  }
  
  // Sort results by input cuts (lexicographically)
  std::sort(results.begin(), results.end());
  
  // Print sorted results
  for (const auto& result : results) {
    const auto& sortedIns = result.first;
    const auto& sortedOuts = result.second;
    
    // print inputs
    for (size_t t = 0; t < sortedIns.size(); ++t) {
      if (t) printf(" ");
      printf("%d", sortedIns[t]);
    }
    printf(" : ");
    // print outputs
    for (size_t t = 0; t < sortedOuts.size(); ++t) {
      if (t) printf(" ");
      printf("%d", sortedOuts[t]);
    }
    printf("\n");
  }

  return 0;
}
#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <set>
#include <vector>
#include <map>
#include <algorithm>

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintMOCuts(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocut", Lsv_CommandPrintMOCuts, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

void Lsv_NtkPrintNodes(Abc_Ntk_t* pNtk) {
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i) {
    printf("Object Id = %d, name = %s\n", Abc_ObjId(pObj) + 1, Abc_ObjName(pObj));
    Abc_Obj_t* pFanin;
    int j;
    Abc_ObjForEachFanin(pObj, pFanin, j) {
      printf("  Fanin-%d: Id = %d, name = %s\n", j, Abc_ObjId(pFanin) + 1, Abc_ObjName(pFanin));
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
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) goto usage;
  if (!pNtk) {Abc_Print(-1, "Empty network.\n"); return 1;}
  Lsv_NtkPrintNodes(pNtk);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_print_nodes [-h]\n");
  Abc_Print(-2, "\t        prints the nodes in the network\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}

// k-l multi-output cuts

void Lsv_findMOCuts(Abc_Ntk_t* pNtk, int k, int l) {
  
  Abc_Obj_t* pObj;
  int i;
  typedef std::set<std::set<int>> CutSet;
  std::map<int, CutSet> cuts;
  std::map<std::set<int>, std::set<int>> cut_outputs;

  Abc_NtkForEachNode(pNtk, pObj, i) {
    CutSet curr_cuts, curr_cuts_filtered;
    // printf("Object Id = %d, name = %s\n", Abc_ObjId(pObj), Abc_ObjName(pObj));

    Abc_Obj_t* pFanin;
    int j;
    std::vector<CutSet> nxt_cuts; // cuts of fanins
    std::vector<int> nxt_ids; // ids of fanins
    Abc_ObjForEachFanin(pObj, pFanin, j) {
      // printf("  Fanin-%d: Id = %d, name = %s\n", j, Abc_ObjId(pFanin), Abc_ObjName(pFanin));
      nxt_cuts.push_back(cuts[Abc_ObjId(pFanin)]);
      nxt_ids.push_back(Abc_ObjId(pFanin));
    }

    std::set<int> nxt_ids_set;
    for(auto &id: nxt_ids) nxt_ids_set.insert(id);
    curr_cuts.insert(nxt_ids_set);

    if (nxt_cuts.size() != 0) { // internal node
      for(auto &s: nxt_cuts[0]) {
        auto t = s; t.insert(nxt_ids[1]);
        if(t.size() <= k) curr_cuts.insert(t);
      }
      for(auto &s: nxt_cuts[1]) {
        auto t = s; t.insert(nxt_ids[0]);
        if(t.size() <= k) curr_cuts.insert(t);
      }
      curr_cuts.insert(nxt_ids_set);
    }

    // filter redundant cuts
    for(auto p: curr_cuts) {
      bool is_redundant = false;
      for(auto q: curr_cuts) {
        if(p == q || p.size() > q.size()) continue;
        if(std::includes(q.begin(), q.end(), p.begin(), p.end())) { is_redundant = true; break; }
      }
      if(!is_redundant) curr_cuts_filtered.insert(p);
    }

    // find the outputs of each cut
    cuts[Abc_ObjId(pObj)] = curr_cuts_filtered;
    for(auto &s: curr_cuts_filtered) {
      bool found = false;
      for(auto &it: cut_outputs) {
        if(s == it.first) { found = true; it.second.insert(Abc_ObjId(pObj)); break; }
      }
      if(!found) {
        std::set<int> tmp; tmp.insert(Abc_ObjId(pObj)); cut_outputs[s] = tmp;
      }
    }
  }

  /// output the results
  for(auto &it: cut_outputs) {
    if(it.second.size() >= l) {
      for(auto &id: it.first) printf("%d ", id);
      printf(": ");
      for(auto &id: it.second) printf("%d ", id);
      printf("\n");
    }
  }

}

int Lsv_CommandPrintMOCuts(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c, k = 0, l = 0;
  if(argc != 3) goto usage;
  k = atoi(argv[1]), l = atoi(argv[2]);
  if(k < 3 || k > 6 || l < 1 || l > 4) goto usage;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) goto usage;
  
  if (!pNtk) { Abc_Print(-1, "Empty network.\n"); return 1;}

  Lsv_findMOCuts(pNtk, k, l);

  return 0;

usage:
  Abc_Print(-2, "usage: lsv_print_mocut [-h] <k> <l>\n");
  Abc_Print(-2, "\t        prints the k-l multi-output cuts in the AIG\n");
  Abc_Print(-2, "\t        for 3 <= k <= 6 and 1 <= l <= 4\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}
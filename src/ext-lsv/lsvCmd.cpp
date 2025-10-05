#include "base/abc/abc.h"
#include "aig/aig/aig.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

#include <iostream>
#include <vector>
#include <algorithm>
#include <unordered_map>
#include <string>

using std::cout;
using std::vector;
using std::unordered_map;

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintMultiCuts(Abc_Frame_t* pAbc, int argc, char** argv);

extern "C" {
  Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
} 

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocut", Lsv_CommandPrintMultiCuts, 0);

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













bool isSubset(const std::vector<int>& a, const std::vector<int>& b) {
    return std::includes(a.begin(), a.end(), b.begin(), b.end());
}

void removeDuplicates(std::vector<std::vector<int>>& vecs) {
    for (auto it = vecs.begin(); it != vecs.end(); ++it) {
        bool subset = false;
        for (const auto& v : vecs) {
            if (it->size()>v.size() && isSubset(*it, v)) {
                subset = true;
                break;
            }
        }
        if (subset) {
            it = vecs.erase(it);
            --it;
        }
    }
}


static inline std::vector<int>
merge_unique_sorted(const std::vector<int>& a, const std::vector<int>& b) {
  std::vector<int> out;
  out.reserve(a.size() + b.size());
  size_t i = 0, j = 0;
  while (i < a.size() || j < b.size()) {
    int pick;
    if (j == b.size() || (i < a.size() && a[i] < b[j])) pick = a[i++];
    else if (i == a.size() || b[j] < a[i])               pick = b[j++];
    else { pick = a[i]; ++i; ++j; } // equal
    if (out.empty() || out.back() != pick) out.push_back(pick);
  }
  return out;
}

static inline void canonicalize_cuts(std::vector<std::vector<int>>& cuts) {
  // every cut must be sorted & unique leaves
  for (auto& c : cuts) {
    std::sort(c.begin(), c.end());
    c.erase(std::unique(c.begin(), c.end()), c.end());
  }
  // remove exact duplicates (lexicographic uniq)
  std::sort(cuts.begin(), cuts.end());
  cuts.erase(std::unique(cuts.begin(), cuts.end()), cuts.end());
}

static inline void remove_supersets(std::vector<std::vector<int>>& cuts) {
  if (cuts.empty()) return;
  // after canonicalization, we can drop strict supersets
  std::vector<char> keep(cuts.size(), 1);
  for (size_t a = 0; a < cuts.size(); ++a) {
    if (!keep[a]) continue;
    for (size_t b = 0; b < cuts.size(); ++b) {
      if (a == b || !keep[b]) continue;
      // if cuts[a] is a strict superset of cuts[b], drop a
      if (cuts[b].size() < cuts[a].size()
          && std::includes(cuts[a].begin(), cuts[a].end(),
                           cuts[b].begin(), cuts[b].end())) {
        keep[a] = 0; break;
      }
    }
  }
  std::vector<std::vector<int>> pruned;
  pruned.reserve(cuts.size());
  for (size_t i = 0; i < cuts.size(); ++i)
    if (keep[i]) pruned.push_back(std::move(cuts[i]));
  cuts.swap(pruned);
}

void genCutSeq(const std::vector<int>& cut, std::string &cutSeq){
  for(auto c: cut) cutSeq=cutSeq+std::to_string(c)+" ";
}

void Lsv_NtkPrintCuts(Abc_Ntk_t* pNtk, int k, int l) {
  // normalize to AIG
  // Abc_Ntk_t* pNtkAig = Abc_NtkStrash(pNtk, 0, 1, 0);
  Aig_Man_t* p       = Abc_NtkToDar(pNtk, 0, 1);

  // id -> list of cuts (each cut is sorted vector<int> of leaf IDs)
  std::unordered_map<int, std::vector<std::vector<int>>> V;

  int nPIs=Abc_NtkPiNum(pNtk);
  int nNs=Abc_NtkNodeNum(pNtk);
  int nPOs=Abc_NtkPoNum(pNtk);
  // cout<< nPIs<< " "<< nNs<< " "<< nPOs<< "\n";
  
  // Seed PIs: trivial cut = { id }
  Aig_Obj_t* pObj; int i;
  Aig_ManForEachPiSeq(p, pObj, i) {
    const int id = Aig_ObjId(pObj);
    V[id].push_back({id});
    // printf("%d: %d\n", id, id);
  }

  // Aig_ManForEachPoSeq(p, pObj, i){
  //   const int id = Aig_ObjId(pObj);
  //   cout<< id<< " ";
  // }
  // cout<< "\n";

  // AND nodes: combine fanin cuts
  Aig_ManForEachNode(p, pObj, i) {
    const int id0   = Aig_ObjId(pObj);
    const int id0F0 = Aig_ObjId(Aig_ObjFanin0(pObj));
    const int id0F1 = Aig_ObjId(Aig_ObjFanin1(pObj));

    const int id=(id0>nPIs&&id0<=nPIs+nNs)?id0+nPOs:id0;
    const int idF0=(id0F0>nPIs&&id0F0<=nPIs+nNs)?id0F0+nPOs:id0F0;
    const int idF1=(id0F1>nPIs&&id0F1<=nPIs+nNs)?id0F1+nPOs:id0F1;

    std::vector<std::vector<int>> cuts;

    cuts.push_back({id});

    const auto& cuts0 = V[idF0]; // map default-constructs empty if missing
    const auto& cuts1 = V[idF1];

    for (const auto& P : cuts0) {
      if ((int)P.size() > k) continue; // quick prune
      for (const auto& Q : cuts1) {
        if ((int)Q.size() > k) continue; // quick prune

        auto U = merge_unique_sorted(P, Q);
        if ((int)U.size() <= k){
          // for(int i=0;i<U.size();i++)
          //   if(U[i]>nPIs&&U[i]<=nPIs+nNs) {cout<< U[i]<< " "; U[i]+=nPOs; cout<< U[i]<< "\n";}
          cuts.push_back(std::move(U));
        }
          
      }
    }

    // Canonicalize and prune
    canonicalize_cuts(cuts);
    remove_supersets(cuts);

    V[id] = std::move(cuts);

    // Print this node's cuts
    // for (const auto& C : V[id]) {
    //   Abc_Obj_t* obj=Abc_NtkObj(pNtk, id);
    //   cout<< id<< "("<< Abc_ObjName(obj)<< "):";
    //   // printf("%d: ", id);
    //   for (int leaf : C){
    //     Abc_Obj_t* obj=Abc_NtkObj(pNtk, leaf);
    //     cout<< leaf<< "("<< Abc_ObjName(obj)<< ") ";
    //     // printf("%d ", leaf);
    //   } 
    //   printf("\n");
    // }
  }

  std::unordered_map<std::string, std::vector<int>> Vm;
  for(const auto& v: V){
    int node=v.first;
    auto& cuts=v.second;
    for(const auto& cut: cuts){
      std::string cutSeq="";
      genCutSeq(cut, cutSeq);
      Vm[cutSeq].push_back(node);
    }
  }
  for(auto& vm: Vm){
    auto& nodes=vm.second;
    if(nodes.size()>=l){
      std::sort(nodes.begin(), nodes.end());
      cout<< vm.first<< ": ";
      for(const auto& node: vm.second) cout<< node<< " ";
      cout<< "\n";
    }
    
  }


}

int Lsv_CommandPrintMultiCuts(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);


  int k=atoi(argv[1]);
  int l=atoi(argv[2]);

  
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
  Lsv_NtkPrintCuts(pNtk, k, l);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_printmocut <k> <l> [-h]\n");
  Abc_Print(-2, "\t        prints multi cuts in the network\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}
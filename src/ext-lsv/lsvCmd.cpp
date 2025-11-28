#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "bdd/cudd/cudd.h"
#include <vector>
#include <set>
#include <algorithm>
#include <cstdlib>
#include <unordered_map>
#include <map>
#include <string>

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintMoCut(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandUnateBDD(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandUnateSAT(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocut", Lsv_CommandPrintMoCut, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_unate_bdd", Lsv_CommandUnateBDD, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_unate_sat", Lsv_CommandUnateSAT, 0);
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
      //printf("  Fanin-%d: Id = %d, name = %s\n", j, Abc_ObjId(pFanin),Abc_ObjName(pFanin));
    }
    if (Abc_NtkHasSop(pNtk)) {
      //printf("The SOP of this node:\n%s", (char*)pObj->pData);
    }
  }
}
static std::vector<std::set<int>> create_cut(
    int k,
    int fanin0,
    int fanin1,
    const std::vector<std::vector<std::set<int>>>& cuts) {
  std::set<std::set<int>> unique_cuts;
  const auto& cuts0 = cuts[fanin0];
  const auto& cuts1 = cuts[fanin1];
  //printf("merged %d and %d :\n",fanin0,fanin1);

  for (const auto& a : cuts0) {
    for (const auto& b : cuts1) {
      std::set<int> merged;
      std::set_union(a.begin(), a.end(), b.begin(), b.end(),
                     std::inserter(merged, merged.begin()));
      if ((int)merged.size() <= k) {
        unique_cuts.insert(std::move(merged));
      }
    }
  }
  // Convert to vector
  return std::vector<std::set<int>>(unique_cuts.begin(), unique_cuts.end());
}



void Lsv_NtkPrintCut(Abc_Ntk_t* pNtk, int k, int l) {
  Abc_Obj_t* pObj;
  int i;

  int id_max = 0;
  int level_max = 0;
  Abc_NtkForEachNode(pNtk, pObj, i) {
    id_max = std::max(id_max, (int)Abc_ObjId(pObj));
    level_max = std::max(level_max, Abc_ObjLevel(pObj));
  }


  std::vector<std::vector<int>> fanin(id_max+1);
  std::vector<std::vector<int>> level_vec(level_max+1);

  Abc_NtkForEachNode(pNtk, pObj, i) {
    int id = Abc_ObjId(pObj);
    int level = Abc_ObjLevel(pObj);
    //printf("Object Id = %d, name = %s ObjLevel = %d\n", id, Abc_ObjName(pObj), level);
    Abc_Obj_t* pFanin;
    level_vec[level].push_back(id);
    int j;
    Abc_ObjForEachFanin(pObj, pFanin, j) {
      int fid = (int)Abc_ObjId(pFanin);
      fanin[id].push_back(fid);
      if (fid > id_max) {
        id_max = fid;
      }
    }
  }
  std::vector<std::vector<std::set<int>>> cuts(id_max+1);
  for(int id =0;id<id_max;id++){
    cuts[id].push_back(std::set<int>{id});
  }
  for (int cur_level = 0; cur_level <= level_max; ++cur_level) {
    for (int id : level_vec[cur_level]) {
      

      // Build from fanin cuts
      const int f0 = fanin[id][0];
      const int f1 = fanin[id][1];
      if(cur_level ==1){
        cuts[id].push_back(std::set<int>{f0,f1});
      }
      else{
        auto merged = create_cut(k, f0, f1, cuts);
        // Dedup with existing
        std::set<std::set<int>> uniq(cuts[id].begin(), cuts[id].end());
        for (auto& s : merged) uniq.insert(s);
        cuts[id].assign(uniq.begin(), uniq.end());
      }
    }
  }
  
  // Remove single element sets in cuts
  for (int id = 0; id <= id_max; ++id) {
    cuts[id].erase(
      std::remove_if(cuts[id].begin(), cuts[id].end(),
        [](const std::set<int>& s) { return s.size() == 1; }),
      cuts[id].end()
    );
  }

  int total_cut = 0;
  std::map<std::set<int>, std::set<int>> cut_to_output;
  for (int id = 0; id <= id_max; ++id) {
    total_cut+=cuts[id].size();
    for(auto cut_set: cuts[id]){
      cut_to_output[cut_set].insert(id);
    }
  }
  for(auto iter:cut_to_output){
    if(iter.second.size()<l) continue;
    for(auto c: iter.first){
      printf("%d ",c);

    }
    printf(": ");
    bool first = true;
    for(auto o: iter.second){
      if(!first) printf(" ");
      printf("%d",o);
      first = false;
    }
    printf("\n");

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

int Lsv_CommandPrintMoCut(Abc_Frame_t* pAbc, int argc, char** argv) {

  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
      case 'h':
        Abc_Print(-2, "usage: lsv_printmocut <k> <l> [-h]\n");
        Abc_Print(-2, "\t        prints the k-l cut in the network\n");
        Abc_Print(-2, "\t-h    : print the command usage\n");
        return 1;
      default:
        Abc_Print(-2, "usage: lsv_printmocut <k> <l> [-h]\n");
        Abc_Print(-2, "\t        prints the k-l cut in the network\n");
        Abc_Print(-2, "\t-h    : print the command usage\n");
        return 1;
    }
  }
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  if (argc < 3) {
    Abc_Print(-2, "usage: lsv_printmocut <k> <l> [-h]\n");
    Abc_Print(-2, "\t        prints the k-l cut in the network\n");
    Abc_Print(-2, "\t-h    : print the command usage\n");
    return 1;
  }
  int k = atoi(argv[1]);
  int l = atoi(argv[2]);
  if (k <= 2 || l < 1) {
    Abc_Print(-2, "usage: lsv_printmocut <k> <l> [-h]\n");
    Abc_Print(-2, "\t        prints the k-l cut in the network\n");
    Abc_Print(-2, "\t-h    : print the command usage\n");
    return 1;
  }
  Lsv_NtkPrintCut(pNtk, k, l);
  return 0;
}

int Lsv_CommandUnateBDD(Abc_Frame_t* pAbc, int argc, char** argv){
    if (argc < 2){
      Abc_Print(-2, "usage: lsv_unate_bdd <k> <i>\n");\
      return 1;
    }
    int k = atoi(argv[1]);
    int input_index = atoi(argv[2]);

    Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    Extra_UtilGetoptReset();
    Abc_Obj_t* pPo = Abc_NtkPo(pNtk, k);
    Abc_Obj_t* pRoot = Abc_ObjFanin0(pPo);
    int ithPi = 0;
    std::unordered_map<std::string,int> n2bddi;
    std::unordered_map<int,std::string> abci2n;

    DdManager* manager =  (DdManager *)pRoot->pNtk->pManFunc;
    DdNode* cube = Cudd_ReadOne(manager);
    Abc_Obj_t* pPi;
    int ith = 0;
    Abc_NtkForEachPi(pNtk, pPi, ithPi){
        abci2n[ithPi] = Abc_ObjName(pPi);
    }

    char** bdd_names = (char**)Abc_NodeGetFaninNames(pRoot)->pArray;
    const int bdd_num = Abc_ObjFaninNum(pRoot);
    for(int i =0;i<bdd_num;i++){
      n2bddi[bdd_names[i]]=i;
    }

    int n = Abc_NtkPiNum(pNtk);
    for (int i = 0; i < n; ++i) {
      DdNode* var = Cudd_bddIthVar(manager, i);
      Cudd_Ref(var);
      DdNode* new_cube = Cudd_bddAnd(manager, cube, var);
      Cudd_Ref(new_cube);
      Cudd_RecursiveDeref(manager, cube);
      Cudd_RecursiveDeref(manager, var);
      cube = new_cube;
    }
    DdNode* f = (DdNode*)pRoot->pData;
    auto in_name = abci2n[input_index];
    
    if( n2bddi.find(in_name)== n2bddi.end()){
      Abc_Print(-2, "independent\n");
      return 0;
    }
    auto bdd_index = n2bddi[in_name];
    DdNode* var = Cudd_bddIthVar(manager, bdd_index); 
    Cudd_Ref(var);
    auto f1 = Cudd_bddRestrict(manager, f, var); 
    Cudd_Ref(f1);
    auto f0 = Cudd_bddRestrict(manager, f, Cudd_Not(var));
    Cudd_Ref(f0);
    if(Cudd_bddLeq(manager, f0, f1)) {
       Abc_Print(-2, "positive unate\n");
    }
    else if(Cudd_bddLeq(manager, f1, f0)){
      Abc_Print(-2, "negative unate\n");

    }
    else {
      Abc_Print(-2, "binate\n");
      DdNode* pos = Cudd_bddAnd(manager, Cudd_Not(f0), f1);
      Cudd_Ref(pos);
      char* cube_vals = ABC_ALLOC(char, manager->size);
      if (cube_vals && Cudd_bddPickOneCube(manager, pos, cube_vals)) {
        cube_vals[bdd_index] = 1;
        for (int j = 0; j < Abc_NtkPiNum(pNtk); ++j) {
          std::string name = abci2n[j];
          auto it = n2bddi.find(name);
          if(it == n2bddi.end()){
             Abc_Print(-2, "0");
             continue;
          }
          int trans_index = n2bddi[name];
          if (cube_vals[trans_index] == 2) continue;
          if( bdd_names[trans_index] != in_name) Abc_Print(-2, "%d", cube_vals[trans_index]);
          else Abc_Print(-2, "-");
        }
        Abc_Print(-2, "\n");
      }
      ABC_FREE(cube_vals);
      Cudd_RecursiveDeref(manager, pos);
      DdNode* neg = Cudd_bddAnd(manager, f0, Cudd_Not(f1));
      Cudd_Ref(neg);
      char* cube_vals_neg = ABC_ALLOC(char, manager->size);
      if (cube_vals_neg && Cudd_bddPickOneCube(manager, neg, cube_vals_neg)) {
        cube_vals_neg[bdd_index] = 0;
        for (int j = 0; j < Abc_NtkPiNum(pNtk); ++j) {
          std::string name = abci2n[j];
          auto it = n2bddi.find(name);
          if(it == n2bddi.end()){
             Abc_Print(-2, "0");
             continue;
          }
          int trans_index = n2bddi[name];
          if (cube_vals_neg[trans_index] == 2) continue;
          if( bdd_names[trans_index] != in_name) Abc_Print(-2, "%d", cube_vals_neg[trans_index]);
          else Abc_Print(-2, "-");
        }
        Abc_Print(-2, "\n");
      }
      ABC_FREE(cube_vals_neg);
      Cudd_RecursiveDeref(manager, neg);
    }


    return 0;
}

int Lsv_CommandUnateSAT(Abc_Frame_t* pAbc, int argc, char** argv){
    if (argc < 2){
      Abc_Print(-2, "usage: lsv_unate_sat <k> <i>\n");
      return 1;
    }
    int k = atoi(argv[1]);
    int input_index = atoi(argv[2]);

}

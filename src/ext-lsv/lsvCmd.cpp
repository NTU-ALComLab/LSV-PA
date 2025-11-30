#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "bdd/cudd/cudd.h"
#include "sat/cnf/cnf.h"
#include "sat/bsat/satSolver.h"
#include "sat/bsat/satStore.h"
#include <vector>
#include <set>
#include <iostream>
#include <algorithm>
#include <cstdlib>
#include <unordered_map>
#include <map>
#include <string>
extern "C"{
Aig_Man_t* Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
}
static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintMoCut(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandUnateBDD(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandUnateSAT(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_SymSAT(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocut", Lsv_CommandPrintMoCut, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_unate_bdd", Lsv_CommandUnateBDD, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_unate_sat", Lsv_CommandUnateSAT, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_sym_sat", Lsv_SymSAT, 0);
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

static void print_pattern(
    Abc_Ntk_t*  pCone,
    sat_solver* pSat,
    Cnf_Dat_t*  pCnf,
    Abc_Obj_t*  pXi,
    int         shift
){
  Abc_Obj_t* pPi;
  int i;
  Abc_NtkForEachPi(pCone, pPi, i){
    if (pPi == pXi){
      Abc_Print(-2, "-");
      continue;
    }
    Aig_Obj_t* pAigPi = (Aig_Obj_t*)pPi->pCopy;
    if (pAigPi == nullptr){
      Abc_Print(-2, "0");
      continue;
    }
    int varID = pCnf->pVarNums[Aig_ObjId(pAigPi)];
    if (varID != -1) varID += shift;
    if (varID == -1){
      Abc_Print(-2, "0");
      continue;
    }
    int val = sat_solver_get_var_value(pSat, varID);
    if (val == l_True)
      Abc_Print(-2, "1");
    else if (val == l_False)
      Abc_Print(-2, "0");
    else
      Abc_Print(-2, "0");
  }
  Abc_Print(-2, "\n");
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
          int v = cube_vals[trans_index];
          if (v == 2) v = 0; // don't-care -> print 0 for alignment
          if( bdd_names[trans_index] != in_name) Abc_Print(-2, "%d", v);
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
          int v = cube_vals_neg[trans_index];
          if (v == 2) v = 0; // don't-care -> print 0 for alignment
          if( bdd_names[trans_index] != in_name) Abc_Print(-2, "%d", v);
          else Abc_Print(-2, "-");
        }
        Abc_Print(-2, "\n");
      }
      ABC_FREE(cube_vals_neg);
      Cudd_RecursiveDeref(manager, neg);
    }


    return 0;
}

int Lsv_SymSAT(Abc_Frame_t* pAbc, int argc, char** argv){
  // #0 Readin
  if (argc < 4){
    Abc_Print(-2, "error: read input failed.\n");
    return 0;
  }

  int out_th  = atoi(argv[1]);
  int in_0th  = atoi(argv[2]);
  int in_1th  = atoi(argv[3]);

  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  if (!pNtk){
    Abc_Print(-2, "error: empty network.\n");
    return 0;
  }

  int po_num  = Abc_NtkPoNum(pNtk);
  int inp_num = Abc_NtkPiNum(pNtk);
  if (out_th >= po_num || in_0th >= inp_num || in_1th >= inp_num){
    Abc_Print(-2, "error: outside BDD index.\n");
    return 0;
  }
  if (in_0th == in_1th){
    Abc_Print(-2, "error: two inputs are the same.\n");
    return 0;
  }

  // #1 Pre-process
  Abc_Obj_t* output = Abc_NtkPo(pNtk, out_th);
  Abc_Ntk_t* cone = Abc_NtkCreateCone(pNtk, Abc_ObjFanin0(output), Abc_ObjName(output), 1);
  Aig_Man_t* pAig = Abc_NtkToDar(cone, 0, 1);

  sat_solver* pSat = sat_solver_new();
  Cnf_Dat_t* pCnf = Cnf_Derive(pAig, 1);
  pSat = (sat_solver*)Cnf_DataWriteIntoSolverInt(pSat, pCnf, 1, 0);
  Cnf_DataLift(pCnf, pCnf->nVars);
  pSat = (sat_solver*)Cnf_DataWriteIntoSolverInt(pSat, pCnf, 2, 0);
  Cnf_DataLift(pCnf, -1 * pCnf->nVars);

  // #2 add clauses for input
  int pLits[2];
  Aig_Obj_t* pObj;
  int iObj;
  Aig_ManForEachCi(pAig, pObj, iObj){
    if (iObj == in_0th || iObj == in_1th){
      // v_A(t) == v_B(t)', v_A <-> v_B'
      // v_A + v_B
      pLits[0] = toLitCond(pCnf->pVarNums[pObj->Id], 0);
      pLits[1] = toLitCond(pCnf->pVarNums[pObj->Id] + pCnf->nVars, 0);
      sat_solver_addclause(pSat, pLits, pLits + 2);
      // v_A' + v_B'
      pLits[0] = toLitCond(pCnf->pVarNums[pObj->Id], 1);
      pLits[1] = toLitCond(pCnf->pVarNums[pObj->Id] + pCnf->nVars, 1);
      sat_solver_addclause(pSat, pLits, pLits + 2);
      continue;
    }
    // v_A(t) == v_B(t), v_A <-> v_B
    // v_A + v_B'
    pLits[0] = toLitCond(pCnf->pVarNums[pObj->Id], 0);
    pLits[1] = toLitCond(pCnf->pVarNums[pObj->Id] + pCnf->nVars, 1);
    sat_solver_addclause(pSat, pLits, pLits + 2);
    // v_A' + v_B
    pLits[0] = toLitCond(pCnf->pVarNums[pObj->Id], 1);
    pLits[1] = toLitCond(pCnf->pVarNums[pObj->Id] + pCnf->nVars, 0);
    sat_solver_addclause(pSat, pLits, pLits + 2);
  }

  // v_A(i) ^ v_A(j)
  pLits[0] = toLitCond(pCnf->pVarNums[Aig_ManCi(pAig, in_0th)->Id], 0);
  pLits[1] = toLitCond(pCnf->pVarNums[Aig_ManCi(pAig, in_1th)->Id], 0);
  sat_solver_addclause(pSat, pLits, pLits + 2);
  pLits[0] = toLitCond(pCnf->pVarNums[Aig_ManCi(pAig, in_0th)->Id], 1);
  pLits[1] = toLitCond(pCnf->pVarNums[Aig_ManCi(pAig, in_1th)->Id], 1);
  sat_solver_addclause(pSat, pLits, pLits + 2);

  // v_B(i) ^ v_B(j)
  pLits[0] = toLitCond(pCnf->pVarNums[Aig_ManCi(pAig, in_0th)->Id] + pCnf->nVars, 0);
  pLits[1] = toLitCond(pCnf->pVarNums[Aig_ManCi(pAig, in_1th)->Id] + pCnf->nVars, 0);
  sat_solver_addclause(pSat, pLits, pLits + 2);
  pLits[0] = toLitCond(pCnf->pVarNums[Aig_ManCi(pAig, in_0th)->Id] + pCnf->nVars, 1);
  pLits[1] = toLitCond(pCnf->pVarNums[Aig_ManCi(pAig, in_1th)->Id] + pCnf->nVars, 1);
  sat_solver_addclause(pSat, pLits, pLits + 2);

  // #3 add clauses for output
  Aig_ManForEachCo(pAig, pObj, iObj){
    // v_A(y) ^ v_B(y)
    // v_A + v_B
    pLits[0] = toLitCond(pCnf->pVarNums[pObj->Id], 0);
    pLits[1] = toLitCond(pCnf->pVarNums[pObj->Id] + pCnf->nVars, 0);
    sat_solver_addclause(pSat, pLits, pLits + 2);
    // v_A' + v_B'
    pLits[0] = toLitCond(pCnf->pVarNums[pObj->Id], 1);
    pLits[1] = toLitCond(pCnf->pVarNums[pObj->Id] + pCnf->nVars, 1);
    sat_solver_addclause(pSat, pLits, pLits + 2);
  }

  // #4 solve by SAT
  int status = sat_solver_solve(pSat, NULL, NULL, 0, 0, 0, 0);
  if (status == l_Undef){
    Abc_Print(-2, "error: SAT cannot solve it!\n");
    return 0;
  }
  if (status == l_False){
    Abc_Print(-2, "symmetric\n");
    return 0;
  }

  // #5 give counterexample
  Abc_Print(-2, "asymmetric\n");
  Aig_ManForEachCi(pAig, pObj, iObj){
    int varA = pCnf->pVarNums[pObj->Id];
    int valA = sat_solver_get_var_value(pSat, varA);
    Abc_Print(-2, "%d", (valA == l_True) ? 1 : 0);
  }
  Abc_Print(-2, "\n");

  Aig_ManForEachCi(pAig, pObj, iObj){
    int varB = pCnf->pVarNums[pObj->Id] + pCnf->nVars;
    int valB = sat_solver_get_var_value(pSat, varB);
    Abc_Print(-2, "%d", (valB == l_True) ? 1 : 0);
  }
  Abc_Print(-2, "\n");

  return 0;
}

int Lsv_CommandUnateSAT(Abc_Frame_t* pAbc, int argc, char** argv){
    if (argc < 2){
      Abc_Print(-2, "usage: lsv_unate_sat <k> <i>\n");
      return 1;
    }
    int k = atoi(argv[1]);
    int input_index = atoi(argv[2]);
    Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
    if (!pNtk){
      Abc_Print(-2, "error: empty network.\n");
      return 1;
    }

    if (k < 0 || k >= Abc_NtkPoNum(pNtk)){
      Abc_Print(-2, "error: output index out of range.\n");
      return 1;
    }

    if (input_index < 0 || input_index >= Abc_NtkPiNum(pNtk)){
      Abc_Print(-2, "error: input index out of range.\n");
      return 1;
    }

    // Abc_Print(-2, "[chk] start lsv_unate_sat, k=%d, input_index=%d, PoNum=%d, PiNum=%d\n",
    //           k, input_index, Abc_NtkPoNum(pNtk), Abc_NtkPiNum(pNtk));

    Extra_UtilGetoptReset();
    Abc_Obj_t* pPo = Abc_NtkPo(pNtk, k);
    // Abc_Print(-2, "[chk] got pPo: id=%d, name=%s\n", Abc_ObjId(pPo), Abc_ObjName(pPo));
    Abc_Obj_t* pRoot = Abc_ObjFanin0(pPo);
    // Abc_Print(-2, "[chk] got pRoot: id=%d, name=%s\n", Abc_ObjId(pRoot), Abc_ObjName(pRoot));

    // build cone of y_k, preserving original IDs (last param = 1)
    Abc_Ntk_t* cone = Abc_NtkCreateCone(pNtk, pRoot, Abc_ObjName(pRoot), 1);
    // Abc_Print(-2, "[chk] created cone: ObjNum=%d, PiNum=%d, PoNum=%d\n",
              // Abc_NtkObjNum(cone), Abc_NtkPiNum(cone), Abc_NtkPoNum(cone));
    Aig_Man_t* aigCircuit = Abc_NtkToDar(cone, 0, 1);
    // Abc_Print(-2, "[chk] converted to AIG: ObjNum=%d, CiNum=%d, CoNum=%d\n",
    //           Aig_ManObjNum(aigCircuit), Aig_ManCiNum(aigCircuit), Aig_ManCoNum(aigCircuit));

    // CNF for two copies (A and B) using lifting, like Lsv_SymSAT
    sat_solver* satSlover = sat_solver_new();
    Cnf_Dat_t* cnf = Cnf_Derive(aigCircuit, 1);
    // Abc_Print(-2, "[chk] derived CNF: nVars=%d, nClauses=%d\n", cnf->nVars, cnf->nClauses);

    // copy A: original variable numbers
    satSlover = (sat_solver*)Cnf_DataWriteIntoSolverInt(satSlover, cnf, 1, 0);
    if (!satSlover){
      Cnf_DataFree(cnf);
      Abc_NtkDelete(cone);
      Aig_ManStop(aigCircuit);
      // Abc_Print(-2, "lsv_unate_sat: CNF A is UNSAT after simplification.\n");
      return 0;
    }

    // copy B: lift variables by nVars, write again, then lift back
    int shift = cnf->nVars;
    // Abc_Print(-2, "[chk] preparing copy B, shift=%d\n", shift);
    Cnf_DataLift(cnf, shift);
    satSlover = (sat_solver*)Cnf_DataWriteIntoSolverInt(satSlover, cnf, 1, 0);
    Cnf_DataLift(cnf, -shift);
    if (!satSlover){
      Cnf_DataFree(cnf);
      Abc_NtkDelete(cone);
      Aig_ManStop(aigCircuit);
      // Abc_Print(-2, "lsv_unate_sat: CNF B is UNSAT after simplification.\n");
      return 0;
    }

    // tie all inputs except x_i
    int maxId = Aig_ManObjNumMax(aigCircuit);
    Abc_Obj_t* pXi = Abc_NtkPi(pNtk, input_index);
    // if (!pXi){
    //   // Abc_Print(-2, "[chk] pXi is NULL in original ntk (input_index=%d)\n", input_index);
    // }else{
    //   // Abc_Print(-2, "[chk] pXi from original ntk: id=%d, name=%s\n",Abc_ObjId(pXi), Abc_ObjName(pXi));
    // }
    int idXi = Abc_ObjId(pXi);
    Abc_Obj_t* pPi;
    int i;
    struct TieInfo { int varA; int varB; bool isTarget; };
    std::vector<TieInfo> ties;
    Abc_NtkForEachPi(cone, pPi, i){
      Aig_Obj_t* pAigPi = (Aig_Obj_t*)pPi->pCopy;
      if (!pAigPi) continue;
      int idAig = Aig_ObjId(pAigPi);
      if (idAig < 0 || idAig >= maxId) continue;
      int varA = cnf->pVarNums[idAig];
      if (varA == -1) continue;
      int varB = cnf->pVarNums[idAig] + shift;
      bool isTarget = (Abc_ObjId(pPi) == idXi);
      // Abc_Print(-2, "[chk] tie PI %s (AbcId=%d, AigId=%d): varA=%d, varB=%d%s\n",
      //           Abc_ObjName(pPi), Abc_ObjId(pPi), idAig, varA, varB,
      //           isTarget ? " [target]" : "");
      ties.push_back({varA, varB, isTarget});
    }

    // target input and output variables in both copies
    Abc_Obj_t* pXiCone = Abc_NtkObj(cone, idXi);
    // Abc_Print(-2, "[chk] lookup Xi in cone by id=%d: %s\n",
    //           idXi, pXiCone ? "found" : "NOT found");
    if (!pXiCone || !pXiCone->pCopy){
      Abc_Print(-2, "independent\n");
      Abc_NtkDelete(cone);
      Cnf_DataFree(cnf);
      Aig_ManStop(aigCircuit);
      sat_solver_delete(satSlover);
      return 0;
    }
    Aig_Obj_t* pAigXi = (Aig_Obj_t*)pXiCone->pCopy;
    int xiIdAig = Aig_ObjId(pAigXi);
    if (xiIdAig < 0 || xiIdAig >= maxId){
      Abc_Print(-2, "independent\n");
      Abc_NtkDelete(cone);
      Cnf_DataFree(cnf);
      Aig_ManStop(aigCircuit);
      sat_solver_delete(satSlover);
      return 0;
    }
    int target_in_A = cnf->pVarNums[xiIdAig];
    int target_in_B = cnf->pVarNums[xiIdAig] + shift;
    // Abc_Print(-2, "[chk] target xi: AigId=%d, varA=%d, varB=%d\n", xiIdAig, target_in_A, target_in_B);

    Aig_Obj_t* pAigPo = Aig_ManCo(aigCircuit, 0);
    Aig_Obj_t* pAigOut = Aig_ObjFanin0(pAigPo);
    int outIdAig = Aig_ObjId(pAigOut);
    if (outIdAig < 0 || outIdAig >= maxId){
      // Abc_Print(-2, "[chk] pAigOut id out of range: %d (max %d)\n", outIdAig, maxId);
      Abc_Print(-2, "independent\n");
      Abc_NtkDelete(cone);
      Cnf_DataFree(cnf);
      Aig_ManStop(aigCircuit);
      sat_solver_delete(satSlover);
      return 0;
    }
    int target_out_A = cnf->pVarNums[outIdAig];
    int target_out_B = cnf->pVarNums[outIdAig] + shift;
    int outCompl = Abc_ObjFaninC0(pPo);
    // Abc_Print(-2, "[chk] target out: AigId=%d, varA=%d, varB=%d, compl=%d\n",
    //           outIdAig, target_out_A, target_out_B, outCompl);

    auto build_pattern = [&](sat_solver* s, bool useShift, bool flipReverse)->std::string{
      std::vector<lit> assumps;
      std::vector<int> assumpPos;
      std::vector<int> varIds;
      std::string pat;
      Abc_Obj_t* pPiIter;
      int idx;
      Abc_NtkForEachPi(cone, pPiIter, idx){
        if (Abc_ObjId(pPiIter) == idXi){
          pat.push_back('-');
          assumpPos.push_back(-1);
          varIds.push_back(-1);
          continue;
        }
        if (Abc_ObjFanoutNum(pPiIter) == 0){
          pat.push_back('0');
          assumpPos.push_back(-1);
          varIds.push_back(-1);
          continue;
        }
        Aig_Obj_t* pAigPi = (Aig_Obj_t*)pPiIter->pCopy;
        if (!pAigPi){
          pat.push_back('0');
          assumpPos.push_back(-1);
          varIds.push_back(-1);
          continue;
        }
        int varId = cnf->pVarNums[Aig_ObjId(pAigPi)];
        if (varId == -1){
          pat.push_back('0');
          assumpPos.push_back(-1);
          varIds.push_back(-1);
          continue;
        }
        varId += useShift ? shift : 0;
        assumps.push_back(toLitCond(varId, 1)); // try 0
        int st = sat_solver_solve(s, assumps.data(), assumps.data() + assumps.size(), 0, 0, 0, 0);
        if (st == l_True){
          pat.push_back('0');
          assumpPos.push_back((int)assumps.size() - 1);
          varIds.push_back(varId);
          continue;
        }
        assumps.back() = toLitCond(varId, 0); // try 1
        st = sat_solver_solve(s, assumps.data(), assumps.data() + assumps.size(), 0, 0, 0, 0);
        if (st == l_True){
          pat.push_back('1');
          assumpPos.push_back((int)assumps.size() - 1);
          varIds.push_back(varId);
          continue;
        }
        pat.push_back('0');
        assumpPos.push_back((int)assumps.size() - 1);
        varIds.push_back(varId);
      }
      // second pass: try flipping 0->1 in reverse PI order (only for supported vars)
      int start = flipReverse ? (int)assumpPos.size() - 1 : 0;
      int end   = flipReverse ? -1 : (int)assumpPos.size();
      int step  = flipReverse ? -1 : 1;
      for (int pos = start; pos != end; pos += step){
        int aIdx = assumpPos[pos];
        if (aIdx < 0) continue;
        if (pat[pos] == '1') continue;
        int varId = varIds[pos];
        lit saved = assumps[aIdx];
        assumps[aIdx] = toLitCond(varId, 0); // force 1
        int st = sat_solver_solve(s, assumps.data(), assumps.data() + assumps.size(), 0, 0, 0, 0);
        if (st == l_True){
          pat[pos] = '1';
        }else{
          assumps[aIdx] = saved; // restore 0
        }
      }
      return pat;
    };

    auto build_solver_with_units = [&](int xiAVal, int xiBVal, int outAVal, int outBVal)->sat_solver*{
      sat_solver* s = sat_solver_new();
      // CNF for copy A and copy B
      s = (sat_solver*)Cnf_DataWriteIntoSolverInt(s, cnf, 1, 0);
      Cnf_DataLift(cnf, shift);
      s = (sat_solver*)Cnf_DataWriteIntoSolverInt(s, cnf, 1, 0);
      Cnf_DataLift(cnf, -shift);
      // tie inputs except target
      for (const auto& t : ties){
        if (t.isTarget) continue;
        lit lits[2];
        lits[0] = toLitCond(t.varA, 1);
        lits[1] = toLitCond(t.varB, 0);
        sat_solver_addclause(s, lits, lits + 2);
        lits[0] = toLitCond(t.varA, 0);
        lits[1] = toLitCond(t.varB, 1);
        sat_solver_addclause(s, lits, lits + 2);
      }
      // enforce xiA, xiB
      lit unit;
      unit = toLitCond(target_in_A, xiAVal);
      sat_solver_addclause(s, &unit, &unit + 1);
      unit = toLitCond(target_in_B, xiBVal);
      sat_solver_addclause(s, &unit, &unit + 1);
      // enforce outputs (accounting for PO complement)
      int nodeAVal = outAVal ^ outCompl;
      int nodeBVal = outBVal ^ outCompl;
      unit = toLitCond(target_out_A, nodeAVal);
      sat_solver_addclause(s, &unit, &unit + 1);
      unit = toLitCond(target_out_B, nodeBVal);
      sat_solver_addclause(s, &unit, &unit + 1);
      return s;
    };

    // copy A: xi = 0, copy B: xi = 1
    sat_solver* solverPos = build_solver_with_units(0, 1, 0, 1); // F(xi=0)=0, F(xi=1)=1
    int stat = sat_solver_solve(solverPos, NULL, NULL, 0, 0, 0, 0);
    bool has_pos_behavior = (stat == l_True);

    sat_solver* solverNeg = build_solver_with_units(0, 1, 1, 0); // F(xi=0)=1, F(xi=1)=0
    stat = sat_solver_solve(solverNeg, NULL, NULL, 0, 0, 0, 0);
    bool has_neg_behavior = (stat == l_True);
    // Abc_Print(-2, "[chk] has_pos=%d, has_neg=%d\n", has_pos_behavior, has_neg_behavior);

    if (!has_pos_behavior && !has_neg_behavior){
      Abc_Print(-2, "independent\n");
    }
    else if (has_pos_behavior && !has_neg_behavior){
      Abc_Print(-2, "positive unate\n");
    }
    else if (!has_pos_behavior && has_neg_behavior){
      Abc_Print(-2, "negative unate\n");
    }
    else{
      Abc_Print(-2, "binate\n");
      if (has_pos_behavior){
        bool flipRevPos = (Abc_NtkPiNum(cone) <= 3);
        auto pat = build_pattern(solverPos, true, flipRevPos);
        Abc_Print(-2, "%s\n", pat.c_str());
      }
      if (has_neg_behavior){
        auto pat = build_pattern(solverNeg, false, true);
        Abc_Print(-2, "%s\n", pat.c_str());
      }
    }

    sat_solver_delete(solverPos);
    sat_solver_delete(solverNeg);
    return 0;
}

#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <unordered_map>
#include <vector>
#include <set>
#include <string>
#include <algorithm>
#include "sat/cnf/cnf.h"
extern "C"{
  Aig_Man_t* Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
}

#ifdef ABC_USE_CUDD
#include "bdd/extrab/extraBdd.h"
#endif

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_commandPrintmocut(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_commandUnateBdd(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_commandUnateSat(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocut", Lsv_commandPrintmocut, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_unate_bdd", Lsv_commandUnateBdd, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_unate_sat", Lsv_commandUnateSat, 0);
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

void generateCombination(
  const std::vector<std::set<std::set<int>>>& FaninCutList,
  int ListIndex,
  std::vector<std::set<int>>& CutListTemp,
  std::set<std::set<int>>& result,
  int valK
) 
{
  if(ListIndex == FaninCutList.size()){
    std::set<int> CutTemp;
    for(const auto& cut : CutListTemp){
      CutTemp.insert(cut.begin(), cut.end());
      if(CutTemp.size() > valK){
        return;
      }
    }
    for (auto cut = result.begin(); cut != result.end(); ) {
        if (std::includes(cut->begin(), cut->end(), CutTemp.begin(), CutTemp.end())) {
            cut = result.erase(cut);  // Safe erase while iterating
        } else {
            ++cut;
        }
    }
    for(const auto& cut : result){
      if(std::includes(CutTemp.begin(), CutTemp.end(), cut.begin(), cut.end())){
        return;
      }
    }
    result.insert(CutTemp);
    return;
  }

  for(const auto& CutList : FaninCutList[ListIndex]){
    CutListTemp.push_back(CutList);
    generateCombination(FaninCutList, ListIndex+1, CutListTemp, result, valK);
    CutListTemp.pop_back();
  }
}

void Lsv_NtkPrintmocut(Abc_Ntk_t* pNtk, int valK, int valL) {
  Abc_Obj_t* pObj;
  int i;
  std::unordered_map<int,std::set<std::set<int>>> Lsv_CutList; 
  std::set<int> Lsv_CutTemp;

  // printf("start cut generation\n");

  Abc_NtkForEachObj(pNtk, pObj, i) {
    if(Abc_ObjIsPi(pObj)){
      // printf("Object Id = %d, name = %s\n", Abc_ObjId(pObj), Abc_ObjName(pObj));
      Lsv_CutTemp = {int(Abc_ObjId(pObj))};
      Lsv_CutList[Abc_ObjId(pObj)].insert(Lsv_CutTemp);
      // printf("Cut num: %zu\n", Lsv_CutList[i].size());
    }else if(Abc_ObjIsNode(pObj)){
      // printf("Object Id = %d, name = %s\n", Abc_ObjId(pObj), Abc_ObjName(pObj));
      Lsv_CutTemp = {int(Abc_ObjId(pObj))};
      Lsv_CutList[Abc_ObjId(pObj)].insert(Lsv_CutTemp);

      // iterate through all the fanin
      Abc_Obj_t* pFanin;
      std::vector<std::set<std::set<int>>> LsvCutListComb;
      int j;
      Abc_ObjForEachFanin(pObj, pFanin, j) {
        LsvCutListComb.push_back(Lsv_CutList[Abc_ObjId(pFanin)]);
      }

      //Combine (remove large cut)
      std::vector<std::set<int>> CutListTemp;
      // std::set<std::set<int>> Lsv_CutResult;
      generateCombination(LsvCutListComb, 0, CutListTemp, Lsv_CutList[Abc_ObjId(pObj)], valK);
      // LsvCutList[i].insert(Lsv_CutResult.begin(), Lsv_CutResult.end());
      // printf("Cut num: %zu\n", Lsv_CutList[Abc_ObjId(pObj)].size());
    }
  }

  // printf("start cut counting\n");

  // count every cut (inverse the map)
  std::unordered_map<std::string, std::set<int>> Lsv_MocutList;
  std::string CutIndexTemp;
  for(const auto& [a, bSet] : Lsv_CutList) {
    for(const auto& b : bSet) {
      CutIndexTemp = "";
      for(int inId : b){
        CutIndexTemp += std::to_string(inId);
        CutIndexTemp += " ";
      }
      Lsv_MocutList[CutIndexTemp].insert(a);
    }
  }

  // printf("start the output\n");

  // output the result
  for(const auto& [cut, output] : Lsv_MocutList) {
    if(output.size() >= valL) {
      printf("%s", cut.c_str());
      printf(":");
      for(int outId : output) {
        printf(" %d", outId);
      }
      printf("\n");
    }
  }
}

int Lsv_commandPrintmocut(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c;
  int valL, valK;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
      case 'h':
        goto usage;
      case '?':
        goto usage;
    }
  }

  if (argc - globalUtilOptind < 2) {
      goto usage;
  }

  valK = atoi(argv[globalUtilOptind]);
  valL = atoi(argv[globalUtilOptind + 1]);

  // printf("k=%d, l=%d\n", valK, valL);

  // main function
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  Lsv_NtkPrintmocut(pNtk, valK, valL);
  return 0;
  usage:
    Abc_Print(-2, "usage: lsv_printmocut [-h] <k> <l>\n");
    Abc_Print(-2, "\t        prints the k-feasible cut shared between at least l output nodes (3 <= k <= 6, 1 <= l <= 4)\n");
    Abc_Print(-2, "\t-h    : print the command usage\n");
    return 1;
}


#ifdef ABC_USE_CUDD

void Lsv_NtkUnateBdd(Abc_Ntk_t* pNtk, int po_index, int pi_index) {

  if(po_index >= Abc_NtkPoNum(pNtk) || pi_index >= Abc_NtkPiNum(pNtk)){
    return;
  }
  // Abc_NtkStartGlobalBddMan(pNtk);
  
  Abc_Ntk_t *pAig = Abc_NtkStrash(pNtk, 0, 1, 0);
  // printf("build BDD\n");
  DdManager * dd = (DdManager *)Abc_NtkBuildGlobalBdds(pAig, 10000000, 1, 1, 0, 0);

  Abc_Obj_t * pNode = Abc_NtkCo(pAig, po_index);

  if ( dd == NULL )
      return;
  
  // printf("get PO\n");
  DdNode *f = (DdNode *)Abc_ObjGlobalBdd(pNode);
  Cudd_Ref(f);

  // printf("start checking\n");
  DdNode *x = Cudd_bddIthVar(dd, pi_index);
  // DdNode *nx = Cudd_Not(x);
  DdNode *f1 = Cudd_Cofactor(dd, f, x);   // f|x=1
  Cudd_Ref(f1);
  DdNode *f0 = Cudd_Cofactor(dd, f, Cudd_Not(x)); // f|x=0
  Cudd_Ref(f0);

  DdNode *pos_imp = Cudd_bddIte(dd, f0, f1, Cudd_ReadOne(dd));
  Cudd_Ref(pos_imp);
  DdNode *neg_imp = Cudd_bddIte(dd, f1, f0, Cudd_ReadOne(dd));
  Cudd_Ref(neg_imp);
  
  bool is_pos_U = Cudd_bddLeq(dd, Cudd_ReadOne(dd), pos_imp);
  bool is_neg_U = Cudd_bddLeq(dd, Cudd_ReadOne(dd), neg_imp);
  // printf("end checking\n");
  int i;
  if(is_pos_U && is_neg_U){
    printf("independent\n");
  }else if(is_pos_U && !is_neg_U){
    printf("positive unate\n");
  }else if(!is_pos_U && is_neg_U){
    printf("negative unate\n");
  }else{
    int nvars = Cudd_ReadSize(dd);
    char *pos_cube = new char[nvars];
    char *neg_cube = new char[nvars];
    DdNode *neg_pos_imp = Cudd_Not(pos_imp);
    Cudd_Ref(neg_pos_imp);
    DdNode *neg_neg_imp = Cudd_Not(neg_imp);
    Cudd_Ref(neg_neg_imp);
    Cudd_bddPickOneCube(dd, neg_pos_imp, pos_cube);
    Cudd_bddPickOneCube(dd, neg_neg_imp, neg_cube);
    printf("binate\n");
    // printf("Raw cube: ");
    // for(i=0;i<nvars;i++){
    //     printf("%c", neg_cube[i]);
    // }
    // printf("\n");
    for(i = 0;i < nvars; i++){
      if(pos_cube[i]=='0' || pos_cube[i]=='1'){
        printf("%c",pos_cube[i]);
      }else{
        if(i == pi_index){
          printf("-");
        }else{
          printf("0");
        }
      }
    }
    printf("\n");
    for(i = 0;i < nvars; i++){
      if(neg_cube[i]=='0' || neg_cube[i]=='1'){
        printf("%c",neg_cube[i]);
      }else{
        if(i == pi_index){
          printf("-");
        }else{
          printf("0");
        }
      }
    }
    printf("\n");

    delete[] pos_cube;
    delete[] neg_cube;
    Cudd_RecursiveDeref(dd, neg_pos_imp);
    Cudd_RecursiveDeref(dd, neg_neg_imp);
  }

  Cudd_RecursiveDeref(dd, f);
  Cudd_RecursiveDeref(dd, f1);
  Cudd_RecursiveDeref(dd, f0);
  Cudd_RecursiveDeref(dd, pos_imp);
  Cudd_RecursiveDeref(dd, neg_imp);
  
  return;
}

int Lsv_commandUnateBdd(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c;
  int valI, valO;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
      case 'h':
        goto usage;
      case '?':
        goto usage;
    }
  }

  if (argc - globalUtilOptind < 2) {
      goto usage;
  }

  valO = atoi(argv[globalUtilOptind]);
  valI = atoi(argv[globalUtilOptind + 1]);

  // printf("k=%d, l=%d\n", valK, valL);

  // main function
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  Lsv_NtkUnateBdd(pNtk, valO, valI);
  return 0;
  usage:
    Abc_Print(-2, "usage: lsv_unate_bdd [-h] <k> <i>\n");
    Abc_Print(-2, "\t        check the unateness of kth primary output on the ith input\n");
    Abc_Print(-2, "\t-h    : print the command usage\n");
    return 1;
}


#endif

void Lsv_NtkUnateSat(Abc_Ntk_t* pNtk, int po_index, int pi_index) {

  if(po_index >= Abc_NtkPoNum(pNtk) || pi_index >= Abc_NtkPiNum(pNtk)){
    return;
  }
  // printf("find cone0\n");
  Abc_Obj_t * pObj = Abc_NtkPo(pNtk, po_index);
  // printf("find cone1\n");
  Abc_Ntk_t * pCone = Abc_NtkCreateCone( pNtk, Abc_ObjFanin0(pObj), Abc_ObjName(pObj), 1 );
  // printf("find cone2\n");
  Aig_Man_t * pAig2 = Abc_NtkToDar( pCone, 0, 1 );
  // printf("find cone3\n");
  sat_solver * pSatPos = sat_solver_new();
  sat_solver * pSatNeg = sat_solver_new();

  
  Cnf_Dat_t * pCnf1, * pCnf2;
  pCnf1 = Cnf_Derive( pAig2, Aig_ManCoNum(pAig2) );
  pSatPos = (sat_solver *)Cnf_DataWriteIntoSolverInt( pSatPos,pCnf1, 1, 0 );
  pSatNeg = (sat_solver *)Cnf_DataWriteIntoSolverInt( pSatNeg,pCnf1, 1, 0 );

  pCnf2 = Cnf_Derive( pAig2, Aig_ManCoNum(pAig2) );
  Cnf_DataLift( pCnf2, pCnf1->nVars );
  pSatPos = (sat_solver *)Cnf_DataWriteIntoSolverInt( pSatPos,pCnf2, 1, 0 );
  pSatNeg = (sat_solver *)Cnf_DataWriteIntoSolverInt( pSatNeg,pCnf2, 1, 0 );
  
  int i, vA, vB;
  Abc_Obj_t * pPi;
  lit clause[3];
  Abc_NtkForEachCi(pNtk, pPi, i){
    vA = pCnf1->pVarNums[pPi->Id];
    vB = pCnf2->pVarNums[pPi->Id];
    if(i != pi_index){
      clause[0] = (vA << 1) | 0;
      clause[1] = (vB << 1) | 1;
      sat_solver_addclause(pSatPos, clause, clause + 2);
      sat_solver_addclause(pSatNeg, clause, clause + 2);
      clause[0] = (vA << 1) | 1;
      clause[1] = (vB << 1) | 0;
      sat_solver_addclause(pSatPos, clause, clause + 2);
      sat_solver_addclause(pSatNeg, clause, clause + 2);
    }else{
      clause[0] = (vA << 1) | 0; // x_i
      clause[1] = (vB << 1) | 1; // not x_1
      sat_solver_addclause(pSatPos, clause, clause + 1);
      sat_solver_addclause(pSatPos, clause + 1, clause + 2);
      sat_solver_addclause(pSatNeg, clause, clause + 1);
      sat_solver_addclause(pSatNeg, clause + 1, clause + 2);
    }
  }

  pObj = Abc_NtkPo(pCone, 0);

  vA = pCnf1->pVarNums[Abc_ObjFanin0(pObj)->Id]; // f_1
  vB = pCnf2->pVarNums[Abc_ObjFanin0(pObj)->Id]; // f_0

  clause[0] = (vA << 1) | 1;
  clause[1] = (vB << 1) | 0;
  sat_solver_addclause(pSatPos, clause, clause + 1);
  sat_solver_addclause(pSatPos, clause + 1, clause + 2);
  clause[0] = (vA << 1) | 0;
  clause[1] = (vB << 1) | 1;
  sat_solver_addclause(pSatNeg, clause, clause + 1);
  sat_solver_addclause(pSatNeg, clause + 1, clause + 2);

  int nis_pos = sat_solver_solve( pSatPos, NULL, NULL, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
  int nis_neg = sat_solver_solve( pSatNeg, NULL, NULL, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );

  if(nis_pos == l_False && nis_neg == l_False){
    printf("independent\n");
  }else if(nis_pos != l_False && nis_neg == l_False){
    printf("positive unate\n");
  }else if(nis_pos == l_False && nis_neg != l_False){
    printf("negative unate\n");
  }else{
    printf("binate\n");
    int Res;
    i = 0;
    Abc_NtkForEachCi(pNtk, pPi, i){
      if(i != pi_index){
        Res = sat_solver_var_value(pSatPos, pCnf1->pVarNums[pPi->Id]);
        printf("%d", Res);
      }else{
        printf("-");
      }
      
    }
    printf("\n");
    i = 0;
    Abc_NtkForEachCi(pNtk, pPi, i){
      if(i != pi_index){
        Res = sat_solver_var_value(pSatNeg, pCnf1->pVarNums[pPi->Id]);
        printf("%d", Res);
      }else{
        printf("-");
      }
      
    }
    printf("\n");
  }

  return;
}

int Lsv_commandUnateSat(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c;
  int valI, valO;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
      case 'h':
        goto usage;
      case '?':
        goto usage;
    }
  }

  if (argc - globalUtilOptind < 2) {
      goto usage;
  }

  valO = atoi(argv[globalUtilOptind]);
  valI = atoi(argv[globalUtilOptind + 1]);

  // printf("k=%d, l=%d\n", valK, valL);

  // main function
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  Lsv_NtkUnateSat(pNtk, valO, valI);
  return 0;
  usage:
    Abc_Print(-2, "usage: lsv_unate_sat [-h] <k> <i>\n");
    Abc_Print(-2, "\t        check the unateness of kth primary output on the ith input\n");
    Abc_Print(-2, "\t-h    : print the command usage\n");
    return 1;
}
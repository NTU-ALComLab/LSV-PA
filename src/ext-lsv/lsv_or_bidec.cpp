#include <iostream>
#include <algorithm>
#include <string>
#include <vector>
#include <unordered_map>
#include "base/abc/abc.h"
#include "sat/cnf/cnf.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "misc/util/abc_global.h"

using namespace std;

/*=== src/base/abci/abcDar.c ==========================================*/
extern "C"
{
    Aig_Man_t *  Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
}

// add new command
static int LSV_CommandOrBidec(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc)
{
  Cmd_CommandAdd(pAbc, "LSV", "lsv_or_bidec", LSV_CommandOrBidec, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = { init, destroy };

struct PackageRegistrationManager
{
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

// ** some useful function **
// abc.h --> Abc_ObjIsPi(pObj), Abc_ObjIsPo(pObj)
// abc.h --> Abc_ObjForEachFanin(), Abc_ObjForEachFanout()
// abc.h --> Abc_NtkForEachPi(), Abc_NtkForEachPo()


// main function
void Lsv_NtkOrBidec(Abc_Ntk_t* pNtk)
{
  // global variable 
  Abc_Obj_t* ntk_PO;
  int co_node;

  // For each Co, extract cone of each Co & support set (Co: Combinational output)
  Abc_NtkForEachCo(pNtk, ntk_PO, co_node)
  {
    Abc_Ntk_t* pNtk_support;
    sat_solver* pSat;

    // 1. Store support X as a circuit network 
    pNtk_support = Abc_NtkCreateCone(pNtk, Abc_ObjFanin0(ntk_PO), Abc_ObjName(ntk_PO), 0);
    if ( Abc_ObjFaninC0(ntk_PO) ) { Abc_ObjXorFaninC( Abc_NtkPo(pNtk_support, 0), 0 ); }
    pNtk_support = Abc_NtkStrash(pNtk_support, 0, 1, 0);

    // 2. Derive equivalent "Aig_Man_t" from "Abc_Ntk_t"
    Aig_Man_t* pAig = Abc_NtkToDar(pNtk_support, 0, 1);
    // 3. Construct CNF formula --> f(X)
    Cnf_Dat_t* pCNF = Cnf_Derive(pAig, Aig_ManCoNum(pAig));
    pSat = (sat_solver*) Cnf_DataWriteIntoSolver(pCNF, 1, 0);

    Aig_Obj_t* PO;
    Aig_Obj_t* PI;
    Aig_Obj_t* pObj;
    int node, PO_id, var;
    int VarShift = 0;
    vector<int> PI_var_list;
    Aig_ManForEachObj(pAig, pObj, node)
    {
      var = pCNF->pVarNums[pObj->Id];
      if (var > VarShift) { VarShift = var; }
      // cout << "node" << node << " Id : " << pObj->Id << " --> Type = " << Aig_ObjType(pObj) << endl;
      if (Aig_ObjType(pObj) == AIG_OBJ_CI) { PI_var_list.push_back(pObj->Id); }
      if (Aig_ObjType(pObj) == AIG_OBJ_CO) { PO_id = pObj->Id; }
    }
    // f(X)
    int f_X_var = pCNF->pVarNums[PO_id];
    int f_X_lit = Abc_Var2Lit(f_X_var, 0);
    int *f_X = &f_X_lit;
    sat_solver_addclause(pSat, f_X, f_X+1);

    // debug
    // pSat->fPrintClause = true;

    vector<int> xi_list, xi_prime_list, xi_prime2_list;
    int count_used = 0;
    // store input 
    for (int i = 0 ; i < PI_var_list.size() ; ++i)
    {
        xi_list.push_back(pCNF->pVarNums[PI_var_list[i]]); 
        xi_prime_list.push_back(pCNF->pVarNums[PI_var_list[i]] + VarShift);
        xi_prime2_list.push_back(pCNF->pVarNums[PI_var_list[i]] + 2*VarShift);
        ++count_used;
    } 
    // negate f(X')
    Cnf_DataLift(pCNF, VarShift);
    int f_X_prime_lit = Abc_Var2Lit(f_X_var + VarShift, 1);
    int *f_X_prime = &f_X_prime_lit;
    sat_solver_addclause(pSat, f_X_prime, f_X_prime+1);
    // add function content f(X')
    for (int i = 0 ; i < pCNF->nClauses ; ++i) { sat_solver_addclause(pSat, pCNF->pClauses[i], pCNF->pClauses[i+1]); }
    // negate f(X'')
    Cnf_DataLift(pCNF, VarShift);
    int f_X_prime2_lit = Abc_Var2Lit(f_X_var + 2*VarShift, 1);
    int *f_X_prime2 = &f_X_prime2_lit;
    sat_solver_addclause(pSat, f_X_prime2, f_X_prime2+1);
    // add function content f(X'')
    for (int i = 0 ; i < pCNF->nClauses ; ++i) { sat_solver_addclause(pSat, pCNF->pClauses[i], pCNF->pClauses[i+1]); }
    // addVar controlling variable (a_i & b_i) * nVar 個 (= count_used 個)
        // sat_solver_addvar 會回傳 new variable 的 number, 要記錄下來 (maybe array)
    vector<int> control_a, control_b; 
    int a_begin = 3*VarShift + 1;
    int a_end = a_begin + count_used - 1;
    int b_begin = a_end + 1;
    int b_end = b_begin + count_used - 1;
    // add var
    for (int i = 0 ; i < count_used ; ++i) { sat_solver_addvar(pSat); }
    for (int i = 0 ; i < count_used ; ++i) { sat_solver_addvar(pSat); }
    // store the var 
    for (int i = a_begin ; i < a_end + 1 ; ++i) { control_a.push_back(i); }
    for (int i = b_begin ; i < b_end + 1 ; ++i) { control_b.push_back(i); }
    // Add clause of controlling variable 
        // (a' + b + c) --> a': Abc_Var2Lit(pVarnum[i], 1) --> 存 int array [a', b, c] 然後傳進 addclause
    for (int i = 0 ; i < count_used ; ++i) 
    {
      int a1_clause[3] = {Abc_Var2Lit(xi_list[i], 1), Abc_Var2Lit(xi_prime_list[i], 0), Abc_Var2Lit(control_a[i], 0)};
      sat_solver_addclause(pSat, a1_clause, a1_clause + 3);

      int a2_clause[3] = {Abc_Var2Lit(xi_list[i], 0), Abc_Var2Lit(xi_prime_list[i], 1), Abc_Var2Lit(control_a[i], 0)};
      sat_solver_addclause(pSat, a2_clause, a2_clause + 3);

      int b1_clause[3] = {Abc_Var2Lit(xi_list[i], 1), Abc_Var2Lit(xi_prime2_list[i], 0), Abc_Var2Lit(control_b[i], 0)};
      sat_solver_addclause(pSat, b1_clause, b1_clause + 3);

      int b2_clause[3] = {Abc_Var2Lit(xi_list[i], 0), Abc_Var2Lit(xi_prime2_list[i], 1), Abc_Var2Lit(control_b[i], 0)};
      sat_solver_addclause(pSat, b2_clause, b2_clause + 3);
    }

    // debug
    // pSat->fPrintClause = false;

    // 4. Solve a non-trivial variable partition
    bool find_partition = false;
    // 若 PI 只有一個, 不會有 bidecomposition
    if (count_used > 1)
    {
      for (int i = 0 ; i < count_used-1 ; ++i)
      {
        for (int j = i+1 ; j < count_used ; ++j)
        {
          int solve_ans; 
          find_partition = false;
          vector<int> assumpList;
          // assumpList
          for (int k = 0 ; k < count_used ; ++k)
          {
            // (x2_a, x2_b) = (0, 1) in xB
            if (k == i) 
            { 
              assumpList.push_back(toLitCond(control_a[k], 1));
              assumpList.push_back(toLitCond(control_b[k], 0));
            }
            // (x1_a, x1_b) = (1, 0) in xA
            else if (k == j)
            {
              assumpList.push_back(toLitCond(control_a[k], 0));
              assumpList.push_back(toLitCond(control_b[k], 1));
            }
            // other (0, 0) in xC
            else 
            {
              assumpList.push_back(toLitCond(control_a[k], 1));
              assumpList.push_back(toLitCond(control_b[k], 1));
            }
          }
          // pass into sat_solver_solve
              // satInterP.c --> sat_solver will return "l_Undef", "l_True", "l_False"
              // proof/abs/absOldSat.c --> how "sat_solver_final" work
              // sat/bmc/bmcEco.c --> how "sat_solver_final" work
          solve_ans = sat_solver_solve(pSat, &assumpList[0], &assumpList[assumpList.size()], 0, 0, 0, 0);
          // if UNSAT, get relevant SAT literals
          int nCoreLits, * pCoreLits;
          vector<int> ans_candidate, ans;
          if (solve_ans == l_False)
          {
            find_partition = true;
            nCoreLits = sat_solver_final(pSat, &pCoreLits);
            // save literals
                // (1): if int(lit/2)=var 不在 control_a, control_b 內 --> 丟掉不考慮 (考慮a, b ; 不考慮 x_i)
                // (2): if var_a = 0 且 var_b = 0 --> 歸類在 xC
                // (3): if 只有 var_a = 0 --> 歸類在 xB (a, b assume to be positive)
                // (4): if 只有 var_b = 0 --> 歸類在 xA
                // (5): if 都不存在這些歸類, 代表哪邊都可以 --> either xA or xB --> 這邊統一丟在 xA
            for (int k = 0 ; k < nCoreLits ; ++k)
            {
              if ((std::find(control_a.begin(), control_a.end(), int(pCoreLits[k]/2)) != control_a.end()) || \
                  (std::find(control_b.begin(), control_b.end(), int(pCoreLits[k]/2)) != control_b.end()))
              {
                ans_candidate.push_back(int(pCoreLits[k]/2));
              }
            }
            for (int k = 0 ; k < count_used ; ++k)
            {
              // 該 seed partition 自己成功分類的 node 要加進去
              if (k == i)
              {
                ans.push_back(1);
                continue;
              }
              if (k == j)
              {
                ans.push_back(2);
                continue;
              }
              if ((std::find(ans_candidate.begin(), ans_candidate.end(), control_a[k]) != ans_candidate.end()) && \
                  (std::find(ans_candidate.begin(), ans_candidate.end(), control_b[k]) != ans_candidate.end()))
              {
                ans.push_back(0);
                continue;
              }
              else if ((std::find(ans_candidate.begin(), ans_candidate.end(), control_a[k]) != ans_candidate.end()) && \
                        (std::find(ans_candidate.begin(), ans_candidate.end(), control_b[k]) == ans_candidate.end()))
              {
                ans.push_back(1);
                continue;
              }
              else if ((std::find(ans_candidate.begin(), ans_candidate.end(), control_a[k]) == ans_candidate.end()) && \
                        (std::find(ans_candidate.begin(), ans_candidate.end(), control_b[k]) != ans_candidate.end()))
              {
                ans.push_back(2);
                continue;
              }
              else if ((std::find(ans_candidate.begin(), ans_candidate.end(), control_a[k]) == ans_candidate.end()) && \
                        (std::find(ans_candidate.begin(), ans_candidate.end(), control_b[k]) == ans_candidate.end())) // 都沒在上面分類就全塞到 xB
              {
                ans.push_back(1);
                continue;
              }
            }
            // output : PO <po-name> support partition: 1
            //          <partition> (2: xA, 1: xB, 0: xC)
            cout << "PO " << Abc_ObjName(ntk_PO) << " support partition: " << find_partition << endl;
            for (int k = 0 ; k < ans.size() ; ++k) { cout << ans[k]; }
            cout << endl;
          }
          // cout << "partition find ? " << find_partition << endl;
          if (find_partition) { break; }
        }
        if (find_partition) { break; }
      }
      if (!find_partition) { cout << "PO " << Abc_ObjName(ntk_PO) << " support partition: " << find_partition << endl; }
    }
    else { cout << "PO " << Abc_ObjName(ntk_PO) << " support partition: " << find_partition << endl; }
  }
}


// Define command function : LSV_CommandOrBidec
int LSV_CommandOrBidec(Abc_Frame_t* pAbc, int argc, char** argv)
{
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF)
  {
    switch (c)
    {
      case 'h':
        goto usage;
      default:
        goto usage;
    }
  }
  if (!pNtk)
  {
    Abc_Print(-1, "Empty network.\n");
    return -1;
  }
  // main function
  Lsv_NtkOrBidec(pNtk);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_or_bidec [-h]\n");
  Abc_Print(-2, "\t        check the OR bi-decomposition in the network\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;

}
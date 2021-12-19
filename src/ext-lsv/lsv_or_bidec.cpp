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
    Abc_Ntk_t* pNtk_support;
    sat_solver* pSat;
    int i;

    // For each Co, extract cone of each Co & support set (Co: Combinational output)
    Abc_NtkForEachCo(pNtk, ntk_PO, i)
    {
        // 1. Store support X as a circuit network 
        pNtk_support = Abc_NtkCreateCone(pNtk, Abc_ObjFanin0(ntk_PO), Abc_ObjName(ntk_PO), 0);
        pNtk_support = Abc_NtkStrash(pNtk_support, 0, 0, 0);

        // 2. Derive equivalent "Aig_Man_t" from "Abc_Ntk_t"
        Aig_Man_t* pAig = Abc_NtkToDar(pNtk_support, 0, 0);
            // 找 aig 的 PO (看 type 或 foreachaigpo) --> 參考 PA1 line 84
        Aig_Obj_t* PO;
        int node, PO_id;
        Aig_ManForEachCo(pAig, PO, node) { PO_id = PO->Id; }
        // 3. Construct CNF formula --> f(X)
            // cnf.h --> struct Cnf_Dat_t_
            // abc_global.h --> Abc_Var2Lit(), 參數吃 1 代表 negation
        Cnf_Dat_t* pCNF = Cnf_Derive(pAig, 1);
        pSat = (sat_solver*) Cnf_DataWriteIntoSolver(pCNF, 1, 0);
            // Obtain "VarShift" by extracting the max varnum() in CNF
        int VarShift = 0, X_VarNum = pCNF->nVars, f_X_var = pCNF->pVarNums[PO_id];
        // int *xi_list, *xi_prime_list, *xi_prime2_list;  // 存 var list pointer 就好, 不用存 lit (lit: 涵蓋 phase 資訊)
        // f(X)
        // xi_list = pCNF->pVarNums;
            // Store varnum(f(X)) & add to CNF: Aig_Obj_t->Id --> Abc_Var2Lit
        cout << "1" << endl;
        cout << "f_X_var : " << f_X_var << endl;
        int *f_X = (int *) Abc_Var2Lit(f_X_var, 0);
        cout << "2" << endl;
            // sat_solver_addclause (參考 cnfMan.c 的用法)
        sat_solver_addclause(pSat, f_X, f_X+1);
        cout << "2.5" << endl;
        int count_used = 0;
        for (int i = 0 ; i < sizeof(pCNF->pVarNums)/sizeof(int) ; ++i)
        {
            // if unused, no need to be stored
            if (pCNF->pVarNums[i] == -1) { continue; }
            // cout << "var " <<  i << " id : " << pCNF->pVarNums[i] << endl;
            if (pCNF->pVarNums[i] > VarShift) { VarShift = pCNF->pVarNums[i]; }
            ++count_used;
            cout << "varnum : " << pCNF->pVarNums[i] << endl;
        } 
        int *xi_list = new int(count_used);
        int *xi_prime_list = new int(count_used);
        int *xi_prime2_list = new int(count_used);
        int count_added = 0;
        for (int i = 0 ; i < sizeof(pCNF->pVarNums)/sizeof(int) ; ++i)
        {
            // if unused, no need to be stored
            if (pCNF->pVarNums[i] != -1) 
            { 
              xi_list[count_added] = pCNF->pVarNums[i]; 
              xi_prime_list[count_added] = pCNF->pVarNums[i] + VarShift;
              xi_prime2_list[count_added] = pCNF->pVarNums[i] + 2*VarShift;
              ++count_added; 
            }
        } 
        // negate f(X')
        Cnf_DataLift(pCNF, VarShift);
        // xi_prime_list = pCNF->pVarNums;
            // abc_global.h --> Abc_Var2Lit(), 參數吃 1 代表 negation
        cout << "3" << endl;
        int *f_X_prime = (int *) Abc_Var2Lit(f_X_var + VarShift, 1);
        cout << "4" << endl;
        sat_solver_addclause(pSat, f_X_prime, f_X_prime+1);
            // add function content f(X')
        for (int i = 0 ; i < X_VarNum ; ++i) { sat_solver_addclause(pSat, pCNF->pClauses[i], pCNF->pClauses[i+1]); }
        // negate f(X'')
        Cnf_DataLift(pCNF, VarShift);
        // xi_prime2_list = pCNF->pVarNums;
        cout << "5" << endl;
        int *f_X_prime2 = (int *) Abc_Var2Lit(f_X_var + 2*VarShift, 1);
        cout << "6" << endl;
        sat_solver_addclause(pSat, f_X_prime2, f_X_prime2+1);
            // add function content f(X')
        for (int i = 0 ; i < X_VarNum ; ++i) { sat_solver_addclause(pSat, pCNF->pClauses[i], pCNF->pClauses[i+1]); }
        // addVar controlling variable (a_i & b_i) * nVar 個 (= X_VarNum 個)
            // sat_solver_addvar 會回傳 new variable 的 number, 要記錄下來 (maybe array)
        vector<int> control_a, control_b; 
        for (int i = 0 ; i < X_VarNum ; ++i)
        {
          control_a.push_back(sat_solver_addvar(pSat));
          control_b.push_back(sat_solver_addvar(pSat));
        }
            // Add clause of controlling variable 
            // (a' + b + c) --> a': Abc_Var2Lit(pVarnum[i], 1) --> 存 int array [a', b, c] 然後傳進 addclause
        for (int i = 0 ; i < X_VarNum ; ++i) 
        {
          cout << "7" << endl;
          int a1_clause[3] = {Abc_Var2Lit(xi_list[i], 1), Abc_Var2Lit(xi_prime_list[i], 0), Abc_Var2Lit(control_a[i], 0)};
          cout << "8" << endl;
          int a2_clause[3] = {Abc_Var2Lit(xi_list[i], 0), Abc_Var2Lit(xi_prime_list[i], 1), Abc_Var2Lit(control_a[i], 0)};
          cout << "9" << endl;
          int b1_clause[3] = {Abc_Var2Lit(xi_list[i], 1), Abc_Var2Lit(xi_prime2_list[i], 0), Abc_Var2Lit(control_b[i], 0)};
          cout << "10" << endl;
          int b2_clause[3] = {Abc_Var2Lit(xi_list[i], 0), Abc_Var2Lit(xi_prime2_list[i], 1), Abc_Var2Lit(control_b[i], 0)};
          sat_solver_addclause(pSat, &a1_clause[0], &a1_clause[2]);
          sat_solver_addclause(pSat, &a2_clause[0], &a2_clause[2]);
          sat_solver_addclause(pSat, &b1_clause[0], &b1_clause[2]);
          sat_solver_addclause(pSat, &b2_clause[0], &b2_clause[2]);
        }
        // 4. Solve a non-trivial variable partition
        int solve_ans;
        for (int i = 0 ; i < X_VarNum-1 ; ++i)
        {
          for (int j = i+1 ; j < X_VarNum ; ++j)
          {
            int *assumpList = new int(2*X_VarNum);
            int count = 0;
            // assumpList
            for (int k = 0 ; k < X_VarNum ; ++k)
            {
              // (x1_a, x1_b) = (1, 0) in xA
              if (k == i) 
              { 
                cout << "11" << endl;
                assumpList[count] = Abc_Var2Lit(control_a[k], 0);
                assumpList[count+1] = Abc_Var2Lit(control_b[k], 1);
                cout << "12" << endl;
              }
              // (x2_a, x2_b) = (0, 1) in xB
              else if (k == j)
              {
                cout << "13" << endl;
                assumpList[count] = Abc_Var2Lit(control_a[k], 1);
                assumpList[count+1] = Abc_Var2Lit(control_b[k], 0);
                cout << "14" << endl;
              }
              // other (0, 0) in xC
              else 
              {
                cout << "15" << endl;
                assumpList[count] = Abc_Var2Lit(control_a[k], 1);
                assumpList[count+1] = Abc_Var2Lit(control_b[k], 1);
                cout << "16" << endl;
              }
              count += 2;
            }
            // pass into sat_solver_solve
                // satInterP.c --> sat_solver will return "l_Undef", "l_True", "l_False"
                // proof/abs/absOldSat.c --> how "sat_solver_final" work
                // sat/bmc/bmcEco.c --> how "sat_solver_final" work
            solve_ans = sat_solver_solve(pSat, &assumpList[0], &assumpList[2*X_VarNum], (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0);
                // if UNSAT, get relevant SAT literals
            int nCoreLits, * pCoreLits;
            vector<int> ans_candidate;
            string ans = "";
            if (solve_ans == l_False)
            {
              nCoreLits = sat_solver_final(pSat, &pCoreLits);
              // save literals
                  // (1): if int(lit/2)=var 不在 control_a, control_b 內 --> 丟掉不考慮 (考慮a, b ; 不考慮 x_i)
                  // (2): if var_a = 0 且 var_b = 0 --> 歸類在 xC
                  // (3): if 只有 var_a = 0 --> 歸類在 xB (a, b assume to be positive)
                  // (4): if 只有 var_b = 0 --> 歸類在 xA
                  // (5): if 都不存在這些歸類, 代表哪邊都可以 --> either xA or xB --> 這邊統一丟在 xA
              printf("PO %s support partition: 1", Abc_ObjName(ntk_PO));
              for (int k = 0 ; k < nCoreLits ; ++k)
              {
                if ((std::find(control_a.begin(), control_a.end(), int(pCoreLits[k]/2)) != control_a.end()) || \
                    (std::find(control_b.begin(), control_b.end(), int(pCoreLits[k]/2)) != control_b.end()))
                {
                  ans_candidate.push_back(int(pCoreLits[k]/2));
                }
              }
              for (int k = 0 ; k < X_VarNum ; ++k)
              {
                if ((std::find(ans_candidate.begin(), ans_candidate.end(), control_a[k]) != ans_candidate.end()) && \
                    (std::find(ans_candidate.begin(), ans_candidate.end(), control_b[k]) != ans_candidate.end()))
                {
                  ans.append("0");
                }
                else if ((std::find(ans_candidate.begin(), ans_candidate.end(), control_a[k]) != ans_candidate.end()) && \
                         (std::find(ans_candidate.begin(), ans_candidate.end(), control_b[k]) == ans_candidate.end()))
                {
                  ans.append("1");
                }
                else if ((std::find(ans_candidate.begin(), ans_candidate.end(), control_a[k]) == ans_candidate.end()) && \
                         (std::find(ans_candidate.begin(), ans_candidate.end(), control_b[k]) != ans_candidate.end()))
                {
                  ans.append("2");
                }
              }
              // output : PO <po-name> support partition: 1
              //          <partition> (2: xA, 1: xB, 0: xC)
              printf("%s", ans);
            }
            else 
            {
              // output : PO <po-name> support partition: 0
              printf("PO %s support partition: 0", Abc_ObjName(ntk_PO));
            }
          }
        }
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
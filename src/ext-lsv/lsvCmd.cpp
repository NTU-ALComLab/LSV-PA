#include "base/abc/abc.h"#include "base/main/main.h"
#include "base/main/mainInt.h"

#include <vector>
#include <set>
#include <map>
#include <algorithm>
#include <iostream>

#include "sat/cnf/cnf.h"
#include "sat/bsat/satSolver.h"
#include "bdd/cudd/cuddInt.h"  // For CUDD internals if needed
using namespace std;

// Abc_NtkToDar() 介面（照 PA2 提示）
extern "C"{
Aig_Man_t* Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
}

// #define LSV_DEBUG_UNATE 1

#if LSV_DEBUG_UNATE
  #define DBGPRINT(...) Abc_Print( 1, __VA_ARGS__ )
#else
  #define DBGPRINT(...)
#endif


//============================================================================
// Command registration
//============================================================================

static int Lsv_CommandPrintMocut( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Lsv_CommandUnateSat   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Lsv_CommandUnateBdd(Abc_Frame_t* pAbc, int argc, char** argv);
void init( Abc_Frame_t * pAbc )
{
    Cmd_CommandAdd( pAbc, "LSV", "lsv_printmocut", Lsv_CommandPrintMocut, 0 );
    Cmd_CommandAdd( pAbc, "LSV", "lsv_unate_sat" , Lsv_CommandUnateSat,    0 );
    Cmd_CommandAdd( pAbc, "LSV", "lsv_unate_bdd", Lsv_CommandUnateBdd, 0 );
}

void destroy( Abc_Frame_t * pAbc ) {}

Abc_FrameInitializer_t frame_initializer = { init, destroy };

struct PackageRegistrationManager
{
    PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

////////////////////////////////////////////////////////////////////////
/// Data structures
////////////////////////////////////////////////////////////////////////

struct Cut
{
  vector<int> nodes; // sorted ascending
  bool operator<(const Cut &other) const
  {
    return nodes < other.nodes;
  }
};

////////////////////////////////////////////////////////////////////////
/// Helper functions
////////////////////////////////////////////////////////////////////////

// merge two cuts
static bool MergeCuts(const Cut &a, const Cut &b, Cut &result, int k)
{
  result.nodes.clear();
  set_union(a.nodes.begin(), a.nodes.end(),
            b.nodes.begin(), b.nodes.end(),
            back_inserter(result.nodes));
  return (int)result.nodes.size() <= k;
}

// check subset
static bool IsSubset(const Cut &a, const Cut &b)
{
  return includes(b.nodes.begin(), b.nodes.end(),
                  a.nodes.begin(), a.nodes.end());
}

// add cut if irredundant
static void AddCut(vector<Cut> &cuts, const Cut &newCut)
{
  // check if redundant
  for (auto &c : cuts)
  {
    if (IsSubset(c, newCut))
      return; // existing smaller cut
  }
  // remove supersets of newCut
  cuts.erase(remove_if(cuts.begin(), cuts.end(),
                       [&](Cut &c)
                       { return IsSubset(newCut, c); }),
             cuts.end());
  cuts.push_back(newCut);
}

////////////////////////////////////////////////////////////////////////
/// Core enumeration
////////////////////////////////////////////////////////////////////////

static void EnumerateCuts(Abc_Ntk_t *pNtk, int k,
                          vector<vector<Cut>> &nodeCuts)
{
  nodeCuts.resize(Abc_NtkObjNumMax(pNtk));

  Abc_Obj_t *pObj;
  int i;

  Abc_NtkForEachObj(pNtk, pObj, i)
  {
    nodeCuts[i].clear();
    // constant node
    if (Abc_AigNodeIsConst(pObj))
    {
      Cut c; // empty cut
      nodeCuts[i].push_back(c);
    }
    // primary input
    else if (Abc_ObjIsPi(pObj))
    {
      Cut c;
      c.nodes.push_back(Abc_ObjId(pObj));
      nodeCuts[i].push_back(c);
    }
    // AND node
    else if (Abc_ObjIsNode(pObj))
    {
      Abc_Obj_t *f0 = Abc_ObjFanin0(pObj);
      Abc_Obj_t *f1 = Abc_ObjFanin1(pObj);
      // printf("Node %d fanin0=%d fanin1=%d\n", pObj->Id, f0->Id, f1->Id);

      vector<Cut> &cuts0 = nodeCuts[Abc_ObjId(f0)];
      vector<Cut> &cuts1 = nodeCuts[Abc_ObjId(f1)];

      for (auto &c0 : cuts0)
      {
        for (auto &c1 : cuts1)
        {
          Cut merged;
          if (MergeCuts(c0, c1, merged, k))
          {
            AddCut(nodeCuts[i], merged);
          }
        }
      }
      Cut selfCut;
      selfCut.nodes.push_back(Abc_ObjId(pObj));
      AddCut(nodeCuts[i], selfCut);
    }
  }
}

////////////////////////////////////////////////////////////////////////
/// Command implementation
////////////////////////////////////////////////////////////////////////

int Lsv_CommandPrintMocut(Abc_Frame_t *pAbc, int argc, char **argv)
{
  if (argc != 3)
  {
    Abc_Print(-1, "Usage: lsv_printmocut <k> <l>\n");
    return 1;
  }
  int k = atoi(argv[1]);
  int l = atoi(argv[2]);
  if (k < 3 || k > 6 || l < 1 || l > 4)
  {
    Abc_Print(-1, "k must be 3~6, l must be 1~4\n");
    return 1;
  }

  Abc_Ntk_t *pNtk = Abc_FrameReadNtk(pAbc);
  if (!pNtk)
  {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  if (!Abc_NtkIsStrash(pNtk))
  {
    Abc_Print(-1, "Network is not in AIG form. Run strash first.\n");
    return 1;
  }

  // enumerate cuts
  vector<vector<Cut>> nodeCuts;
  EnumerateCuts(pNtk, k, nodeCuts);

  // map: Cut -> list of output nodes
  map<Cut, vector<int>> cutMap;

  Abc_Obj_t *pObj;
  int i;
  Abc_NtkForEachObj(pNtk, pObj, i)
  {
    if (!(Abc_ObjIsPi(pObj) || Abc_ObjIsNode(pObj)))
      continue;
    for (auto &c : nodeCuts[i])
    {
      sort(c.nodes.begin(), c.nodes.end());
      cutMap[c].push_back(i);
    }
  }

  // print results
  for (auto &kv : cutMap)
  {
    if ((int)kv.second.size() >= l)
    {
      // print inputs
      for (size_t m = 0; m < kv.first.nodes.size(); m++)
      {
        printf("%d", kv.first.nodes[m]);
        if (m + 1 < kv.first.nodes.size())
          printf(" ");
      }
      printf(" : ");
      // print outputs
      sort(kv.second.begin(), kv.second.end());
      for (size_t m = 0; m < kv.second.size(); m++)
      {
        printf("%d", kv.second[m]);
        if (m + 1 < kv.second.size())
          printf(" ");
      }
      printf("\n");
    }
  }

  return 0;
}

////////////////////////////////////////////////////////////////////////
/// Helpers for unate_bdd  （在 strash AIG + global BDD 上做）
////////////////////////////////////////////////////////////////////////

// 建立：PI index -> CUDD 變數 index 的對應
static void Lsv_BddBuildPiVarIndex( Abc_Ntk_t *pNtk, std::vector<int> &piVarIndex )
{
    int nPi = Abc_NtkPiNum( pNtk );
    piVarIndex.assign( nPi, -1 );

    // 建 object id -> CI 變數 index 的 map
    std::map<int,int> id2var;
    Abc_Obj_t *pCi;
    int iCi;
    Abc_NtkForEachCi( pNtk, pCi, iCi )
        id2var[ Abc_ObjId(pCi) ] = iCi;

    // 把每個 PI 對應到它的 CI index（也就是 BDD var index）
    Abc_Obj_t *pPi;
    int iPi;
    Abc_NtkForEachPi( pNtk, pPi, iPi )
    {
        auto it = id2var.find( Abc_ObjId(pPi) );
        if ( it != id2var.end() )
            piVarIndex[iPi] = it->second;
    }
}


// 從一個非空的 BDD set bSet 抽一組 assignment，
// 轉成 pattern 字串（長度 = #PI，指定的 x_i 印 '-'，其他印 0/1）
static void Lsv_BddPickPattern(
    DdManager *dd, Abc_Ntk_t *pNtk,
    const std::vector<int> &piVarIndex,
    DdNode *bSet, int iInput,
    std::string &pattern )
{
    pattern.clear();

    int nVars = dd->size;                     // CUDD 變數個數
    char *cube = (char *)ABC_ALLOC( char, nVars );
    if ( cube == NULL )
    {
        // OOM fallback：給一個全 0、x_i='-' 的 pattern
        Abc_Obj_t *pPi;
        int i;
        Abc_NtkForEachPi( pNtk, pPi, i )
            pattern.push_back( i == iInput ? '-' : '0' );
        return;
    }

    int ok = Cudd_bddPickOneCube( dd, bSet, cube );
    if ( ok == 0 )
    {
        // 理論上 bSet 非空就不該失敗；保險起見
        ABC_FREE( cube );
        Abc_Obj_t *pPi;
        int i;
        Abc_NtkForEachPi( pNtk, pPi, i )
            pattern.push_back( i == iInput ? '-' : '0' );
        return;
    }

    int nPi = Abc_NtkPiNum( pNtk );
    pattern.reserve( nPi );

    for ( int i = 0; i < nPi; ++i )
    {
        if ( i == iInput )
        {
            pattern.push_back( '-' );     // 指定的 xi 用 '-'
            continue;
        }

        int varIndex = (i < (int)piVarIndex.size()) ? piVarIndex[i] : -1;
        char c = '0';

        if ( varIndex >= 0 && varIndex < nVars )
        {
            // cube[varIndex] 是 0 / 1 / 2 (2 = don't care)
            int v = (int)cube[varIndex];
            if ( v == 1 )
                c = '1';
            else
                c = '0';                 // don't care 也當作 0
        }

        pattern.push_back( c );
    }

    ABC_FREE( cube );
}

////////////////////////////////////////////////////////////////////////
/// lsv_unate_bdd
////////////////////////////////////////////////////////////////////////

static int Lsv_CommandUnateBdd( Abc_Frame_t *pAbc, int argc, char **argv )
{
    if ( argc != 3 )
    {
        Abc_Print( -1, "usage: lsv_unate_bdd <k> <i>\n" );
        return 1;
    }

    int k      = atoi( argv[1] );
    int iInput = atoi( argv[2] );

    Abc_Ntk_t *pNtk = Abc_FrameReadNtk( pAbc );
    if ( !pNtk )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    //（可選）檢查一開始是否是 collapse 後的 BDD net
    if ( !Abc_NtkHasBdd( pNtk ) )
    {
        Abc_Print( -1, "Network is not in BDD form. Run collapse first.\n" );
        return 1;
    }

    // ★ 先把目前網路轉成 AIG（你要求的步驟）
    Abc_Ntk_t *pNtkAig = Abc_NtkStrash( pNtk, 0, 0, 0 );
    if ( pNtkAig == NULL )
    {
        Abc_Print( -1, "Strashing failed in lsv_unate_bdd.\n" );
        return 1;
    }

    int nPi = Abc_NtkPiNum( pNtkAig );
    int nPo = Abc_NtkPoNum( pNtkAig );
    if ( k < 0 || k >= nPo || iInput < 0 || iInput >= nPi )
    {
        Abc_Print( -1, "PO index k in [0..%d], PI index i in [0..%d]\n", nPo - 1, nPi - 1 );
        Abc_NtkDelete( pNtkAig );
        return 1;
    }

    DBGPRINT( "[UNATE-BDD] Command called with k=%d, i=%d\n", k, iInput );
    DBGPRINT( "[UNATE-BDD]   AIG Network: #PI = %d, #PO = %d\n", nPi, nPo );

    // ★ 對 AIG 網路建 global BDDs（模仿 print_unate）
    DdManager *dd = (DdManager *)Abc_NtkBuildGlobalBdds(
        pNtkAig,
        10000000, // node limit
        1,        // fBddSize
        1,        // fDropInternal
        0,        // fReorder
        0         // fVerbose
    );
    if ( dd == NULL )
    {
        Abc_Print( -1, "[UNATE-BDD] Abc_NtkBuildGlobalBdds failed.\n" );
        Abc_NtkDelete( pNtkAig );
        return 1;
    }

    // 取第 k 個 PO 的函數 F(x)（用 AIG 網路）
    Abc_Obj_t *pPo = Abc_NtkPo( pNtkAig, k );
    DdNode    *F   = (DdNode *)Abc_ObjGlobalBdd( pPo );
    if ( F == NULL )
    {
        Abc_Print( -1, "[UNATE-BDD]   PO %d has no global BDD.\n", k );
        Abc_NtkFreeGlobalBdds( pNtkAig, 1 );
        Abc_NtkDelete( pNtkAig );
        return 1;
    }

    DBGPRINT( "[UNATE-BDD]   PO %d name=%s\n", k, Abc_ObjName( pPo ) );

    // 取第 i 個 PI（在 AIG 網路裡）
    Abc_Obj_t *pPi = Abc_NtkPi( pNtkAig, iInput );

    // 在所有 CI 裡找到這個 pPi 對應的 CI index（也就是 BDD var index）
    Abc_Obj_t *pCi;
    int iCi, idxXi = -1;
    Abc_NtkForEachCi( pNtkAig, pCi, iCi )
    {
        if ( pCi == pPi )
        {
            idxXi = iCi;
            break;
        }
    }

    if ( idxXi == -1 )
    {
        // 找不到就當作 independent（理論上不會發生在這個作業）
        DBGPRINT( "[UNATE-BDD]   PI %d not found among CIs -> independent.\n", iInput );
        printf( "independent\n" );
        Abc_NtkFreeGlobalBdds( pNtkAig, 1 );
        Abc_NtkDelete( pNtkAig );
        return 0;
    }

    // 這裡才用 CUDD 變數 index 建 x_i
    DdNode *varXi = Cudd_bddIthVar( dd, idxXi );  Cudd_Ref( varXi );

    DBGPRINT( "[UNATE-BDD]   PI %d name=%s, BDD var index=%d\n",
              iInput, Abc_ObjName( pPi ), idxXi );

    // (1) F0 = F|x_i=0, F1 = F|x_i=1
    DdNode *F0 = Cudd_Cofactor( dd, F, Cudd_Not( varXi ) );  Cudd_Ref( F0 );
    DdNode *F1 = Cudd_Cofactor( dd, F, varXi );              Cudd_Ref( F1 );

    DBGPRINT( "[UNATE-BDD]   Cofactors computed.\n" );

    // (2) Pos / Neg
    DdNode *Pos = Cudd_bddAnd( dd, Cudd_Not( F0 ), F1 );     Cudd_Ref( Pos );
    DdNode *Neg = Cudd_bddAnd( dd, F0, Cudd_Not( F1 ) );     Cudd_Ref( Neg );

    DdNode *bZero = Cudd_ReadLogicZero( dd );
    int satPos = ( Pos != bZero );
    int satNeg = ( Neg != bZero );

    DBGPRINT( "[UNATE-BDD]   Pos non-empty = %d, Neg non-empty = %d\n", satPos, satNeg );

    if ( !satPos && !satNeg )
    {
        printf( "independent\n" );
    }
    else if ( satPos && !satNeg )
    {
        printf( "positive unate\n" );
    }
    else if ( !satPos && satNeg )
    {
        printf( "negative unate\n" );
    }
    else
    {
        printf( "binate\n" );

        std::vector<int> piVarIndex;
        Lsv_BddBuildPiVarIndex( pNtkAig, piVarIndex );

        std::string pat1, pat2;

        Lsv_BddPickPattern( dd, pNtkAig, piVarIndex, Pos, iInput, pat1 );
        Lsv_BddPickPattern( dd, pNtkAig, piVarIndex, Neg, iInput, pat2 );

        printf( "%s\n", pat1.c_str() );
        printf( "%s\n", pat2.c_str() );
    }

    // (4) deref + free global BDD + delete AIG net
    Cudd_RecursiveDeref( dd, F0 );
    Cudd_RecursiveDeref( dd, F1 );
    Cudd_RecursiveDeref( dd, Pos );
    Cudd_RecursiveDeref( dd, Neg );
    Cudd_RecursiveDeref( dd, varXi );

    Abc_NtkFreeGlobalBdds( pNtkAig, 1 );
    Abc_NtkDelete( pNtkAig );

    // ★ 執行一次 ABC 的 "collapse" 指令，把 current network 變回 BDD ★
    if ( Cmd_CommandExecute( pAbc, "collapse" ) )
        Abc_Print( -1, "[UNATE-BDD] auto collapse failed.\n" );

    return 0;
}



/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////
/// Helpers for unate_sat
////////////////////////////////////////////////////////////////////////

// 把一個 Cnf_Dat_t 裡所有 clause 丟進 SAT solver
static bool Lsv_AddCnfToSolver( sat_solver *pSat, Cnf_Dat_t *pCnf )
{
    for ( int c = 0; c < pCnf->nClauses; ++c )
    {
        lit *pBeg = pCnf->pClauses[c];
        lit *pEnd = pCnf->pClauses[c + 1];
        if ( !sat_solver_addclause( pSat, pBeg, pEnd ) )
            return false; // formula 直接 UNSAT
    }
    return true;
}

// 根據「輸出 F 的值」（考慮 PO 是否補相）產生對 root 變數的 literal
static inline lit Lsv_LitForOutputValue( int varRoot, int fComplPo, int valueF )
{
    // F = (fComplPo ? !root : root)
    int rootVal = fComplPo ? !valueF : valueF;
    int litSign   = rootVal ? 0 : 1; // var=1 -> literal 正相, var=0 -> literal 反相
    return toLitCond( varRoot, litSign );
}

// 從 SAT model 抽出輸入 pattern（xi 用 '-'）
static void Lsv_ExtractPattern( Abc_Ntk_t *pNtk, Cnf_Dat_t *pCnf, sat_solver *pSat,
                                int iInput, std::string &pattern )
{
    pattern.clear();
    Abc_Obj_t *pPi;
    int i;

    Abc_NtkForEachPi( pNtk, pPi, i )
    {
        if ( i == iInput )
        {
            pattern.push_back( '-' );
            continue;
        }

        int objId = Abc_ObjId( pPi );
        int varA  = pCnf->pVarNums[ objId ];
        int val   = 0;

        if ( varA >= 0 )
            val = sat_solver_var_value( pSat, varA ); // 0 或 1

        pattern.push_back( val ? '1' : '0' );
    }
}

////////////////////////////////////////////////////////////////////////
/// lsv_unate_sat
////////////////////////////////////////////////////////////////////////

static int Lsv_CommandUnateSat( Abc_Frame_t *pAbc, int argc, char **argv )
{
    if ( argc != 3 )
    {
        Abc_Print( -1, "usage: lsv_unate_sat <k> <i>\n" );
        return 1;
    }

    int k      = atoi( argv[1] );
    int iInput = atoi( argv[2] );

    Abc_Ntk_t *pNtk = Abc_FrameReadNtk( pAbc );
    if ( !pNtk )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash( pNtk ) )
    {
        Abc_Print( -1, "Network is not in AIG form. Run strash first.\n" );
        return 1;
    }

    int nPi = Abc_NtkPiNum( pNtk );
    int nPo = Abc_NtkPoNum( pNtk );
    if ( k < 0 || k >= nPo || iInput < 0 || iInput >= nPi )
    {
        Abc_Print( -1, "PO index k in [0..%d], PI index i in [0..%d]\n", nPo - 1, nPi - 1 );
        return 1;
    }

    DBGPRINT( "[UNATE-SAT] Command called with k=%d, i=%d\n", k, iInput );
    DBGPRINT( "[UNATE-SAT]   Network: #PI = %d, #PO = %d\n", nPi, nPo );

    // 取得要看的 PO 及其 root
    Abc_Obj_t *pPo   = Abc_NtkPo( pNtk, k );
    Abc_Obj_t *pRoot = Abc_ObjFanin0( pPo );
    int        fComplPoOrig = Abc_ObjFaninC0( pPo ); // ★ yk 對 root 的補相
    DBGPRINT( "[UNATE-SAT]   PO %d name=%s, root obj id=%d, fComplPo(original)=%d\n",
              k, Abc_ObjName( pPo ), Abc_ObjId( pRoot ), Abc_ObjFaninC0( pPo ) );

    // (1) 建 cone（最後一個參數一定要 1，照 Hint 3）
    Abc_Ntk_t *pCone = Abc_NtkCreateCone( pNtk, pRoot, Abc_ObjName( pPo ), 1 );
    if ( !pCone )
    {
        Abc_Print( -1, "[UNATE-SAT]   Abc_NtkCreateCone failed.\n" );
        return 1;
    }
    DBGPRINT( "[UNATE-SAT]   Cone created: #PI = %d, #PO = %d, ObjNumMax = %d\n",
              Abc_NtkPiNum( pCone ), Abc_NtkPoNum( pCone ), Abc_NtkObjNumMax( pCone ) );

    // (2) cone -> AIG
    Aig_Man_t *pAig = Abc_NtkToDar( pCone, 0, 0 );
    if ( !pAig )
    {
        Abc_Print( -1, "[UNATE-SAT]   Abc_NtkToDar failed.\n" );
        Abc_NtkDelete( pCone );
        return 1;
    }
    DBGPRINT( "[UNATE-SAT]   AIG created: ObjNumMax = %d, #CI = %d, #CO = %d\n",
              Aig_ManObjNumMax( pAig ), Aig_ManCiNum( pAig ), Aig_ManCoNum( pAig ) );

    // AIG 的輸出 (只有一個 PO)
    Aig_Obj_t *pCoAig   = Aig_ManCo( pAig, 0 );
    Aig_Obj_t *pRootAig = Aig_ObjFanin0( pCoAig );
    int        fComplPo = Aig_ObjFaninC0( pCoAig );
    DBGPRINT( "[UNATE-SAT]   AIG root id=%d, fComplPo(AIG)=%d\n", pRootAig->Id, fComplPo );

    // (4) AIG -> CNF，一份即可
    Cnf_Dat_t *pCnf = Cnf_Derive( pAig, 1 );
    if ( !pCnf )
    {
        Abc_Print( -1, "[UNATE-SAT]   Cnf_Derive failed.\n" );
        Aig_ManStop( pAig );
        Abc_NtkDelete( pCone );
        return 1;
    }
    DBGPRINT( "[UNATE-SAT]   CNF: nVars = %d, nClauses = %d\n", pCnf->nVars, pCnf->nClauses );

    // xi 在 copy A 的變數（用原 network 的 PI id，照 Hint 3）
    Abc_Obj_t *pXi  = Abc_NtkPi( pNtk, iInput );
    int        idXi = Abc_ObjId( pXi );
    int        varXiA = pCnf->pVarNums[ idXi ];

    if ( varXiA < 0 )
    {
        // xi 完全不在 cone 裡 => 一定 independent
        DBGPRINT( "[UNATE-SAT]   PI %d (id=%d) not in cone CNF -> independent\n", iInput, idXi );
        printf( "independent\n" );
        Cnf_DataFree( pCnf );
        Aig_ManStop( pAig );
        Abc_NtkDelete( pCone );
        return 0;
    }

    // 輸出 root 在 copy A 的變數
    int varY_A = pCnf->pVarNums[ pRootAig->Id ];
    if ( varY_A < 0 )
    {
        Abc_Print( -1, "[UNATE-SAT]   Root AIG node has no CNF var.\n" );
        Cnf_DataFree( pCnf );
        Aig_ManStop( pAig );
        Abc_NtkDelete( pCone );
        return 1;
    }

    // copy B 的變數就是整個 CNF 變數 + nVars
    int varXiB = pCnf->nVars + varXiA;
    int varY_B = pCnf->nVars + varY_A;

    DBGPRINT( "[UNATE-SAT]   varXiA=%d, varY_A=%d, varXiB=%d, varY_B=%d\n",
              varXiA, varY_A, varXiB, varY_B );

    // (3) SAT solver
    sat_solver *pSat = sat_solver_new();
    if ( !pSat )
    {
        Abc_Print( -1, "[UNATE-SAT]   sat_solver_new failed.\n" );
        Cnf_DataFree( pCnf );
        Aig_ManStop( pAig );
        Abc_NtkDelete( pCone );
        return 1;
    }
    sat_solver_setnvars( pSat, 2 * pCnf->nVars ); // 兩份 CNF
    DBGPRINT( "[UNATE-SAT]   SAT solver created, nVars reserved = %d\n",
              sat_solver_nvars( pSat ) );

    // (5) 加入 CNF A
    if ( !Lsv_AddCnfToSolver( pSat, pCnf ) )
    {
        DBGPRINT( "[UNATE-SAT]   CNF A makes formula UNSAT, treat as independent.\n" );
        printf( "independent\n" );
        sat_solver_delete( pSat );
        Cnf_DataFree( pCnf );
        Aig_ManStop( pAig );
        Abc_NtkDelete( pCone );
        return 0;
    }
    DBGPRINT( "[UNATE-SAT]   CNF A added.\n" );

    // (6) lift CNF 為 copy B，加入，再 lift 回來
    Cnf_DataLift( pCnf, pCnf->nVars );
    DBGPRINT( "[UNATE-SAT]   CNF lifted by %d for copy B.\n", pCnf->nVars );

    if ( !Lsv_AddCnfToSolver( pSat, pCnf ) )
    {
        DBGPRINT( "[UNATE-SAT]   CNF B makes formula UNSAT, treat as independent.\n" );
        printf( "independent\n" );
        Cnf_DataLift( pCnf, -pCnf->nVars );
        sat_solver_delete( pSat );
        Cnf_DataFree( pCnf );
        Aig_ManStop( pAig );
        Abc_NtkDelete( pCone );
        return 0;
    }
    DBGPRINT( "[UNATE-SAT]   CNF B added.\n" );

    // 把 pCnf 的變數編號 restore 回 original（之後用 pVarNums 做 mapping）
    Cnf_DataLift( pCnf, -pCnf->nVars );

    // (7) 把所有 t ≠ i 的輸入，設成 vA(t) = vB(t)
    Abc_Obj_t *pPi;
    int i;
    Abc_NtkForEachPi( pNtk, pPi, i )
    {
        int id  = Abc_ObjId( pPi );
        int varA = pCnf->pVarNums[ id ];
        if ( varA < 0 )
            continue;          // 這個 PI 沒出現在 CNF 裡
        if ( i == iInput )
            continue;          // xi 不要綁在一起

        int varB = pCnf->nVars + varA;
        sat_solver_add_buffer( pSat, varA, varB, 0 ); // varA ↔ varB
    }
    DBGPRINT( "[UNATE-SAT]   Buffer constraints for all inputs except x_%d added.\n", iInput );

    // (8) 兩種 pattern 的 SAT 查詢
    lit Assump1[4];
    lit Assump2[4];

    // Pattern 1: F(0) = 0, F(1) = 1  => 檢查「可以當成 +unate counterexample」的情況
    Assump1[0] = toLitCond( varXiA, 1 ); // xiA = 0
    Assump1[1] = toLitCond( varXiB, 0 ); // xiB = 1
    Assump1[2] = Lsv_LitForOutputValue( varY_A, fComplPoOrig, 0 ); // yA = 0
    Assump1[3] = Lsv_LitForOutputValue( varY_B, fComplPoOrig, 1 ); // yB = 1

    int status1 = sat_solver_solve( pSat, Assump1, Assump1 + 4, 0, 0, 0, 0 );
    DBGPRINT( "[UNATE-SAT]   Solve #1 (F(0)=0,F(1)=1) -> %d (1=SAT,0=UNSAT)\n", status1 );

    // Pattern 2: F(0) = 1, F(1) = 0  => 「可以當成 -unate counterexample」
    Assump2[0] = toLitCond( varXiA, 1 ); // xiA = 0
    Assump2[1] = toLitCond( varXiB, 0 ); // xiB = 1
    Assump2[2] = Lsv_LitForOutputValue( varY_A, fComplPoOrig, 1 ); // yA = 1
    Assump2[3] = Lsv_LitForOutputValue( varY_B, fComplPoOrig, 0 ); // yB = 0

    int status2 = sat_solver_solve( pSat, Assump2, Assump2 + 4, 0, 0, 0, 0 );
    DBGPRINT( "[UNATE-SAT]   Solve #2 (F(0)=1,F(1)=0) -> %d (1=SAT,0=UNSAT)\n", status2 );

    int sat1 = (status1 == 1);
    int sat2 = (status2 == 1);

    // (9) 判斷性質 + 如果 binate 就印 pattern
    if ( !sat1 && !sat2 )
    {
        printf( "independent\n" );
    }
    else if ( sat1 && !sat2 )
    {
        printf( "positive unate\n" );
    }
    else if ( !sat1 && sat2 )
    {
        printf( "negative unate\n" );
    }
    else // sat1 && sat2 => binate
    {
        printf( "binate\n" );

        std::string pat1, pat2;

        // 再各 solve 一次拿 model，抽出 pattern 1 / 2
        status1 = sat_solver_solve( pSat, Assump1, Assump1 + 4, 0, 0, 0, 0 );
        if ( status1 == 1 )
        {
            Lsv_ExtractPattern( pNtk, pCnf, pSat, iInput, pat1 );
            printf( "%s\n", pat1.c_str() );
        }
        else
        {
            DBGPRINT( "[UNATE-SAT]   Unexpected: pattern1 became UNSAT (%d)\n", status1 );
        }

        status2 = sat_solver_solve( pSat, Assump2, Assump2 + 4, 0, 0, 0, 0 );
        if ( status2 == 1 )
        {
            Lsv_ExtractPattern( pNtk, pCnf, pSat, iInput, pat2 );
            printf( "%s\n", pat2.c_str() );
        }
        else
        {
            DBGPRINT( "[UNATE-SAT]   Unexpected: pattern2 became UNSAT (%d)\n", status2 );
        }
    }

    // cleanup
    sat_solver_delete( pSat );
    Cnf_DataFree( pCnf );
    Aig_ManStop( pAig );
    Abc_NtkDelete( pCone );

    return 0;
}

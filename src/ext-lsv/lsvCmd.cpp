#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "bdd/cudd/cudd.h"
#include "aig/aig/aig.h"
#include "sat/cnf/cnf.h"
#include "sat/bsat/satSolver.h"
#include "misc/vec/vec.h"
#include <vector>
#include <map>
#include <algorithm>
#include <cstdlib>
#include <cstdio>

static int Lsv_CommandPrintMOCut(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandUnateBdd( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Lsv_CommandUnateSat( Abc_Frame_t * pAbc, int argc, char ** argv );

extern "C" {
Aig_Man_t* Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
}

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocut", Lsv_CommandPrintMOCut, 0);
  Cmd_CommandAdd( pAbc, "LSV", "lsv_unate_bdd", Lsv_CommandUnateBdd, 0 );
  Cmd_CommandAdd( pAbc, "LSV", "lsv_unate_sat", Lsv_CommandUnateSat, 0 );
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

// func
static inline void Normalize(std::vector<int>& v) {
    std::sort(v.begin(), v.end());
    v.erase(std::unique(v.begin(), v.end()), v.end());
}

static inline bool IsSubset(const std::vector<int>& a, const std::vector<int>& b) {
    size_t i = 0, j = 0;
    while (i < a.size() && j < b.size()) {
        if (a[i] == b[j]) { ++i; ++j; }
        else if (a[i] > b[j]) { ++j; }
        else { return false; } // a[i] is not in b
    }
    return i == a.size();
}

static inline void InsertIrredundant(std::vector<std::vector<int>>& bucket,
                                     std::vector<int> cut, int k) {
    Normalize(cut);
    if ((int)cut.size() > k) return;

    // 如果 bucket 中已有 subset ⊆ newCut，則 newCut 是冗餘的，不加入
    for (auto const& oldCut : bucket) {
        if (IsSubset(oldCut, cut)) return;
    }
    // 反過來：移除所有是 newCut 的超集合的舊 cut
    std::vector<std::vector<int>> kept;
    kept.reserve(bucket.size());
    for (auto const& oldCut : bucket) {
        if (!IsSubset(cut, oldCut)) kept.push_back(oldCut);
    }
    kept.push_back(std::move(cut));
    bucket.swap(kept);
}

void Lsv_NtkPrintMOCut(Abc_Ntk_t* pNtk, int k, int l) {
  // Abc_Print(1, "lsv_printmocut called with k = %d, l = %d\n", k, l);
  // TODO: 在這裡實作 multi-output cut enumeration
  // Cuts 存每個 node 的所有 cut
  std::vector<std::vector<std::vector<int>>> Cuts(Abc_NtkObjNumMax(pNtk) + 1);

  Abc_Obj_t* pObj; int i;
  Abc_NtkForEachObj(pNtk, pObj, i) {
      int id = Abc_ObjId(pObj);
      if (Abc_ObjIsPi(pObj)) {
          // PI 的 cut = {自己}
          InsertIrredundant(Cuts[id], std::vector<int>{id}, k);
      }
      else if (Abc_ObjIsNode(pObj)) {
          InsertIrredundant(Cuts[id], std::vector<int>{id}, k);
          // AND node → 由 fanin 的 cut 合併
          Abc_Obj_t* f0 = Abc_ObjFanin0(pObj);
          Abc_Obj_t* f1 = Abc_ObjFanin1(pObj);
          auto& cuts0 = Cuts[Abc_ObjId(f0)];
          auto& cuts1 = Cuts[Abc_ObjId(f1)];

          for (auto& c0 : cuts0) {
              for (auto& c1 : cuts1) {
                  std::vector<int> merged = c0;
                  merged.insert(merged.end(), c1.begin(), c1.end());
                  InsertIrredundant(Cuts[id], std::move(merged), k);
              }
          }
      }
      else {
          // 常數、PO 不用處理
      }
  }
  std::map<std::vector<int>, std::vector<int>> cut2nodes;

  Abc_Obj_t* pObj1;
  int i1;
  Abc_NtkForEachObj(pNtk, pObj1, i1) {
      if (!Abc_ObjIsNode(pObj1)) continue;  // 只考慮 AND nodes
      int id = Abc_ObjId(pObj1);

      for (auto& cut : Cuts[id]) {
          Normalize(cut);
          cut2nodes[cut].push_back(id);
      }
  }

  // 印出結果
  for (auto& kv : cut2nodes) {
      auto& cut = kv.first;
      auto& nodes = kv.second;
      // if (nodes.size() <= 1) continue; // 只有一個 node 不算 group
      if ((int)cut.size() <= k && (int)nodes.size() >= l) {
        // printf("Cut { ");
        for (size_t j=0;j<cut.size();++j) printf("%d ", cut[j]);
        printf(": ");
        for (size_t j=0;j<nodes.size();++j) printf("%d ", nodes[j]);
        printf("\n");
      }
  }
  // // 列印所有 AIG node 的所有 cut（若也想看 PI 的 trivial cut，就把條件改成包含 Abc_ObjIsPi）
  // Abc_Obj_t* pObj2; int i2;
  // Abc_NtkForEachObj(pNtk, pObj2, i2) {
  //     if (!Abc_ObjIsNode(pObj2)) continue;  // 只印 AND nodes；若想包含 PI，改成: if (!(Abc_ObjIsNode(pObj2) || Abc_ObjIsPi(pObj2))) continue;
  //     int id = Abc_ObjId(pObj2);
  //     Abc_Print(1, "Node %d (%s):\n", id, Abc_ObjIsNode(pObj2) ? "AND" : "PI");

  //     auto& myCuts = Cuts[id];
  //     for (size_t t = 0; t < myCuts.size(); ++t) {
  //         const auto& cut = myCuts[t];
  //         printf("  cut %zu: ", t);
  //         for (size_t j = 0; j < cut.size(); ++j) {
  //             printf("%d ", cut[j]);
  //         }
  //         printf("\n");
  //     }
  // }
}

int Lsv_CommandPrintMOCut(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c;
  int k = atoi(argv[globalUtilOptind]);
  int l = atoi(argv[globalUtilOptind + 1]);
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

  if (argc - globalUtilOptind != 2) {
    Abc_Print(-1, "Expect two arguments: <k> <l>.\n");
    goto usage;
  }


  if (k < 3 || k > 6 || l < 1 || l > 4) {
    Abc_Print(-1, "Invalid arguments: k must be 3..6, l must be 1..4.\n");
    goto usage;
  }

  Lsv_NtkPrintMOCut(pNtk, k, l);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_printmocut <k> <l> [-h]\n");
  Abc_Print(-2, "\t    enumerate k-l multi-output cuts in the network\n");
  Abc_Print(-2, "\t-h : print this command usage\n");
  return 1;
}
// -----------------------------------------------------------------
static int Lsv_CommandUnateBdd( Abc_Frame_t * pAbc, int argc, char ** argv )
{
#ifdef ABC_USE_CUDD
    Abc_Ntk_t * pNtk;          // 當前 frame 裡的 network（可能是 collapse 後）
    Abc_Ntk_t * pAig;          // 我們自己要用來做 BDD 的 AIG
    Abc_Ntk_t * pAigToDelete = NULL; // 如果是我們新建的 AIG，最後要刪掉

    DdManager * dd;
    Abc_Obj_t * pCo;
    DdNode * f, * x, * nx;
    DdNode * f0, * f1;
    DdNode * bad_pos, * bad_neg;
    DdNode * pZero;

    int poIdx, piIdx;
    int nPi, nCi;

    // ---------------- parse arguments ----------------
    if ( argc != 3 )
    {
        Abc_Print( 1, "usage: lsv_unate_bdd <po_index> <pi_index>\n" );
        return 1;
    }
    poIdx = atoi( argv[1] );
    piIdx = atoi( argv[2] );

    // ---------------- get current network ----------------
    pNtk = Abc_FrameReadNtk( pAbc );
    if ( pNtk == NULL )
    {
        Abc_Print( 1, "lsv_unate_bdd: empty network.\n" );
        return 1;
    }

    // ---------------- 確保有 AIG：不是 AIG 就自己 strash 一份 ----------------
    if ( Abc_NtkIsStrash( pNtk ) )
    {
        // 已經是 AIG，就直接用
        pAig = pNtk;
    }
    else
    {
        // 例如 collapse 後的 network，先轉成 AIG
        pAig = Abc_NtkStrash( pNtk, 0, 0, 0 );
        if ( pAig == NULL )
        {
            Abc_Print( 1, "lsv_unate_bdd: Abc_NtkStrash failed.\n" );
            return 1;
        }
        pAigToDelete = pAig; // 記得這是我們生的，最後要刪
    }

    nPi = Abc_NtkPiNum( pAig );
    nCi = Abc_NtkCiNum( pAig );

    if ( poIdx < 0 || poIdx >= Abc_NtkPoNum( pAig ) )
    {
        Abc_Print( 1, "lsv_unate_bdd: po_index %d out of range.\n", poIdx );
        if ( pAigToDelete ) Abc_NtkDelete( pAigToDelete );
        return 1;
    }
    if ( piIdx < 0 || piIdx >= nPi )
    {
        Abc_Print( 1, "lsv_unate_bdd: pi_index %d out of range (0..%d).\n", piIdx, nPi-1 );
        if ( pAigToDelete ) Abc_NtkDelete( pAigToDelete );
        return 1;
    }

    // ---------------- 在「自己的 AIG」上建 global BDDs ----------------
    // 這裡完全不理 collapse 的 BDD manager，每次都自己建、自己 free
    dd = (DdManager *)Abc_NtkBuildGlobalBdds( pAig, 10000000, 1, 1, 0, 0 );
    if ( dd == NULL )
    {
        Abc_Print( 1, "lsv_unate_bdd: Abc_NtkBuildGlobalBdds() failed.\n" );
        if ( pAigToDelete ) Abc_NtkDelete( pAigToDelete );
        return 1;
    }

    // ---------------- get f (PO 的 BDD) ----------------
    pCo = Abc_NtkCo( pAig, poIdx );
    if ( pCo == NULL )
    {
        Abc_Print( 1, "lsv_unate_bdd: cannot find CO %d.\n", poIdx );
        Abc_NtkFreeGlobalBdds( pAig, 1 );
        if ( pAigToDelete ) Abc_NtkDelete( pAigToDelete );
        return 1;
    }

    // f 是我們剛 build 的 global BDD，由 ABC 管，不要 Ref/Deref
    f = (DdNode *)Abc_ObjGlobalBdd( pCo );
    if ( f == NULL )
    {
        Abc_Print( 1, "lsv_unate_bdd: PO %d has no global BDD.\n", poIdx );
        Abc_NtkFreeGlobalBdds( pAig, 1 );
        if ( pAigToDelete ) Abc_NtkDelete( pAigToDelete );
        return 1;
    }

    // ---------------- compute cofactors f0, f1 ----------------
    x  = Cudd_bddIthVar( dd, piIdx );  // 把 piIdx 當第 piIdx 個 BDD 變數
    nx = Cudd_Not( x );

    f0 = Cudd_Cofactor( dd, f, nx );   // f(xi=0, others)
    if ( f0 == NULL )
    {
        Abc_Print( 1, "lsv_unate_bdd: Cudd_Cofactor(f, !xi) failed.\n" );
        Abc_NtkFreeGlobalBdds( pAig, 1 );
        if ( pAigToDelete ) Abc_NtkDelete( pAigToDelete );
        return 1;
    }
    Cudd_Ref( f0 );

    f1 = Cudd_Cofactor( dd, f, x );    // f(xi=1, others)
    if ( f1 == NULL )
    {
        Abc_Print( 1, "lsv_unate_bdd: Cudd_Cofactor(f, xi) failed.\n" );
        Cudd_RecursiveDeref( dd, f0 );
        Abc_NtkFreeGlobalBdds( pAig, 1 );
        if ( pAigToDelete ) Abc_NtkDelete( pAigToDelete );
        return 1;
    }
    Cudd_Ref( f1 );

    // ---- debug: print f0, f1 BDDs ----
    // Abc_Print( 1, "Debug: f0 = f with x_%d = 0\n", piIdx );
    // Cudd_PrintDebug( dd, f0, Cudd_ReadSize(dd), 2 );

    // Abc_Print( 1, "Debug: f1 = f with x_%d = 1\n", piIdx );
    // Cudd_PrintDebug( dd, f1, Cudd_ReadSize(dd), 2 );

    // ---------------- independent? (f0 == f1) ----------------
    if ( f0 == f1 )
    {
        Abc_Print( 1, "independent\n" );
        Cudd_RecursiveDeref( dd, f0 );
        Cudd_RecursiveDeref( dd, f1 );
        Abc_NtkFreeGlobalBdds( pAig, 1 );
        if ( pAigToDelete ) Abc_NtkDelete( pAigToDelete );
        return 0;
    }

    // ---------------- compute bad_pos / bad_neg ----------------
    // bad_pos: 1→0 (違反 positive unate)
    bad_pos = Cudd_bddAnd( dd, f0, Cudd_Not( f1 ) );
    if ( bad_pos == NULL )
    {
        Abc_Print( 1, "lsv_unate_bdd: Cudd_bddAnd(f0, !f1) failed.\n" );
        Cudd_RecursiveDeref( dd, f0 );
        Cudd_RecursiveDeref( dd, f1 );
        Abc_NtkFreeGlobalBdds( pAig, 1 );
        if ( pAigToDelete ) Abc_NtkDelete( pAigToDelete );
        return 1;
    }
    Cudd_Ref( bad_pos );

    // bad_neg: 0→1 (違反 negative unate)
    bad_neg = Cudd_bddAnd( dd, Cudd_Not( f0 ), f1 );
    if ( bad_neg == NULL )
    {
        Abc_Print( 1, "lsv_unate_bdd: Cudd_bddAnd(!f0, f1) failed.\n" );
        Cudd_RecursiveDeref( dd, bad_pos );
        Cudd_RecursiveDeref( dd, f0 );
        Cudd_RecursiveDeref( dd, f1 );
        Abc_NtkFreeGlobalBdds( pAig, 1 );
        if ( pAigToDelete ) Abc_NtkDelete( pAigToDelete );
        return 1;
    }
    Cudd_Ref( bad_neg );

    pZero = Cudd_ReadLogicZero( dd );
    
    // ---- debug print: bad_pos, bad_neg ----
    // Abc_Print(1, "Debug: bad_pos (violates positive unate: 1→0)\n");
    // Cudd_PrintDebug(dd, bad_pos, Cudd_ReadSize(dd), 2);

    // Abc_Print(1, "Debug: bad_neg (violates negative unate: 0→1)\n");
    // Cudd_PrintDebug(dd, bad_neg, Cudd_ReadSize(dd), 2);

    // ---------------- classify non-binate cases ----------------
    if ( bad_pos == pZero && bad_neg == pZero )
    {
        Abc_Print( 1, "independent\n" );
        Cudd_RecursiveDeref( dd, bad_pos );
        Cudd_RecursiveDeref( dd, bad_neg );
        Cudd_RecursiveDeref( dd, f0 );
        Cudd_RecursiveDeref( dd, f1 );
        Abc_NtkFreeGlobalBdds( pAig, 1 );
        if ( pAigToDelete ) Abc_NtkDelete( pAigToDelete );
        return 0;
    }
    else if ( bad_pos == pZero )
    {
        Abc_Print( 1, "positive unate\n" );
        Cudd_RecursiveDeref( dd, bad_pos );
        Cudd_RecursiveDeref( dd, bad_neg );
        Cudd_RecursiveDeref( dd, f0 );
        Cudd_RecursiveDeref( dd, f1 );
        Abc_NtkFreeGlobalBdds( pAig, 1 );
        if ( pAigToDelete ) Abc_NtkDelete( pAigToDelete );
        return 0;
    }
    else if ( bad_neg == pZero )
    {
        Abc_Print( 1, "negative unate\n" );
        Cudd_RecursiveDeref( dd, bad_pos );
        Cudd_RecursiveDeref( dd, bad_neg );
        Cudd_RecursiveDeref( dd, f0 );
        Cudd_RecursiveDeref( dd, f1 );
        Abc_NtkFreeGlobalBdds( pAig, 1 );
        if ( pAigToDelete ) Abc_NtkDelete( pAigToDelete );
        return 0;
    }

    // ---------------- binate: 兩個 witness pattern ----------------
    {
        Abc_Print( 1, "binate\n" );

        char *pattern1 = (char *)malloc( sizeof(char) * (nPi + 1) );
        char *pattern2 = (char *)malloc( sizeof(char) * (nPi + 1) );
        if ( pattern1 == NULL || pattern2 == NULL )
        {
            Abc_Print( 1, "lsv_unate_bdd: malloc(pattern) failed.\n" );
            free( pattern1 );
            free( pattern2 );
            Cudd_RecursiveDeref( dd, bad_pos );
            Cudd_RecursiveDeref( dd, bad_neg );
            Cudd_RecursiveDeref( dd, f0 );
            Cudd_RecursiveDeref( dd, f1 );
            Abc_NtkFreeGlobalBdds( pAig, 1 );
            if ( pAigToDelete ) Abc_NtkDelete( pAigToDelete );
            return 1;
        }

        DdNode *w0, *w1;

        // -------- pattern1: 從 bad_neg (f0=0, f1=1 → y 像 x_i) --------
        for ( int j = 0; j < nPi; ++j )
        {
            if ( j == piIdx )
            {
                pattern1[j] = '-';
                continue;
            }

            DdNode *var = Cudd_bddIthVar( dd, j );
            w0 = Cudd_Cofactor( dd, bad_neg, Cudd_Not( var ) );
            if ( w0 == NULL )
            {
                Abc_Print( 1, "lsv_unate_bdd: Cudd_Cofactor(bad_neg, !x_%d) failed.\n", j );
                Cudd_RecursiveDeref( dd, bad_pos );
                Cudd_RecursiveDeref( dd, bad_neg );
                Cudd_RecursiveDeref( dd, f0 );
                Cudd_RecursiveDeref( dd, f1 );
                Abc_NtkFreeGlobalBdds( pAig, 1 );
                free( pattern1 );
                free( pattern2 );
                if ( pAigToDelete ) Abc_NtkDelete( pAigToDelete );
                return 1;
            }
            Cudd_Ref( w0 );

            w1 = Cudd_Cofactor( dd, bad_neg, var );
            if ( w1 == NULL )
            {
                Abc_Print( 1, "lsv_unate_bdd: Cudd_Cofactor(bad_neg, x_%d) failed.\n", j );
                Cudd_RecursiveDeref( dd, w0 );
                Cudd_RecursiveDeref( dd, bad_pos );
                Cudd_RecursiveDeref( dd, bad_neg );
                Cudd_RecursiveDeref( dd, f0 );
                Cudd_RecursiveDeref( dd, f1 );
                Abc_NtkFreeGlobalBdds( pAig, 1 );
                free( pattern1 );
                free( pattern2 );
                if ( pAigToDelete ) Abc_NtkDelete( pAigToDelete );
                return 1;
            }
            Cudd_Ref( w1 );

            if ( w0 != Cudd_ReadLogicZero( dd ) && w1 == Cudd_ReadLogicZero( dd ) )
                pattern1[j] = '0';
            else if ( w1 != Cudd_ReadLogicZero( dd ) && w0 == Cudd_ReadLogicZero( dd ) )
                pattern1[j] = '1';
            else
                pattern1[j] = '0';  // don't care → 統一補 0

            Cudd_RecursiveDeref( dd, w0 );
            Cudd_RecursiveDeref( dd, w1 );
        }
        pattern1[nPi] = '\0';
        Abc_Print( 1, "%s\n", pattern1 );

        // -------- pattern2: 從 bad_pos (f0=1, f1=0 → y 像 !x_i) --------
        for ( int j = 0; j < nPi; ++j )
        {
            if ( j == piIdx )
            {
                pattern2[j] = '-';
                continue;
            }

            DdNode *var = Cudd_bddIthVar( dd, j );
            w0 = Cudd_Cofactor( dd, bad_pos, Cudd_Not( var ) );
            if ( w0 == NULL )
            {
                Abc_Print( 1, "lsv_unate_bdd: Cudd_Cofactor(bad_pos, !x_%d) failed.\n", j );
                Cudd_RecursiveDeref( dd, bad_pos );
                Cudd_RecursiveDeref( dd, bad_neg );
                Cudd_RecursiveDeref( dd, f0 );
                Cudd_RecursiveDeref( dd, f1 );
                Abc_NtkFreeGlobalBdds( pAig, 1 );
                free( pattern1 );
                free( pattern2 );
                if ( pAigToDelete ) Abc_NtkDelete( pAigToDelete );
                return 1;
            }
            Cudd_Ref( w0 );

            w1 = Cudd_Cofactor( dd, bad_pos, var );
            if ( w1 == NULL )
            {
                Abc_Print( 1, "lsv_unate_bdd: Cudd_Cofactor(bad_pos, x_%d) failed.\n", j );
                Cudd_RecursiveDeref( dd, w0 );
                Cudd_RecursiveDeref( dd, bad_pos );
                Cudd_RecursiveDeref( dd, bad_neg );
                Cudd_RecursiveDeref( dd, f0 );
                Cudd_RecursiveDeref( dd, f1 );
                Abc_NtkFreeGlobalBdds( pAig, 1 );
                free( pattern1 );
                free( pattern2 );
                if ( pAigToDelete ) Abc_NtkDelete( pAigToDelete );
                return 1;
            }
            Cudd_Ref( w1 );

            if ( w0 != Cudd_ReadLogicZero( dd ) && w1 == Cudd_ReadLogicZero( dd ) )
                pattern2[j] = '0';
            else if ( w1 != Cudd_ReadLogicZero( dd ) && w0 == Cudd_ReadLogicZero( dd ) )
                pattern2[j] = '1';
            else
                pattern2[j] = '0';

            Cudd_RecursiveDeref( dd, w0 );
            Cudd_RecursiveDeref( dd, w1 );
        }
        pattern2[nPi] = '\0';
        Abc_Print( 1, "%s\n", pattern2 );

        free( pattern1 );
        free( pattern2 );
    }

    // ---------------- cleanup BDDs & AIG ----------------
    Cudd_RecursiveDeref( dd, bad_pos );
    Cudd_RecursiveDeref( dd, bad_neg );
    Cudd_RecursiveDeref( dd, f0 );
    Cudd_RecursiveDeref( dd, f1 );

    Abc_NtkFreeGlobalBdds( pAig, 1 );
    if ( pAigToDelete )
        Abc_NtkDelete( pAigToDelete );

    return 0;

#else
    Abc_Print( 1, "lsv_unate_bdd: ABC was compiled without CUDD (ABC_USE_CUDD not defined).\n" );
    return 1;
#endif
}



// ----------------bdd myself---------------------
// static int Lsv_CommandUnateBdd( Abc_Frame_t * pAbc, int argc, char ** argv )
// {
// #ifdef ABC_USE_CUDD
//     Abc_Ntk_t * pNtk;
//     DdManager * dd;
//     Abc_Obj_t * pCo;
//     DdNode * f, * x, * nx;
//     DdNode * f0, * f1;
//     DdNode * bad_pos, * bad_neg;
//     DdNode * pZero;

//     int poIdx, piIdx;
//     int nPi, nCi;

//     // ---------------- parse arguments ----------------
//     if ( argc != 3 )
//     {
//         Abc_Print( 1, "usage: lsv_unate_bdd <po_index> <pi_index>\n" );
//         return 1;
//     }
//     poIdx = atoi( argv[1] );
//     piIdx = atoi( argv[2] );

//     // ---------------- basic checks ----------------
//     pNtk = Abc_FrameReadNtk( pAbc );
//     if ( pNtk == NULL )
//     {
//         Abc_Print( 1, "lsv_unate_bdd: empty network.\n" );
//         return 1;
//     }

//     // 跟 print_unate 一樣：要求 AIG network
//     if ( !Abc_NtkIsStrash( pNtk ) )
//     {
//         Abc_Print( 1, "lsv_unate_bdd: this command works only for AIGs (run \"strash\").\n" );
//         return 1;
//     }

//     nPi = Abc_NtkPiNum( pNtk );
//     nCi = Abc_NtkCiNum( pNtk );

//     if ( poIdx < 0 || poIdx >= Abc_NtkPoNum( pNtk ) )
//     {
//         Abc_Print( 1, "lsv_unate_bdd: po_index %d out of range.\n", poIdx );
//         return 1;
//     }
//     if ( piIdx < 0 || piIdx >= nPi )
//     {
//         Abc_Print( 1, "lsv_unate_bdd: pi_index %d out of range (0..%d).\n", piIdx, nPi-1 );
//         return 1;
//     }

//     // ---------------- build global BDDs (跟 Abc_NtkPrintUnate 一樣) ----------------
//     // 10000000 = max nodes, 1/1/0/0 = flags, 詳細意義照 abcUnate.c
//     dd = (DdManager *)Abc_NtkBuildGlobalBdds( pNtk, 10000000, 1, 1, 0, 0 );
//     if ( dd == NULL )
//     {
//         Abc_Print( 1, "lsv_unate_bdd: Abc_NtkBuildGlobalBdds() failed.\n" );
//         return 1;
//     }

//     // ---------------- get f (PO 的 BDD) ----------------
//     pCo = Abc_NtkCo( pNtk, poIdx );
//     if ( pCo == NULL )
//     {
//         Abc_Print( 1, "lsv_unate_bdd: cannot find CO %d.\n", poIdx );
//         Abc_NtkFreeGlobalBdds( pNtk, 1 );
//         return 1;
//     }

//     // 注意：f 是 global BDD，由 Abc_NtkBuildGlobalBdds 管理 → 不要 Ref/Deref f
//     f = (DdNode *)Abc_ObjGlobalBdd( pCo );
//     if ( f == NULL )
//     {
//         Abc_Print( 1, "lsv_unate_bdd: PO %d has no global BDD.\n", poIdx );
//         Abc_NtkFreeGlobalBdds( pNtk, 1 );
//         return 1;
//     }

//     // ---------------- compute cofactors f0, f1 ----------------
//     x  = Cudd_bddIthVar( dd, piIdx );  // 把 piIdx 當成第 piIdx 個 BDD 變數
//     nx = Cudd_Not( x );

//     f0 = Cudd_Cofactor( dd, f, nx );   // f(xi=0, others)
//     if ( f0 == NULL )
//     {
//         Abc_Print( 1, "lsv_unate_bdd: Cudd_Cofactor(f, !xi) failed.\n" );
//         Abc_NtkFreeGlobalBdds( pNtk, 1 );
//         return 1;
//     }
//     Cudd_Ref( f0 );

//     f1 = Cudd_Cofactor( dd, f, x );    // f(xi=1, others)
//     if ( f1 == NULL )
//     {
//         Abc_Print( 1, "lsv_unate_bdd: Cudd_Cofactor(f, xi) failed.\n" );
//         Cudd_RecursiveDeref( dd, f0 );
//         Abc_NtkFreeGlobalBdds( pNtk, 1 );
//         return 1;
//     }
//     Cudd_Ref( f1 );

//     // ---- debug: print f0, f1 BDDs ----
//     Abc_Print( 1, "Debug: f0 = f with x_%d = 0\n", piIdx );
//     Cudd_PrintDebug( dd, f0, Cudd_ReadSize(dd), 2 );

//     Abc_Print( 1, "Debug: f1 = f with x_%d = 1\n", piIdx );
//     Cudd_PrintDebug( dd, f1, Cudd_ReadSize(dd), 2 );

//     // ---------------- independent? (f0 == f1) ----------------
//     if ( f0 == f1 )
//     {
//         Abc_Print( 1, "independent\n" );
//         Cudd_RecursiveDeref( dd, f0 );
//         Cudd_RecursiveDeref( dd, f1 );
//         Abc_NtkFreeGlobalBdds( pNtk, 1 );
//         return 0;
//     }

//     // ---------------- compute bad_pos / bad_neg ----------------
//     // bad_pos: 1→0 (違反 positive unate)
//     bad_pos = Cudd_bddAnd( dd, f0, Cudd_Not( f1 ) );
//     if ( bad_pos == NULL )
//     {
//         Abc_Print( 1, "lsv_unate_bdd: Cudd_bddAnd(f0, !f1) failed.\n" );
//         Cudd_RecursiveDeref( dd, f0 );
//         Cudd_RecursiveDeref( dd, f1 );
//         Abc_NtkFreeGlobalBdds( pNtk, 1 );
//         return 1;
//     }
//     Cudd_Ref( bad_pos );

//     // bad_neg: 0→1 (違反 negative unate)
//     bad_neg = Cudd_bddAnd( dd, Cudd_Not( f0 ), f1 );
//     if ( bad_neg == NULL )
//     {
//         Abc_Print( 1, "lsv_unate_bdd: Cudd_bddAnd(!f0, f1) failed.\n" );
//         Cudd_RecursiveDeref( dd, bad_pos );
//         Cudd_RecursiveDeref( dd, f0 );
//         Cudd_RecursiveDeref( dd, f1 );
//         Abc_NtkFreeGlobalBdds( pNtk, 1 );
//         return 1;
//     }
//     Cudd_Ref( bad_neg );

//     pZero = Cudd_ReadLogicZero( dd );
    
//     // ---- debug print: bad_pos, bad_neg ----
//     Abc_Print(1, "Debug: bad_pos (violates positive unate: 1→0)\n");
//     Cudd_PrintDebug(dd, bad_pos, Cudd_ReadSize(dd), 2);

//     Abc_Print(1, "Debug: bad_neg (violates negative unate: 0→1)\n");
//     Cudd_PrintDebug(dd, bad_neg, Cudd_ReadSize(dd), 2);


//     // ---------------- classify non-binate cases ----------------
//     if ( bad_pos == pZero && bad_neg == pZero )
//     {
//         // 理論上不會發生（因為 f0==f1 已經被抓走），保險起見當 independent
//         Abc_Print( 1, "independent\n" );
//         Cudd_RecursiveDeref( dd, bad_pos );
//         Cudd_RecursiveDeref( dd, bad_neg );
//         Cudd_RecursiveDeref( dd, f0 );
//         Cudd_RecursiveDeref( dd, f1 );
//         Abc_NtkFreeGlobalBdds( pNtk, 1 );
//         return 0;
//     }
//     else if ( bad_pos == pZero )
//     {
//         Abc_Print( 1, "positive unate\n" );
//         Cudd_RecursiveDeref( dd, bad_pos );
//         Cudd_RecursiveDeref( dd, bad_neg );
//         Cudd_RecursiveDeref( dd, f0 );
//         Cudd_RecursiveDeref( dd, f1 );
//         Abc_NtkFreeGlobalBdds( pNtk, 1 );
//         return 0;
//     }
//     else if ( bad_neg == pZero )
//     {
//         Abc_Print( 1, "negative unate\n" );
//         Cudd_RecursiveDeref( dd, bad_pos );
//         Cudd_RecursiveDeref( dd, bad_neg );
//         Cudd_RecursiveDeref( dd, f0 );
//         Cudd_RecursiveDeref( dd, f1 );
//         Abc_NtkFreeGlobalBdds( pNtk, 1 );
//         return 0;
//     }

//         // ---------------- binate: 兩個 witness pattern ----------------
//     {
//         Abc_Print( 1, "binate\n" );

//         char *pattern1 = (char *)malloc( sizeof(char) * (nPi + 1) );
//         char *pattern2 = (char *)malloc( sizeof(char) * (nPi + 1) );
//         if ( pattern1 == NULL || pattern2 == NULL )
//         {
//             Abc_Print( 1, "lsv_unate_bdd: malloc(pattern) failed.\n" );
//             free( pattern1 );
//             free( pattern2 );
//             Cudd_RecursiveDeref( dd, bad_pos );
//             Cudd_RecursiveDeref( dd, bad_neg );
//             Cudd_RecursiveDeref( dd, f0 );
//             Cudd_RecursiveDeref( dd, f1 );
//             Abc_NtkFreeGlobalBdds( pNtk, 1 );
//             return 1;
//         }

//         DdNode *w0, *w1;

//         // -------- pattern1: 從 bad_neg (f0=0, f1=1 → y 像 x_i) --------
//         for ( int j = 0; j < nPi; ++j )
//         {
//             if ( j == piIdx )
//             {
//                 pattern1[j] = '-';
//                 continue;
//             }

//             DdNode *var = Cudd_bddIthVar( dd, j );
//             // w0 = bad_neg | x_j = 0
//             w0 = Cudd_Cofactor( dd, bad_neg, Cudd_Not( var ) );
//             if ( w0 == NULL )
//             {
//                 Abc_Print( 1, "lsv_unate_bdd: Cudd_Cofactor(bad_neg, !x_%d) failed.\n", j );
//                 Cudd_RecursiveDeref( dd, bad_pos );
//                 Cudd_RecursiveDeref( dd, bad_neg );
//                 Cudd_RecursiveDeref( dd, f0 );
//                 Cudd_RecursiveDeref( dd, f1 );
//                 Abc_NtkFreeGlobalBdds( pNtk, 1 );
//                 free( pattern1 );
//                 free( pattern2 );
//                 return 1;
//             }
//             Cudd_Ref( w0 );

//             // w1 = bad_neg | x_j = 1
//             w1 = Cudd_Cofactor( dd, bad_neg, var );
//             if ( w1 == NULL )
//             {
//                 Abc_Print( 1, "lsv_unate_bdd: Cudd_Cofactor(bad_neg, x_%d) failed.\n", j );
//                 Cudd_RecursiveDeref( dd, w0 );
//                 Cudd_RecursiveDeref( dd, bad_pos );
//                 Cudd_RecursiveDeref( dd, bad_neg );
//                 Cudd_RecursiveDeref( dd, f0 );
//                 Cudd_RecursiveDeref( dd, f1 );
//                 Abc_NtkFreeGlobalBdds( pNtk, 1 );
//                 free( pattern1 );
//                 free( pattern2 );
//                 return 1;
//             }
//             Cudd_Ref( w1 );

//             if ( w0 != Cudd_ReadLogicZero( dd ) && w1 == Cudd_ReadLogicZero( dd ) )
//                 pattern1[j] = '0';
//             else if ( w1 != Cudd_ReadLogicZero( dd ) && w0 == Cudd_ReadLogicZero( dd ) )
//                 pattern1[j] = '1';
//             else
//                 pattern1[j] = '0';  // don't care → 統一補 0

//             Cudd_RecursiveDeref( dd, w0 );
//             Cudd_RecursiveDeref( dd, w1 );
//         }
//         pattern1[nPi] = '\0';
//         Abc_Print( 1, "%s\n", pattern1 );

//         // -------- pattern2: 從 bad_pos (f0=1, f1=0 → y 像 !x_i) --------
//         for ( int j = 0; j < nPi; ++j )
//         {
//             if ( j == piIdx )
//             {
//                 pattern2[j] = '-';
//                 continue;
//             }

//             DdNode *var = Cudd_bddIthVar( dd, j );
//             w0 = Cudd_Cofactor( dd, bad_pos, Cudd_Not( var ) );
//             if ( w0 == NULL )
//             {
//                 Abc_Print( 1, "lsv_unate_bdd: Cudd_Cofactor(bad_pos, !x_%d) failed.\n", j );
//                 Cudd_RecursiveDeref( dd, bad_pos );
//                 Cudd_RecursiveDeref( dd, bad_neg );
//                 Cudd_RecursiveDeref( dd, f0 );
//                 Cudd_RecursiveDeref( dd, f1 );
//                 Abc_NtkFreeGlobalBdds( pNtk, 1 );
//                 free( pattern1 );
//                 free( pattern2 );
//                 return 1;
//             }
//             Cudd_Ref( w0 );

//             w1 = Cudd_Cofactor( dd, bad_pos, var );
//             if ( w1 == NULL )
//             {
//                 Abc_Print( 1, "lsv_unate_bdd: Cudd_Cofactor(bad_pos, x_%d) failed.\n", j );
//                 Cudd_RecursiveDeref( dd, w0 );
//                 Cudd_RecursiveDeref( dd, bad_pos );
//                 Cudd_RecursiveDeref( dd, bad_neg );
//                 Cudd_RecursiveDeref( dd, f0 );
//                 Cudd_RecursiveDeref( dd, f1 );
//                 Abc_NtkFreeGlobalBdds( pNtk, 1 );
//                 free( pattern1 );
//                 free( pattern2 );
//                 return 1;
//             }
//             Cudd_Ref( w1 );

//             if ( w0 != Cudd_ReadLogicZero( dd ) && w1 == Cudd_ReadLogicZero( dd ) )
//                 pattern2[j] = '0';
//             else if ( w1 != Cudd_ReadLogicZero( dd ) && w0 == Cudd_ReadLogicZero( dd ) )
//                 pattern2[j] = '1';
//             else
//                 pattern2[j] = '0';

//             Cudd_RecursiveDeref( dd, w0 );
//             Cudd_RecursiveDeref( dd, w1 );
//         }
//         pattern2[nPi] = '\0';
//         Abc_Print( 1, "%s\n", pattern2 );

//         free( pattern1 );
//         free( pattern2 );
//     }



//     // ---------------- cleanup BDDs & manager ----------------
//     Cudd_RecursiveDeref( dd, bad_pos );
//     Cudd_RecursiveDeref( dd, bad_neg );
//     Cudd_RecursiveDeref( dd, f0 );
//     Cudd_RecursiveDeref( dd, f1 );

//     Abc_NtkFreeGlobalBdds( pNtk, 1 );
//     return 0;

// #else
//     Abc_Print( 1, "lsv_unate_bdd: ABC was compiled without CUDD (ABC_USE_CUDD not defined).\n" );
//     return 1;
// #endif
// }
// ----------------bdd myself---------------------

// static int Lsv_CommandUnateBdd( Abc_Frame_t * pAbc, int argc, char ** argv )
// {
// #ifdef ABC_USE_CUDD
//     Abc_Ntk_t * pNtk;
//     DdManager * dd;
//     Abc_Obj_t * pCo;
//     DdNode * f, * x, * nx;
//     DdNode * f0, * f1;
//     DdNode * bad_pos, * bad_neg;
//     DdNode * pZero;

//     int poIdx, piIdx;
//     int nPi;

//     // ---------------- parse arguments ----------------
//     if ( argc != 3 )
//     {
//         Abc_Print( 1, "usage: lsv_unate_bdd <po_index> <pi_index>\n" );
//         return 1;
//     }
//     poIdx = atoi( argv[1] );
//     piIdx = atoi( argv[2] );

//     // ---------------- basic checks ----------------
//     pNtk = Abc_FrameReadNtk( pAbc );
//     if ( pNtk == NULL )
//     {
//         Abc_Print( 1, "lsv_unate_bdd: empty network.\n" );
//         return 1;
//     }

//     nPi = Abc_NtkPiNum( pNtk );

//     if ( poIdx < 0 || poIdx >= Abc_NtkPoNum( pNtk ) )
//     {
//         Abc_Print( 1, "lsv_unate_bdd: po_index %d out of range.\n", poIdx );
//         return 1;
//     }
//     if ( piIdx < 0 || piIdx >= nPi )
//     {
//         Abc_Print( 1, "lsv_unate_bdd: pi_index %d out of range (0..%d).\n", piIdx, nPi-1 );
//         return 1;
//     }

//     // ---------------- get global BDD manager from collapse ----------------
//     dd = (DdManager *)Abc_NtkGlobalBddMan( pNtk );
//     if ( dd == NULL )
//     {
//         Abc_Print( 1, "lsv_unate_bdd: no global BDD manager. Did you run \"collapse\"?\n" );
//         return 1;
//     }

//     // ---------------- get f (PO 的 BDD) ----------------
//     pCo = Abc_NtkCo( pNtk, poIdx );
//     if ( pCo == NULL )
//     {
//         Abc_Print( 1, "lsv_unate_bdd: cannot find CO %d.\n", poIdx );
//         return 1;
//     }

//     // 注意：f 是 collapse 建的 global BDD，不要 Ref/Deref f
//     f = (DdNode *)Abc_ObjGlobalBdd( pCo );
//     if ( f == NULL )
//     {
//         Abc_Print( 1, "lsv_unate_bdd: PO %d has no global BDD.\n", poIdx );
//         return 1;
//     }

//     // ---------------- compute cofactors f0, f1 ----------------
//     x  = Cudd_bddIthVar( dd, piIdx );
//     nx = Cudd_Not( x );

//     f0 = Cudd_Cofactor( dd, f, nx );   // f(xi=0, others)
//     if ( f0 == NULL )
//     {
//         Abc_Print( 1, "lsv_unate_bdd: Cudd_Cofactor(f, !xi) failed.\n" );
//         return 1;
//     }
//     Cudd_Ref( f0 );

//     f1 = Cudd_Cofactor( dd, f, x );    // f(xi=1, others)
//     if ( f1 == NULL )
//     {
//         Abc_Print( 1, "lsv_unate_bdd: Cudd_Cofactor(f, xi) failed.\n" );
//         Cudd_RecursiveDeref( dd, f0 );
//         return 1;
//     }
//     Cudd_Ref( f1 );

//     // （debug，要的話留著）
//     Abc_Print( 1, "Debug: f0 = f with x_%d = 0\n", piIdx );
//     Cudd_PrintDebug( dd, f0, Cudd_ReadSize(dd), 2 );

//     Abc_Print( 1, "Debug: f1 = f with x_%d = 1\n", piIdx );
//     Cudd_PrintDebug( dd, f1, Cudd_ReadSize(dd), 2 );

//     // ---------------- independent? (f0 == f1) ----------------
//     if ( f0 == f1 )
//     {
//         Abc_Print( 1, "independent\n" );
//         Cudd_RecursiveDeref( dd, f0 );
//         Cudd_RecursiveDeref( dd, f1 );
//         return 0;
//     }

//     // ---------------- compute bad_pos / bad_neg ----------------
//     // bad_pos: 1→0 (違反 positive unate)
//     bad_pos = Cudd_bddAnd( dd, f0, Cudd_Not( f1 ) );
//     if ( bad_pos == NULL )
//     {
//         Abc_Print( 1, "lsv_unate_bdd: Cudd_bddAnd(f0, !f1) failed.\n" );
//         Cudd_RecursiveDeref( dd, f0 );
//         Cudd_RecursiveDeref( dd, f1 );
//         return 1;
//     }
//     Cudd_Ref( bad_pos );

//     // bad_neg: 0→1 (違反 negative unate)
//     bad_neg = Cudd_bddAnd( dd, Cudd_Not( f0 ), f1 );
//     if ( bad_neg == NULL )
//     {
//         Abc_Print( 1, "lsv_unate_bdd: Cudd_bddAnd(!f0, f1) failed.\n" );
//         Cudd_RecursiveDeref( dd, bad_pos );
//         Cudd_RecursiveDeref( dd, f0 );
//         Cudd_RecursiveDeref( dd, f1 );
//         return 1;
//     }
//     Cudd_Ref( bad_neg );

//     pZero = Cudd_ReadLogicZero( dd );

//     Abc_Print(1, "Debug: bad_pos (violates positive unate: 1→0)\n");
//     Cudd_PrintDebug(dd, bad_pos, Cudd_ReadSize(dd), 2);

//     Abc_Print(1, "Debug: bad_neg (violates negative unate: 0→1)\n");
//     Cudd_PrintDebug(dd, bad_neg, Cudd_ReadSize(dd), 2);

//     // ---------------- classify non-binate cases ----------------
//     if ( bad_pos == pZero && bad_neg == pZero )
//     {
//         Abc_Print( 1, "independent\n" );
//         Cudd_RecursiveDeref( dd, bad_pos );
//         Cudd_RecursiveDeref( dd, bad_neg );
//         Cudd_RecursiveDeref( dd, f0 );
//         Cudd_RecursiveDeref( dd, f1 );
//         return 0;
//     }
//     else if ( bad_pos == pZero )
//     {
//         Abc_Print( 1, "positive unate\n" );
//         Cudd_RecursiveDeref( dd, bad_pos );
//         Cudd_RecursiveDeref( dd, bad_neg );
//         Cudd_RecursiveDeref( dd, f0 );
//         Cudd_RecursiveDeref( dd, f1 );
//         return 0;
//     }
//     else if ( bad_neg == pZero )
//     {
//         Abc_Print( 1, "negative unate\n" );
//         Cudd_RecursiveDeref( dd, bad_pos );
//         Cudd_RecursiveDeref( dd, bad_neg );
//         Cudd_RecursiveDeref( dd, f0 );
//         Cudd_RecursiveDeref( dd, f1 );
//         return 0;
//     }

//     // ---------------- binate: 兩個 witness pattern ----------------
//     {
//         Abc_Print( 1, "binate\n" );

//         char *pattern1 = (char *)malloc( sizeof(char) * (nPi + 1) );
//         char *pattern2 = (char *)malloc( sizeof(char) * (nPi + 1) );
//         if ( pattern1 == NULL || pattern2 == NULL )
//         {
//             Abc_Print( 1, "lsv_unate_bdd: malloc(pattern) failed.\n" );
//             free( pattern1 );
//             free( pattern2 );
//             Cudd_RecursiveDeref( dd, bad_pos );
//             Cudd_RecursiveDeref( dd, bad_neg );
//             Cudd_RecursiveDeref( dd, f0 );
//             Cudd_RecursiveDeref( dd, f1 );
//             return 1;
//         }

//         DdNode *w0, *w1;

//         // -------- pattern1: 從 bad_neg (f0=0, f1=1 → y 像 x_i) --------
//         for ( int j = 0; j < nPi; ++j )
//         {
//             if ( j == piIdx )
//             {
//                 pattern1[j] = '-';
//                 continue;
//             }

//             DdNode *var = Cudd_bddIthVar( dd, j );
//             w0 = Cudd_Cofactor( dd, bad_neg, Cudd_Not( var ) );  // x_j = 0
//             if ( w0 == NULL )
//             {
//                 Abc_Print( 1, "lsv_unate_bdd: Cudd_Cofactor(bad_neg, !x_%d) failed.\n", j );
//                 free( pattern1 );
//                 free( pattern2 );
//                 Cudd_RecursiveDeref( dd, bad_pos );
//                 Cudd_RecursiveDeref( dd, bad_neg );
//                 Cudd_RecursiveDeref( dd, f0 );
//                 Cudd_RecursiveDeref( dd, f1 );
//                 return 1;
//             }
//             Cudd_Ref( w0 );

//             w1 = Cudd_Cofactor( dd, bad_neg, var );             // x_j = 1
//             if ( w1 == NULL )
//             {
//                 Abc_Print( 1, "lsv_unate_bdd: Cudd_Cofactor(bad_neg, x_%d) failed.\n", j );
//                 Cudd_RecursiveDeref( dd, w0 );
//                 free( pattern1 );
//                 free( pattern2 );
//                 Cudd_RecursiveDeref( dd, bad_pos );
//                 Cudd_RecursiveDeref( dd, bad_neg );
//                 Cudd_RecursiveDeref( dd, f0 );
//                 Cudd_RecursiveDeref( dd, f1 );
//                 return 1;
//             }
//             Cudd_Ref( w1 );

//             if ( w0 != Cudd_ReadLogicZero( dd ) && w1 == Cudd_ReadLogicZero( dd ) )
//                 pattern1[j] = '0';
//             else if ( w1 != Cudd_ReadLogicZero( dd ) && w0 == Cudd_ReadLogicZero( dd ) )
//                 pattern1[j] = '1';
//             else
//                 pattern1[j] = '0';  // don't care → 補 0

//             Cudd_RecursiveDeref( dd, w0 );
//             Cudd_RecursiveDeref( dd, w1 );
//         }
//         pattern1[nPi] = '\0';
//         Abc_Print( 1, "%s\n", pattern1 );

//         // -------- pattern2: 從 bad_pos (f0=1, f1=0 → y 像 !x_i) --------
//         for ( int j = 0; j < nPi; ++j )
//         {
//             if ( j == piIdx )
//             {
//                 pattern2[j] = '-';
//                 continue;
//             }

//             DdNode *var = Cudd_bddIthVar( dd, j );
//             w0 = Cudd_Cofactor( dd, bad_pos, Cudd_Not( var ) );
//             if ( w0 == NULL )
//             {
//                 Abc_Print( 1, "lsv_unate_bdd: Cudd_Cofactor(bad_pos, !x_%d) failed.\n", j );
//                 free( pattern1 );
//                 free( pattern2 );
//                 Cudd_RecursiveDeref( dd, bad_pos );
//                 Cudd_RecursiveDeref( dd, bad_neg );
//                 Cudd_RecursiveDeref( dd, f0 );
//                 Cudd_RecursiveDeref( dd, f1 );
//                 return 1;
//             }
//             Cudd_Ref( w0 );

//             w1 = Cudd_Cofactor( dd, bad_pos, var );
//             if ( w1 == NULL )
//             {
//                 Abc_Print( 1, "lsv_unate_bdd: Cudd_Cofactor(bad_pos, x_%d) failed.\n", j );
//                 Cudd_RecursiveDeref( dd, w0 );
//                 free( pattern1 );
//                 free( pattern2 );
//                 Cudd_RecursiveDeref( dd, bad_pos );
//                 Cudd_RecursiveDeref( dd, bad_neg );
//                 Cudd_RecursiveDeref( dd, f0 );
//                 Cudd_RecursiveDeref( dd, f1 );
//                 return 1;
//             }
//             Cudd_Ref( w1 );

//             if ( w0 != Cudd_ReadLogicZero( dd ) && w1 == Cudd_ReadLogicZero( dd ) )
//                 pattern2[j] = '0';
//             else if ( w1 != Cudd_ReadLogicZero( dd ) && w0 == Cudd_ReadLogicZero( dd ) )
//                 pattern2[j] = '1';
//             else
//                 pattern2[j] = '0';

//             Cudd_RecursiveDeref( dd, w0 );
//             Cudd_RecursiveDeref( dd, w1 );
//         }
//         pattern2[nPi] = '\0';
//         Abc_Print( 1, "%s\n", pattern2 );

//         free( pattern1 );
//         free( pattern2 );
//     }

//     // ---------------- cleanup (只清我們自己 Ref 的) ----------------
//     Cudd_RecursiveDeref( dd, bad_pos );
//     Cudd_RecursiveDeref( dd, bad_neg );
//     Cudd_RecursiveDeref( dd, f0 );
//     Cudd_RecursiveDeref( dd, f1 );

//     return 0;

// #else
//     Abc_Print( 1, "lsv_unate_bdd: ABC was compiled without CUDD (ABC_USE_CUDD not defined).\n" );
//     return 1;
// #endif
// }

// static int Lsv_CommandUnateBdd( Abc_Frame_t * pAbc, int argc, char ** argv )
// {
// #ifdef ABC_USE_CUDD
//     Abc_Ntk_t * pNtk;
//     DdManager * dd;
//     Abc_Obj_t * pCo;
//     DdNode * f, * x, * nx;
//     DdNode * f0, * f1;
//     DdNode * bad_pos, * bad_neg;
//     DdNode * pZero;

//     int poIdx, piIdx;
//     int nPi;

//     // ---------------- parse arguments ----------------
//     if ( argc != 3 )
//     {
//         Abc_Print( 1, "usage: lsv_unate_bdd <po_index> <pi_index>\n" );
//         return 1;
//     }
//     poIdx = atoi( argv[1] );
//     piIdx = atoi( argv[2] );

//     // ---------------- basic checks ----------------
//     pNtk = Abc_FrameReadNtk( pAbc );
//     if ( pNtk == NULL )
//     {
//         Abc_Print( 1, "lsv_unate_bdd: empty network.\n" );
//         return 1;
//     }

//     // if ( !Abc_NtkIsStrash( pNtk ) )
//     // {
//     //     Abc_Print( 1, "lsv_unate_bdd: this command works only for AIGs (run \"strash\").\n" );
//     //     return 1;
//     // }

//     nPi = Abc_NtkPiNum( pNtk );
//     if ( poIdx < 0 || poIdx >= Abc_NtkPoNum( pNtk ) )
//     {
//         Abc_Print( 1, "lsv_unate_bdd: po_index %d out of range.\n", poIdx );
//         return 1;
//     }
//     if ( piIdx < 0 || piIdx >= nPi )
//     {
//         Abc_Print( 1, "lsv_unate_bdd: pi_index %d out of range (0..%d).\n", piIdx, nPi-1 );
//         return 1;
//     }

//     // ---------------- build our own global BDDs ----------------
//         // ---------------- get BDD manager ----------------
//     int fOwnBdds = 0;   // 我們自己建的才要負責 free

//     dd = (DdManager *)Abc_NtkGlobalBddMan( pNtk );
//     if ( dd == NULL )
//     {
//         // network 裡目前沒有 global BDD (例如 TA 只做 strash 沒有 collapse)
//         // 這時候用 AIG 來 build 一份
//         if ( !Abc_NtkIsStrash( pNtk ) )
//         {
//             Abc_Print( 1, "lsv_unate_bdd: no global BDD; need AIG network (run \"strash\" without collapse).\n" );
//             return 1;
//         }

//         dd = (DdManager *)Abc_NtkBuildGlobalBdds( pNtk, 10000000, 1, 1, 0, 0 );
//         if ( dd == NULL )
//         {
//             Abc_Print( 1, "lsv_unate_bdd: Abc_NtkBuildGlobalBdds() failed.\n" );
//             return 1;
//         }
//         fOwnBdds = 1;   // 記得這是我們自己建的
//     }


//     // ---------------- get f (PO 的 BDD) ----------------
//     pCo = Abc_NtkCo( pNtk, poIdx );
//     if ( pCo == NULL )
//     {
//         Abc_Print( 1, "lsv_unate_bdd: cannot find CO %d.\n", poIdx );
//         if ( fOwnBdds )
//           Abc_NtkFreeGlobalBdds( pNtk, 1 );

//         return 1;
//     }

//     f = (DdNode *)Abc_ObjGlobalBdd( pCo );
//     if ( f == NULL )
//     {
//         Abc_Print( 1, "lsv_unate_bdd: PO %d has no global BDD.\n", poIdx );
//         if ( fOwnBdds )
//           Abc_NtkFreeGlobalBdds( pNtk, 1 );

//         return 1;
//     }

//     // ---------------- compute cofactors f0, f1 ----------------
//     x  = Cudd_bddIthVar( dd, piIdx );
//     nx = Cudd_Not( x );

//     f0 = Cudd_Cofactor( dd, f, nx );   // xi = 0
//     if ( f0 == NULL )
//     {
//         Abc_Print( 1, "lsv_unate_bdd: Cudd_Cofactor(f, !xi) failed.\n" );
//         if ( fOwnBdds )
//           Abc_NtkFreeGlobalBdds( pNtk, 1 );
//         return 1;
//     }
//     Cudd_Ref( f0 );

//     f1 = Cudd_Cofactor( dd, f, x );    // xi = 1
//     if ( f1 == NULL )
//     {
//         Abc_Print( 1, "lsv_unate_bdd: Cudd_Cofactor(f, xi) failed.\n" );
//         Cudd_RecursiveDeref( dd, f0 );
//         if ( fOwnBdds )
//           Abc_NtkFreeGlobalBdds( pNtk, 1 );
//         return 1;
//     }
//     Cudd_Ref( f1 );

//     // ---------------- independent? ----------------
//     if ( f0 == f1 )
//     {
//         Abc_Print( 1, "independent\n" );
//         Cudd_RecursiveDeref( dd, f0 );
//         Cudd_RecursiveDeref( dd, f1 );
//         if ( fOwnBdds )
//           Abc_NtkFreeGlobalBdds( pNtk, 1 );
//         return 0;
//     }

//     // ---------------- bad_pos / bad_neg ----------------
//     bad_pos = Cudd_bddAnd( dd, f0, Cudd_Not( f1 ) ); // 1→0
//     if ( bad_pos == NULL )
//     {
//         Abc_Print( 1, "lsv_unate_bdd: Cudd_bddAnd(f0, !f1) failed.\n" );
//         Cudd_RecursiveDeref( dd, f0 );
//         Cudd_RecursiveDeref( dd, f1 );
//         if ( fOwnBdds )
//           Abc_NtkFreeGlobalBdds( pNtk, 1 );
//         return 1;
//     }
//     Cudd_Ref( bad_pos );

//     bad_neg = Cudd_bddAnd( dd, Cudd_Not( f0 ), f1 ); // 0→1
//     if ( bad_neg == NULL )
//     {
//         Abc_Print( 1, "lsv_unate_bdd: Cudd_bddAnd(!f0, f1) failed.\n" );
//         Cudd_RecursiveDeref( dd, bad_pos );
//         Cudd_RecursiveDeref( dd, f0 );
//         Cudd_RecursiveDeref( dd, f1 );
//         if ( fOwnBdds )
//           Abc_NtkFreeGlobalBdds( pNtk, 1 );
//         return 1;
//     }
//     Cudd_Ref( bad_neg );

//     pZero = Cudd_ReadLogicZero( dd );

//     // ---------------- classify non-binate ----------------
//     if ( bad_pos == pZero && bad_neg == pZero )
//     {
//         Abc_Print( 1, "independent\n" );
//         Cudd_RecursiveDeref( dd, bad_pos );
//         Cudd_RecursiveDeref( dd, bad_neg );
//         Cudd_RecursiveDeref( dd, f0 );
//         Cudd_RecursiveDeref( dd, f1 );
//         if ( fOwnBdds )
//           Abc_NtkFreeGlobalBdds( pNtk, 1 );
//         return 0;
//     }
//     else if ( bad_pos == pZero )
//     {
//         Abc_Print( 1, "positive unate\n" );
//         Cudd_RecursiveDeref( dd, bad_pos );
//         Cudd_RecursiveDeref( dd, bad_neg );
//         Cudd_RecursiveDeref( dd, f0 );
//         Cudd_RecursiveDeref( dd, f1 );
//         if ( fOwnBdds )
//           Abc_NtkFreeGlobalBdds( pNtk, 1 );
//         return 0;
//     }
//     else if ( bad_neg == pZero )
//     {
//         Abc_Print( 1, "negative unate\n" );
//         Cudd_RecursiveDeref( dd, bad_pos );
//         Cudd_RecursiveDeref( dd, bad_neg );
//         Cudd_RecursiveDeref( dd, f0 );
//         Cudd_RecursiveDeref( dd, f1 );
//         if ( fOwnBdds )
//           Abc_NtkFreeGlobalBdds( pNtk, 1 );
//         return 0;
//     }

//     // ---------------- binate: pick one cube from each ----------------
//     {
//         Abc_Print( 1, "binate\n" );

//         int nVars = Cudd_ReadSize( dd );
//         char *cube = (char *)malloc( sizeof(char) * nVars );
//         char *pat1 = (char *)malloc( sizeof(char) * (nPi + 1) );
//         char *pat2 = (char *)malloc( sizeof(char) * (nPi + 1) );

//         if ( cube == NULL || pat1 == NULL || pat2 == NULL )
//         {
//             Abc_Print( 1, "lsv_unate_bdd: malloc in binate failed.\n" );
//             free( cube ); free( pat1 ); free( pat2 );
//             Cudd_RecursiveDeref( dd, bad_pos );
//             Cudd_RecursiveDeref( dd, bad_neg );
//             Cudd_RecursiveDeref( dd, f0 );
//             Cudd_RecursiveDeref( dd, f1 );
//             if ( fOwnBdds )
//               Abc_NtkFreeGlobalBdds( pNtk, 1 );
//             return 1;
//         }

//         // ----- pattern1 from bad_neg (behaves like x_i) -----
//         if ( Cudd_bddPickOneCube( dd, bad_neg, cube ) == 0 )
//         {
//             Abc_Print( 1, "lsv_unate_bdd: Cudd_bddPickOneCube(bad_neg) failed.\n" );
//         }
//         else
//         {
//             for ( int j = 0; j < nPi; ++j )
//             {
//                 if ( j == piIdx ) { pat1[j] = '-'; continue; }

//                 char c = cube[j];
//                 int bit;
//                 if ( c == '0' || c == 0 ) bit = 0;
//                 else if ( c == '1' || c == 1 ) bit = 1;
//                 else bit = 0; // don't care

//                 pat1[j] = bit ? '1' : '0';
//             }
//             pat1[nPi] = '\0';
//             Abc_Print( 1, "%s\n", pat1 );
//         }

//         // ----- pattern2 from bad_pos (behaves like !x_i) -----
//         if ( Cudd_bddPickOneCube( dd, bad_pos, cube ) == 0 )
//         {
//             Abc_Print( 1, "lsv_unate_bdd: Cudd_bddPickOneCube(bad_pos) failed.\n" );
//         }
//         else
//         {
//             for ( int j = 0; j < nPi; ++j )
//             {
//                 if ( j == piIdx ) { pat2[j] = '-'; continue; }

//                 char c = cube[j];
//                 int bit;
//                 if ( c == '0' || c == 0 ) bit = 0;
//                 else if ( c == '1' || c == 1 ) bit = 1;
//                 else bit = 0;

//                 pat2[j] = bit ? '1' : '0';
//             }
//             pat2[nPi] = '\0';
//             Abc_Print( 1, "%s\n", pat2 );
//         }

//         free( cube );
//         free( pat1 );
//         free( pat2 );
//     }

//     // ---------------- cleanup ----------------
//     Cudd_RecursiveDeref( dd, bad_pos );
//     Cudd_RecursiveDeref( dd, bad_neg );
//     Cudd_RecursiveDeref( dd, f0 );
//     Cudd_RecursiveDeref( dd, f1 );

//     if ( fOwnBdds )
//         Abc_NtkFreeGlobalBdds( pNtk, 1 );
//     return 0;

// #else
//     Abc_Print( 1, "lsv_unate_bdd: ABC was compiled without CUDD.\n" );
//     return 1;
// #endif
// }





// ---------------------------------------------------------
//----------------unate check w/ sat---------------------------------------
// 小工具：印 pattern（長度 = 原本網路的 PI 數）
static void Lsv_PrintPatternFromConePattern(
    char * pPatCone,      // 長度 nPiCone, 用 '0','1','-' 表示（cone 內）
    int nPiCone,
    int * pMapOrig2Cone,  // 長度 nPiOrig, 每個 origPI -> 對應 conePI index 或 -1
    int nPiOrig,
    int iXi               // 原始網路中 xi 的 index
)
{
    int i;
    for ( i = 0; i < nPiOrig; ++i )
    {
        if ( i == iXi )
        {
            putchar('-');
            continue;
        }
        int t = pMapOrig2Cone[i];
        char c = '0'; // cone 裡沒有的變數，隨便給 0
        if ( t >= 0 && t < nPiCone )
        {
            c = pPatCone[t];
            if ( c == '-' )
                c = '0'; // 理論上只有 xi 那個會是 '-'，但這邊保險一下
        }
        putchar(c);
    }
    putchar('\n');
}

// SAT 命令主體
static int Lsv_CommandUnateSat( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk;
    int k, i;
    int c;

    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "h")) != EOF )
    {
        switch ( c )
        {
        case 'h':
        default:
            Abc_Print( -2, "usage: lsv_unate_sat <k> <i>\n" );
            return 1;
        }
    }

    if ( argc - globalUtilOptind != 2 )
    {
        Abc_Print( -2, "usage: lsv_unate_sat <k> <i>\n" );
        return 1;
    }

    k = atoi( argv[globalUtilOptind] );
    i = atoi( argv[globalUtilOptind+1] );

    pNtk = Abc_FrameReadNtk( pAbc );
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "lsv_unate_sat: there is no current network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsStrash( pNtk ) )
    {
        Abc_Print( -1, "lsv_unate_sat: this command works only for AIGs (run \"strash\").\n" );
        return 1;
    }

    if ( k < 0 || k >= Abc_NtkPoNum(pNtk) )
    {
        Abc_Print( -1, "lsv_unate_sat: PO index %d is out of range.\n", k );
        return 1;
    }
    if ( i < 0 || i >= Abc_NtkPiNum(pNtk) )
    {
        Abc_Print( -1, "lsv_unate_sat: PI index %d is out of range.\n", i );
        return 1;
    }

    // debug: 基本資訊
    // Abc_Print( 1, "==== lsv_unate_sat debug ====\n" );
    // Abc_Print( 1, "Network name: %s\n", Abc_NtkName(pNtk) );
    // Abc_Print( 1, "Total POs = %d, Total PIs = %d\n",
    //            Abc_NtkPoNum(pNtk), Abc_NtkPiNum(pNtk) );
    // {
    //     Abc_Obj_t * pPoDbg = Abc_NtkPo( pNtk, k );
    //     Abc_Obj_t * pPiDbg = Abc_NtkPi( pNtk, i );
    //     Abc_Print( 1, "Target PO k=%d name=%s\n", k, Abc_ObjName(pPoDbg) );
    //     Abc_Print( 1, "Target PI i=%d name=%s\n", i, Abc_ObjName(pPiDbg) );
    // }

    // 抽出單一 PO 的 cone
    Abc_Obj_t * pPo   = Abc_NtkPo( pNtk, k );
    Abc_Obj_t * pRoot = Abc_ObjFanin0( pPo ); // driver
    int         fPoCompl = Abc_ObjFaninC0( pPo );  // ★ 原本 PO 這條 edge 上的補號

    if ( pRoot == NULL )
    {
        Abc_Print( -1, "lsv_unate_sat: PO %d has no fanin.\n", k );
        return 1;
    }

    // 檢查 root 型別是否符合 Abc_NtkCreateCone 的 assert
    if ( !Abc_ObjIsNode( pRoot ) &&
         !( Abc_NtkIsStrash( pNtk ) &&
            ( Abc_AigNodeIsConst( pRoot ) || Abc_ObjIsCi( pRoot ) ) ) )
    {
        Abc_Print( -1, "lsv_unate_sat: invalid cone root for PO %d.\n", k );
        return 1;
    }

    Abc_Ntk_t * pCone = Abc_NtkCreateCone( pNtk, pRoot, Abc_ObjName(pPo), 1 );
    if ( pCone == NULL )
    {
        Abc_Print( -1, "lsv_unate_sat: cannot create cone.\n" );
        return 1;
    }

    // ===== Debug: print cone structure =====
    // // Abc_Print(1, "=== Cone CI (PIs of cone) ===\n");
    // Abc_Obj_t * pObj;
    // int iii;

    // Abc_NtkForEachCi( pCone, pObj, iii )
    // {
    //     Abc_Print(1, "  CI %d: name=%s (ObjId=%d)\n",
    //               iii, Abc_ObjName(pObj), Abc_ObjId(pObj));
    // }

    // Abc_Print(1, "=== Cone CO (PO of cone) ===\n");
    // Abc_NtkForEachCo( pCone, pObj, iii )
    // {
    //     Abc_Print(1, "  CO %d: name=%s (ObjId=%d), fanin0 ObjId=%d\n",
    //               iii,
    //               Abc_ObjName(pObj),
    //               Abc_ObjId(pObj),
    //               Abc_ObjFanin0(pObj) ? Abc_ObjFanin0(pObj)->Id : -1);
    // }

    // Abc_Print(1, "=== Cone internal nodes (AND nodes) ===\n");
    // Abc_NtkForEachNode( pCone, pObj, iii )
    // {
    //     Abc_Obj_t * pF0 = Abc_ObjFanin0(pObj);
    //     Abc_Obj_t * pF1 = Abc_ObjFanin1(pObj);
    //     Abc_Print(1, "  Node ObjId=%d  fanin0=%d fanin1=%d\n",
    //               Abc_ObjId(pObj),
    //               pF0 ? Abc_ObjId(pF0) : -1,
    //               pF1 ? Abc_ObjId(pF1) : -1);
    // }
    // ===== end cone debug =====

    int nPiOrig = Abc_NtkPiNum( pNtk );
    int nPiCone = Abc_NtkPiNum( pCone );
    int ii, tt;

    // Abc_Print( 1, "Cone: nPiOrig = %d, nPiCone = %d\n", nPiOrig, nPiCone );
    // Abc_Print( 1, "Cone PIs:\n" );
    // for ( tt = 0; tt < nPiCone; ++tt )
    // {
    //     Abc_Obj_t * pPiConeDbg = Abc_NtkPi( pCone, tt );
    //     Abc_Print( 1, "  conePI[%d] name=%s\n", tt, Abc_ObjName(pPiConeDbg) );
    // }

    // 建立 origPI -> conePI 的對應（用名字比）
    int * pMapOrig2Cone = (int *)ABC_ALLOC( int, nPiOrig );
    for ( ii = 0; ii < nPiOrig; ++ii )
        pMapOrig2Cone[ii] = -1;

    for ( tt = 0; tt < nPiCone; ++tt )
    {
        Abc_Obj_t * pPiCone = Abc_NtkPi( pCone, tt );
        char const * pNameCone = Abc_ObjName( pPiCone );
        for ( ii = 0; ii < nPiOrig; ++ii )
        {
            Abc_Obj_t * pPiOrig = Abc_NtkPi( pNtk, ii );
            if ( !strcmp( Abc_ObjName(pPiOrig), pNameCone ) )
            {
                pMapOrig2Cone[ii] = tt;
                break;
            }
        }
    }

    // Abc_Print( 1, "Orig PI to Cone PI mapping (origIdx: name -> coneIdx):\n" );
    // for ( ii = 0; ii < nPiOrig; ++ii )
    // {
    //     Abc_Obj_t * pPiOrigDbg = Abc_NtkPi( pNtk, ii );
    //     Abc_Print( 1, "  origPI[%d] name=%s -> conePI=%d\n",
    //                ii, Abc_ObjName(pPiOrigDbg), pMapOrig2Cone[ii] );
    // }

    int iConeXi = pMapOrig2Cone[i];
    // Abc_Print( 1, "Target PI i=%d name=%s maps to conePI index %d\n",
    //            i, Abc_ObjName(Abc_NtkPi(pNtk, i)), iConeXi );

    // 如果 xi 不在 cone 裡 => independent
    if ( iConeXi == -1 )
    {
        Abc_Print( 1, "independent\n" );
        ABC_FREE( pMapOrig2Cone );
        Abc_NtkDelete( pCone );
        return 0;
    }

    // 轉成 AIG
    Aig_Man_t * pAig = Abc_NtkToDar( pCone, 0, 0 );
    if ( pAig == NULL )
    {
        Abc_Print( -1, "lsv_unate_sat: Abc_NtkToDar() failed.\n" );
        ABC_FREE( pMapOrig2Cone );
        Abc_NtkDelete( pCone );
        return 1;
    }

    // ===== Debug: print AIG structure =====
    // Abc_Print(1, "=== AIG CIs ===\n");
    // Aig_Obj_t * pAigObj;
    // int idx;

    // Aig_ManForEachCi( pAig, pAigObj, idx )
    // {
    //     Abc_Print(1, "  CI %d: AigId=%d\n", idx, Aig_ObjId(pAigObj));
    // }

    // Abc_Print(1, "=== AIG COs ===\n");
    // Aig_ManForEachCo( pAig, pAigObj, idx )
    // {
    //     Aig_Obj_t * pFan = Aig_ObjFanin0(pAigObj);
    //     int fCompl = Aig_ObjFaninC0(pAigObj);
    //     Abc_Print(1, "  CO %d: AigId=%d, fanin0 AigId=%d, compl=%d\n",
    //               idx, Aig_ObjId(pAigObj),
    //               pFan ? Aig_ObjId(pFan) : -1,
    //               fCompl);
    // }

    // Abc_Print(1, "=== AIG AND nodes ===\n");
    // Aig_ManForEachNode( pAig, pAigObj, idx )
    // {
    //     Aig_Obj_t * pF0 = Aig_ObjFanin0(pAigObj);
    //     Aig_Obj_t * pF1 = Aig_ObjFanin1(pAigObj);
    //     int c0 = Aig_ObjFaninC0(pAigObj);
    //     int c1 = Aig_ObjFaninC1(pAigObj);
    //     Abc_Print(1, "  Node AigId=%d  AND(%s%d, %s%d)\n",
    //               Aig_ObjId(pAigObj),
    //               c0 ? "~" : "", pF0 ? Aig_ObjId(pF0) : -1,
    //               c1 ? "~" : "", pF1 ? Aig_ObjId(pF1) : -1);
    // }
    // ===== end AIG debug =====

    // 建 CNF (copy A / copy B)
    Cnf_Dat_t * pCnfA = Cnf_Derive( pAig, 1 );
    Cnf_Dat_t * pCnfB = Cnf_Derive( pAig, 1 );

    if ( pCnfA == NULL || pCnfB == NULL )
    {
        Abc_Print( -1, "lsv_unate_sat: Cnf_Derive() failed.\n" );
        if ( pCnfA ) Cnf_DataFree( pCnfA );
        if ( pCnfB ) Cnf_DataFree( pCnfB );
        Aig_ManStop( pAig );
        ABC_FREE( pMapOrig2Cone );
        Abc_NtkDelete( pCone );
        return 1;
    }

    // ===== Debug Print CNF =====
    // 印 CNF A
    // Abc_Print(1, "===== CNF A =====\n");
    // for (int c = 0; c < pCnfA->nClauses; c++)
    // {
    //     int * pBeg = pCnfA->pClauses[c];
    //     int * pEnd = pCnfA->pClauses[c+1];  // 指到下一個 clause 的開頭

    //     Abc_Print(1, "clause %d: ", c);
    //     for (int * pLit = pBeg; pLit < pEnd; pLit++)
    //         Abc_Print(1, "%d ", *pLit);

    //     Abc_Print(1, "0\n");  // 這個 0 只是你印好看的，不是 CNF 裡原本的
    // }

    // // 印 CNF B
    // Abc_Print(1, "===== CNF B =====\n");
    // for (int c = 0; c < pCnfB->nClauses; c++)
    // {
    //     int * pBeg = pCnfB->pClauses[c];
    //     int * pEnd = pCnfB->pClauses[c+1];

    //     Abc_Print(1, "clause %d: ", c);
    //     for (int * pLit = pBeg; pLit < pEnd; pLit++)
    //         Abc_Print(1, "%d ", *pLit);

    //     Abc_Print(1, "0\n");
    // }

    // ===== End Debug Print CNF =====
    // ===== 真值表檢查：只用 copy A 檢查 CNF 是否等價於 cone =====
    // {
    //     // 只開一個新的 SAT，用 pCnfA
    //     sat_solver * pSatDbg = sat_solver_new();
    //     Cnf_DataWriteIntoSolverInt( pSatDbg, pCnfA, 1, 1 );

    //     int nPiCone = Abc_NtkPiNum( pCone );
    //     int * vA_pis_dbg = (int *)ABC_ALLOC( int, nPiCone );

    //     // 映射每個 cone PI -> CNF 變數
    //     for ( tt = 0; tt < nPiCone; ++tt )
    //     {
    //         Abc_Obj_t * pPiCone = Abc_NtkPi( pCone, tt );
    //         Aig_Obj_t * pPiAig  = (Aig_Obj_t *)pPiCone->pCopy;
    //         assert( pPiAig != NULL );
    //         vA_pis_dbg[tt] = pCnfA->pVarNums[ Aig_ObjId(pPiAig) ];
    //     }

    //     // y
    //     Aig_Obj_t * pCoAigDbg   = Aig_ManCo( pAig, 0 );
    //     Aig_Obj_t * pRootAigDbg = Aig_ObjFanin0(pCoAigDbg);
    //     int        fComplYCoDbg   = Aig_ObjFaninC0(pCoAigDbg);
    //     int        fComplYDbg   = fPoCompl ^ fComplYCoDbg;
    //     int        vA_y_dbg     = pCnfA->pVarNums[ Aig_ObjId(pRootAigDbg) ];

    //     Vec_Int_t * vAssump = Vec_IntAlloc( 8 );

    //     Abc_Print( 1, "=== Truth table check for cone (copy A) ===\n" );

    //     // 只適用小 cone（例如 2 個 PI 的 test_ab）
    //     if ( nPiCone <= 4 )
    //     {
    //         int numAssign = 1 << nPiCone; // 2^(nPiCone)
    //         for ( int mask = 0; mask < numAssign; ++mask )
    //         {
    //             Vec_IntClear( vAssump );

    //             // 設定每個 PI 的值
    //             for ( tt = 0; tt < nPiCone; ++tt )
    //             {
    //                 int bit = (mask >> tt) & 1; // 這個 PI 的 0/1
    //                 int var = vA_pis_dbg[tt];
    //                 // Abc_Var2Lit( var, sign )，sign=1 代表取反 (=0)，sign=0 代表 =1
    //                 Vec_IntPush( vAssump, Abc_Var2Lit( var, bit ? 0 : 1 ) );
    //             }

    //             int status = sat_solver_solve(
    //                 pSatDbg,
    //                 Vec_IntArray(vAssump),
    //                 Vec_IntArray(vAssump) + Vec_IntSize(vAssump),
    //                 0,0,0,0
    //             );
    //             assert( status == l_True ); // 組合電路 + 指定所有 PI 一定 SAT

    //             int valRoot = sat_solver_var_value( pSatDbg, vA_y_dbg );
    //             int valY    = fComplYDbg ? !valRoot : valRoot;

    //             Abc_Print( 1, "mask=%d : ", mask );
    //             for ( tt = 0; tt < nPiCone; ++tt )
    //             {
    //                 Abc_Obj_t * pPiConeDbg = Abc_NtkPi( pCone, tt );
    //                 int bit = (mask >> tt) & 1;
    //                 Abc_Print( 1, "%s=%d ", Abc_ObjName(pPiConeDbg), bit );
    //             }
    //             Abc_Print( 1, "-> y=%d\n", valY );
    //         }
    //     }

    //     Vec_IntFree( vAssump );
    //     ABC_FREE( vA_pis_dbg );
    //     sat_solver_delete( pSatDbg );
    // }
    // ===== 真值表檢查結束 =====

    // 把 copy B 的變數編號全部加上 offset
    Cnf_DataLift( pCnfB, pCnfA->nVars );

    // 建 SAT solver 並加入兩份 CNF
    sat_solver * pSat = sat_solver_new();
    Cnf_DataWriteIntoSolverInt( pSat, pCnfA, 1, 1 );
    Cnf_DataWriteIntoSolverInt( pSat, pCnfB, 1, 1 );

    // 找出每個 PI 在 A / B copy 的 SAT 變數（用 pCopy 對到 AIG）
    int * vA_pis = (int *)ABC_ALLOC( int, nPiCone );
    int * vB_pis = (int *)ABC_ALLOC( int, nPiCone );
    for ( tt = 0; tt < nPiCone; ++tt )
    {
        Abc_Obj_t * pPiCone = Abc_NtkPi( pCone, tt );
        Aig_Obj_t * pPiAig  = (Aig_Obj_t *)pPiCone->pCopy;  // ★ 正確 mapping
        assert( pPiAig != NULL );

        int id = Aig_ObjId( pPiAig );
        vA_pis[tt] = pCnfA->pVarNums[id];
        vB_pis[tt] = pCnfB->pVarNums[id];
    }

    // xi 的 SAT 變數（同樣用 pCopy）
    Abc_Obj_t * pXiCone = Abc_NtkPi( pCone, iConeXi );
    Aig_Obj_t * pXiAig  = (Aig_Obj_t *)pXiCone->pCopy;
    assert( pXiAig != NULL );

    int vA_xi = pCnfA->pVarNums[ Aig_ObjId( pXiAig ) ];
    int vB_xi = pCnfB->pVarNums[ Aig_ObjId( pXiAig ) ];

    // 正確取得 y 的 AIG node：CO 的 driver
    Aig_Obj_t * pCoAig   = Aig_ManCo( pAig, 0 );
    Aig_Obj_t * pRootAig = Aig_ObjFanin0(pCoAig);  // 這才是真正的 y function node
    // cone/AIG 裡 CO 的補號：
    int fComplCoAig = Aig_ObjFaninC0(pCoAig);
    // 真正 y 的總補號 = 原網路的補號 XOR cone/AIG 裡的補號
    int fComplY = fPoCompl ^ fComplCoAig;        // ★ 關鍵

    int vA_y = pCnfA->pVarNums[Aig_ObjId(pRootAig)];
    int vB_y = pCnfB->pVarNums[Aig_ObjId(pRootAig)];

    // Abc_Print( 1, "CNF var mapping for PIs:\n" );
    // for ( tt = 0; tt < nPiCone; ++tt )
    // {
    //     Abc_Obj_t * pPiConeDbg = Abc_NtkPi( pCone, tt );
    //     Abc_Print( 1, "  conePI[%d] name=%s vA=%d vB=%d\n",
    //                tt, Abc_ObjName(pPiConeDbg), vA_pis[tt], vB_pis[tt] );
    // }
    // Abc_Print( 1, "xi in cone: index=%d name=%s vA_xi=%d vB_xi=%d\n",
    //            iConeXi, Abc_ObjName(pXiCone), vA_xi, vB_xi );
    // Abc_Print( 1, "y vars: vA_y=%d vB_y=%d, fComplY=%d\n", vA_y, vB_y, fComplY );

    // 對除了 xi 以外所有 input 加 equality clause： vA == vB
    for ( tt = 0; tt < nPiCone; ++tt )
    {
        if ( tt == iConeXi )
            continue;

        int vA = vA_pis[tt];
        int vB = vB_pis[tt];
        lit Lits[2];

        // (¬vA ∨ vB)
        Lits[0] = Abc_Var2Lit( vA, 1 );
        Lits[1] = Abc_Var2Lit( vB, 0 );
        sat_solver_addclause( pSat, Lits, Lits+2 );

        // (vA ∨ ¬vB)
        Lits[0] = Abc_Var2Lit( vA, 0 );
        Lits[1] = Abc_Var2Lit( vB, 1 );
        sat_solver_addclause( pSat, Lits, Lits+2 );
    }

    // 開始做兩個 pattern 的 SAT 查詢
    Vec_Int_t * vAssump = Vec_IntAlloc( 8 );
    int has01 = 0, has10 = 0;
    char * pPat01 = NULL;
    char * pPat10 = NULL;

    int status;

    // (1) 0 -> 1 pattern: xiA=0, xiB=1, yA=0, yB=1
    // 若 y 在 CO 上有補 (~root)，就把 y=0/1 的 assignment 極性反過來
    int pol_yA_0 = fComplY ? 0 : 1; // y=0 -> root=1 if compl, else 0
    int pol_yA_1 = fComplY ? 1 : 0; // y=1 -> root=0 if compl, else 1

    Vec_IntClear( vAssump );
    Vec_IntPush( vAssump, Abc_Var2Lit( vA_xi, 1 ) ); // xiA=0
    Vec_IntPush( vAssump, Abc_Var2Lit( vB_xi, 0 ) ); // xiB=1
    // yA=0, yB=1  (根據 compl 做對應)
    Vec_IntPush( vAssump, Abc_Var2Lit( vA_y , pol_yA_0 ) );
    Vec_IntPush( vAssump, Abc_Var2Lit( vB_y , pol_yA_1 ) );

    status = sat_solver_solve( pSat,
        Vec_IntArray(vAssump),
        Vec_IntArray(vAssump) + Vec_IntSize(vAssump),
        0, 0, 0, 0 );

    // Abc_Print( 1, "[DEBUG] has01 solve status = %d (1=True, 0=False)\n", status );
    if ( status == l_True )
    {
        has01 = 1;
        // int val_xiA = sat_solver_var_value( pSat, vA_xi );
        // int val_xiB = sat_solver_var_value( pSat, vB_xi );
        // int val_yA  = sat_solver_var_value( pSat, vA_y );
        // int val_yB  = sat_solver_var_value( pSat, vB_y );
        // Abc_Print( 1, "[DEBUG] has01 model: xiA=%d xiB=%d yA=%d yB=%d\n",
        //            val_xiA, val_xiB, val_yA, val_yB );

        pPat01 = (char *)ABC_ALLOC( char, nPiCone );
        for ( tt = 0; tt < nPiCone; ++tt )
        {
            if ( tt == iConeXi )
            {
                pPat01[tt] = '-';
                continue;
            }
            int v = vA_pis[tt];
            int val = sat_solver_var_value( pSat, v ); // 0 or 1
            pPat01[tt] = val ? '1' : '0';
        }
    }

    // (2) 1 -> 0 pattern: xiA=0, xiB=1, yA=1, yB=0
    Vec_IntClear( vAssump );
    Vec_IntPush( vAssump, Abc_Var2Lit( vA_xi, 1 ) ); // xiA=0
    Vec_IntPush( vAssump, Abc_Var2Lit( vB_xi, 0 ) ); // xiB=1
    // yA=1, yB=0
    Vec_IntPush( vAssump, Abc_Var2Lit( vA_y , pol_yA_1 ) );
    Vec_IntPush( vAssump, Abc_Var2Lit( vB_y , pol_yA_0 ) );

    status = sat_solver_solve( pSat,
        Vec_IntArray(vAssump),
        Vec_IntArray(vAssump) + Vec_IntSize(vAssump),
        0, 0, 0, 0 );

    // Abc_Print( 1, "[DEBUG] has10 solve status = %d (1=True, 0=False)\n", status );
    if ( status == l_True )
    {
        has10 = 1;

        // int val_xiA = sat_solver_var_value( pSat, vA_xi );
        // int val_xiB = sat_solver_var_value( pSat, vB_xi );
        // int val_yA  = sat_solver_var_value( pSat, vA_y );
        // int val_yB  = sat_solver_var_value( pSat, vB_y );

        // Abc_Print( 1, "[DEBUG] has10 model: xiA=%d xiB=%d yA=%d yB=%d\n",
        //           val_xiA, val_xiB, val_yA, val_yB );

        // Abc_Print( 1, "[DEBUG] has10 PI assignments (copy A):\n" );
        // for (tt = 0; tt < nPiCone; ++tt)
        // {
        //     Abc_Obj_t * pPiConeDbg = Abc_NtkPi(pCone, tt);
        //     int varA = vA_pis[tt];
        //     int val  = sat_solver_var_value(pSat, varA);

        //     Abc_Print( 1, "  %s = %d\n",
        //               Abc_ObjName(pPiConeDbg),
        //               val );
        // }

        pPat10 = (char *)ABC_ALLOC( char, nPiCone );
        for ( tt = 0; tt < nPiCone; ++tt )
        {
            if ( tt == iConeXi )
            {
                pPat10[tt] = '-';
                continue;
            }
            int v = vA_pis[tt];
            int val = sat_solver_var_value( pSat, v );
            pPat10[tt] = val ? '1' : '0';
        }
    }

    // Abc_Print( 1, "[DEBUG] has01=%d, has10=%d\n", has01, has10 );

    // 根據 has01 / has10 分類
    if ( !has01 && !has10 )
    {
        Abc_Print( 1, "independent\n" );
    }
    else if ( has01 && !has10 )
    {
        Abc_Print( 1, "positive unate\n" );
    }
    else if ( !has01 && has10 )
    {
        Abc_Print( 1, "negative unate\n" );
    }
    else // has01 && has10
    {
        Abc_Print( 1, "binate\n" );
        // 印兩個 pattern，長度照「原網路的 PI 數」
        Lsv_PrintPatternFromConePattern(
            pPat01, nPiCone, pMapOrig2Cone, nPiOrig, i );
        Lsv_PrintPatternFromConePattern(
            pPat10, nPiCone, pMapOrig2Cone, nPiOrig, i );
    }

    // free 資源
    if ( pPat01 ) ABC_FREE( pPat01 );
    if ( pPat10 ) ABC_FREE( pPat10 );
    Vec_IntFree( vAssump );
    ABC_FREE( vA_pis );
    ABC_FREE( vB_pis );
    sat_solver_delete( pSat );
    Cnf_DataFree( pCnfA );
    Cnf_DataFree( pCnfB );
    Aig_ManStop( pAig );
    ABC_FREE( pMapOrig2Cone );
    Abc_NtkDelete( pCone );

    return 0;
}


// static int Lsv_CommandUnateSat( Abc_Frame_t * pAbc, int argc, char ** argv )
// {
//     Abc_Ntk_t * pNtk;
//     int k, i;
//     int c;

//     Extra_UtilGetoptReset();
//     while ( (c = Extra_UtilGetopt(argc, argv, "h")) != EOF )
//     {
//         switch ( c )
//         {
//         case 'h':
//         default:
//             Abc_Print( -2, "usage: lsv_unate_sat <k> <i>\n" );
//             return 1;
//         }
//     }

//     if ( argc - globalUtilOptind != 2 )
//     {
//         Abc_Print( -2, "usage: lsv_unate_sat <k> <i>\n" );
//         return 1;
//     }

//     k = atoi( argv[globalUtilOptind] );
//     i = atoi( argv[globalUtilOptind+1] );

//     pNtk = Abc_FrameReadNtk( pAbc );
//     if ( pNtk == NULL )
//     {
//         Abc_Print( -1, "lsv_unate_sat: there is no current network.\n" );
//         return 1;
//     }

//     if ( !Abc_NtkIsStrash( pNtk ) )
//     {
//         Abc_Print( -1, "lsv_unate_sat: this command works only for AIGs (run \"strash\").\n" );
//         return 1;
//     }

//     if ( k < 0 || k >= Abc_NtkPoNum(pNtk) )
//     {
//         Abc_Print( -1, "lsv_unate_sat: PO index %d is out of range.\n", k );
//         return 1;
//     }
//     if ( i < 0 || i >= Abc_NtkPiNum(pNtk) )
//     {
//         Abc_Print( -1, "lsv_unate_sat: PI index %d is out of range.\n", i );
//         return 1;
//     }

//     // debug: 基本資訊
//     Abc_Print( 1, "==== lsv_unate_sat debug ====\n" );
//     Abc_Print( 1, "Network name: %s\n", Abc_NtkName(pNtk) );
//     Abc_Print( 1, "Total POs = %d, Total PIs = %d\n",
//                Abc_NtkPoNum(pNtk), Abc_NtkPiNum(pNtk) );
//     {
//         Abc_Obj_t * pPoDbg = Abc_NtkPo( pNtk, k );
//         Abc_Obj_t * pPiDbg = Abc_NtkPi( pNtk, i );
//         Abc_Print( 1, "Target PO k=%d name=%s\n", k, Abc_ObjName(pPoDbg) );
//         Abc_Print( 1, "Target PI i=%d name=%s\n", i, Abc_ObjName(pPiDbg) );
//     }

//     // 抽出單一 PO 的 cone
//     Abc_Obj_t * pPo   = Abc_NtkPo( pNtk, k );
//     Abc_Obj_t * pRoot = Abc_ObjFanin0( pPo ); // driver

//     if ( pRoot == NULL )
//     {
//         Abc_Print( -1, "lsv_unate_sat: PO %d has no fanin.\n", k );
//         return 1;
//     }

//     // 檢查 root 型別是否符合 Abc_NtkCreateCone 的 assert
//     if ( !Abc_ObjIsNode( pRoot ) &&
//          !( Abc_NtkIsStrash( pNtk ) &&
//             ( Abc_AigNodeIsConst( pRoot ) || Abc_ObjIsCi( pRoot ) ) ) )
//     {
//         Abc_Print( -1, "lsv_unate_sat: invalid cone root for PO %d.\n", k );
//         return 1;
//     }

//     Abc_Ntk_t * pCone = Abc_NtkCreateCone( pNtk, pRoot, Abc_ObjName(pPo), 1 );
//     if ( pCone == NULL )
//     {
//         Abc_Print( -1, "lsv_unate_sat: cannot create cone.\n" );
//         return 1;
//     }
//     // ===== Debug: print cone structure =====
//     Abc_Print(1, "=== Cone CI (PIs of cone) ===\n");
//     Abc_Obj_t * pObj;
//     int iii;

//     Abc_NtkForEachCi( pCone, pObj, iii )
//     {
//         Abc_Print(1, "  CI %d: name=%s (ObjId=%d)\n",
//                   iii, Abc_ObjName(pObj), Abc_ObjId(pObj));
//     }

//     Abc_Print(1, "=== Cone CO (PO of cone) ===\n");
//     Abc_NtkForEachCo( pCone, pObj, iii )
//     {
//         Abc_Print(1, "  CO %d: name=%s (ObjId=%d), fanin0 ObjId=%d\n",
//                   iii,
//                   Abc_ObjName(pObj),
//                   Abc_ObjId(pObj),
//                   Abc_ObjFanin0(pObj) ? Abc_ObjFanin0(pObj)->Id : -1);
//     }

//     Abc_Print(1, "=== Cone internal nodes (AND nodes) ===\n");
//     Abc_NtkForEachNode( pCone, pObj, iii )
//     {
//         Abc_Obj_t * pF0 = Abc_ObjFanin0(pObj);
//         Abc_Obj_t * pF1 = Abc_ObjFanin1(pObj);
//         Abc_Print(1, "  Node ObjId=%d  fanin0=%d fanin1=%d\n",
//                   Abc_ObjId(pObj),
//                   pF0 ? Abc_ObjId(pF0) : -1,
//                   pF1 ? Abc_ObjId(pF1) : -1);
//     }
//     // ===== end cone debug =====

//     int nPiOrig = Abc_NtkPiNum( pNtk );
//     int nPiCone = Abc_NtkPiNum( pCone );
//     int ii, tt;

//     Abc_Print( 1, "Cone: nPiOrig = %d, nPiCone = %d\n", nPiOrig, nPiCone );
//     Abc_Print( 1, "Cone PIs:\n" );
//     for ( tt = 0; tt < nPiCone; ++tt )
//     {
//         Abc_Obj_t * pPiConeDbg = Abc_NtkPi( pCone, tt );
//         Abc_Print( 1, "  conePI[%d] name=%s\n", tt, Abc_ObjName(pPiConeDbg) );
//     }

//     // 建立 origPI -> conePI 的對應（用名字比）
//     int * pMapOrig2Cone = (int *)ABC_ALLOC( int, nPiOrig );
//     for ( ii = 0; ii < nPiOrig; ++ii )
//         pMapOrig2Cone[ii] = -1;

//     for ( tt = 0; tt < nPiCone; ++tt )
//     {
//         Abc_Obj_t * pPiCone = Abc_NtkPi( pCone, tt );
//         char const * pNameCone = Abc_ObjName( pPiCone );
//         for ( ii = 0; ii < nPiOrig; ++ii )
//         {
//             Abc_Obj_t * pPiOrig = Abc_NtkPi( pNtk, ii );
//             if ( !strcmp( Abc_ObjName(pPiOrig), pNameCone ) )
//             {
//                 pMapOrig2Cone[ii] = tt;
//                 break;
//             }
//         }
//     }

//     Abc_Print( 1, "Orig PI to Cone PI mapping (origIdx: name -> coneIdx):\n" );
//     for ( ii = 0; ii < nPiOrig; ++ii )
//     {
//         Abc_Obj_t * pPiOrigDbg = Abc_NtkPi( pNtk, ii );
//         Abc_Print( 1, "  origPI[%d] name=%s -> conePI=%d\n",
//                    ii, Abc_ObjName(pPiOrigDbg), pMapOrig2Cone[ii] );
//     }

//     int iConeXi = pMapOrig2Cone[i];
//     Abc_Print( 1, "Target PI i=%d name=%s maps to conePI index %d\n",
//                i, Abc_ObjName(Abc_NtkPi(pNtk, i)), iConeXi );

//     // 如果 xi 不在 cone 裡 => independent
//     if ( iConeXi == -1 )
//     {
//         Abc_Print( 1, "independent\n" );
//         ABC_FREE( pMapOrig2Cone );
//         Abc_NtkDelete( pCone );
//         return 0;
//     }

//     // 轉成 AIG
//     Aig_Man_t * pAig = Abc_NtkToDar( pCone, 0, 0 );
//     if ( pAig == NULL )
//     {
//         Abc_Print( -1, "lsv_unate_sat: Abc_NtkToDar() failed.\n" );
//         ABC_FREE( pMapOrig2Cone );
//         Abc_NtkDelete( pCone );
//         return 1;
//     }
//     // ===== Debug: print AIG structure =====
//     Abc_Print(1, "=== AIG CIs ===\n");
//     Aig_Obj_t * pAigObj;
//     Aig_ManForEachCi( pAig, pAigObj, i )
//     {
//         Abc_Print(1, "  CI %d: AigId=%d\n", i, Aig_ObjId(pAigObj));
//     }

//     Abc_Print(1, "=== AIG COs ===\n");
//     Aig_ManForEachCo( pAig, pAigObj, i )
//     {
//         Aig_Obj_t * pFan = Aig_ObjFanin0(pAigObj);
//         int fCompl = Aig_ObjFaninC0(pAigObj);
//         Abc_Print(1, "  CO %d: AigId=%d, fanin0 AigId=%d, compl=%d\n",
//                   i, Aig_ObjId(pAigObj),
//                   pFan ? Aig_ObjId(pFan) : -1,
//                   fCompl);
//     }

//     Abc_Print(1, "=== AIG AND nodes ===\n");
//     Aig_ManForEachNode( pAig, pAigObj, i )
//     {
//         Aig_Obj_t * pF0 = Aig_ObjFanin0(pAigObj);
//         Aig_Obj_t * pF1 = Aig_ObjFanin1(pAigObj);
//         int c0 = Aig_ObjFaninC0(pAigObj);
//         int c1 = Aig_ObjFaninC1(pAigObj);
//         Abc_Print(1, "  Node AigId=%d  AND(%s%d, %s%d)\n",
//                   Aig_ObjId(pAigObj),
//                   c0 ? "~" : "", pF0 ? Aig_ObjId(pF0) : -1,
//                   c1 ? "~" : "", pF1 ? Aig_ObjId(pF1) : -1);
//     }
//     // ===== end AIG debug =====
    
//     sat_solver * pSat = sat_solver_new();
//     // 建 CNF (copy A / copy B)
//     Cnf_Dat_t * pCnfA = Cnf_Derive( pAig, 1 );
//     Cnf_Dat_t * pCnfB = Cnf_Derive( pAig, 1 );
//     // ===== Debug Print CNF =====
//     Abc_Print(1, "===== CNF A =====\n");
//     for (int c = 0; c < pCnfA->nClauses; c++)
//     {
//         int * pClause = pCnfA->pClauses[c];
//         Abc_Print(1, "clause %d: ", c);

//         for (int k = 0; pClause[k] != 0; k++)
//             Abc_Print(1, "%d ", pClause[k]);

//         Abc_Print(1, "0\n");
//     }

//     Abc_Print(1, "===== CNF B =====\n");
//     for (int c = 0; c < pCnfB->nClauses; c++)
//     {
//         int * pClause = pCnfB->pClauses[c];   // <<<<<<<< 這裡一定要用 pCnfB！
//         Abc_Print(1, "clause %d: ", c);

//         for (int k = 0; pClause[k] != 0; k++)
//             Abc_Print(1, "%d ", pClause[k]);

//         Abc_Print(1, "0\n");
//     }

//     // ===== End Debug Print CNF =====

//     if ( pCnfA == NULL || pCnfB == NULL )
//     {
//         Abc_Print( -1, "lsv_unate_sat: Cnf_Derive() failed.\n" );
//         if ( pCnfA ) Cnf_DataFree( pCnfA );
//         if ( pCnfB ) Cnf_DataFree( pCnfB );
//         Aig_ManStop( pAig );
//         ABC_FREE( pMapOrig2Cone );
//         Abc_NtkDelete( pCone );
//         return 1;
//     }

    
//     // 建 SAT solver 並加入兩份 CNF
//     Cnf_DataWriteIntoSolverInt( pSat, pCnfA, 1, 1 );
//     // 把 copy B 的變數編號全部加上 offset
//     Cnf_DataLift( pCnfB, pCnfA->nVars );
//     Cnf_DataWriteIntoSolverInt( pSat, pCnfB, 1, 1 );

//     // 找出每個 PI 在 A / B copy 的 SAT 變數（用 Abc_ObjId 對到 AIG）
//     int * vA_pis = (int *)ABC_ALLOC( int, nPiCone );
//     int * vB_pis = (int *)ABC_ALLOC( int, nPiCone );
//     for ( tt = 0; tt < nPiCone; ++tt )
//     {
//         Abc_Obj_t * pPiCone = Abc_NtkPi( pCone, tt );
//         Aig_Obj_t * pPiAig  = Aig_ManObj( pAig, Abc_ObjId( pPiCone ) );
//         int id = Aig_ObjId( pPiAig );
//         vA_pis[tt] = pCnfA->pVarNums[id];
//         vB_pis[tt] = pCnfB->pVarNums[id];
//     }

//     // xi 的 SAT 變數（用同樣的方式）
//     Abc_Obj_t * pXiCone = Abc_NtkPi( pCone, iConeXi );
//     Aig_Obj_t * pXiAig  = Aig_ManObj( pAig, Abc_ObjId( pXiCone ) );
//     int vA_xi = pCnfA->pVarNums[ Aig_ObjId( pXiAig ) ];
//     int vB_xi = pCnfB->pVarNums[ Aig_ObjId( pXiAig ) ];

//     // 正確取得 y 的 AIG node：CO 的 driver
//     Aig_Obj_t * pCoAig = Aig_ManCo( pAig, 0 );
//     Aig_Obj_t * pRootAig = Aig_ObjFanin0(pCoAig);  // 這才是真正的 y function node

//     int vA_y = pCnfA->pVarNums[Aig_ObjId(pRootAig)];
//     int vB_y = pCnfB->pVarNums[Aig_ObjId(pRootAig)];


//     Abc_Print( 1, "CNF var mapping for PIs:\n" );
//     for ( tt = 0; tt < nPiCone; ++tt )
//     {
//         Abc_Obj_t * pPiConeDbg = Abc_NtkPi( pCone, tt );
//         Abc_Print( 1, "  conePI[%d] name=%s vA=%d vB=%d\n",
//                    tt, Abc_ObjName(pPiConeDbg), vA_pis[tt], vB_pis[tt] );
//     }
//     Abc_Print( 1, "xi in cone: index=%d name=%s vA_xi=%d vB_xi=%d\n",
//                iConeXi, Abc_ObjName(pXiCone), vA_xi, vB_xi );
//     Abc_Print( 1, "y vars: vA_y=%d vB_y=%d\n", vA_y, vB_y );

//     // 對除了 xi 以外所有 input 加 equality clause： vA == vB
//     for ( tt = 0; tt < nPiCone; ++tt )
//     {
//         if ( tt == iConeXi )
//             continue;

//         int vA = vA_pis[tt];
//         int vB = vB_pis[tt];
//         lit Lits[2];

//         // (¬vA ∨ vB)
//         Lits[0] = Abc_Var2Lit( vA, 1 );
//         Lits[1] = Abc_Var2Lit( vB, 0 );
//         sat_solver_addclause( pSat, Lits, Lits+2 );

//         // (vA ∨ ¬vB)
//         Lits[0] = Abc_Var2Lit( vA, 0 );
//         Lits[1] = Abc_Var2Lit( vB, 1 );
//         sat_solver_addclause( pSat, Lits, Lits+2 );
//     }

//     // 開始做兩個 pattern 的 SAT 查詢
//     Vec_Int_t * vAssump = Vec_IntAlloc( 8 );
//     int has01 = 0, has10 = 0;
//     char * pPat01 = NULL;
//     char * pPat10 = NULL;

//     int status;

//     // (1) 0 -> 1 pattern: xiA=0, xiB=1, yA=0, yB=1
//     Vec_IntClear( vAssump );
//     Vec_IntPush( vAssump, Abc_Var2Lit( vA_xi, 1 ) ); // xiA=0
//     Vec_IntPush( vAssump, Abc_Var2Lit( vB_xi, 0 ) ); // xiB=1
//     Vec_IntPush( vAssump, Abc_Var2Lit( vA_y , 1 ) ); // yA=0
//     Vec_IntPush( vAssump, Abc_Var2Lit( vB_y , 0 ) ); // yB=1

//     status = sat_solver_solve( pSat,
//         Vec_IntArray(vAssump),
//         Vec_IntArray(vAssump) + Vec_IntSize(vAssump),
//         0, 0, 0, 0 );

//     Abc_Print( 1, "[DEBUG] has01 solve status = %d (1=True, 0=False)\n", status );
//     if ( status == l_True )
//     {
//         has01 = 1;
//         int val_xiA = sat_solver_var_value( pSat, vA_xi );
//         int val_xiB = sat_solver_var_value( pSat, vB_xi );
//         int val_yA  = sat_solver_var_value( pSat, vA_y );
//         int val_yB  = sat_solver_var_value( pSat, vB_y );
//         Abc_Print( 1, "[DEBUG] has01 model: xiA=%d xiB=%d yA=%d yB=%d\n",
//                    val_xiA, val_xiB, val_yA, val_yB );

//         pPat01 = (char *)ABC_ALLOC( char, nPiCone );
//         for ( tt = 0; tt < nPiCone; ++tt )
//         {
//             if ( tt == iConeXi )
//             {
//                 pPat01[tt] = '-';
//                 continue;
//             }
//             int v = vA_pis[tt];
//             int val = sat_solver_var_value( pSat, v ); // 0 or 1
//             pPat01[tt] = val ? '1' : '0';
//         }
//     }

//     // (2) 1 -> 0 pattern: xiA=0, xiB=1, yA=1, yB=0
//     Vec_IntClear( vAssump );
//     Vec_IntPush( vAssump, Abc_Var2Lit( vA_xi, 1 ) ); // xiA=0
//     Vec_IntPush( vAssump, Abc_Var2Lit( vB_xi, 0 ) ); // xiB=1
//     Vec_IntPush( vAssump, Abc_Var2Lit( vA_y , 0 ) ); // yA=1
//     Vec_IntPush( vAssump, Abc_Var2Lit( vB_y , 1 ) ); // yB=0

//     status = sat_solver_solve( pSat,
//         Vec_IntArray(vAssump),
//         Vec_IntArray(vAssump) + Vec_IntSize(vAssump),
//         0, 0, 0, 0 );

//     Abc_Print( 1, "[DEBUG] has10 solve status = %d (1=True, 0=False)\n", status );
//     if ( status == l_True )
//     {
//         has10 = 1;

//         int val_xiA = sat_solver_var_value( pSat, vA_xi );
//         int val_xiB = sat_solver_var_value( pSat, vB_xi );
//         int val_yA  = sat_solver_var_value( pSat, vA_y );
//         int val_yB  = sat_solver_var_value( pSat, vB_y );

//         Abc_Print( 1, "[DEBUG] has10 model: xiA=%d xiB=%d yA=%d yB=%d\n",
//                   val_xiA, val_xiB, val_yA, val_yB );

//         // ★ 新增：把所有 cone PI (copy A) 的值印出來
//         Abc_Print( 1, "[DEBUG] has10 PI assignments (copy A):\n" );
//         for (tt = 0; tt < nPiCone; ++tt)
//         {
//             Abc_Obj_t * pPiConeDbg = Abc_NtkPi(pCone, tt);
//             int varA = vA_pis[tt];
//             int val  = sat_solver_var_value(pSat, varA);

//             Abc_Print( 1, "  %s = %d\n",
//                       Abc_ObjName(pPiConeDbg),
//                       val );
//         }

//         // 原本的 pattern 抽取
//         pPat10 = (char *)ABC_ALLOC( char, nPiCone );
//         for ( tt = 0; tt < nPiCone; ++tt )
//         {
//             if ( tt == iConeXi )
//             {
//                 pPat10[tt] = '-';
//                 continue;
//             }
//             int v = vA_pis[tt];
//             int val = sat_solver_var_value( pSat, v );
//             pPat10[tt] = val ? '1' : '0';
//         }
//     }


//     Abc_Print( 1, "[DEBUG] has01=%d, has10=%d\n", has01, has10 );

//     // 根據 has01 / has10 分類
//     if ( !has01 && !has10 )
//     {
//         Abc_Print( 1, "independent\n" );
//     }
//     else if ( has01 && !has10 )
//     {
//         Abc_Print( 1, "positive unate\n" );
//     }
//     else if ( !has01 && has10 )
//     {
//         Abc_Print( 1, "negative unate\n" );
//     }
//     else // has01 && has10
//     {
//         Abc_Print( 1, "binate\n" );
//         // 印兩個 pattern，長度照「原網路的 PI 數」
//         Lsv_PrintPatternFromConePattern(
//             pPat01, nPiCone, pMapOrig2Cone, nPiOrig, i );
//         Lsv_PrintPatternFromConePattern(
//             pPat10, nPiCone, pMapOrig2Cone, nPiOrig, i );
//     }

//     // free 資源
//     if ( pPat01 ) ABC_FREE( pPat01 );
//     if ( pPat10 ) ABC_FREE( pPat10 );
//     Vec_IntFree( vAssump );
//     ABC_FREE( vA_pis );
//     ABC_FREE( vB_pis );
//     sat_solver_delete( pSat );
//     Cnf_DataFree( pCnfA );
//     Cnf_DataFree( pCnfB );
//     Aig_ManStop( pAig );
//     ABC_FREE( pMapOrig2Cone );
//     Abc_NtkDelete( pCone );

//     return 0;
// }

// -------------unate check w/ sat end----------------------------

// void Lsv_NtkPrintNodes(Abc_Ntk_t* pNtk) {
//   Abc_Obj_t* pObj;
//   int i;
//   Abc_NtkForEachNode(pNtk, pObj, i) {
//     printf("Object Id = %d, name = %s\n", Abc_ObjId(pObj), Abc_ObjName(pObj));
//     Abc_Obj_t* pFanin;
//     int j;
//     Abc_ObjForEachFanin(pObj, pFanin, j) {
//       printf("  Fanin-%d: Id = %d, name = %s\n", j, Abc_ObjId(pFanin),
//              Abc_ObjName(pFanin));
//     }
//     if (Abc_NtkHasSop(pNtk)) {
//       printf("The SOP of this node:\n%s", (char*)pObj->pData);
//     }
//   }
// }

// int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv) {
//   Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
//   int c;
//   Extra_UtilGetoptReset();
//   while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
//     switch (c) {
//       case 'h':
//         goto usage;
//       default:
//         goto usage;
//     }
//   }
//   if (!pNtk) {
//     Abc_Print(-1, "Empty network.\n");
//     return 1;
//   }
//   Lsv_NtkPrintNodes(pNtk);
//   return 0;

// usage:
//   Abc_Print(-2, "usage: lsv_print_nodes [-h]\n");
//   Abc_Print(-2, "\t        prints the nodes in the network\n");
//   Abc_Print(-2, "\t-h    : print the command usage\n");
//   return 1;
// }
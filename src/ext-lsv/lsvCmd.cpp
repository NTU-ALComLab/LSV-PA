#include "base/abc/abc.h"
#include "aig/aig/aig.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

#include <iostream>
#include <vector>
#include <algorithm>
#include <unordered_map>
#include <string>
#include <bdd/cudd/cudd.h>
#include <bdd/extrab/extraBdd.h>
#include "sat/cnf/cnf.h"
#include "sat/bsat/satSolver.h"

using std::cout;
using std::vector;
using std::unordered_map;

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintMultiCuts(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintUnateBdd(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintUnateSat(Abc_Frame_t* pAbc, int argc, char** argv);

extern "C" {
  Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
} 

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocut", Lsv_CommandPrintMultiCuts, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_unate_bdd", Lsv_CommandPrintUnateBdd, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_unate_sat", Lsv_CommandPrintUnateSat, 0);

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

static void Lsv_PrintPattern( Abc_Ntk_t * pNtk, char * cube, int * ciVarIndex, int iCi )
{
    int nCi = Abc_NtkCiNum( pNtk );

    for ( int j = 0; j < nCi; j++ )
    {
        if ( j == iCi )
        {
            printf( "-" );
            continue;
        }

        int v;
        if ( ciVarIndex )
            v = ciVarIndex[j];
        else
            v = j; 

        char c = cube[v];
        if ( c == '0' || c == 0 )
            printf( "0" );
        else if ( c == '1' || c == 1 )
            printf( "1" );
        else
            printf( "0" );
    }
    printf( "\n" );
}


void Lsv_unate_bdd( Abc_Ntk_t * pNtk, int k, int iCi )
{
    Abc_Ntk_t * pNtkAig = Abc_NtkStrash( pNtk, 0, 1, 0 );
    assert( Abc_NtkIsStrash( pNtkAig ) );

    DdManager *dd = (DdManager *)Abc_NtkBuildGlobalBdds( pNtkAig, 10000000, 1, 1, 0, 0 );
    if ( dd == NULL )
    {
        printf("Error: Abc_NtkBuildGlobalBdds failed.\n");
        Abc_NtkDelete( pNtkAig );
        return;
    }

    
    Abc_Obj_t * pCo = Abc_NtkCo( pNtkAig, k );
    assert( pCo != NULL );

    DdNode * bF = (DdNode *)Abc_ObjGlobalBdd( pCo );
    assert( bF != NULL );
    Cudd_Ref( bF );

    
    int nCi = Abc_NtkCiNum( pNtkAig );
    assert( 0 <= iCi && iCi < nCi );

    DdNode * bVar = Cudd_bddIthVar( dd, iCi );

    
    DdNode * bCof0 = Cudd_Cofactor( dd, bF, Cudd_Not(bVar) );  Cudd_Ref( bCof0 );
    DdNode * bCof1 = Cudd_Cofactor( dd, bF, bVar );            Cudd_Ref( bCof1 );

    int le01 = Cudd_bddLeq( dd, bCof0, bCof1 );
    int le10 = Cudd_bddLeq( dd, bCof1, bCof0 );

    if ( le01 && le10 )
        printf("independent\n");
    else if ( le01 && !le10 )
        printf("positive unate\n");
    else if ( le10 && !le01 )
        printf("negative unate\n");
    else
    {
        printf("binate\n");

        DdNode * bPos = Cudd_bddAnd( dd, Cudd_Not(bCof0), bCof1 ); Cudd_Ref( bPos );
        DdNode * bNeg = Cudd_bddAnd( dd, bCof0, Cudd_Not(bCof1) ); Cudd_Ref( bNeg );

        char * cube = ABC_ALLOC( char, dd->size );

        if ( Cudd_bddPickOneCube( dd, bPos, cube ) )
            Lsv_PrintPattern( pNtkAig, cube, NULL, iCi );
        else
            printf("<pattern 1>\n");

        if ( Cudd_bddPickOneCube( dd, bNeg, cube ) )
            Lsv_PrintPattern( pNtkAig, cube, NULL, iCi );
        else
            printf("<pattern 2>\n");

        ABC_FREE( cube );
        Cudd_RecursiveDeref( dd, bPos );
        Cudd_RecursiveDeref( dd, bNeg );
    }

    Cudd_RecursiveDeref( dd, bCof0 );
    Cudd_RecursiveDeref( dd, bCof1 );
    Cudd_RecursiveDeref( dd, bF );

    Abc_NtkFreeGlobalBdds( pNtkAig, 1 );
    Abc_NtkDelete( pNtkAig );
}







int Lsv_CommandPrintUnateBdd(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);


  int k=atoi(argv[1]);
  int i=atoi(argv[2]);

  
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
  if ( Abc_NtkIsBddLogic(pNtk)) Lsv_unate_bdd(pNtk, k, i);
  else std::cout<< "not BDD.\n";
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_unate_bdd <k> <i> [-h]\n");
  Abc_Print(-2, "\t        prints something\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}



static void Lsv_FillModelCube( 
    Abc_Ntk_t * pNtk, 
    Abc_Ntk_t * pCone, 
    Cnf_Dat_t * pCnfA, 
    sat_solver * pSat, 
    int iCi,
    char * cube )
{
    int nCi = Abc_NtkCiNum( pNtk );

    for ( int j = 0; j < nCi; j++ )
    {
        if ( j == iCi )
        {
            cube[j] = '-';
            continue;
        }

        Abc_Obj_t * pCiOrig = Abc_NtkCi( pNtk, j );
        Abc_Obj_t * pCiCone = Abc_NtkObj( pCone, Abc_ObjId( pCiOrig ) );

        if ( pCiCone == NULL )
        {
            cube[j] = '0';
            continue;
        }

        Aig_Obj_t * pAigCi = (Aig_Obj_t *)pCiCone->pCopy;
        int vA = pCnfA->pVarNums[ pAigCi->Id ];

        if ( vA < 0 )
        {
            cube[j] = '0';
            continue;
        }

        int satVal = sat_solver_var_value( pSat, vA );
        cube[j] = (satVal == 0 ? '0' : '1');
    }

    cube[nCi] = '\0';
}



void Lsv_unate_sat( Abc_Ntk_t * pNtk, int k, int iCi )
{
    Abc_Ntk_t * pCone = NULL;
    Abc_Obj_t * pPo = NULL, * pPoCone = NULL, * pRoot = NULL;
    Abc_Obj_t * pCiOrigXi = NULL, * pCiXiCone = NULL, * pCiCone = NULL;
    Aig_Man_t * pAig = NULL;
    Cnf_Dat_t * pCnfA = NULL, * pCnfB = NULL;
    sat_solver * pSat = NULL;
    int nCi = Abc_NtkCiNum( pNtk );
    int status;
    int i;

    int fComplY;
    int isNotPosUnate = 0;
    int isNotNegUnate = 0;

    char * cubePos = NULL;
    char * cubeNeg = NULL;
    int hasPosCube = 0;
    int hasNegCube = 0;


    // sanity checks
    if ( !pNtk )
    {
        Abc_Print( 1, "Lsv_unate_sat: NULL network.\n" );
        return;
    }
    if ( k < 0 || k >= Abc_NtkCoNum(pNtk) )
    {
        Abc_Print( 1, "Lsv_unate_sat: PO index %d out of range.\n", k );
        return;
    }
    if ( iCi < 0 || iCi >= nCi )
    {
        Abc_Print( 1, "Lsv_unate_sat: CI index %d out of range.\n", iCi );
        return;
    }

    // PO and cone: build cone from the *driver* of PO[k]
    pPo = Abc_NtkCo( pNtk, k );
    Abc_Obj_t * pRootOrig = Abc_ObjFanin0( pPo );
    int fComplYOrig       = Abc_ObjFaninC0( pPo ); // original phase on PO

    pCone = Abc_NtkCreateCone( pNtk, pRootOrig, Abc_ObjName(pPo), 1 );
    if ( pCone == NULL )
    {
        Abc_Print( 1, "Lsv_unate_sat: failed to create cone.\n" );
        return;
    }

    pPoCone = Abc_NtkPo( pCone, 0 );
    pRoot   = Abc_ObjFanin0( pPoCone );
    fComplY = fComplYOrig; // we still care about original PO polarity

    // locate xi in original and cone
    pCiOrigXi = Abc_NtkCi( pNtk, iCi );
    pCiXiCone = Abc_NtkObj( pCone, Abc_ObjId(pCiOrigXi) );
    if ( pCiXiCone == NULL || !Abc_ObjIsCi( pCiXiCone ) )
    {
        // y_k does not depend on x_i structurally
        Abc_Print( 1, "independent\n" );
        Abc_NtkDelete( pCone );
        return;
    }

    // cone -> AIG
    pAig = Abc_NtkToDar( pCone, 0, 0 );
    if ( pAig == NULL )
    {
        Abc_Print( 1, "Lsv_unate_sat: Abc_NtkToDar failed.\n" );
        Abc_NtkDelete( pCone );
        return;
    }

    // derive CNFs for two copies
    pCnfA = Cnf_Derive( pAig, 1 );  // use 1 (standard in ABC examples)
    if ( pCnfA == NULL )
    {
        Abc_Print( 1, "Lsv_unate_sat: Cnf_Derive A failed.\n" );
        Aig_ManStop( pAig );
        Abc_NtkDelete( pCone );
        return;
    }
    pCnfB = Cnf_Derive( pAig, 1 );
    if ( pCnfB == NULL )
    {
        Abc_Print( 1, "Lsv_unate_sat: Cnf_Derive B failed.\n" );
        Cnf_DataFree( pCnfA );
        Aig_ManStop( pAig );
        Abc_NtkDelete( pCone );
        return;
    }
    Cnf_DataLift( pCnfB, pCnfA->nVars ); // lift B vars

    // new SAT solver
    pSat = sat_solver_new();
    sat_solver_setnvars( pSat, pCnfA->nVars + pCnfB->nVars );

    // write CNFs
    Cnf_DataWriteIntoSolverInt( pSat, pCnfA, 1, 0 );
    Cnf_DataWriteIntoSolverInt( pSat, pCnfB, 1, 0 );

    status = sat_solver_simplify( pSat );
    if ( status == 0 )
    {
        // cone output is constant
        Abc_Print( 1, "independent\n" );
        sat_solver_delete( pSat );
        Cnf_DataFree( pCnfA );
        Cnf_DataFree( pCnfB );
        Aig_ManStop( pAig );
        Abc_NtkDelete( pCone );
        return;
    }

    cubePos = (char *)malloc( nCi + 1 );
    cubeNeg = (char *)malloc( nCi + 1 );

    // add x^A_t = x^B_t for all CIs except xi
    Abc_NtkForEachCi( pCone, pCiCone, i )
    {
        if ( pCiCone == pCiXiCone )
            continue; // skip the distinguished xi

        Aig_Obj_t * pAigCi = (Aig_Obj_t *)pCiCone->pCopy;
        int vA = pCnfA->pVarNums[ pAigCi->Id ];
        int vB = pCnfB->pVarNums[ pAigCi->Id ];

        if ( vA < 0 || vB < 0 )
            continue; // CI not in support

        lit litA  = toLitCond( vA, 0 );
        lit litAn = lit_neg( litA );
        lit litB  = toLitCond( vB, 0 );
        lit litBn = lit_neg( litB );

        lit cls1[2] = { litA,  litBn };  // xA or not xB
        lit cls2[2] = { litAn, litB  };  // not xA or xB

        sat_solver_addclause( pSat, cls1, cls1 + 2 );
        sat_solver_addclause( pSat, cls2, cls2 + 2 );
    }

    // map xi and y to CNF vars
    Aig_Obj_t * pAigXi = (Aig_Obj_t *)pCiXiCone->pCopy;
    int vXiA = pCnfA->pVarNums[ pAigXi->Id ];
    int vXiB = pCnfB->pVarNums[ pAigXi->Id ];
    if ( vXiA < 0 || vXiB < 0 )
    {
        Abc_Print( 1, "independent\n" );
        sat_solver_delete( pSat );
        Cnf_DataFree( pCnfA );
        Cnf_DataFree( pCnfB );
        Aig_ManStop( pAig );
        Abc_NtkDelete( pCone );
        return;
    }

    Aig_Obj_t * pAigY = (Aig_Obj_t *)pRoot->pCopy;
    int vY_A = pCnfA->pVarNums[ pAigY->Id ];
    int vY_B = pCnfB->pVarNums[ pAigY->Id ];
    if ( vY_A < 0 || vY_B < 0 )
    {
        Abc_Print( 1, "independent\n" );
        sat_solver_delete( pSat );
        Cnf_DataFree( pCnfA );
        Cnf_DataFree( pCnfB );
        Aig_ManStop( pAig );
        Abc_NtkDelete( pCone );
        return;
    }

    // helper: desired y (0/1) -> literal on vY considering PO complement
    // y = f xor fComplY => f = y xor fComplY
    auto yLit = [fComplY]( int vY, int yVal ) {
        int f = (yVal ^ fComplY); // underlying function f
        int sign = f ? 0 : 1;     // f=1 => literal x, f=0 => literal not x
        return toLitCond( vY, sign );
    };

    // (A) positive-unate violation: f(0)=1, f(1)=0 -> not x_i
    {
        lit assump[4];
        assump[0] = toLitCond( vXiA, 1 );   // xA=0
        assump[1] = toLitCond( vXiB, 0 );   // xB=1
        assump[2] = yLit( vY_A, 1 );        // yA=1
        assump[3] = yLit( vY_B, 0 );        // yB=0

        status = sat_solver_solve( pSat, assump, assump + 4, 0,0,0,0 );
        if ( status == l_True )
        {
            isNotPosUnate = 1;
            hasPosCube = 1;
            Lsv_FillModelCube( pNtk, pCone, pCnfA, pSat, iCi, cubePos );
        }
    }

    // (B) negative-unate violation: f(0)=0, f(1)=1 -> x_i
    {
        lit assump[4];
        assump[0] = toLitCond( vXiA, 1 );   // xA=0
        assump[1] = toLitCond( vXiB, 0 );   // xB=1
        assump[2] = yLit( vY_A, 0 );        // yA=0
        assump[3] = yLit( vY_B, 1 );        // yB=1

        status = sat_solver_solve( pSat, assump, assump + 4, 0,0,0,0 );
        if ( status == l_True )
        {
            isNotNegUnate = 1;
            hasNegCube = 1;
            Lsv_FillModelCube( pNtk, pCone, pCnfA, pSat, iCi, cubeNeg );
        }
    }


    if ( !isNotPosUnate && !isNotNegUnate )
    {
        Abc_Print( 1, "independent\n" );
    }
    else if ( !isNotPosUnate &&  isNotNegUnate )
    {
        Abc_Print( 1, "positive unate\n" );
    }
    else if (  isNotPosUnate && !isNotNegUnate )
    {
        Abc_Print( 1, "negative unate\n" );
    }
    else
    {
        // binate: Pattern 1 -> x_i, Pattern 2 -> not x_i
        Abc_Print( 1, "binate\n" );

        // Pattern 1: cubeNeg  (f|cube = x_i)
        if ( hasNegCube )
            Lsv_PrintPattern( pNtk, cubeNeg, NULL, iCi );

        // Pattern 2: cubePos  (f|cube = not x_i)
        if ( hasPosCube )
            Lsv_PrintPattern( pNtk, cubePos, NULL, iCi );
    }


    if ( cubePos ) free( cubePos );
    if ( cubeNeg ) free( cubeNeg );



    // cleanup
    sat_solver_delete( pSat );
    Cnf_DataFree( pCnfA );
    Cnf_DataFree( pCnfB );
    Aig_ManStop( pAig );
    Abc_NtkDelete( pCone );
}

int Lsv_CommandPrintUnateSat(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);


  int k=atoi(argv[1]);
  int i=atoi(argv[2]);

  
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
  Lsv_unate_sat(pNtk, k, i);
  
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_unate_bdd <k> <i> [-h]\n");
  Abc_Print(-2, "\t        prints something\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}
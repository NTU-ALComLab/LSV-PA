
#include "aig/aig/aig.h"
#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "bdd/cudd/cudd.h"
#include "misc/util/abc_global.h"
#include "misc/vec/vecPtr.h"
#include "sat/bsat/satVec.h"
#include "sat/cnf/cnf.h"
#include "aig/gia/giaAig.h"
#include "sat/bsat/satSolver.h"
#include "base/io/ioAbc.h"

#include <cstring>
#include <set>
#include <map>
#include <vector>
#include <iostream>
#include <algorithm>

#define S_ZERO 0
#define S_ONE ~0

extern "C"{
extern Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
}

using namespace std;

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintCut(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintMoCut(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandSdc(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandOdc(Abc_Frame_t* pAbc, int argc, char** argv);
// static int Abc_CommandCheckUnateAig(Abc_Frame_t* pAbc, int argc, char** argv);

void Lsv_NtkSdc(Abc_Ntk_t* pNtk, int id, int* pat, int fVerbose, int fSim );
int Lsv_NtkOdc(Abc_Ntk_t* pNtk, int id, int* pat, int fVerbose, int fSim );

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_printcut", Lsv_CommandPrintCut, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocut", Lsv_CommandPrintMoCut, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_sdc", Lsv_CommandSdc, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_odc", Lsv_CommandOdc, 0);
//   Cmd_CommandAdd(pAbc, "LSV", "lsv_unate_aig", Abc_CommandCheckUnateAig, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

int *Lsv_SimulatePattern( Abc_Ntk_t * pNtk, int * pModel )
{
    Abc_Obj_t * pNode;
    int * pValues, Value0, Value1, i;
    int fStrashed = 0;
    if ( Abc_NtkIsStrash(pNtk) )
    {
        pNtk = Abc_NtkStrash(pNtk, 0, 0, 0);
        fStrashed = 1;
    }

    // increment the trav ID
    Abc_NtkIncrementTravId( pNtk );
    // set the CI values
    Abc_AigConst1(pNtk)->pCopy = (Abc_Obj_t *)1;
    Abc_NtkForEachCi( pNtk, pNode, i )
        pNode->pCopy = (Abc_Obj_t *)(ABC_PTRINT_T)pModel[i];
    // simulate in the topological order
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        Value0 = ((int)(ABC_PTRINT_T)Abc_ObjFanin0(pNode)->pCopy) ^ ((int)Abc_ObjFaninC0(pNode) ? ~0 : 0);
        Value1 = ((int)(ABC_PTRINT_T)Abc_ObjFanin1(pNode)->pCopy) ^ ((int)Abc_ObjFaninC1(pNode) ? ~0 : 0);
        pNode->pCopy = (Abc_Obj_t *)(ABC_PTRINT_T)(Value0 & Value1);
    }
    // fill the output values
    pValues = ABC_ALLOC( int, Abc_NtkCoNum(pNtk) );
    Abc_NtkForEachCo( pNtk, pNode, i )
        pValues[i] = ((int)(ABC_PTRINT_T)Abc_ObjFanin0(pNode)->pCopy) ^ ((int)Abc_ObjFaninC0(pNode) ? ~0 : 0);
    if ( fStrashed )
        Abc_NtkDelete( pNtk );
    return pValues;
}


int Abc_NtkMyAppend( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int fAddPos )
{
    Abc_Obj_t * pObj;
    char * pName;
    int i, nNewCis;
    // the first network should be an AIG
    assert( Abc_NtkIsStrash(pNtk1) );
    assert( Abc_NtkIsLogic(pNtk2) || Abc_NtkIsStrash(pNtk2) ); 
    if ( Abc_NtkIsLogic(pNtk2) && !Abc_NtkToAig(pNtk2) )
    {
        printf( "Converting to AIGs has failed.\n" );
        return 0;
    }
    // check that the networks have the same PIs
    // reorder PIs of pNtk2 according to pNtk1

    // fuck

    // perform strashing
    nNewCis = 0;
    Abc_NtkCleanCopy( pNtk2 );
    if ( Abc_NtkIsStrash(pNtk2) )
        Abc_AigConst1(pNtk2)->pCopy = Abc_AigConst1(pNtk1);
    Abc_NtkForEachCi( pNtk2, pObj, i )
    {
        pName = Abc_ObjName(pObj);
        pObj->pCopy = Abc_NtkFindCi(pNtk1, Abc_ObjName(pObj));
        if ( pObj->pCopy == NULL )
        {
            pObj->pCopy = Abc_NtkDupObj(pNtk1, pObj, 1);
            nNewCis++;
        }
    }
    if ( nNewCis )
        printf( "Warning: Procedure Abc_NtkAppend() added %d new CIs.\n", nNewCis );
    // add pNtk2 to pNtk1 while strashing
    Abc_NtkForEachNode( pNtk2, pObj, i )
        pObj->pCopy = Abc_AigAnd( (Abc_Aig_t *)pNtk1->pManFunc, Abc_ObjChild0Copy(pObj), Abc_ObjChild1Copy(pObj) );
    // add the COs of the second network
    if ( fAddPos )
    {
        Abc_NtkForEachPo( pNtk2, pObj, i )
        {
            Abc_NtkDupObj( pNtk1, pObj, 0 );
            Abc_ObjAddFanin( pObj->pCopy, Abc_ObjChild0Copy(pObj) );
            Abc_ObjAssignName( pObj->pCopy, Abc_ObjName(pObj), NULL );
        }
    }
    else
    {
        Abc_Obj_t * pObjOld, * pDriverOld, * pDriverNew;
        int fCompl, iNodeId;
        // OR the choices
        Abc_NtkForEachCo( pNtk2, pObj, i )
        {
            iNodeId = Nm_ManFindIdByNameTwoTypes( pNtk1->pManName, Abc_ObjName(pObj), ABC_OBJ_PO, ABC_OBJ_BI );
//            if ( iNodeId < 0 )
//                continue;
            assert( iNodeId >= 0 );
            pObjOld = Abc_NtkObj( pNtk1, iNodeId );
            // derive the new driver
            pDriverOld = Abc_ObjChild0( pObjOld );
            pDriverNew = Abc_ObjChild0Copy( pObj );
            pDriverNew = Abc_AigOr( (Abc_Aig_t *)pNtk1->pManFunc, pDriverOld, pDriverNew );
            if ( Abc_ObjRegular(pDriverOld) == Abc_ObjRegular(pDriverNew) )
                continue;
            // replace the old driver by the new driver
            fCompl = Abc_ObjRegular(pDriverOld)->fPhase ^ Abc_ObjRegular(pDriverNew)->fPhase;
            Abc_ObjPatchFanin( pObjOld, Abc_ObjRegular(pDriverOld), Abc_ObjNotCond(Abc_ObjRegular(pDriverNew), fCompl) );
        }
    }
    // make sure that everything is okay
    if ( !Abc_NtkCheck( pNtk1 ) )
    {
        printf( "Abc_NtkAppend: The network check has failed.\n" );
        return 0;
    }
    return 1;
}

void Lsv_NtkPrintNodes(Abc_Ntk_t* pNtk, int fSkip ) {
  Abc_Obj_t* pObj;
  int i;

  Abc_NtkForEachCi( pNtk, pObj, i )
  {
    printf( "%s\n", Abc_ObjName(pObj) );
  }
  return ;

  if ( !fSkip )
  {
    Abc_NtkForEachNode(pNtk, pObj, i)
    {
        if ( Abc_ObjFaninNum(pObj) < 2 ) continue;

        int pat [4];
        printf("lsv_sdc %d\n", Abc_ObjId(pObj));
        Lsv_NtkSdc(pNtk, i, pat, 0, 1);

        if ( pat[0] && pat[1] && pat[2] && pat[3] ) 
            printf("no sdc\n", Abc_ObjId(pObj));
        else 
        {
            for ( int j = 0; j < 4; j++ )
            {
                if ( !pat[j] ) printf("%d%d\n", j >> 1, j % 1 );
            }
        }
        fflush(stdout);

    }
  }

  Abc_NtkForEachNodeReverse(pNtk, pObj, i)
  {
    if ( Abc_ObjFaninNum(pObj) < 2 ) continue;

    int pat [4];
    Lsv_NtkSdc(pNtk, i, pat, 0, 1);


    if ( !Lsv_NtkOdc(pNtk, i, pat, 0, 1) )
    {
        printf("lsv_odc %d\n", Abc_ObjId(pObj));
        if ( !pat[0] && !pat[1] && !pat[2] && !pat[3] ) 
            printf("no odc\n", Abc_ObjId(pObj));
        else 
        {
            for ( int j = 0; j < 4; j++ )
            {
                if ( pat[j] ) printf("%d%d\n", j >> 1, j % 1 );
            }
        }
        fflush(stdout);
    }
  }

}

inline void printCut( const set<int> &cut )
{
    for ( auto it : cut ) cout << it << " ";
}
inline void printCuts( int id, set<set<int> > &cuts )
{
    for ( auto &it : cuts )
    {
        cout << id << ": ";
        printCut(it);
        cout << endl;
    }
}

void Lsv_NtkPrintCuts(Abc_Ntk_t* pNtk, int k) {

    Abc_Obj_t * pObj;
    int i, id0, id1;
    bool insert;

    vector<set<set<int> > > vCuts;
    vector<set<int> > vRemove;
    vCuts.resize(Abc_NtkObjNum(pNtk));

    Abc_NtkForEachObj(pNtk, pObj, i)
    {
        if ( Abc_ObjId(pObj) == 0 ) continue; 
        vCuts[i].insert({i});
        if ( Abc_ObjFaninNum(pObj) < 2 ) continue; 

        id0 = Abc_ObjFaninId0(pObj);
        id1 = Abc_ObjFaninId1(pObj);

        for( auto &cut0 : vCuts[id0] )
        {
            for( auto &cut1 : vCuts[id1] )
            {
                set<int> tmp;
                for ( auto id : cut0 ) tmp.insert(id);
                for ( auto id : cut1 ) tmp.insert(id);

                if ( tmp.size() <= k ) 
                {
                    if ( vCuts[i].find(tmp) != vCuts[i].end() ) continue;
                    insert = true;
                    for( auto &cut : vCuts[i] )
                    {
                        if ( cut.size() < tmp.size() )
                        {
                            if ( insert && includes(tmp.begin(), tmp.end(), cut.begin(), cut.end()) )
                                insert = false;
                        }
                        else if ( cut.size() > tmp.size() )
                        {
                            if ( includes(cut.begin(), cut.end(), tmp.begin(), tmp.end()) )
                            {
                                assert( insert == true );
                                vRemove.push_back(cut);
                            }
                        }
                    }
                    for ( auto &cut : vRemove ) vCuts[i].erase(cut);
                    vRemove.clear();

                    if ( insert ) vCuts[i].insert(tmp);
                }
            }
        }
    }
    Abc_NtkForEachCo(pNtk, pObj, i)
    {
        id0 = Abc_ObjId(pObj);
        vCuts[id0] = vCuts[Abc_ObjFaninId0(pObj)];
        vCuts[id0].insert({id0});
    }
    Abc_NtkForEachObj(pNtk, pObj, i)
    {
        if ( i == 0 ) continue;
        printCuts( i, vCuts[i] );
    }
}


void Lsv_NtkPrintMoCuts(Abc_Ntk_t* pNtk, int k, int l) {

    Abc_Obj_t * pObj;
    int i, id0, id1;
    bool insert;

    vector<set<set<int> > > vCuts;
    vector<set<int> > vRemove;
    vCuts.resize(Abc_NtkObjNum(pNtk));

    Abc_NtkForEachObj(pNtk, pObj, i)
    {
        if ( Abc_ObjId(pObj) == 0 ) continue; 
        vCuts[i].insert({i});
        if ( Abc_ObjFaninNum(pObj) < 2 ) continue; 

        id0 = Abc_ObjFaninId0(pObj);
        id1 = Abc_ObjFaninId1(pObj);

        for( auto &cut0 : vCuts[id0] )
        {
            for( auto &cut1 : vCuts[id1] )
            {
                set<int> tmp;
                for ( auto id : cut0 ) tmp.insert(id);
                for ( auto id : cut1 ) tmp.insert(id);

                if ( tmp.size() <= k ) 
                {
                    if ( vCuts[i].find(tmp) != vCuts[i].end() ) continue;
                    insert = true;
                    for( auto &cut : vCuts[i] )
                    {
                        if ( cut.size() < tmp.size() )
                        {
                            if ( insert && includes(tmp.begin(), tmp.end(), cut.begin(), cut.end()) )
                                insert = false;
                        }
                        else if ( cut.size() > tmp.size() )
                        {
                            if ( includes(cut.begin(), cut.end(), tmp.begin(), tmp.end()) )
                            {
                                assert( insert == true );
                                vRemove.push_back(cut);
                            }
                        }
                    }
                    for ( auto &cut : vRemove ) vCuts[i].erase(cut);
                    vRemove.clear();

                    if ( insert ) vCuts[i].insert(tmp);
                }
            }
        }
    }

    std::map<std::set<int>, std::vector<int> > cut_to_roots;
    for ( int rid = 0; rid < (int)vCuts.size(); ++rid )
    {
        for ( const auto &cut : vCuts[rid] )
        {
            auto &vec = cut_to_roots[cut];
            // 避免重複加入相同 root id（理論上不會，但保險）
            if (vec.empty() || vec.back() != rid) vec.push_back(rid);
        }
    }
    for ( const auto &kv : cut_to_roots )
    {
        const auto &cut = kv.first;
        const auto &roots = kv.second;

        if ((int)roots.size() >= l)
        {
            // 印 cut ids
            for (int x : cut)
                printf("%d ", x);

            // 冒號
            printf(": ");

            // 印 root node ids
            for (int r : roots)
                printf("%d ", r);

            printf("\n");

        }
    }
}

void Lsv_NtkSdc(Abc_Ntk_t* pNtk, int id, int* pat, int fVerbose, int fSim ) 
{
    Abc_Obj_t* pObj;
    Abc_Obj_t* pTarget = Abc_NtkObj(pNtk, id);
    Abc_Ntk_t* pCone;
    int i, j;


    Abc_Obj_t* pRoot = Abc_ObjFanin0( Abc_NtkPo(pNtk, 2) );
    pCone = Abc_NtkCreateCone( pNtk, pRoot, "name", 1);
    Aig_Man_t * pMan = Abc_NtkToDar( pCone, 0, 0 );
    if ( pMan == NULL ) printf("NULL!\n");
    else {
        printf("no problem! %d\n", pCone->ntkType);
        Abc_NtkPrintStats(pCone, 0,0,0,0,0,0,0,0,0,0);
        Aig_ManStop(pMan);
    }
    Abc_NtkDelete(pCone);
    
    // init
    for ( i = 0; i < 4; i++ ) pat[i] = 0;

    // create fanin cone
    Vec_Ptr_t * vFanin = Vec_PtrAlloc(2);
    Vec_PtrPushTwo(vFanin, Abc_ObjFanin0(pTarget), Abc_ObjFanin1(pTarget));
    pCone = Abc_NtkCreateConeArray(pNtk, vFanin, 0);
    if ( Abc_ObjFaninC0(pTarget) ) Abc_ObjXorFaninC( Abc_NtkPo(pCone, 0), 0);
    if ( Abc_ObjFaninC1(pTarget) ) Abc_ObjXorFaninC( Abc_NtkPo(pCone, 1), 0);
    Vec_PtrFree( vFanin );

    // simulation
    int nRound = fSim ? 64 : 0;
    int simPi [Abc_NtkPiNum(pCone)];
    int * simPo;
    int val;
    int nPatLeft = 4;
    for ( i = 0; i < nRound; i++ )
    {
        Abc_NtkForEachPi(pCone, pObj, j)
        for ( j = 0; j < Abc_NtkPiNum(pCone); j++ )
        {
            simPi[j] = Abc_RandomW(0);
        }
        simPo =Lsv_SimulatePattern(pCone, simPi);
        for ( j = 0; j < 4; j ++ )
        {
            if ( pat[j] ) continue;
            val = ( j>>1 ? simPo[0] : ~simPo[0] ) & (j%2 ? simPo[1] : ~simPo[1]) ;
            if ( val != 0 ) 
            {
                pat[j] = 1;
                if ( fVerbose ) printf("Simulation found pattern %d%d\n", j>>1, j%2 );
                nPatLeft --;
            }
        }

        if ( nPatLeft == 0 ) break;
    }

    if ( nPatLeft )
    {

        if ( fVerbose ) printf("start SAT solver\n");

        // derive cnf
        Aig_Man_t * pMan = Abc_NtkToDar( pCone, 0, 0 );
        Cnf_Dat_t * pCnf = Cnf_Derive( pMan, 2 );
        sat_solver *solver = sat_solver_new();
        solver = (sat_solver *)Cnf_DataWriteIntoSolverInt( solver, pCnf, 1, 1 );
        // Cnf_DataPrint(pCnf, 1);  

        lit assump [2];
        int var [2];
        for ( i = 0; i < 2; i++ ) var[i] = pCnf->pVarNums[Aig_ObjId(Aig_ManCo(pMan, i))];

        // printf("var[0]=%d var[1]=%d\n", var[0], var[1]);

        for ( i = 0; i < 4; i++ )
        {
            if ( pat[i] ) continue;

            assump [0] = Abc_Var2Lit(var[0], (i>>1) ? 0 : 1 );
            assump [1] = Abc_Var2Lit(var[1], (i%2) ? 0 : 1 );

            int status = sat_solver_solve(solver, assump, assump+2, 0, 0, 0, 0);
            if ( status == l_True )
            {
                if ( fVerbose ) printf("SAT solver found pattern %d%d\n", i >> 1, i % 2 );
                pat[i] = 1;
            }
            else 
            {
                if ( fVerbose ) printf("SAT solver can't found pattern %d%d\n", i >> 1, i % 2 );
            }
        }

        Aig_ManStop(pMan);
        Cnf_DataFree(pCnf);
        sat_solver_delete(solver);

    }


    // clean up
    Abc_NtkDelete(pCone);
}


int Lsv_NtkOdc(Abc_Ntk_t* pNtk, int id, int* pat, int fVerbose, int fSim ) 
{

    Abc_Obj_t* pObj;
    Abc_Obj_t* pTarget = Abc_NtkObj(pNtk, id);
    Abc_Obj_t * pFanout;
    int i, j;

    // create ntk2 with pNode flipped
    Abc_Ntk_t * pNtk2 = Abc_NtkDup(pNtk);
    pObj = Abc_NtkObj(pNtk2, id);
    Abc_ObjForEachFanout(pObj, pFanout, i)
    {
        Abc_ObjXorFaninC(pFanout, Abc_ObjFanoutFaninNum(pFanout, pObj) );
    }

    // creat miter
    Abc_Ntk_t * pMiter = Abc_NtkMiter(pNtk, pNtk2, 1, 0, 0, 0);

    // collect fanin
    Vec_Ptr_t * vFanin = Vec_PtrAlloc(2);
    Vec_PtrPushTwo(vFanin, Abc_ObjFanin0(pTarget), Abc_ObjFanin1(pTarget));

    // add the fanin cone to miter
    Abc_Ntk_t * pCone = Abc_NtkCreateConeArray(pNtk, vFanin, 1);
    char name0 [32];
    char name1 [32];
    strcpy(name0, Abc_ObjName(Abc_NtkPo(pCone, 0)));
    strcpy(name1, Abc_ObjName(Abc_NtkPo(pCone, 1)));

    // Abc_NtkForEachPo(pCone, pObj, i) printf("pcone %s %d\n", Abc_ObjName(pObj),  Abc_ObjFaninC0(Abc_ObjFanin0(pObj)));

    if ( Abc_ObjFaninC0(pTarget) ) Abc_ObjXorFaninC( Abc_NtkPo(pCone, 0), 0);
    if ( Abc_ObjFaninC1(pTarget) ) Abc_ObjXorFaninC( Abc_NtkPo(pCone, 1), 0);

    assert( Abc_NtkAppend(pMiter, pCone, 1) );
    // assert( Abc_NtkMyAppend(pMiter, pCone, 1) );
    Vec_PtrFree(vFanin);

    if ( strcmp(name0, Abc_ObjName(Abc_NtkPo(pCone, 0))) != 0 )
    {
        if ( fVerbose )
        {
            printf("[warning] fanin order changed.\n");
        }
        Abc_NtkDelete(pNtk2);
        Abc_NtkDelete(pMiter);
        Abc_NtkDelete(pCone);
        return 1;
    }

    // Abc_NtkForEachPo(pMiter, pObj, i)
    // {
    //     printf("pMiter %s %d\n", Abc_ObjName(pObj),  Abc_ObjFaninC0(Abc_ObjFanin0(pObj)));
    // }
    // Abc_NtkForEachPo(pCone, pObj, i)
    // {
    //     printf("pcone %s %d\n", Abc_ObjName(pObj),  Abc_ObjFaninC0(Abc_ObjFanin0(pObj)));
    // }

    int nPatLeft = 0;
    // use simlation to locate some cares
    int nRound = fSim ? 64 : 0;
    int simPi [Abc_NtkPiNum(pMiter)];
    int * simPo;
    int val;
    for( i = 0; i < 4; i ++ ) if ( pat[i] ) nPatLeft++;
    for ( i = 0; i < nRound; i++ )
    {
        Abc_NtkForEachPi(pMiter, pObj, j)
        for ( j = 0; j < Abc_NtkPiNum(pMiter); j++ )
        {
            simPi[j] = Abc_RandomW(0);
        }
        simPo = Lsv_SimulatePattern(pMiter, simPi);
        for ( j = 0; j < 4; j ++ )
        {
            if ( !pat[j] ) continue; // is already in care set or sdc
            val = ( j>>1 ? simPo[1] : ~simPo[1] ) & (j%2 ? simPo[2] : ~simPo[2]) & simPo[0];
            if ( val != 0 ) 
            {
                pat[j] = 0;
                if ( fVerbose ) printf("Simulation found pattern %d%d in care set\n", j>>1, j%2 );
                nPatLeft -= 1;
                if ( fVerbose ) printf("pat left: %d\n", nPatLeft);
            }
        }
        if ( nPatLeft == 0 ) break;
    }


    if ( nPatLeft != 0 )
    {

        if ( fVerbose ) printf("start SAT solver\n");

        // create CNF
        Aig_Man_t * pMiterAig = Abc_NtkToDar(pMiter, 0, 0);
        Cnf_Dat_t *pCnf = Cnf_Derive(pMiterAig, 3);
        sat_solver *solver = sat_solver_new();
        solver = (sat_solver *)Cnf_DataWriteIntoSolverInt(solver, pCnf, 1, 0);

        // Cnf_DataPrint(pCnf, 1);

        // set the assumptions
        int poVar [3];
        for ( i = 0; i < 3; i++ )
            poVar[i] = pCnf->pVarNums[Aig_ObjId(Aig_ManCo(pMiterAig, i))];

        // assumptions
        lit assump [2];
        assump[0] = Abc_Var2Lit(poVar[0], 0);
        assert ( sat_solver_addclause(solver, assump, assump+1) );

        // add simulated pat
        for ( i = 0; i < 4; i++ )
        {
            if ( pat[i] ) continue;
            assump[0] = Abc_Var2Lit(poVar[1], i>>1);
            assump[1] = Abc_Var2Lit(poVar[2], i%2);
            assert ( sat_solver_addclause(solver, assump, assump+2) );
            if ( fVerbose ) printf( "block solution %d%d\n", i >> 1, i % 2 );
        }

        int status, val0, val1;
        lit clause [2];


        // solve and block until unsat
        for ( i = 0; i < nPatLeft; ++i) {

            // solve the SAT problem
            status = sat_solver_solve(solver, 0, 0, 0, 0, 0, 0);

            if ( status == l_True)
            {
                // found care, record pat
                val0 = sat_solver_var_value(solver, poVar[1]);
                val1 = sat_solver_var_value(solver, poVar[2]);
                pat[val0*2+val1] = 0;
                if ( fVerbose )printf("SAT with fanin value %d %d\n", val0, val1);
                clause[0] = Abc_Var2Lit(poVar[1], val0);
                clause[1] = Abc_Var2Lit(poVar[2], val1);
                if ( !sat_solver_addclause(solver, clause, clause+2) )
                {
                    if ( fVerbose ) printf("UNSAT (last sol blocked)\n");
                    break;
                }
            }
            else 
            {
                // unsat, all care set found
                if ( fVerbose ) printf("UNSAT (or timeout)\n");
                break;
            }
        }

        Aig_ManStop(pMiterAig);
        Cnf_DataFree(pCnf);
    }

    Abc_NtkDelete(pNtk2);
    Abc_NtkDelete(pMiter);
    Abc_NtkDelete(pCone);

    return 0;
}

int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c;
  int fSkip = 0;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "hs")) != EOF) {
    switch (c) {
      case 's':
        fSkip = 1;
        break;
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

  Lsv_NtkPrintNodes(pNtk, fSkip);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_print_nodes [-h]\n");
  Abc_Print(-2, "\t        prints the nodes in the network\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}

int Lsv_CommandPrintCut(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c, k;
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
  k = atoi(argv[globalUtilOptind]);
  Lsv_NtkPrintCuts(pNtk, k);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_printcut [-h] <k>\n");
  Abc_Print(-2, "\t        prints the nodes in the network\n");
  Abc_Print(-2, "\t<k>   : k-feasible cut\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}

int Lsv_CommandPrintMoCut(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c, k, l;
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
  if (argc <= globalUtilOptind+1) {
        goto usage;
  }
  k = atoi(argv[globalUtilOptind]);
  l = atoi(argv[globalUtilOptind+1]);
  Lsv_NtkPrintMoCuts(pNtk, k, l);

  return 0;

usage:
  Abc_Print(-2, "usage: lsv_printmocut [-h] <k> <l>\n");
  Abc_Print(-2, "\t        prints the nodes in the network\n");
  Abc_Print(-2, "\t<k>   : number of inputs\n");
  Abc_Print(-2, "\t<l>   : number ouf outputs\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}

int Lsv_CommandSdc(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c, id, fVerbose = 0, fSim = 1;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "hsv")) != EOF) {
    switch (c) {
        case 'v':
        fVerbose = 1; break;
        case 's':
        fSim = 0; break;
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
  id = atoi(argv[globalUtilOptind]);
  int pat [4];
  Lsv_NtkSdc(pNtk, id, pat, fVerbose, fSim );
  if ( pat[0] && pat[1] && pat[2] && pat[3] )
  {
    Abc_Print(1, "no sdc\n");
  }
  else 
  {
    for ( int i = 0; i < 4; i++ )
    {
        if (!pat[i]) 
        {
            Abc_Print(1, "%d%d\n", (i & 2) ? 1 : 0, (i & 1) ? 1 : 0);
        }
    }
 }
  
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_sdc <n>\n");
  Abc_Print(-2, "\t        given an AIG, prints the sdc of node <n>\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}

int Lsv_CommandOdc(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t *pNtk = Abc_FrameReadNtk(pAbc);
  int c, id, fVerbose = 0, fSim = 1;
  int pat [4];
  Extra_UtilGetoptReset();

  while ((c = Extra_UtilGetopt(argc, argv, "hsv")) != EOF) {
    switch (c) {
    case 'v':
        fVerbose = 1;
        break;
    case 's':
        fSim = 0;
        break;
    case 'h':
    default:
      goto usage;
    }
  }
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  id = atoi(argv[globalUtilOptind]);


  // find appearing pats
  Lsv_NtkSdc(pNtk, id, pat, fVerbose, fSim );
  if ( fVerbose ) printf("SDC done\n");

  // remove careset from pat
  Lsv_NtkOdc(pNtk, id, pat, fVerbose, fSim );

  if (!pat[0] && !pat[1] && !pat[2] && !pat[3]) {
    Abc_Print(1, "no odc\n");
  } else {
    for (int i = 0; i < 4; i++) {
      if (pat[i]) {
        Abc_Print(1, "%d%d\n", i>>1, i%2);
      }
    }
  }

  return 0;

usage:
  Abc_Print(-2, "usage: lsv_sdc <n>\n");
  Abc_Print(-2, "\t        given an AIG, prints the sdc of node <n>\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}

// int Abc_CommandCheckUnateAig(Abc_Frame_t *pAbc, int argc, char **argv){
//     if (argc != 3) {
//         Abc_Print(-1, "Usage: lsv_unate_aig <po> <ci>\n");
//         return 1;
//     }

//     int k = atoi(argv[1]);   // output index
//     int i = atoi(argv[2]);   // input index

//     Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
//     if ( pNtk == NULL ) { Abc_Print(-1,"No network\n"); return 1; }

//     if (!Abc_NtkIsStrash(pNtk))
//     {
//         Abc_Print(-1, "Warning: Network is not AIG. Force-strashing now...\n");
//         pNtk = Abc_NtkStrash(pNtk, 0, 0, 0);
//         Abc_FrameSetCurrentNetwork(pAbc, pNtk);
//     }

//     Abc_Obj_t * pPo = Abc_NtkPo(pNtk, k);
//     if ( pPo == NULL ) { Abc_Print(-1,"PO idx out of range\n"); return 1; }

//     Abc_Obj_t* pRoot = Abc_ObjFanin0(pPo);

//     // create cone
//     Abc_Ntk_t * pCone = Abc_NtkCreateCone( pNtk, pRoot, Abc_ObjName(pPo), 0);
//     if ( pCone == NULL ) { Abc_Print(-1,"Failed to create cone\n"); return 1; }
//     Abc_Print(1, "DEBUG: cone type = %d (AIG=1, STRASH=2)\n", pCone->ntkType);

//     Abc_NtkPrintStats(pCone, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0);

//     // convert the cone to AIG (Dar)
//     Aig_Man_t * pAig = Abc_NtkToDar( pCone, 0, 0 );
//     if ( pAig == NULL ) { Abc_Print(-1,"Abc_NtkToDar failed\n"); Abc_NtkDelete(pCone); return 1; }
// }
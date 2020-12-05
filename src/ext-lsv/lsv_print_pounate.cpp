
#include "ext-lsv/lsv_cmd.h"

extern "C"
{
    /// in /base/abci/abcDar.c
    Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
    
    /// in /proof/fra/fraCec.c
    int Fra_FraigSat( Aig_Man_t * pMan, ABC_INT64_T nConfLimit, ABC_INT64_T nInsLimit, int nLearnedStart, int nLearnedDelta, int nLearnedPerce, int fFlipBits, int fAndOuts, int fNewSolver, int fVerbose );
    /// in /base/abci/abcStrash.c
    Abc_Ntk_t * Abc_NtkStrash( Abc_Ntk_t * pNtk, int fAllNodes, int fCleanup, int fRecord );
    
    void * Cnf_DataWriteIntoSolver2( Cnf_Dat_t * p, int nFrames, int fInit );
    int    Cnf_DataWriteOrClause2( void * pSat, Cnf_Dat_t * pCnf );
}

namespace lsv
{

static void print_cnf( Cnf_Dat_t * pCnf )
{
    /// print CNF
    printf( "CNF stats: Vars = %6d. Clauses = %7d. Literals = %8d. \n", pCnf->nVars, pCnf->nClauses, pCnf->nLiterals );
    Cnf_DataPrint(pCnf, 1);
}

static void add_variable_constraint(
    Aig_Man_t * pMan,
    Aig_Obj_t * pCo, 
    std::vector< Aig_Obj_t* >& xi_vec, 
    std::vector< Aig_Obj_t* >& yi_vec,
    int vi )
{
    /// add variable_constraint for pos unate
    Aig_Obj_t *pF = Aig_ObjFanin0(pCo), *xi, *yi;
    for( int i=0; i<xi_vec.size(); ++i )
    {
        xi = xi_vec[i];
        yi = yi_vec[i];
        if( i==vi )
        {
            pF = Aig_And( pMan, pF, Aig_And( pMan, Aig_Not(xi), yi) );
        }
        else
        {
            /// ( x' + y ) * ( x + y' )
            Aig_Obj_t * pAnd = Aig_And( pMan, 
                                        Aig_Or( pMan, Aig_Not(xi) ,yi ),
                                        Aig_Or( pMan, xi ,Aig_Not(yi) ) );
            pF = Aig_And( pMan, pF, pAnd );
        }
    }
    
    Aig_ObjConnect( pMan, pCo, pF, NULL );
    
}

static Aig_Obj_t * duplicate_aig(
    Aig_Man_t * pMan,
    Aig_Obj_t * node,
    std::vector< Aig_Obj_t* >& xi_vec, 
    std::vector< Aig_Obj_t* >& yi_vec
)
{
    if( node==NULL ) return node;
    if( node->pData!=NULL ) return (Aig_Obj_t *)node->pData;
    
    Aig_Obj_t * Fanin0 = duplicate_aig( pMan, Aig_ObjFanin0(node), xi_vec, yi_vec );
    Aig_Obj_t * Fanin1 = duplicate_aig( pMan, Aig_ObjFanin1(node), xi_vec, yi_vec );
    
    node->pData=node;
    if( Aig_ObjType(node)==AIG_OBJ_CO ) return Fanin0;
    if( Aig_ObjType(node)==AIG_OBJ_CONST1 ) return (Aig_Obj_t *)node->pData;
    if( Aig_ObjType(node)==AIG_OBJ_CI )
    {
        for( int i=0; i<xi_vec.size(); ++i )
        {
            if( xi_vec[i]==node ) node->pData = yi_vec[i];
        }
        return (Aig_Obj_t *)node->pData;
    }
    if( Aig_ObjType(node)==AIG_OBJ_AND )
    {
        node->pData = Aig_And( pMan, 
                               Aig_NotCond(Fanin0, Aig_ObjFaninC0(node)),
                               Aig_NotCond(Fanin1, Aig_ObjFaninC1(node)) );
        return (Aig_Obj_t *)node->pData;
    }
    
    return node;
}

static int solve_single_po_unateness(Abc_Ntk_t * pNtk)
{   
    /// solve unateness for a single cone
    /// 0 is SAT, 1 is UNSAT
    
    int i;
    //Abc_Obj_t* pPO;
    Abc_Obj_t* pPi;
        
    Abc_NtkForEachPi( pNtk, pPi, i )
    {
        std::cout << "input " << Abc_ObjName( pPi ) << ":" << std::endl;
    }
    
    /// convert the cone into Aig Manager
    Aig_Man_t *pMan;
    pMan = Abc_NtkToDar( pNtk, 0, 0 );
    Aig_ManPrintStats(pMan);    // check AIG manager
    
    Aig_Obj_t *pCi, *pCo, *pF1, *pF2;
    
    /// Store CI in the same order as pNtk
    std::vector< Aig_Obj_t* > xi_vec(Aig_ManCiNum(pMan)), yi_vec(Aig_ManCiNum(pMan));
    Aig_ManForEachCi( pMan, pCi, i )
    {
        xi_vec[i] = pCi;
    }
    for( int i=0; i<xi_vec.size(); ++i )
    {
        yi_vec[i] = Aig_ObjCreateCi( pMan );
    }
    /// Find node F1
    Aig_ManForEachCo( pMan, pCo, i )
    {
        
        pF1 = Aig_ObjFanin0(pCo);
    }
    
    /// Duplicate AIG structure, create F2
    Aig_ManCleanData(pMan);
    pF2 = duplicate_aig( pMan, pCo, xi_vec, yi_vec );
        
    /// connect PO to f1 * f2', but they are inverted!!!
    Aig_ObjConnect( pMan, pCo, Aig_And( pMan, Aig_Not(pF1), pF2 ), NULL );
    
    Aig_ManPrintStats(pMan);    // check AIG manager
    
    add_variable_constraint( pMan, pCo, xi_vec, yi_vec, 0 );
    Aig_ManPrintStats(pMan);    // check AIG manager
    //Aig_ManDump(pMan);
    
    
    /// derive CNF
    pMan->pData = NULL;
    Cnf_Dat_t * pCnf = Cnf_Derive( pMan, Aig_ManCoNum(pMan) );
    //Cnf_Dat_t * pCnf = Cnf_DeriveFast( pMan, Aig_ManCoNum(pMan) );
    
    //print_cnf( pCnf );
    
    Vec_Int_t * vCiIds = Cnf_DataCollectPiSatNums( pCnf, pMan );
    /*
    std::cout << "PIs in CNF variable:" << std::endl;
    for( int i=0; i<vCiIds->nSize; ++i )
    {
        std::cout << vCiIds->pArray[i] << std::endl;
    }
    */
    
    /// write to sat_solver2
    sat_solver2 * pSat = (sat_solver2 *)Cnf_DataWriteIntoSolver2( pCnf, 1, 0 );
    /// add the OR clause for the outputs
    if ( !Cnf_DataWriteOrClause2( pSat, pCnf ) )
    {
        sat_solver2_delete( pSat );
        Cnf_DataFree( pCnf );
        Aig_ManStop( pMan );
        return 1;
    }
    
    printf( "Created SAT problem with %d variable and %d clauses. \n", sat_solver2_nvars(pSat), sat_solver2_nclauses(pSat) );
    
    Cnf_DataFree( pCnf );
    
    int status = sat_solver2_simplify(pSat);
    if ( status == 0 )
    {
        Vec_IntFree( vCiIds );
        sat_solver2_delete( pSat );
        Aig_ManStop( pMan );
        return 1;
    }
    
    int RetValue;
    status = sat_solver2_solve( pSat, NULL, NULL, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
    if ( status == l_Undef ) RetValue = -1;
    else if ( status == l_True ) RetValue = 0;
    else if ( status == l_False ) RetValue = 1;
    else assert( 0 );
    
    Sat_Solver2PrintStats( stdout, pSat );
            
    Vec_IntFree( vCiIds );
    sat_solver2_delete( pSat );
    pNtk->pModel = (int *)pMan->pData, pMan->pData = NULL;
    Aig_ManStop( pMan );
    return RetValue;
}

static void print_po_unateness(Abc_Ntk_t* pNtk)
{   
    assert( Abc_NtkIsStrash(pNtk) );
    
    int i;
    Abc_Obj_t* pPO;
    Abc_Obj_t* pPi;
    Abc_NtkForEachPo( pNtk, pPO, i )
    {
        //std::cout << "node " << Abc_ObjName( pPO ) << ":" << std::endl;
    }
    Abc_NtkForEachPi( pNtk, pPi, i )
    {
        //std::cout << "input " << Abc_ObjName( pPi ) << ":" << std::endl;
    }
    
    Abc_NtkForEachPo( pNtk, pPO, i )
    {
        Abc_Ntk_t * pNtkCone = Abc_NtkCreateCone( pNtk, Abc_ObjFanin0(pPO), Abc_ObjName(pPO), 1 );
        
        int RetValue = solve_single_po_unateness( pNtkCone );
        
        if ( RetValue == -1 )
            Abc_Print( 1, "UNDECIDED      \n" );
        else if ( RetValue == 0 )
            Abc_Print( 1, "SATISFIABLE    \n" );
        else
            Abc_Print( 1, "UNSATISFIABLE  \n" );
            
        Abc_NtkDelete( pNtkCone );
    }
}

static void HelpCommandPrintPOUnate()
{  
    Abc_Print(-2, "usage: lsv_print_pounate [-h]\n");
    Abc_Print(-2, "\t        report unateness for each PO\n");
    Abc_Print(-2, "\t-h    : print the command usage\n");
}

int CommandPrintPOUnate(Abc_Frame_t* pAbc, int argc, char** argv)
{
    Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    Extra_UtilGetoptReset();
    while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
        case 'h':
            HelpCommandPrintPOUnate();
            return 1;
        default:
            HelpCommandPrintPOUnate();
            return 1;
    }
    }
    if (!pNtk) {
        Abc_Print(-1, "Empty network.\n");
        return 1;
    }
    
    /// strash network if it is not aig
    Abc_Ntk_t * pNtkRes = pNtk;
    if( !Abc_NtkIsStrash(pNtk) )
    {
        pNtkRes = Abc_NtkStrash( pNtk, 0, 1, 0 );
        if ( pNtkRes == NULL )
        {
            Abc_Print( -1, "Strashing has failed.\n" );
            return 1;
        }
    }
    
    print_po_unateness(pNtkRes);
    Abc_NtkDelete( pNtkRes );
    return 0;
}

}   /// end of namespace lsv
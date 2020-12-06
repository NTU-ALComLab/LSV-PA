
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

static void sat_add_variable_constraint(
    sat_solver2 * pSat, Vec_Int_t * vCiIds, int num_var, int vi )
{
    /*
         vCiIds[0 .. num_var-1] : x1 ... xn
         vCiIds[num_var .. 2*num_var-1] : y1 ... yn
         vCiIds[2*num_var .. 3*num_var] : z0 z1 ... zn
    */
    int * lit_vec = vCiIds->pArray;
    for( int i=0; i<num_var; ++i )
    {
        int lits[3];
        if( i==vi )
        {
            /// add xi' and yi
            lits[0] = 2*lit_vec[i]+1;
            sat_solver2_addclause( pSat, &lits[0], &lits[1],0 );
            lits[0] = 2*lit_vec[i+num_var];
            sat_solver2_addclause( pSat, &lits[0], &lits[1],0 );
        }
        else
        {
            /// add (xi'+yi) and (xi+yi')
            lits[0] = 2*lit_vec[i]+1;
            lits[1] = 2*lit_vec[i+num_var];
            sat_solver2_addclause( pSat, &lits[0], &lits[2],0 );
            lits[0] = 2*lit_vec[i];
            lits[1] = 2*lit_vec[i+num_var]+1;
            sat_solver2_addclause( pSat, &lits[0], &lits[2],0 );
        }
    }
}
static Aig_Obj_t * add_variable_constraint(
    Aig_Man_t * pMan,
    std::vector< Aig_Obj_t* >& xi_vec, 
    std::vector< Aig_Obj_t* >& yi_vec,
    int vi )
{
    /// add variable constraints of unateness for (x1 ... xn, y1 ... yn)
    /// vi is the cofactored variable
    /// returns the top node
    Aig_Obj_t *pF = NULL, *xi, *yi;
    for( int i=0; i<xi_vec.size(); ++i )
    {
        xi = xi_vec[i];
        yi = yi_vec[i];
        if( i==vi )
        {
            if( pF == NULL )
                pF = Aig_And( pMan, Aig_Not(xi), yi);
            else
                pF = Aig_And( pMan, pF, Aig_And( pMan, Aig_Not(xi), yi) );
        }
        else
        {
            /// ( x' + y ) * ( x + y' )
            if( pF == NULL )
            {
                pF = Aig_And( pMan, 
                              Aig_Or( pMan, Aig_Not(xi) ,yi ),
                              Aig_Or( pMan, xi ,Aig_Not(yi) ) );
            }
            else
            {
                Aig_Obj_t * pAnd = Aig_And( pMan, 
                                            Aig_Or( pMan, Aig_Not(xi) ,yi ),
                                            Aig_Or( pMan, xi ,Aig_Not(yi) ) );
                pF = Aig_And( pMan, pF, pAnd );
            }
        }
    }
    
   return pF;
    
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

static void solve_single_po_unateness( Abc_Ntk_t * pNtk, std::vector<Unateness>& unate_vec )
{   
    /// solve unateness for a single cone
    
    unate_vec.resize( Abc_NtkPiNum(pNtk), NONE );
    
    for( int pi_idx=0; pi_idx<Abc_NtkPiNum(pNtk); ++pi_idx)
    {
        int i;
        /// convert the cone into Aig Manager
        Aig_Man_t *pMan;
        pMan = Abc_NtkToDar( pNtk, 0, 0 );
        //Aig_ManPrintStats(pMan);    // check AIG manager
        
        Aig_Obj_t *pCi, *pCo, *pF1, *pF2, *pFc, *pPos, *pNeg;
        
        /// Store CI in the same order as pNtk
        std::vector< Aig_Obj_t* > xi_vec(Aig_ManCiNum(pMan)), yi_vec(Aig_ManCiNum(pMan));
        std::vector< Aig_Obj_t* > zi_vec;
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
            
        /// build variable constraints of unateness
        //pFc = add_variable_constraint( pMan, xi_vec, yi_vec, pi_idx );
        
        /// connect f1 * f2', f1' * f2
        pPos = Aig_And( pMan, Aig_Not(pF2), pF1 );
        pNeg = Aig_And( pMan, Aig_Not(pF1), pF2 );
        
        /// build up SAT variables
        zi_vec.push_back( Aig_ObjCreateCi( pMan ) );
        Aig_Obj_t *pZ0 = zi_vec[0];
        pPos = Aig_Or( pMan, pPos, pZ0 );
        pNeg = Aig_Or( pMan, pNeg, Aig_Not(pZ0) );
        
        //Aig_ObjConnect( pMan, pCo, Aig_And( pMan, Aig_And( pMan, pPos, pNeg ), pFc ), NULL );
        //Aig_ObjConnect( pMan, pCo, Aig_And( pMan, pPos, pFc ), NULL );
        Aig_ObjConnect( pMan, pCo, Aig_And( pMan, pPos, pNeg ), NULL );
        //Aig_ObjConnect( pMan, pCo, pPos, NULL );
        //Aig_ManPrintStats(pMan);    // check AIG manager
        //Aig_ManDump(pMan);
        
        
        /// derive CNF
        pMan->pData = NULL;
        Cnf_Dat_t * pCnf = Cnf_DeriveFast( pMan, Aig_ManCoNum(pMan) );
        //print_cnf( pCnf );
        Vec_Int_t * vCiIds = Cnf_DataCollectPiSatNums( pCnf, pMan );
                
        /// write to sat_solver2
        sat_solver2 * pSat = (sat_solver2 *)Cnf_DataWriteIntoSolver2( pCnf, 1, 0 );
        
        sat_add_variable_constraint( pSat, vCiIds, xi_vec.size(), pi_idx  );
        
        /// add the OR clause for the outputs
        Cnf_DataWriteOrClause2( pSat, pCnf );
        //Cnf_DataWriteAndClauses( pSat, pCnf );
                
        //printf( "Created SAT problem with %d variable and %d clauses. \n", sat_solver2_nvars(pSat), sat_solver2_nclauses(pSat) );
        
        /// simplify the SAT solver
        int status = 0;// = sat_solver2_simplify(pSat);
        /*
        if ( status == 0 )
        {
            /// UNSAT, POS_UNATE
            unate_vec[pi_idx] = POS_UNATE;
            Vec_IntFree( vCiIds );
            Cnf_DataFree( pCnf );
            sat_solver2_delete( pSat );
            pNtk->pModel = (int *)pMan->pData, pMan->pData = NULL;
            Aig_ManStop( pMan );
            continue;
        }*/
        
        /// setup assumption for POS_UNATE
        int num_assumption = 1, num_var = xi_vec.size();
        int* lit_vec = new int[num_assumption+1];
        
        /// order of CI in vCiIds is the same as Aig_ManForEachCi
        lit_vec[0] =  2*vCiIds->pArray[ num_var*2 ]+1;
        /*
        for( int i=0; i<vCiIds->nSize; ++i )
        {
            std::cout << vCiIds->pArray[i] << std::endl;
        }
        std::cout << lit_vec[0] << std::endl;
        */
        //std::cout << "Run SAT Solver" << std::endl;
        
        /// run SAT solver
        //status = sat_solver2_solve( pSat, NULL, NULL, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
        status = sat_solver2_solve( pSat, &lit_vec[0], &lit_vec[num_assumption], (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
        //Sat_Solver2PrintStats( stdout, pSat );
        
        /// l_False = -1 = UNSAT; l_True = 1 = SAT
        //std::cout << "status=" << status << std::endl;
        if ( status == l_False )
        {
            //std::cout << "pos" << std::endl;
            unate_vec[pi_idx] = POS_UNATE;
            Vec_IntFree( vCiIds );
            Cnf_DataFree( pCnf );
            sat_solver2_delete( pSat );
            pNtk->pModel = (int *)pMan->pData, pMan->pData = NULL;
            Aig_ManStop( pMan );
            delete lit_vec;
            continue;
        }
        
        //////////////////////////////////////
        /// not pos_unate, check neg_unate ///
        //////////////////////////////////////
        
        //std::cout << "Run SAT Solver 2" << std::endl;
        
        /// set assumption for NEG_UNATE
        lit_vec[0] = 2*vCiIds->pArray[ num_var*2 ];
        //status = sat_solver2_solve( pSat, NULL, NULL, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
        status = sat_solver2_solve( pSat, &lit_vec[0], &lit_vec[num_assumption], (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
        //Sat_Solver2PrintStats( stdout, pSat );
        
        //std::cout << "status=" << status << std::endl;
        if ( status == l_False )
        {
            unate_vec[pi_idx] = NEG_UNATE;
            //std::cout << "neg" << std::endl;
        }
        else
        {
            unate_vec[pi_idx] = BINATE;
            //std::cout << "binate" << std::endl;
        }
            Vec_IntFree( vCiIds );
            Cnf_DataFree( pCnf );
            sat_solver2_delete( pSat );
            pNtk->pModel = (int *)pMan->pData, pMan->pData = NULL;
            Aig_ManStop( pMan );
            delete lit_vec;
            
        //std::cout << "end of PI" << std::endl;
    }
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
        Abc_Ntk_t * pNtkCone = Abc_NtkCreateCone( pNtk, Abc_ObjFanin0(pPO), Abc_ObjName(pPO), 0 );
        std::vector<Unateness> unate_vec;
        
        solve_single_po_unateness( pNtkCone, unate_vec );
        
        for( auto u : unate_vec ) std::cout << u << std::endl;
        
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
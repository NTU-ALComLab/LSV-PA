
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
    
    void Abc_NtkShow( Abc_Ntk_t * pNtk, int fGateNames, int fSeq, int fUseReverse ); 
}

namespace lsv
{

static void print_cnf( Cnf_Dat_t * pCnf )
{
    /// print CNF
    printf( "CNF stats: Vars = %6d. Clauses = %7d. Literals = %8d. \n", pCnf->nVars, pCnf->nClauses, pCnf->nLiterals );
    Cnf_DataPrint(pCnf, 1);
}

static void sat_make_assumption(
    int* lit_vec, Vec_Int_t * vCiIds, int num_var, int idx, int is_pos )
{
    /*
         vCiIds[0 .. num_var-1] : x1 ... xn
         vCiIds[num_var .. 2*num_var-1] : y1 ... yn
         vCiIds[2*num_var .. 3*num_var] : z1 ... zn, z0
    */
    int i=0;
    for( ; i<num_var; ++i )
    {
        if( i==idx )
        {
            lit_vec[i] =  2*vCiIds->pArray[ num_var*2+i ]+1;    /// set to 0
        }
        else
        {
            lit_vec[i] =  2*vCiIds->pArray[ num_var*2+i ];      /// set to 1
        }
    }
    if( is_pos )
        lit_vec[i] = 2*vCiIds->pArray[ num_var*3 ]+1;
    else
        lit_vec[i] = 2*vCiIds->pArray[ num_var*3 ];
    ++i;
    lit_vec[i] = 2*vCiIds->pArray[ idx ]+1;
    ++i;
    lit_vec[i] = 2*vCiIds->pArray[ num_var+idx ];
}

static void sat_add_variable_constraint(
    sat_solver * pSat, Vec_Int_t * vCiIds, int num_var )
{
    /*
         vCiIds[0 .. num_var-1] : x1 ... xn
         vCiIds[num_var .. 2*num_var-1] : y1 ... yn
         vCiIds[2*num_var .. 3*num_var] : z1 ... zn, z0
    */
    int * lit_vec = vCiIds->pArray;
    for( int i=0; i<num_var; ++i )
    {
        /*
        int lits[3];
        /// add (xi'+yi+zi') and (xi+yi'+zi')
        lits[0] = 2*lit_vec[i]+1;
        lits[1] = 2*lit_vec[i+num_var];
        lits[2] = 2*lit_vec[i+2*num_var]+1;
        sat_solver_addclause( pSat, &lits[0], &lits[3] );
        lits[0] = 2*lit_vec[i];
        lits[1] = 2*lit_vec[i+num_var]+1;
        lits[2] = 2*lit_vec[i+2*num_var]+1;
        sat_solver_addclause( pSat, &lits[0], &lits[3] );
        
        lits[0] = 2*lit_vec[i]+1;
        lits[1] = 2*lit_vec[i+2*num_var];
        sat_solver_addclause( pSat, &lits[0], &lits[2] );
        lits[0] = 2*lit_vec[i+num_var];
        lits[1] = 2*lit_vec[i+2*num_var];
        sat_solver_addclause( pSat, &lits[0], &lits[2] );
        */
        sat_solver_add_buffer_enable( pSat, lit_vec[i], lit_vec[i+num_var], lit_vec[i+2*num_var], 0 );
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
    /// duplicate all internal nodes recursively
    
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

static void aig_all_clause(
    Aig_Man_t * pMan,
    Aig_Obj_t * pCo, 
    Aig_Obj_t * pF1,
    Aig_Obj_t * pF2,
    const std::vector< Aig_Obj_t* >& xi_vec,
    const std::vector< Aig_Obj_t* >& yi_vec,
    const std::vector< Aig_Obj_t* >& zi_vec  )
{
    Aig_Obj_t *pPos, *pNeg, *pc;
    Aig_Obj_t * pZ0 = zi_vec.back();
    pPos = Aig_Or( pMan, Aig_And( pMan, pF1, Aig_Not(pF2) ), pZ0 );
    pNeg = Aig_Or( pMan, Aig_And( pMan, pF2, Aig_Not(pF1) ), Aig_Not(pZ0) );
    /*
    for( int i=0; i<xi_vec.size(); ++i )
    {
        Aig_Obj_t * new_pc1 = Aig_Or( pMan, 
                                      Aig_Or( pMan, Aig_Not(xi_vec[i]), yi_vec[i] ),
                                      Aig_Not(zi_vec[i]) );
        Aig_Obj_t * new_pc2 = Aig_Or( pMan, 
                                      Aig_Or( pMan, xi_vec[i], Aig_Not(yi_vec[i]) ),
                                      Aig_Not(zi_vec[i]) );
        pc = Aig_And( pMan, pc, Aig_And( pMan, new_pc1, new_pc2 ) );
    }
    */
    Aig_ObjConnect( pMan, pCo,
                    Aig_And( pMan, pPos, pNeg ),
                    NULL );
}


static void solve_po_unateness( Abc_Ntk_t * pNtk, std::vector<Unateness>& unate_vec, int is_inverted )
{
    /// solve unateness for a single cone
    unate_vec.resize( Abc_NtkPiNum(pNtk), NONE );
    
    int i, num_pi = Abc_NtkPiNum(pNtk);
    
    Aig_Man_t *pMan;
    pMan = Abc_NtkToDar( pNtk, 0, 0 );
    
    Aig_Obj_t *pf, *pCo;
    Aig_ManForEachCo( pMan, pCo, i )
    {
        pf = Aig_ObjFanin0(pCo);
    }
    if( is_inverted )
    {
        Aig_ObjConnect( pMan, pCo, Aig_Not(pf), NULL );
    }
    
    //Aig_ManDump(pMan);
    
    Cnf_Dat_t * pf1 = Cnf_Derive( pMan, Aig_ManCoNum(pMan) );
    Cnf_Dat_t * pf2 = Cnf_DataDup( pf1 );
    
    //print_cnf( pf1 );
    
    Cnf_DataLift( pf2, pf1->nVars );
    
    //print_cnf( pf2 );
    
    int num_var = pf1->nVars + pf2->nVars;
    
    Vec_Int_t * vCiIds1 = Cnf_DataCollectPiSatNums( pf1, pMan );
    Vec_Int_t * vCiIds2 = Cnf_DataCollectPiSatNums( pf2, pMan );
        
    sat_solver * pSat = (sat_solver *)sat_solver_new();
    sat_solver_setnvars( pSat, num_var + num_pi + 1 );
    
    int po_clause[2];
    
    /// write clauses to SAT solver
    for ( i = 0; i < pf1->nClauses; i++ )
        sat_solver_addclause( pSat, pf1->pClauses[i], pf1->pClauses[i+1] );
    
    /// f1 + z0
    po_clause[0] = (1)*2;   
    po_clause[1] = (num_var+num_pi)*2;
    sat_solver_addclause( pSat, po_clause, po_clause+2 );
    /// f1' + z0'
    po_clause[0] = (1)*2+1;   
    po_clause[1] = (num_var+num_pi)*2+1;
    sat_solver_addclause( pSat, po_clause, po_clause+2 );
    
    for ( i = 0; i < pf2->nClauses; i++ )
        sat_solver_addclause( pSat, pf2->pClauses[i], pf2->pClauses[i+1] );
    
    /// f2' + z0
    po_clause[0] = (pf1->nVars+1)*2 +1 ;
    po_clause[1] = (num_var+num_pi)*2;
    sat_solver_addclause( pSat, po_clause, po_clause+2 );
    /// f2 + z0'
    po_clause[0] = (pf1->nVars+1)*2 ;
    po_clause[1] = (num_var+num_pi)*2+1;
    sat_solver_addclause( pSat, po_clause, po_clause+2 );
        
    for( i = 0; i<num_pi; i++ )
        sat_solver_add_buffer_enable( pSat, vCiIds1->pArray[i], vCiIds2->pArray[i], num_var+i, 0 );
    
    /// solve for each PI
    for( int pi_idx=0; pi_idx<num_pi; pi_idx++ )
    {
        int num_assumption = num_pi+3;
        int * lit_vec = new int[num_assumption+1];
        
        /// make assumption
        for( int j=0; j<num_pi; j++ )
        {
            if( j==pi_idx )
            {
                lit_vec[j] = 2*(num_var+j)+1;
            }
            else
            {
                lit_vec[j] = 2*(num_var+j);
            }
        }
        lit_vec[num_pi] = 2*(vCiIds1->pArray[pi_idx])+1;
        lit_vec[num_pi+1] = 2*(vCiIds2->pArray[pi_idx]);
        lit_vec[num_pi+2] = 2*(num_var+num_pi)+1;
        
        /// solve pos
        int status = sat_solver_solve( pSat, lit_vec, lit_vec+num_assumption, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
        
        //std::cout << status << std::endl;
        
        if ( status == l_False )
        {
            unate_vec[pi_idx] = POS_UNATE;
        }
        else
        {
            /// assumption for neg unate
            //lit_vec[num_pi] = 2*(vCiIds1->pArray[pi_idx])+1;
            //lit_vec[num_pi+1] = 2*(vCiIds2->pArray[pi_idx]);
            lit_vec[num_pi+2] = 2*(num_var+num_pi);
            /// solve neg
            status = sat_solver_solve( pSat, lit_vec, lit_vec+num_assumption, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
            
            //std::cout << status << std::endl;
        
            if ( status == l_False )
            {
                unate_vec[pi_idx] = NEG_UNATE;
            }
            else
            {
                unate_vec[pi_idx] = BINATE;
            }
        }
        
        delete[] lit_vec;
    }
}

static void solve_single_po_unateness( Abc_Ntk_t * pNtk, std::vector<Unateness>& unate_vec )
{   
    /// solve unateness for a single cone
    
    unate_vec.resize( Abc_NtkPiNum(pNtk), NONE );
    
        int i;
        /// convert the cone into Aig Manager
        Aig_Man_t *pMan;
        pMan = Abc_NtkToDar( pNtk, 0, 0 );
        //Aig_ManPrintStats(pMan);    // check AIG manager
        
        Aig_Obj_t *pCi, *pCo, *pF1, *pF2, *pFc, *pPos, *pNeg;
        
        /// Store CI in the same order as pNtk
        std::vector< Aig_Obj_t* > xi_vec(Aig_ManCiNum(pMan)), yi_vec(Aig_ManCiNum(pMan));
        std::vector< Aig_Obj_t* > zi_vec(Aig_ManCiNum(pMan)+1);
        Aig_ManForEachCi( pMan, pCi, i )
        {
            xi_vec[i] = pCi;
        }
        for( int i=0; i<xi_vec.size(); ++i )
        {
            yi_vec[i] = Aig_ObjCreateCi( pMan );
        }
        /// Add SAT variables z0 z1 ... zn
        for( int i=0; i<zi_vec.size(); ++i )
        {
            zi_vec[i] = Aig_ObjCreateCi( pMan );
        }
        /// Find node F1
        Aig_ManForEachCo( pMan, pCo, i )
        {
            pF1 = Aig_ObjFanin0(pCo);
        }
        //Aig_ManDump(pMan);
        
        /// Duplicate AIG structure, create F2
        Aig_ManCleanData(pMan);
        pF2 = duplicate_aig( pMan, pCo, xi_vec, yi_vec );
            
        /// build variable constraints of unateness
        //pFc = add_variable_constraint( pMan, xi_vec, yi_vec, pi_idx );
        
        /// Build up first part of CNF in aig
        Aig_Obj_t *pZ0 = zi_vec.back();
        //std::cout << "inverted " << Aig_ObjFaninC0(pCo) << std::endl;
        //pPos = Aig_Or( pMan, 
        //               Aig_And( pMan, pF1, Aig_Not(pF2) ),
        //               pZ0 );
        //pNeg = Aig_Or( pMan, 
        //               Aig_And( pMan, Aig_Not(pF1), pF2 ),
        //               Aig_Not(pZ0) );
        
        
        //pPos = Aig_And( pMan, pF1, Aig_Not(pF2) );
        //pNeg = Aig_Or( pMan, pNeg, Aig_Not(pZ0) );
        //Aig_ObjConnect( pMan, pCo, Aig_And( pMan, Aig_And( pMan, pPos, pNeg ), pFc ), NULL );
        //Aig_ObjConnect( pMan, pCo, Aig_And( pMan, pPos, pFc ), NULL );
        //Aig_ObjConnect( pMan, pCo, Aig_And( pMan, pPos, pNeg ), NULL );
        //Aig_ObjConnect( pMan, pCo, pPos, NULL );
        //Aig_ManPrintStats(pMan);    // check AIG manager
        
        aig_all_clause( pMan, pCo, pF1, pF2, xi_vec, yi_vec, zi_vec );
        
        //Aig_ManDump(pMan);
        
        
        /// derive CNF for the first part
        pMan->pData = NULL;
        Cnf_Dat_t * pCnf = Cnf_Derive( pMan, Aig_ManCoNum(pMan) );
        //print_cnf( pCnf );
        Vec_Int_t * vCiIds = Cnf_DataCollectPiSatNums( pCnf, pMan );
                
        for( int i=0; i<vCiIds->nSize; ++i )
        {
            std::cout << vCiIds->pArray[i] << std::endl;
        }
        
        /// write to sat_solver2
        sat_solver * pSat = (sat_solver *)Cnf_DataWriteIntoSolver( pCnf, 1, 0 );
        sat_add_variable_constraint( pSat, vCiIds, xi_vec.size() );
        
        
    int num_var = xi_vec.size();
    int num_assumption = num_var+3; 
    int* lit_vec = new int[num_assumption+1];
    
    for( int pi_idx=0; pi_idx<Abc_NtkPiNum(pNtk); ++pi_idx)
    {
        int status = 0;
        
        /// setup assumption
        sat_make_assumption( lit_vec, vCiIds, num_var , pi_idx, 1 );
        
        
        /// run SAT solver
        //status = sat_solver2_solve( pSat, NULL, NULL, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
        status = sat_solver_solve( pSat, lit_vec, lit_vec+num_assumption, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
        //Sat_Solver2PrintStats( stdout, pSat );
        
        std::cout << "status=" << status << std::endl;
        /// l_False = -1 = UNSAT; l_True = 1 = SAT
        if ( status == l_False )
        {
            unate_vec[pi_idx] = POS_UNATE;
            continue;
        }
        
        /// set assumption for NEG_UNATE
        sat_make_assumption( lit_vec, vCiIds, num_var , pi_idx, 0 );
        
        //status = sat_solver2_solve( pSat, NULL, NULL, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
        status = sat_solver_solve( pSat, lit_vec, lit_vec+num_assumption, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
        //Sat_Solver2PrintStats( stdout, pSat );
        
        std::cout << "status=" << status << std::endl;
        if ( status == l_False )
        {
            unate_vec[pi_idx] = NEG_UNATE;
        }
        else
        {
            unate_vec[pi_idx] = BINATE;
        }
    }
    
    Vec_IntFree( vCiIds );
    Cnf_DataFree( pCnf );
    sat_solver_delete( pSat );
    pNtk->pModel = (int *)pMan->pData, pMan->pData = NULL;
    Aig_ManStop( pMan );
    delete lit_vec;
}

static void print_po_unateness(Abc_Ntk_t* pNtk)
{   
    assert( Abc_NtkIsStrash(pNtk) );
    
    int i;
    Abc_Obj_t* pPO;
    Abc_Obj_t* pPi;
    
    Abc_NtkForEachPo( pNtk, pPO, i )
    {
        Abc_Ntk_t * pNtkCone = Abc_NtkCreateCone( pNtk, Abc_ObjFanin0(pPO), Abc_ObjName(pPO), 0 );
        std::vector<Unateness> unate_vec;
        
        solve_po_unateness( pNtkCone, unate_vec, Abc_ObjFaninC0(pPO) );
        
        int j;
        Abc_Obj_t * ptr;
        Abc_NtkForEachPi( pNtkCone, ptr, j )
        {
            std::cout << Abc_ObjName(ptr) << "\t: " << unate_vec[j] << std::endl;
        }
        //for( auto u : unate_vec ) std::cout << u << std::endl;
        
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
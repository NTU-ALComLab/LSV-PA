#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "sat/cnf/cnf.h"
#include "sat/bsat/satStore.h"
#include "aig/aig/aig.h"

#include <stdio.h>
#include <vector>
#include <string>
#include <algorithm>
#include <iostream>
using namespace std;

static int Lsv_CommandPrintPounate(Abc_Frame_t* pAbc, int argc, char** argv);

void lsv_print_pounate_init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_pounate", Lsv_CommandPrintPounate, 0);
}

void lsv_print_pounate_destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t lsv_print_pounate_initializer = {lsv_print_pounate_init, lsv_print_pounate_destroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&lsv_print_pounate_initializer); }
} lsv_print_pounate_PackageRegistrationManager;

//int Cnf_Lit2Var( int Lit )        { return (Lit & 1)? -(Lit >> 1)-1 : (Lit >> 1)+1;  }
//int Cnf_Lit2VatAbs( int Lit )        { return (Lit & 1)? (Lit >> 1)+1 : (Lit >> 1)+1;  }

int Cnf_Lit2Var( int Lit )        { return (Lit & 1)? -(Lit >> 1)-1 : (Lit >> 1)+1;  }
int Cnf_Lit2VatAbs( int Lit )        { return (Lit & 1)? (Lit >> 1) : (Lit >> 1);  }
/**Function*************************************************************

  Synopsis    [Converts the network from the AIG manager into ABC.]

  Description [Assumes that registers are ordered after PIs/POs.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters )
{
    Vec_Ptr_t * vNodes;
    Aig_Man_t * pMan;
    Aig_Obj_t * pObjNew;
    Abc_Obj_t * pObj;
    int i, nNodes, nDontCares;
    // make sure the latches follow PIs/POs
    if ( fRegisters ) 
    { 
        assert( Abc_NtkBoxNum(pNtk) == Abc_NtkLatchNum(pNtk) );
        Abc_NtkForEachCi( pNtk, pObj, i )
            if ( i < Abc_NtkPiNum(pNtk) )
            {
                assert( Abc_ObjIsPi(pObj) );
                if ( !Abc_ObjIsPi(pObj) )
                    Abc_Print( 1, "Abc_NtkToDar(): Temporary bug: The PI ordering is wrong!\n" );
            }
            else
                assert( Abc_ObjIsBo(pObj) );
        Abc_NtkForEachCo( pNtk, pObj, i )
            if ( i < Abc_NtkPoNum(pNtk) )
            {
                assert( Abc_ObjIsPo(pObj) );
                if ( !Abc_ObjIsPo(pObj) )
                    Abc_Print( 1, "Abc_NtkToDar(): Temporary bug: The PO ordering is wrong!\n" );
            }
            else
                assert( Abc_ObjIsBi(pObj) );
        // print warning about initial values
        nDontCares = 0;
        Abc_NtkForEachLatch( pNtk, pObj, i )
            if ( Abc_LatchIsInitDc(pObj) )
            {
                Abc_LatchSetInit0(pObj);
                nDontCares++;
            }
        if ( nDontCares )
        {
            Abc_Print( 1, "Warning: %d registers in this network have don't-care init values.\n", nDontCares );
            Abc_Print( 1, "The don't-care are assumed to be 0. The result may not verify.\n" );
            Abc_Print( 1, "Use command \"print_latch\" to see the init values of registers.\n" );
            Abc_Print( 1, "Use command \"zero\" to convert or \"init\" to change the values.\n" );
        }
    }
    // create the manager
    pMan = Aig_ManStart( Abc_NtkNodeNum(pNtk) + 100 );
    pMan->fCatchExor = fExors;
    pMan->nConstrs = pNtk->nConstrs;
    pMan->nBarBufs = pNtk->nBarBufs;
    pMan->pName = Extra_UtilStrsav( pNtk->pName );
    pMan->pSpec = Extra_UtilStrsav( pNtk->pSpec );
    // transfer the pointers to the basic nodes
    Abc_AigConst1(pNtk)->pCopy = (Abc_Obj_t *)Aig_ManConst1(pMan);
    Abc_NtkForEachCi( pNtk, pObj, i )
    {
        pObj->pCopy = (Abc_Obj_t *)Aig_ObjCreateCi(pMan);
        // initialize logic level of the CIs
        ((Aig_Obj_t *)pObj->pCopy)->Level = pObj->Level;
    }

    // complement the 1-values registers
    if ( fRegisters ) {
        Abc_NtkForEachLatch( pNtk, pObj, i )
            if ( Abc_LatchIsInit1(pObj) )
                Abc_ObjFanout0(pObj)->pCopy = Abc_ObjNot(Abc_ObjFanout0(pObj)->pCopy);
    }
    // perform the conversion of the internal nodes (assumes DFS ordering)
//    pMan->fAddStrash = 1;
    vNodes = Abc_NtkDfs( pNtk, 0 );
    Vec_PtrForEachEntry( Abc_Obj_t *, vNodes, pObj, i )
//    Abc_NtkForEachNode( pNtk, pObj, i )
    {
        pObj->pCopy = (Abc_Obj_t *)Aig_And( pMan, (Aig_Obj_t *)Abc_ObjChild0Copy(pObj), (Aig_Obj_t *)Abc_ObjChild1Copy(pObj) );
//        Abc_Print( 1, "%d->%d ", pObj->Id, ((Aig_Obj_t *)pObj->pCopy)->Id );
    }
    Vec_PtrFree( vNodes );
    pMan->fAddStrash = 0;
    // create the POs
    Abc_NtkForEachCo( pNtk, pObj, i )
        Aig_ObjCreateCo( pMan, (Aig_Obj_t *)Abc_ObjChild0Copy(pObj) );
    // complement the 1-valued registers
    Aig_ManSetRegNum( pMan, Abc_NtkLatchNum(pNtk) );
    if ( fRegisters )
        Aig_ManForEachLiSeq( pMan, pObjNew, i )
            if ( Abc_LatchIsInit1(Abc_ObjFanout0(Abc_NtkCo(pNtk,i))) )
                pObjNew->pFanin0 = Aig_Not(pObjNew->pFanin0);
    // remove dangling nodes
    nNodes = (Abc_NtkGetChoiceNum(pNtk) == 0)? Aig_ManCleanup( pMan ) : 0;
    if ( !fExors && nNodes )
        Abc_Print( 1, "Abc_NtkToDar(): Unexpected %d dangling nodes when converting to AIG!\n", nNodes );
//Aig_ManDumpVerilog( pMan, "test.v" );
    // save the number of registers
    if ( fRegisters )
    {
        Aig_ManSetRegNum( pMan, Abc_NtkLatchNum(pNtk) );
        pMan->vFlopNums = Vec_IntStartNatural( pMan->nRegs );
//        pMan->vFlopNums = NULL;
//        pMan->vOnehots = Abc_NtkConverLatchNamesIntoNumbers( pNtk );
        if ( pNtk->vOnehots )
            pMan->vOnehots = (Vec_Ptr_t *)Vec_VecDupInt( (Vec_Vec_t *)pNtk->vOnehots );
    }
    if ( !Aig_ManCheck( pMan ) )
    {
        Abc_Print( 1, "Abc_NtkToDar: AIG check has failed.\n" );
        Aig_ManStop( pMan );
        return NULL;
    }
    return pMan;
}





int Lsv_NtkPrintPounate(Abc_Ntk_t* pNtk) {
  //vector<char*> pNtk_PiName;
  vector<string> pNtk_PiName;
  vector<char*> pNtk_PiNameC;
  vector<int> pNtk_PiId;

  Abc_Obj_t* pObjTemp;
  Aig_Obj_t * pAigObjTemp;
  int m;
  //printf("pNtk pi :");
  Abc_NtkForEachPi(pNtk, pObjTemp, m){
    //printf("(%s, %d) ", Abc_ObjName(pObjTemp), Abc_ObjId(pObjTemp));
    //string s()/////////////
    //pNtk_PiName.push_back(string s(Abc_ObjName(pObjTemp)));
    string s(Abc_ObjName(pObjTemp));
    pNtk_PiName.push_back(s);
    pNtk_PiNameC.push_back(Abc_ObjName(pObjTemp));
    pNtk_PiId.push_back(Abc_ObjId(pObjTemp));
  }
  //printf("\n");
  
  /*printf("pNtk po :");
  Abc_NtkForEachPo(pNtk, pObjTemp, m){
    printf("(%s, %d) ", Abc_ObjName(pObjTemp), Abc_ObjId(pObjTemp));
    //pNtk_PiName.push_back(Abc_ObjName(pObjTemp));
    //pNtk_PiId.push_back(Abc_ObjId(pObjTemp));
  }
  printf("\n");
  */
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachPo(pNtk, pObj, i) {
    
    //vector<char*> pNtkRes_PiName;
    vector<string> pNtkRes_PiName;
    vector<int> pNtkRes_PiId, pManRes_PiId, pCnfRes_PiId;
    char * pO_Name = Abc_ObjName(pObj);
    int pO_Id = Abc_ObjId(pObj);
    //printf("The Cone of po is (%s, %d) \n", pO_Name, Abc_ObjId(pObj));
    int pNtkRes_PoId = pO_Id, pManRes_PoId = pO_Id, pCnfRes_PoId = -1;

    Abc_Ntk_t  * pNtkRes;
    Aig_Man_t * pManRes;
    Cnf_Dat_t * pCnfRes;
    Cnf_Dat_t * pCnfRes2;

    pNtkRes = Abc_NtkCreateCone( pNtk, Abc_ObjFanin0(pObj), Abc_ObjName(pObj), 0);
    if (pObj && Abc_ObjFaninC0(pObj)) {
      Abc_NtkPo(pNtkRes, 0)->fCompl0 ^= 1;
    }
    int piNum = Abc_NtkPiNum(pNtkRes);
    // get the new network
    pManRes = Abc_NtkToDar(pNtkRes, 0, 0);
    pCnfRes = Cnf_Derive(pManRes, 1);   
    pCnfRes2 = Cnf_Derive(pManRes, 1);
    Cnf_DataLift( pCnfRes2, pCnfRes->nVars );

    
    
    //printf("pNtkRes pi :");
    Abc_NtkForEachPi(pNtkRes, pObjTemp, m){
      //printf("(%s, %d) ", Abc_ObjName(pObjTemp), Abc_ObjId(pObjTemp));
      string s(Abc_ObjName(pObjTemp));
      pNtkRes_PiName.push_back(s);
      pNtkRes_PiId.push_back(Abc_ObjId(pObjTemp));
    }
    //printf("\n");

    /*printf("pNtkRes po :");
    Abc_NtkForEachPo(pNtkRes, pObjTemp, m){
      printf("(%s, %d) ", Abc_ObjName(pObjTemp), Abc_ObjId(pObjTemp));
      pNtkRes_PoId = Abc_ObjId(pObjTemp);
    }
    printf("\n");*/

    //printf("pManRes pi :");
    Aig_ManForEachCi(pManRes, pAigObjTemp, m) {
      //printf("(%s, %d) ",  Abc_ObjName(Abc_NtkObj(pNtkRes, pAigObjTemp->Id)), pAigObjTemp->Id);
      pManRes_PiId.push_back(pAigObjTemp->Id);
    }
    //printf("\n");

    /*printf("pManRes po :");
    Aig_ManForEachCo(pManRes, pAigObjTemp, m) {
      printf("(%s, %d) ",  Abc_ObjName(Abc_NtkObj(pNtkRes, pAigObjTemp->Id)), pAigObjTemp->Id);
      //pManRes_PoId = pAigObjTemp->Id;
    }
    printf("\n");*/
    
    //printf("pCnfRes \n");
    //Cnf_DataPrint(  pCnfRes, 1 );
    //Cnf_DataPrint(  pCnfRes2, 1 );
    
    
    //printf("pCnfRes->nClauses = %d \n", pCnfRes->nClauses);
    //printf("pCnfRes->nVars = %d \n", pCnfRes->nVars);

    // record pi Id in Cnf
    // record po Id in Cnf
    
    //pCnfRes_PiId = pManRes_PiId;
    for (int j = 0; j< piNum; j++) {
      pCnfRes_PiId.push_back(pCnfRes->pVarNums[pManRes_PiId[j]]);
      
    }
    //pCnfRes_PoId = pCnfRes->pVarNums[pManRes_PoId];
    Aig_ManForEachCo(pCnfRes->pMan, pAigObjTemp, m) {
      //printf("(%s, %d) ",  Abc_ObjName(Abc_NtkObj(pNtkRes, pAigObjTemp->Id)), pAigObjTemp->Id);
      //pManRes_PoId = pAigObjTemp->Id;
      pCnfRes_PoId = pCnfRes->pVarNums[pAigObjTemp->Id];
    }

    /*printf("(pManRes_PiId, pCnfRes_PiId) ");
    for (int j = 0; j < piNum; j++) {
      printf("(%d, %d) ", pManRes_PiId[j], pCnfRes_PiId[j]);
    }
    printf("\n");
    printf("(pManRes_PoId, pCnfRes_PoId) ");
    printf("(%d, %d) \n", pManRes_PoId, pCnfRes_PoId);*/
   
 
    int New_nClauses = 2 * piNum + 2;
    int ** New_pClauses = new int * [2 * piNum + 2 +1];
    New_pClauses[0] = new int [2 * piNum * 3 + 2 * 1];
    for (int j = 1; j <= 2 * piNum; j++){
      New_pClauses[j] = New_pClauses[j-1] + 3;
    }
    for (int j= 1; j<= 2; j++) {
      New_pClauses[(2* piNum) + j] = New_pClauses[(2 * piNum) + j-1] + 1;
    }
    
    for (int j=0; j< piNum; j++) {
      int new_Var = pCnfRes->nVars * 2 + j + 1;
      New_pClauses[2 * j][0] = toLitCond(new_Var, 0);
      New_pClauses[2 * j][1] = toLitCond(pCnfRes_PiId[j], 0);
      New_pClauses[2 * j][2] = toLitCond(pCnfRes_PiId[j] + pCnfRes->nVars, 1);

      New_pClauses[2 * j + 1][0] = toLitCond(new_Var, 0);
      New_pClauses[2 * j + 1][1] = toLitCond(pCnfRes_PiId[j], 1);
      New_pClauses[2 * j + 1][2] = toLitCond(pCnfRes_PiId[j] + pCnfRes->nVars, 0);
    }

    New_pClauses[2 * piNum][0] =  toLitCond(pCnfRes_PoId, 0);
    New_pClauses[2 * piNum + 1][0] = toLitCond(pCnfRes_PoId + pCnfRes->nVars, 1);
    
    
    
    /*printf("New_pClauses \n");
    for ( m = 0; m < New_nClauses; m++) {
      for (int *pLit = New_pClauses[m], *pStop = New_pClauses[m+1]; pLit < pStop; pLit ++) {
        if ( (*pLit) & 1) {
          printf("-");
        }
        printf("%d ", (*pLit) >> 1);
      }
      printf("\n");
    }*/

    // add clause to sat_solver
    // start the solver
    sat_solver * pSat;
    int pSat_UNSATIFIABLE = 0;
    pSat = sat_solver_new();
    sat_solver_setnvars( pSat,  pCnfRes->nVars * 2 + piNum + 1);

    //add cluase pCnfRes to sat solver
    for (int j = 0; j < pCnfRes->nClauses; j++ )
    {
        if ( !sat_solver_addclause( pSat, pCnfRes->pClauses[j], pCnfRes->pClauses[j+1] ) )
        {
            /*printf("Adding clause pCnfRes to sat solver Failed. \n");
            delete [] New_pClauses[0];
            delete [] New_pClauses;
            Cnf_DataFree( pCnfRes );
            Cnf_DataFree( pCnfRes2 );
            sat_solver_delete( pSat );
            return 1;*/
            pSat_UNSATIFIABLE = 1;
        }
    }
    //add clause pCnfRes2 to sat solver
    for (int j = 0; j < pCnfRes2->nClauses; j++ )
    {
        if ( !sat_solver_addclause( pSat, pCnfRes2->pClauses[j], pCnfRes2->pClauses[j+1] ) )
        {
            /*printf("Adding clause pCnfRes2 to sat solver Failed. \n");
            delete [] New_pClauses[0];
            delete [] New_pClauses;
            Cnf_DataFree( pCnfRes );
            Cnf_DataFree( pCnfRes2 );
            sat_solver_delete( pSat );
            return 1;*/
            pSat_UNSATIFIABLE = 1;
        }
    }
    // add clause New_pClauses to sat solver
    for (int j = 0; j < New_nClauses; j++ )
    {
        if ( !sat_solver_addclause( pSat, New_pClauses[j], New_pClauses[j+1] ) )
        {
            /*printf("Adding clause New_nClauses to sat solver Failed. \n");
            Cnf_DataPrint(  pCnfRes, 1 );
            Cnf_DataPrint(  pCnfRes2, 1 );
            for ( m = j; m < j+1; m++) {
              for (int *pLit = New_pClauses[m], *pStop = New_pClauses[m+1]; pLit < pStop; pLit ++) {
                if ( (*pLit) & 1) {
                  printf("-");
                }
                printf("%d ", (*pLit) >> 1);
              }
              printf("\n");
            }*/

            /*delete [] New_pClauses[0];
            delete [] New_pClauses;
            Cnf_DataFree( pCnfRes );
            Cnf_DataFree( pCnfRes2 );
            sat_solver_delete( pSat );
            return 1;*/
            pSat_UNSATIFIABLE = 1;
        }
    }

    // record which is positive unate or negative unate
    // original -1 (both positive unate and negative unate), negative unate 0, positive unate 1, binate 2
    vector<int> Arr(piNum, 2);

    if ( ! pSat_UNSATIFIABLE) {
      int status;
      int RetValue;
      status = sat_solver_simplify( pSat );

      // solve incremental SAT problems
      // Positive Unate
      //printf("positive unate \n");
      int * Lits = new int [2 + piNum];
      //Lits[0] = toLitCond( pCnfOn->pVarNums[pObj->Id], 0 );
      for (int j = 0; j< piNum; j++) {
        
        //positive unate
        Lits[0] = toLitCond(pCnfRes_PiId[j], 1);
        Lits[1] = toLitCond(pCnfRes_PiId[j] + pCnfRes->nVars, 0);
        //negtive unate
        /*Lits[0] = toLitCond(pCnfRes_PiId[j], 0);
        Lits[1] = toLitCond(pCnfRes_PiId[j] + pCnfRes->nVars, 1);*/

        for (int k = 0; k < piNum; k++ ){
          if (k < j) {
            Lits[2 + k] = toLitCond(k + pCnfRes->nVars * 2 + 1, 1);
          }else if (k > j) {
            Lits[1 + k] = toLitCond(k + pCnfRes->nVars * 2 + 1, 1);
          }
        }
        /*printf("assumption: ");
        for (int k = 0; k < piNum+1; k++) {
          if (Lits[k] & 1)
            printf("-");
          printf("%d ", Lits[k] >> 1);
        }
        printf("\n");*/
        
        
        status = sat_solver_solve( pSat, Lits, Lits+(1+piNum), (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
        
        /*if ( status == l_Undef )
          {
              printf( "The problem timed out.\n" );
              RetValue = -1;
          }
          else if ( status == l_True )
          {
              printf( "The problem is SATISFIABLE.\n" );
              RetValue = 0;
          }
          else if ( status == l_False )
          {
              Arr[j] = 1;
              printf( "The problem is UNSATISFIABLE.\n" );
              RetValue = 1;
          }*/
        if (status == l_False) {
          Arr[j] = 1;
          //printf( "The problem is UNSATISFIABLE.\n" );
          //RetValue = 1;
        }
          
      }

      // Negtive Unate
      //printf("negtive unate \n");
      
      //Lits[0] = toLitCond( pCnfOn->pVarNums[pObj->Id], 0 );
      for (int j = 0; j< piNum; j++) {
        
        //positive unate
        //Lits[0] = toLitCond(pCnfRes_PiId[j], 1);
        //Lits[1] = toLitCond(pCnfRes_PiId[j] + pCnfRes->nVars, 0);
        //negtive unate
        Lits[0] = toLitCond(pCnfRes_PiId[j], 0);
        Lits[1] = toLitCond(pCnfRes_PiId[j] + pCnfRes->nVars, 1);

        for (int k = 0; k < piNum; k++ ){
          if (k < j) {
            Lits[2 + k] = toLitCond(k + pCnfRes->nVars * 2 + 1, 1);
          }else if (k > j) {
            Lits[1 + k] = toLitCond(k + pCnfRes->nVars * 2 + 1, 1);
          }
        }
        /*printf("assumption: ");
        for (int k = 0; k < piNum+1; k++) {
          if (Lits[k] & 1)
            printf("-");
          printf("%d ", Lits[k] >> 1);
        }
        printf("\n");*/
        
        
        status = sat_solver_solve( pSat, Lits, Lits+(1+piNum), (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
        
        /*if ( status == l_Undef )
          {
              printf( "The problem timed out.\n" );
              RetValue = -1;
          }
          else if ( status == l_True )
          {
              printf( "The problem is SATISFIABLE.\n" );
              RetValue = 0;
          }
          else if ( status == l_False )
          {
              if (Arr[j] == 2) {
                Arr[j] = 0;
              }else{
                Arr[j] = -1;
              }
              printf( "The problem is UNSATISFIABLE.\n" );
              RetValue = 1;
          }*/
          
          if ( status == l_False )
          {
              if (Arr[j] == 2) {
                Arr[j] = 0;
              }else{
                Arr[j] = -1;
              }
              //printf( "The problem is UNSATISFIABLE.\n" );
              //RetValue = 1;
          }
      }
    
      delete [] Lits;
    }
    else
    {
      for (int j = 0; j<piNum; j++) {
        Arr[j] = -1;
      }
    }
    

    // check which is postive unate, negative unate, binate
    // original -1 (both positive unate and negative unate), negative unate 0, positive unate 1, binate 2
    // vector<int> Arr(piNum, 2);
    /*printf("(pManRes_PiId, pCnfRes_PiId, unate) ");
    for (int j = 0; j < piNum; j++) {
      printf("(%d, %d, %d) ", pManRes_PiId[j], pCnfRes_PiId[j], Arr[j]);
    }
    printf("\n");
    printf("Arr :\n");
    for(int j=0; j< piNum; j++) {
      printf("%d ", Arr[j]);
    }
    printf("\n");
    printf("pNtk_PiName ");
    //vector<char*> pNtk_PiName;
    //vector<int> pNtk_PiId;
    for (int j = 0; j< pNtk_PiName.size(); j++) {
      printf("(%s) ", pNtk_PiName[j]);
    }
    printf("\n");
    printf("pNtkRes_PiName ");
    for (int j = 0; j< pNtkRes_PiName.size(); j++) {
       printf("(%s) ", pNtkRes_PiName[j]);
    }
    printf("\n");*/

    /*vector<string> pNtk_PiNameStr;
    for (int j=0; j< pNtk_PiName.size(); j++) {
      string s(pNtk_PiName[j]);
      pNtk_PiNameStr.push_back(s);
    }
    vector<string> pNtkRes_PiNameStr;
    for (int j=0; j<pNtkRes_PiName.size(); j++) {
      string s(pNtkRes_PiName[j]);
      pNtkRes_PiNameStr.push_back(s);
    }*/
    /*printf("pNtk_PiNameStr ");
    for (int j = 0; j< pNtk_PiNameStr.size(); j++) {
      //printf("(%s) ", pNtk_PiNameStr[j]);
      cout<<"("<<pNtk_PiNameStr[j]<<") ";
    }
    printf("\n");
    printf("pNtkRes_PiNameStr ");
    for (int j = 0; j< pNtkRes_PiNameStr.size(); j++) {
       //printf("(%s) ", pNtkRes_PiNameStr[j]);
       cout<<"("<<pNtkRes_PiNameStr[j]<<") ";
    }
    printf("\n");*/
    
    vector<char *> nArr, pArr, bArr;
    for (int j = 0; j < pNtk_PiName.size(); j++) {
    //for (int j = 0; j < pNtk_PiName.size(); j++) {
      //vector<char *>::iterator it;
      //it = find(pNtkRes_PiName.begin(), pNtkRes_PiName.end(), pNtk_PiName[j]);
      //if (it != pNtkRes_PiName.end()) {
      vector<string>::iterator it;
      it = find(pNtkRes_PiName.begin(), pNtkRes_PiName.end(), pNtk_PiName[j]);

      //const char *p = const_cast<char*> (pNtk_PiName[j].c_str());
      if (it != pNtkRes_PiName.end()) {
        int index = it - pNtkRes_PiName.begin();
        
        //printf("index = %d \n", index);
        if (Arr[index] == 2) {
          bArr.push_back(pNtk_PiNameC[j]);
          
        }else if (Arr[index] == 1 ){
          pArr.push_back(pNtk_PiNameC[j]);
          
        }else if (Arr[index] == 0) {
          nArr.push_back(pNtk_PiNameC[j]);
          
        }else{
          pArr.push_back(pNtk_PiNameC[j]);
          nArr.push_back(pNtk_PiNameC[j]);
          
        }

      }else{
        pArr.push_back(pNtk_PiNameC[j]);
        nArr.push_back(pNtk_PiNameC[j]);
      }
    }

    if (!pArr.empty() || !nArr.empty() || !bArr.empty()) {
      printf("node %s:\n", Abc_ObjName(pObj));
      if (pArr.size() != 0) {
        printf("+unate inputs:");
        for (int k=0; k<pArr.size(); ++k) {
          if (k==0) {
            printf(" ");
          }else{
            printf(",");
          }
          printf("%s", pArr[k]);
        }
        printf("\n");
      }
      
      if (nArr.size() != 0) {
        printf("-unate inputs:");
        for (int k=0; k<nArr.size(); ++k) {
          if (k==0) {
            printf(" ");
          }else{
            printf(",");
          }
          printf("%s", nArr[k]);
        }
        printf("\n");
      }
      if (bArr.size() != 0) {
        printf("binate inputs:");
        for (int k=0; k<bArr.size(); ++k) {
          if (k==0) {
            printf(" ");
          }else{
            printf(",");
          }
          printf("%s", bArr[k]);
        }
        printf("\n");
      }
    }
    //delete [] Lits;
    delete [] New_pClauses[0];
    delete [] New_pClauses;
    Cnf_DataFree( pCnfRes );
    Cnf_DataFree( pCnfRes2 );
    sat_solver_delete( pSat );

  }

  return 0;
}

int Lsv_CommandPrintPounate(Abc_Frame_t* pAbc, int argc, char** argv) {
  //printf("Lsv_CommandPrintPounate\n");
  
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
  // make sure the networks are strashed
  if ( !Abc_NtkIsStrash(pNtk) )
  {
    Abc_Print(-1, "Not Aig graph.\n");
    return 1;
  }

  /*if ( !Abc_NtkIsStrash(pNtk) )
  {
    Abc_Ntk_t * pNtkTemp; 
    pNtkTemp = Abc_NtkStrash( pNtk, 0, 1, 0 );
    Abc_NtkDelete(pNtk);
    pNtk = pNtkTemp;   
  }*/
  /*Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachPo(pNtk, pObj, i) {
    printf("(%s) ", Abc_ObjName(pObj));
  }
  printf("\n");*/


  if ( Lsv_NtkPrintPounate(pNtk) ) {
    printf("ERROR \n");
  }

  return 0;

usage:
  Abc_Print(-2, "usage: lsv_print_pounate [-h]\n");
  Abc_Print(-2, "\t        print the unate information for each primary output in terms of all primary inputs\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}



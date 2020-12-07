#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "base/main/mainInt.h"
#include "sat/cnf/cnf.h"
#include <vector>
#include <map>
#include <algorithm>

#include <iostream>
#include <fstream>

extern "C" Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
extern "C" Cnf_Dat_t * Cnf_Derive( Aig_Man_t * pAig, int nOutputs );

bool comp_pa2(const std::pair<int,int> &a,const std::pair<int,int> &b)
{
  return a.first<b.first;
}


static int Lsv_CommandPrintPounate(Abc_Frame_t* pAbc, int argc, char** argv);

void init_pa2(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_pounate", Lsv_CommandPrintPounate, 0);
}

void destroy_pa2(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer_pa2 = {init_pa2, destroy_pa2};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer_pa2); }
} lsvPackageRegistrationManager_pa2;

int Lsv_CommandPrintPounate(Abc_Frame_t* pAbc, int argc, char** argv)
{
  //std::fstream ofs;
	//ofs.open("output.txt",std::ios::out);
  
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  Abc_Obj_t* pObj_PO;
  //Abc_Obj_t* pObj_PI_test;
  int i;
  // Abc_NtkForEachPi(pNtk, pObj_PI_test, i) {
  //     printf("  PI-%d: Id = %d, name = %s\n", i, Abc_ObjId(pObj_PI_test),Abc_ObjName(pObj_PI_test));
  // }
  Abc_NtkForEachPo(pNtk, pObj_PO, i) {
    Abc_Ntk_t* pNtk_PO = Abc_NtkCreateCone( pNtk, Abc_ObjFanin0(pObj_PO), Abc_ObjName(pObj_PO), 1 );  //F

    //check PO negative
    if(Abc_ObjFaninC0(pObj_PO)){
      Abc_NtkPo(pNtk_PO, 0)->fCompl0  ^= 1; //XOR
    }

    //Sorting
    std::vector<std::pair<int,int> > faninV_sort; //(id,fanin_order)
    std::vector<std::pair<int,char*> > faninV; //(count,name)
    Abc_Obj_t* pObj_PI;
    int j;
    Abc_NtkForEachPi(pNtk_PO, pObj_PI, j) {
      //printf("  PI-%d: Id = %d, name = %s\n", j, Abc_ObjId(pObj_PI),Abc_ObjName(pObj_PI));
      faninV.push_back(std::make_pair<int,char*>(-1,Abc_ObjName(pObj_PI)));
      faninV_sort.push_back(std::make_pair<int,int>((int)Abc_ObjId(pObj_PI),(int)j));
    }
    std::sort(faninV_sort.begin(),faninV_sort.end(),comp_pa2);


    Aig_Man_t * pMan;
    Cnf_Dat_t * pCnf;
    Cnf_Dat_t * pCnfp;

    // obtain AIG circuit
    pMan = Abc_NtkToDar( pNtk_PO, 0, 0 );
    Aig_Obj_t* aigObj_PO = Aig_ManCo(pMan,0);
    int PO_id = Aig_ObjId(aigObj_PO);

    // Index mapping
    std::vector<int> AigToNtkIndexMapping; // use Aig_id to get the index in faninV
    Aig_Obj_t* aigObj_PI;
    Aig_ManForEachCi(pMan,aigObj_PI,j){
      int k;
      Abc_NtkForEachPi(pNtk_PO, pObj_PI, k) {
        if(Abc_ObjId(pObj_PI) == Aig_ObjId(aigObj_PI)){
          AigToNtkIndexMapping.push_back(k);
        }
      }
    }


    // derive CNF
    pCnf = Cnf_Derive( pMan, Aig_ManCoNum(pMan) );
    pCnfp = Cnf_DataDup(pCnf);
    Cnf_DataLift(pCnfp,pCnf->nVars);
    //Initalize SAT
    sat_solver * pSat;
    // pSat = sat_solver_new();
    // sat_solver_setnvars(pSat, pCnf->nVars*2   + Abc_NtkPiNum(pNtk_PO));
    pSat = (sat_solver *)Cnf_DataWriteIntoSolver( pCnf, 1, 0 );
    //Add F and F'
    // for ( j = 0; j < pCnf->nClauses; j++ )
    // {
        
    //     lit List[pCnf->pClauses[j+1]-pCnf->pClauses[j]];
    //     lit* k;
    //     int idx = 0;
    //     for ( k = pCnf->pClauses[j]; k < pCnf->pClauses[j+1]; k++ ){
    //       List[idx] = (*k) + shift;
    //       idx++;
    //     } 
    //     if ( !sat_solver_addclause( pSat, pCnf->pClauses[j], pCnf->pClauses[j+1] ) )
    //     {
    //         printf("error in adding clause to SAT\n");
    //         continue;
    //     }
    //     if ( !sat_solver_addclause( pSat, List, List+idx ) )
    //     {
    //         printf("error in adding clause to SAT\n");
    //         continue;
    //     }
    // }
    for ( j = 0; j < pCnfp->nClauses; j++ )
    {
        
        if ( !sat_solver_addclause( pSat, pCnf->pClauses[j], pCnf->pClauses[j+1] ) )
        {
            printf("error in adding clause to SAT\n");
            continue;
        }
    }
    //Add equivalent constraint (Alpha_y' + (y1=y2)) = (y1' + y2 + Alpha_y')(y1 + y2' + Alpha_y')
    //Create the alpha variable for each PI
    //sat_solver_setnvars(pSat,sat_solver_nvars(pSat) + Aig_ManCiNum(pMan));
    std::map<int,int> Alpha_mapping;
    //int Alpha_mapping[Abc_NtkObjNum(pNtk_PO)];
    //int temp = 0;;
    //Aig_Obj_t* aigObj_PI;
    Aig_ManForEachCi(pMan,aigObj_PI,j){
      int alpha = pCnf->nVars*2+j;
      Alpha_mapping.insert(std::pair<int,int>(Aig_ObjId(aigObj_PI),alpha));
      sat_solver_add_buffer_enable(pSat,pCnf->pVarNums[Aig_ObjId(aigObj_PI)],pCnfp->pVarNums[Aig_ObjId(aigObj_PI)],alpha,0);
    }

    // Abc_NtkForEachPi(pNtk_PO, pObj_PI, j) {
    //   //Alpha_mapping[Abc_ObjId(pObj_PI)] = pCnf->nVars*2 + temp+1;
    //   //temp++;
    // }
    // Abc_NtkForEachPi(pNtk_PO, pObj_PI, j) {
    //   int alpha;
    //   int var1;
    //   int var2;
    //   var1 = pCnf->pVarNums[Abc_ObjId(pObj_PI)];
    //   var2 = var1 + pCnf->nVars;
    //   alpha = Alpha_mapping[Abc_ObjId(pObj_PI)];
    //   lit Lits[3];
    //   //(y1' + y2 + Alpha_y')
    //   Lits[0] = toLitCond( var1, 0 );
    //   Lits[1] = toLitCond( var2, 1 );
    //   Lits[2] = toLitCond( alpha, 0 );
    //   if(!sat_solver_addclause( pSat, Lits, Lits + 3 )){
    //     printf("error in adding clause to SAT\n");
    //   }
    //   //(y1 + y2' + Alpha_y')
    //   Lits[0] = toLitCond( var1, 1 );
    //   Lits[1] = toLitCond( var2, 0 );
    //   Lits[2] = toLitCond( alpha, 0 );
    //   if(!sat_solver_addclause( pSat, Lits, Lits + 3 )){
    //     printf("error in adding clause to SAT\n");
    //   }
    // }


    //Add PO constraint
    lit PO_constraint[1];
    PO_constraint[0] = toLitCond(pCnf->pVarNums[PO_id],0);
    sat_solver_addclause(pSat,PO_constraint,PO_constraint+1);  // (F)
    PO_constraint[0] = toLitCond(pCnfp->pVarNums[PO_id],1);
    sat_solver_addclause(pSat,PO_constraint,PO_constraint+1);  // (~F)


    int status = sat_solver_simplify(pSat);
    if ( status == 0 )
    {
        printf("error in sat_solver_simplify\n");
    }
    

    lit Assumption[2+Aig_ManCiNum(pMan)]; // pos-cofactor, neg-cofactor, all alpha
    //Solve positive unate
    Aig_ManForEachCi(pMan,aigObj_PI,j){
      //cofactor
      Assumption[0] = toLitCond(pCnf->pVarNums[Aig_ObjId(aigObj_PI)],1);
      Assumption[1] = toLitCond(pCnfp->pVarNums[Aig_ObjId(aigObj_PI)],0);
      //alpha
      int k;
      Aig_Obj_t* aigObj_PI_temp;
      Aig_ManForEachCi(pMan,aigObj_PI_temp,k){
        if(Aig_ObjId(aigObj_PI_temp) == Aig_ObjId(aigObj_PI)){
          Assumption[2+k] = toLitCond(Alpha_mapping.at(Aig_ObjId(aigObj_PI_temp)),1);
        }
        else{
          Assumption[2+k] = toLitCond(Alpha_mapping.at(Aig_ObjId(aigObj_PI_temp)),0);
        }
      }
      //solve
      status = sat_solver_solve( pSat, Assumption, Assumption+2+Aig_ManCiNum(pMan), (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
      if ( status == l_Undef )
      {
          printf( "The problem timed out.\n" );
      }
      else if ( status == l_True )
      {
  //        printf( "The problem is SATISFIABLE.\n" );
          
      }
      else if ( status == l_False )
      {
  //        printf( "The problem is UNSATISFIABLE.\n" );
            faninV[ AigToNtkIndexMapping[j] ].first = 1;
          
      }
      else
          assert( 0 );
    }
    //Solve negative unate
    Aig_ManForEachCi(pMan,aigObj_PI,j){
      //cofactor
      Assumption[0] = toLitCond(pCnf->pVarNums[Aig_ObjId(aigObj_PI)],0);
      Assumption[1] = toLitCond(pCnfp->pVarNums[Aig_ObjId(aigObj_PI)],1);
      //alpha
      int k;
      Aig_Obj_t* aigObj_PI_temp;
      Aig_ManForEachCi(pMan,aigObj_PI_temp,k){
        if(Aig_ObjId(aigObj_PI_temp) == Aig_ObjId(aigObj_PI)){
          Assumption[2+k] = toLitCond(Alpha_mapping.at(Aig_ObjId(aigObj_PI_temp)),1);
        }
        else{
          Assumption[2+k] = toLitCond(Alpha_mapping.at(Aig_ObjId(aigObj_PI_temp)),0);
        }
      }
      //solve
      status = sat_solver_solve( pSat, Assumption, Assumption+2+Aig_ManCiNum(pMan), (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
      if ( status == l_Undef )
      {
          printf( "The problem timed out.\n" );
      }
      else if ( status == l_True )
      {
  //        printf( "The problem is SATISFIABLE.\n" );
          
      }
      else if ( status == l_False )
      {
  //        printf( "The problem is UNSATISFIABLE.\n" );
            if(faninV[AigToNtkIndexMapping[j]].first == 1)faninV[AigToNtkIndexMapping[j]].first = 3; // both pos and neg unate
            else faninV[AigToNtkIndexMapping[j]].first = 2;
          
      }
      else
          assert( 0 );
    }

  
  //print result
  printf("node %s:\n",Abc_ObjName(pObj_PO));
  int count = 0;
  //printf("+unate inputs: ");
  for(int i = 0; i < faninV_sort.size();i++){
    std::pair<int,char*> p = faninV[faninV_sort[i].second];
    if((p.first == 1) || (p.first == 3)){
      if(count == 0){
        printf("+unate inputs: ");
        printf("%s",p.second);
      }
      else {
        printf(",%s",p.second);
      }
      count++;
    }
  }
  if(count != 0){
    printf("\n");
    count = 0;
  }
  //printf("-unate inputs: ");
  for(int i = 0; i < faninV_sort.size();i++){
    std::pair<int,char*> p = faninV[faninV_sort[i].second];
    if((p.first == 2) || (p.first == 3)){
      if(count == 0){
        printf("-unate inputs: ");
        printf("%s",p.second);
      }
      else {
        printf(",%s",p.second);
      }
      count++;
    }
  }
  if(count != 0){
    printf("\n");
    count = 0;
  }
  //printf("binate inputs: ");
  for(int i = 0; i < faninV_sort.size();i++){
    std::pair<int,char*> p = faninV[faninV_sort[i].second];
    if(p.first == -1){
      if(count == 0){
        printf("binate inputs: ");
        printf("%s",p.second);
      }
      else {
        printf(",%s",p.second);
      }
      count++;
    }
  }
  if(count != 0){
    printf("\n");
    count = 0;
  }


  }
  return 0;
}

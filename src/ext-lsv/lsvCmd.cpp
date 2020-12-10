#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "sat/cnf/cnf.h"
#include <vector>
#include <algorithm> 
static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintSopUnate(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintPoUnate(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_sopunate", Lsv_CommandPrintSopUnate, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_pounate", Lsv_CommandPrintPoUnate, 0);
}



void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;


///// for Nodes

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

//// for SopUnate


int Lsv_sortCompare(Abc_Obj_t ** a, Abc_Obj_t ** b) {
  return Abc_ObjId(*a) > Abc_ObjId(*b);
}


void printUnate(const char * str, Vec_Ptr_t * vec) {
  Abc_Obj_t * pEntry;
  int i, sz = Vec_PtrSize(vec);

  if (sz == 0) ;
  else{
  printf("%s: ", str);
  Vec_PtrForEachEntry( Abc_Obj_t *, vec, pEntry, i )
    printf("%s%c", Abc_ObjName(pEntry), i != sz-1? ',':'\n');
    }
}



void Lsv_NtkPrintSopUnate(Abc_Ntk_t* pNtk) {
  Abc_Obj_t * pObj;
  int i, j;

  Abc_NtkForEachNode(pNtk, pObj, i) {
    char * pSop = (char *)pObj->pData;
    char * pCube;
    char val;
    int nFanins = Abc_ObjFaninNum(pObj);
    bool unateTable[nFanins][2] = {};
    Abc_SopForEachCube(pSop, nFanins, pCube) {
      bool isOnset = *(pCube + nFanins + 1) - '0';
      Abc_CubeForEachVar(pCube, val, j) {
        if (val == '-') continue;
        bool isOne = val - '0';
        unateTable[j][isOne == isOnset] = 1;
      }
    }
    
    Vec_Ptr_t * posUnateVec = Vec_PtrAlloc( nFanins );
    Vec_Ptr_t * negUnateVec = Vec_PtrAlloc( nFanins );
    Vec_Ptr_t * binateVec = Vec_PtrAlloc( nFanins );
    Abc_Obj_t * pFanin;
    Abc_ObjForEachFanin(pObj, pFanin, j) {
      if (unateTable[j][0] && unateTable[j][1]) 
        Vec_PtrPush( binateVec, pFanin );
      else {
        if (!unateTable[j][0]) Vec_PtrPush( posUnateVec, pFanin );
        if (!unateTable[j][1]) Vec_PtrPush( negUnateVec, pFanin );
      }
    }

    Vec_PtrSort( posUnateVec, (int (*)()) Lsv_sortCompare );
    Vec_PtrSort( negUnateVec, (int (*)()) Lsv_sortCompare );
    Vec_PtrSort( binateVec, (int (*)()) Lsv_sortCompare );
    
    
    int sz = Vec_PtrSize(posUnateVec)+Vec_PtrSize(negUnateVec)+Vec_PtrSize(binateVec);

    if (sz == 0) ;
    else {
    printf("node %s:\n", Abc_ObjName(pObj));
    printUnate( "+unate inputs", posUnateVec );
    printUnate( "-unate inputs", negUnateVec );
    printUnate( "binate inputs", binateVec );
}
    Vec_PtrFree( posUnateVec );
    Vec_PtrFree( negUnateVec );
    Vec_PtrFree( binateVec );
  }
}

bool Fanin_idxcmp (Abc_Obj_t i, Abc_Obj_t j) { return (i.Id < j.Id); }


int Lsv_CommandPrintSopUnate(Abc_Frame_t* pAbc, int argc, char** argv) {
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
  Lsv_NtkPrintSopUnate(pNtk);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_print_sopunate [-h]\n");
  Abc_Print(-2, "\t        prints the unate information for each node\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}





extern void sat_solver_delete(sat_solver* s);
extern void Cnf_DataFree(Cnf_Dat_t * p);
extern "C" Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pbc, int fExors, int fRegisters );

int Lsv_CommandPrintPoUnate(Abc_Frame_t* pAbc, int argc, char** argv) {
  
  Vec_Int_t * vLits;
  Aig_Obj_t * pObj,*pObj_In;
  Abc_Obj_t* afanin;
  int i,j,g;
  int statusP, statusN;
  int nObj_ID,pObj_ID;
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);



  
  Aig_Man_t* pMan = Abc_NtkToDar( pNtk,0 ,0);
  Cnf_Dat_t* pCnf = Cnf_Derive(pMan , Aig_ManCoNum(pMan));
  Cnf_Dat_t* nCnf = Cnf_DataDup(pCnf);
  std::vector<Abc_Obj_t> posUnateVec;
  std::vector<Abc_Obj_t> negUnateVec;
  std::vector<Abc_Obj_t> binateVec;

  Cnf_DataLift( nCnf, nCnf -> nVars );
  sat_solver * pSat = (sat_solver *)Cnf_DataWriteIntoSolver(pCnf,1,0);
  sat_solver_setnvars(pSat,  2 * pSat->size );

  for(i = 0; i < nCnf -> nClauses; i++){
    if (!sat_solver_addclause( pSat, nCnf->pClauses[i], nCnf->pClauses[i+1] ) )
      assert(0);
  }
  int satSize = pSat->size;
  //sat_solver_setnvars( pSat, nCnf -> nVars );
  sat_solver_setnvars(pSat,  pSat->size + Aig_ManCiNum(pCnf->pMan));

//enanle
Aig_ManForEachCi( pCnf->pMan, pObj_In, i ) {
    int pObj_In_Id = pCnf -> pVarNums[pObj_In -> Id];     // pos cofactor Id
    int nObj_In_Id = nCnf -> pVarNums[pObj_In -> Id];     // neg cofactor Id
    sat_solver_add_buffer_enable( pSat, pObj_In_Id, nObj_In_Id, satSize + i + 1, 0 );
}

// add one large OR clause
vLits = Vec_IntAlloc( pCnf->nVars);
Aig_ManForEachCo( pCnf->pMan, pObj, i) {               // for each PO of the network
 
    Abc_Obj_t* afanin; 

    std::vector<Abc_Obj_t> posUnateVec;
    std::vector<Abc_Obj_t> negUnateVec;           
    std::vector<Abc_Obj_t> binateVec;
    
    pObj_ID = pCnf->pVarNums[pObj->Id];
    nObj_ID = nCnf->pVarNums[pObj->Id];  
    
  Aig_ManForEachCi( pCnf->pMan, pObj_In, j ){
    int unateness = 0;  
    int pObj_In_Id = pCnf -> pVarNums[pObj_In -> Id];     // pos cofactor Id
    int nObj_In_Id = nCnf -> pVarNums[pObj_In -> Id];     // neg cofactor Id
    //pos
    Vec_IntPush( vLits, toLitCond(pObj_ID, 0) );
    Vec_IntPush( vLits, toLitCond(nObj_ID, 1) );
    

    for(g = 0; g < Aig_ManCiNum(pCnf->pMan); g++){
      if(j == g){
        Vec_IntPush( vLits, toLitCond(satSize + g +1, 1) );
      }
      else 
        Vec_IntPush( vLits, toLitCond(satSize + g +1, 0) );
    }
    Vec_IntPush( vLits, toLitCond(pObj_In_Id, 0));
    Vec_IntPush( vLits, toLitCond(nObj_In_Id, 1));


    statusP = sat_solver_solve( pSat, Vec_IntArray(vLits), Vec_IntArray(vLits) + Vec_IntSize(vLits), (ABC_INT64_T)50000, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
    if (statusP ==  l_True) {
            unateness = 1;
    }
    Vec_IntRemove(vLits,  toLitCond(pObj_ID, 0));                     // remove constraint Fx
    Vec_IntRemove(vLits,  toLitCond(nObj_ID, 1));                     // remove constraint F~x
    
    
    //neg
    Vec_IntPush( vLits, toLitCond(pObj_ID, 1) );
    Vec_IntPush( vLits, toLitCond(nObj_ID, 0) );
    
    statusN = sat_solver_solve( pSat, Vec_IntArray(vLits), Vec_IntArray(vLits) + Vec_IntSize(vLits), (ABC_INT64_T)50000, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
    if (statusN == l_True) {
            if (unateness == 0) {
                unateness = 2;
            }
            else if (unateness == 1) { 
                unateness = 3;
            }
        }
    afanin = Abc_NtkPi(pNtk, j);
    
    if (unateness == 0) {
          posUnateVec.push_back(*afanin);
          negUnateVec.push_back(*afanin);
        } else if (unateness == 1) {
            posUnateVec.push_back(*afanin);
        } else if (unateness == 2) {
            negUnateVec.push_back(*afanin);
        } else {
            binateVec.push_back(*afanin);
        }
    Vec_IntClear( vLits );
  }
  
  printf("node %s:\n", Abc_ObjName(Abc_NtkPo( pNtk,  i )));
  int sz = (posUnateVec.size())+(negUnateVec.size())+(binateVec.size());
  if (sz == 0) ;
  else {
    sz = (posUnateVec.size());
    if (sz ==0);
    else{
      std::sort(posUnateVec.begin(), posUnateVec.end(), Fanin_idxcmp); 
          printf("+unate inputs: ");
          for (int it = 0; it < posUnateVec.size(); ++it) {
              afanin = &posUnateVec[it];
              if (it == 0) printf("%s", Abc_ObjName(afanin));
              else printf(",%s", Abc_ObjName(afanin));
          }
          printf("\n");

    }

    sz = (negUnateVec.size());
    if(sz == 0);
    else{
      std::sort(negUnateVec.begin(), negUnateVec.end(), Fanin_idxcmp); 
      printf("-unate inputs: ");
      for (int it = 0; it < negUnateVec.size(); ++it) {
          afanin = &negUnateVec[it];
          if (it == 0) printf("%s", Abc_ObjName(afanin));
          else printf(",%s", Abc_ObjName(afanin));
      }
      printf("\n");
    }

    sz = (binateVec.size());
    if(sz == 0);
    else{
    std::sort(binateVec.begin(), binateVec.end(), Fanin_idxcmp); 
      printf("binate inputs: ");
      for (int it = 0; it < binateVec.size(); ++it) {
          afanin = &binateVec[it];
          if (it == 0) printf("%s", Abc_ObjName(afanin));
          else printf(",%s", Abc_ObjName(afanin));
      }
      printf("\n");


    }

   
  }
  
}
    sat_solver_delete(pSat);
  Cnf_DataFree(pCnf);
  Cnf_DataFree(nCnf);

  return 0;
}




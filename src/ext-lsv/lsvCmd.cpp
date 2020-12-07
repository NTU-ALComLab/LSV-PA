#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "sat/cnf/cnf.h"
#include "sat/bsat/satSolver2.h"
#include <vector>
#include <string>
#include <algorithm>
#include <iostream>

extern "C"
{
  Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
  //Abc_Ntk_t * Abc_NtkStrash( Abc_Ntk_t * pNtk, int fAllNodes, int fCleanup, int fRecord );
  //Abc_Ntk_t * Abc_NtkDarToCnf( Abc_Ntk_t * pNtk, char * pFileName, int fFastAlgo, int fChangePol, int fVerbose );
  //void * Cnf_DataWriteIntoSolver( Cnf_Dat_t * p, int nFrames, int fInit );
  //int    Cnf_DataWriteOrClause2( void * pSat, Cnf_Dat_t * pCnf );
}

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintSOPUnate(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintPOUnate(Abc_Frame_t* pAbc, int argc, char** argv);

bool debug = false;

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_sopunate", Lsv_CommandPrintSOPUnate, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_pounate", Lsv_CommandPrintPOUnate, 0);
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

void Lsv_NtkPrintSOPUnate(Abc_Ntk_t* pNtk) {
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i) {
    if (debug == true) printf("Object Id = %d, name = %s\n", Abc_ObjId(pObj), Abc_ObjName(pObj));
    Abc_Obj_t* pFanin;
    int j;
    Abc_ObjForEachFanin(pObj, pFanin, j) {
      if (debug == true) printf("  Fanin-%d: Id = %d, name = %s\n", j, Abc_ObjId(pFanin),
             Abc_ObjName(pFanin));
    }
    if (Abc_NtkHasSop(pNtk)) {
      if (debug == true) printf("The SOP of this node:\n%s", (char*)pObj->pData);
      /// initialize array of size j with 0 for storing the unate of variable
      /// unatiness decription 
      /// dont care => 0
      /// positive unate => 1
      /// negative unate => 2
      /// binate => 3
      int* unateness = ABC_CALLOC(int, j);
      /// initialize iteration
      char* t = (char*)pObj->pData;
      int SOPFlag = 0;
      int varCount = 0;
      int negateFlag = 0;
      int isConst = 0;
      /// iterate over pDate
      if (strlen(t) == 3) isConst = 1;
      for (int i = 0; i < strlen(t); i++) {
        if (t[i] == ' ') {
          SOPFlag = 1;
          if (t[i+1] == '0') negateFlag = 1;
        }
        /// deal with each SOP
        if (SOPFlag == 0) {
          //printf("SOP: %c\n", t[i]);
          //printf("varCount: %i\n", varCount);
          /// if 1  && 0 in array => positive unate
          if (t[i] == '1' && unateness[varCount] == 0) unateness[varCount] = 1;
          /// if 0 && 0 in array => negative unate
          if (t[i] == '0' && unateness[varCount] == 0) unateness[varCount] = 2;
          /// if 2 && 1 in array or 1 &&  2 in array => binate
          if ((t[i] == '1' && unateness[varCount] == 2) || (t[i] == '0' && unateness[varCount] == 1)) unateness[varCount] = 3;
          varCount++;
          if (varCount == j) varCount = 0;
        }
        if (t[i] == '\n') SOPFlag = 0;
      }
      /*
      /// traverse all the variable
      int k;
      Abc_ObjForEachFanin(pObj, pFanin, k) {
        printf("%i %s unateness: %i\n", k, Abc_ObjName(pFanin), unateness[k]);        
      }
      */

     /// sort Fain
     int e;
     std::vector<int> faninId(j, 0);
     std::vector<std::string> faninName(j);
     std::vector<int> faninUnate(j, 0);
      Abc_ObjForEachFanin(pObj, pFanin, e) {
        faninId[e] = Abc_ObjId(pFanin);
        faninName[e] = Abc_ObjName(pFanin);
        faninUnate[e] = unateness[e];
        if (debug == true) printf("Name: %s, Id: %i, ", faninName[e].c_str(), faninId[e]);
        if (debug == true) printf("unateness: %i \n", faninUnate[e]);
      }

      for (int k = 0; k < j; k++) {
        for (int l = k + 1; l < j; l++) {
          if (faninId[l] < faninId[k]) {
            std::swap(faninId[l], faninId[k]);
            std::swap(faninName[l], faninName[k]);
            std::swap(faninUnate[l], faninUnate[k]);
          }
        }
      }
      /// check
      int f;
      Abc_ObjForEachFanin(pObj, pFanin, f) {
        if (debug == true) printf("Name: %s, Id: %i, ", faninName[f].c_str(), faninId[f]);
        if (debug == true) printf("unateness: %i \n", faninUnate[f]);
      }

      /// print result
      if (isConst == 0) printf("node %s:\n", Abc_ObjName(pObj));
      /// print positive unat
      int a_count = 0;
      for (int i = 0; i < j; i++) {
        int negation = (negateFlag == 0) ? 1 : 2;
        if (faninUnate[i] == negation) {
          if (a_count == 0) {
            printf("+unate inputs: %s", faninName[i].c_str());
            a_count++;
          }
          else {
            printf(",%s", faninName[i].c_str()); 
          }
        }
      }
      if (a_count == 1) printf("\n");

      /// print negative unate
      int b_count = 0;
      for (int i = 0; i < j; i++) {
        int negation = (negateFlag == 0) ? 2 : 1;
        if (faninUnate[i] == negation) {
          if (b_count == 0) {
            printf("-unate inputs: %s",  faninName[i].c_str());
            b_count++;
          }
          else {
            printf(",%s", faninName[i].c_str()); 
          }
        }
      }
      if (b_count == 1) printf("\n");

      /// print binate
      int c_count = 0;
      for (int i = 0; i < j; i++) {
        if (faninUnate[i]== 3) {
          if (c_count == 0) {
            printf("binate inputs: %s", faninName[i].c_str());
            c_count++;
          }
          else {
            printf(",%s", faninName[i].c_str()); 
          }
        }
      }
      if (c_count == 1) printf("\n");
      
      ABC_FREE(unateness);
    }
  }
}

int Lsv_CommandPrintSOPUnate(Abc_Frame_t* pAbc, int argc, char** argv) {
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
  Lsv_NtkPrintSOPUnate(pNtk);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_print_sopunate [-h]\n");
  Abc_Print(-2, "\t         prints the SOP unate in the network\n");
  Abc_Print(-2, "\t-h     : print the command usage\n");
  return 1;
}

void Lsv_NtkPrintPOUnate(Abc_Ntk_t* pNtk) {
  std::cout << "-----------HI------------" << std::endl;
  // extract cone from Abc_Ntk
  // iterate each PO and find the cone of each PO
  Abc_Obj_t* pPo;
  int i;
  Abc_Ntk_t* pCone;
  Abc_Obj_t* pPi;
  Aig_Man_t* pMan;
  Cnf_Dat_t* pCnfPos, *pCnfNeg;
  sat_solver * pSat;
  int status;

  Abc_NtkForEachPo(pNtk, pPo, i) {
    pCone = Abc_NtkCreateCone( pNtk, Abc_ObjFanin0(pPo), Abc_ObjName(pPo), 0 );
    //Abc_Obj_t* pPi;
    printf("PO Id = %d, name = %s\n", Abc_ObjId(pPo), Abc_ObjName(pPo));
    int j;
    Abc_NtkForEachPi( pNtk, pPi, j ) {
      printf("PI Id = %d, name = %s\n", Abc_ObjId(pPi), Abc_ObjName(pPi));
    }
    std::cout << std::endl;

    // Turn Abc_Ntk into Aig_Man_t
    pCone = Abc_NtkStrash (pCone, 0, 0, 0 );
    pMan = Abc_NtkToDar(pCone, 0, 0 );

    // Turn Aig_Man_t to Cnf_Dat_t (pCnfPos for positive cofactor, pCnfNeg for negetive cofactor)
    pCnfPos = Cnf_Derive( pMan, Aig_ManCoNum(pMan) ); 

    Abc_Print( 1, "CNF stats: Vars = %6d. Clauses = %7d. Literals = %8d.   \n", pCnfPos->nVars, pCnfPos->nClauses, pCnfPos->nLiterals );
    Cnf_DataPrint( pCnfPos, 1  );

    printf("PO Id = %d, cnf Id = %d\n", Abc_ObjId(pPo), pCnfPos->pVarNums[Abc_ObjId(pPo)]);
    Abc_NtkForEachPi( pNtk, pPi, j ) {
      printf("PI Id = %d, cnf Id = %d\n", Abc_ObjId(pPi), pCnfPos->pVarNums[Abc_ObjId(pPi)]);
    }

    // manipulate CNF formula
    pCnfNeg = Cnf_DataDup(pCnfPos);
    Cnf_DataLift(pCnfNeg, pCnfPos->nVars);

    Abc_Print( 1, "CNF stats: Vars = %6d. Clauses = %7d. Literals = %8d.   \n", pCnfNeg->nVars, pCnfNeg->nClauses, pCnfNeg->nLiterals );
    Cnf_DataPrint( pCnfNeg, 1  );

    printf("PO Id = %d, cnf Id = %d\n", Abc_ObjId(pPo), pCnfNeg->pVarNums[Abc_ObjId(pPo)]);
    Abc_NtkForEachPi( pNtk, pPi, j ) {
      printf("PI Id = %d, cnf Id = %d\n", Abc_ObjId(pPi), pCnfNeg->pVarNums[Abc_ObjId(pPi)]);
    }



    // initialize SAT solver
    pSat = (sat_solver *)Cnf_DataWriteIntoSolver( pCnfPos, 1, 0 );
    sat_solver_setnvars( pSat, pCnfPos->nVars * 2 );
    for ( int i = 0; i < pCnfNeg->nClauses; i++ )
    {
      sat_solver_addclause( pSat, pCnfNeg->pClauses[i], pCnfNeg->pClauses[i+1] );
    }

    // assert each output independently
   
    printf( "Created SAT problem with %d variable and %d clauses. \n", sat_solver_nvars(pSat), sat_solver_nclauses(pSat) );

    status = sat_solver_simplify(pSat);

    std::cout << status << std::endl; 
    // manipulate SAT solver
  }  
}

int Lsv_CommandPrintPOUnate(Abc_Frame_t* pAbc, int argc, char** argv) {
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
  Lsv_NtkPrintPOUnate(pNtk);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_print_sopunate [-h]\n");
  Abc_Print(-2, "\t         prints the SOP unate in the network\n");
  Abc_Print(-2, "\t-h     : print the command usage\n");
  return 1;
}
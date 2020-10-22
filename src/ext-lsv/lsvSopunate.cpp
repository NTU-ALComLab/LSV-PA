#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "misc/vec/vec.h"
#include <vector>
#include <string>
using namespace std;

static int Lsv_CommandPrintSopunate(Abc_Frame_t* pAbc, int argc, char** argv);

void lsv_print_sopunate_init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_sopunate", Lsv_CommandPrintSopunate, 0);
}

void lsv_print_sopunate_destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t lsv_print_sopunate_initializer = {lsv_print_sopunate_init, lsv_print_sopunate_destroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&lsv_print_sopunate_initializer); }
} lsv_print_sopunate_PackageRegistrationManager;

void Lsv_NtkPrintSopunate(Abc_Ntk_t* pNtk) {

  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i) {
    
    printf("node %s:\n", Abc_ObjName(pObj));
    if (Abc_NtkHasSop(pNtk)) {
      
      //Vec_Int_t * tArray = Vec_IntStart(Abc_ObjFaninNum(pObj));
      //Vec_Int_t * pArray;
      //Vec_Int_t * nArray;
      //Vec_Int_t * bArray;
      
      vector<char *> pArr, nArr, bArr;
      
      char * pSop;
      pSop = (char *)pObj->pData;
      char * pCube;
      int nFanins = Abc_SopGetVarNum(pSop);
      
      vector<int> Arr(nFanins, -1);
      Abc_SopForEachCube (pSop, nFanins, pCube)
      {
        
        int Value, j;
        Abc_CubeForEachVar (pCube, Value, j)
        {
          if (Arr[j] == -1) {
            if (Value == '1') {
              Arr[j] = 1;
            }else if (Value == '0') {
              Arr[j] = 0;
            }

          } else{
            if (Arr[j] == 1 && Value == '0') {
              Arr[j] = 2;
            }else if (Arr[j] == 0 && Value == '1') {
              Arr[j] = 2;
            }
          }
          
        }

      }
      Abc_Obj_t* pFanin;
      int j;
      Abc_ObjForEachFanin(pObj, pFanin, j) {
        if (Arr[j] == 2) {
          bArr.push_back(Abc_ObjName(pFanin));
        } else if (Arr[j] == 1) {
          pArr.push_back(Abc_ObjName(pFanin));
        } else if (Arr[j] == 0) {
          nArr.push_back(Abc_ObjName(pFanin));
        }else {
          pArr.push_back(Abc_ObjName(pFanin));
          nArr.push_back(Abc_ObjName(pFanin));
        }    
      }
      if (Abc_SopIsComplement(pSop)) {
        

        printf("+unate inputs:");
        for (int k=0; k<nArr.size(); ++k) {
          if (k==0) {
            printf(" ");
          }else{
            printf(",");
          }
          printf("%s", nArr[k]);
        }
        printf("\n");
        printf("-unate inputs:");
        for (int k=0; k<pArr.size(); ++k) {
          if (k==0) {
            printf(" ");
          }else{
            printf(",");
          }
          printf("%s", pArr[k]);
        }
        printf("\n");
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
      }else {
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

      
      
      //printf("\n");
      //printf("The SOP of this node:\n%s", (char*)pObj->pData);
    }
  }
}
int Lsv_CommandPrintSopunate(Abc_Frame_t* pAbc, int argc, char** argv) {
  //printf("Lsv_CommandPrintSopunate\n");
  
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
  Lsv_NtkPrintSopunate(pNtk);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_print_sopunate [-h]\n");
  Abc_Print(-2, "\t        prints the unate information for each node in the network\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}

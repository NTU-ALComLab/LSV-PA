#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "misc/vec/vec.h"
#include <vector>
#include <string>
#include <algorithm>
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


bool pair_sort (pair<char *, int> p1, pair<char *, int> p2) {
        return p1.second < p2.second ;
}

void Lsv_NtkPrintSopunate(Abc_Ntk_t* pNtk) {

  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i) {
    
    
    if (Abc_NtkHasSop(pNtk)) {
      
      //Vec_Int_t * tArray = Vec_IntStart(Abc_ObjFaninNum(pObj));
      //Vec_Int_t * pArray;
      //Vec_Int_t * nArray;
      //Vec_Int_t * bArray;
      //printf("node %s:\n", Abc_ObjName(pObj));
      //typedef pair<string, int> element;
      //vector<char *> pArr, nArr, bArr;
      vector<pair<char *, int> > pArr, nArr, bArr;
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
          //bArr.push_back(Abc_ObjName(pFanin));
          bArr.push_back(pair<char *, int>(Abc_ObjName(pFanin), Abc_ObjId(pFanin)));
          

        } else if (Arr[j] == 1) {
          pArr.push_back(pair<char *, int>(Abc_ObjName(pFanin), Abc_ObjId(pFanin)));
        } else if (Arr[j] == 0) {
          nArr.push_back(pair<char *, int>(Abc_ObjName(pFanin), Abc_ObjId(pFanin)));
        }else {
          pArr.push_back(pair<char *, int>(Abc_ObjName(pFanin), Abc_ObjId(pFanin)));
          nArr.push_back(pair<char *, int>(Abc_ObjName(pFanin), Abc_ObjId(pFanin)));
        }    
      }
      
      sort(pArr.begin(), pArr.end(), pair_sort);
      sort(nArr.begin(), nArr.end(), pair_sort);
      sort(bArr.begin(), bArr.end(), pair_sort);

      if (!pArr.empty() || !nArr.empty() || !bArr.empty()) {
        printf("node %s:\n", Abc_ObjName(pObj));
      }

      if (Abc_SopIsComplement(pSop)) {
        
        if (nArr.size() != 0) {
          printf("+unate inputs:");
          for (int k=0; k<nArr.size(); ++k) {
            if (k==0) {
              printf(" ");
            }else{
              printf(",");
            }
            printf("%s", nArr[k].first);
          }
          printf("\n");
        }
        if (pArr.size() != 0) {
          printf("-unate inputs:");
          for (int k=0; k<pArr.size(); ++k) {
            if (k==0) {
              printf(" ");
            }else{
              printf(",");
            }
            printf("%s", pArr[k].first);
          }
        }
        
        printf("\n");
        
      }else {
        if (pArr.size() != 0) {
          printf("+unate inputs:");
          for (int k=0; k<pArr.size(); ++k) {
            if (k==0) {
              printf(" ");
            }else{
              printf(",");
            }
            printf("%s", pArr[k].first);
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
            printf("%s", nArr[k].first);
          }
          printf("\n");
        }
        
        
      }

      if (bArr.size() != 0) {
        printf("binate inputs:");
        for (int k=0; k<bArr.size(); ++k) {
          if (k==0) {
            printf(" ");
          }else{
            printf(",");
          }
          printf("%s", bArr[k].first);
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

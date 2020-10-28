#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <stdlib.h>

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintSopunate(Abc_Frame_t* pAbc, int argc, char** argv);
static Abc_Obj_t* FaninNow; 

int checkSymbol(char c) {
    switch(c) {
        case '-':
            return 2;
        case '0':
            return 1;
        case '1':
            return 0;
        default:
            fprintf(stderr, "Unknown input of SOP!!\n");
            //printf("Unknown input of SOP!!\n");
            return -1;
    }
}

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_sopunate", Lsv_CommandPrintSopunate, 0); // 0 for the function not changed after command
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

int compare(const void* i1, const void* i2) {
    return  Abc_ObjId( Abc_ObjFanin(FaninNow,*(int*)i1)) > Abc_ObjId( Abc_ObjFanin(FaninNow, *(int*)i2));  
}

void Lsv_FindUnates(Abc_Ntk_t* pNtk) {
    Abc_Obj_t* pObj;
    int i;
    Abc_NtkForEachNode(pNtk, pObj, i) {
        FaninNow = pObj; // set the global Fanin for the compare function

        int nFanins = Abc_ObjFaninNum(pObj);
        if (nFanins) {
            printf("node %s:\n", Abc_ObjName(pObj));
        }
        //printf("The SOP of this node:\n%s", (char*)pObj->pData);
        char* pCube;
        int nateFaninIndex[3][nFanins]; // this store the numbers of fanins
        int nateNums[3]; // this store the number of var in each nate

        memset(nateNums, 0, sizeof(nateNums));

        int var[nFanins];
        for(int i = 0; i < nFanins; i++){
            var[i] = -1;
        }

        Abc_SopForEachCube((char*)pObj->pData, nFanins, pCube){
            int sign = checkSymbol(*(pCube+nFanins+1));
            for(int i = 0; i < nFanins; i++){
                int Fanin = checkSymbol(*(pCube+i));
                if (Fanin != 2) { // not don't care Fanin = 0 or 1 
                    if (sign == 1) {
                        Fanin ^= 1;
                    }
                    if(var[i] != Fanin && var[i] != -1){
                        var[i] = 2;
                    } else{
                        var[i] = Fanin;
                    }
                } 
            }
        }
        for(int i = 0; i < nFanins; i++) { 
            if (var[i] == -1) { // is Don't care so both +unate and -unate
                nateFaninIndex[0][nateNums[0]++] = i;
                nateFaninIndex[1][nateNums[1]++] = i;
            } else{
                nateFaninIndex[var[i]][nateNums[var[i]]++] = i;
            }
        }

        char nate[3][16] = {"+unate", "-unate", "binate"};

        for(int i = 0; i < 3; i++) {
            if(nateNums[i]){
                qsort((void*)nateFaninIndex[i], nateNums[i], sizeof(int), compare); // sort the nateIds with it's id number
                printf("%s inputs: ", nate[i]);
                for(int j = 0; j < nateNums[i]-1; j++){
                    printf("%s,", Abc_ObjName( Abc_ObjFanin(pObj, nateFaninIndex[i][j])));
                }
                printf("%s\n", Abc_ObjName( Abc_ObjFanin(pObj, nateFaninIndex[i][nateNums[i]-1])));
            }
        }
    }
    return ;
}
int Lsv_CommandPrintSopunate(Abc_Frame_t* pAbc, int argc, char** argv) {
    Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    Extra_UtilGetoptReset();
    while((c = Extra_UtilGetopt(argc, argv, "h")) != EOF){
        switch(c){
            case 'h':
                goto usage;
            default:
                goto usage;
        }
    }
    if(!pNtk){
        Abc_Print(-1, "Empty network.\n");
        return 1;
    }
    if(!Abc_NtkIsSopLogic(pNtk)){
        Abc_Print(-1, "Showing SOPs unate information can only be done for logic SOP networks(run \"SOP\").\n");
        return 1;
    }
    Lsv_FindUnates(pNtk);
    return 0;

usage:
  Abc_Print(-2, "usage: lsv_print_sopunate [-h]\n");
  Abc_Print(-2, "\t        prints unate information for each node in the SOP network\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
    
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

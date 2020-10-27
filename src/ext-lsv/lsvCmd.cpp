#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <vector>
#include <string>
#include <algorithm>

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintSOPUnate(Abc_Frame_t* pAbc, int argc, char** argv);

bool debug = true;

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_sopunate", Lsv_CommandPrintSOPUnate, 0);
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
      /// iterate over pDate
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
        printf("Name: %s, Id: %i, ", faninName[e].c_str(), faninId[e]);
        printf("unateness: %i \n", faninUnate[e]);
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
      printf("\n");
      /// check
      int f;
      Abc_ObjForEachFanin(pObj, pFanin, f) {
        printf("Name: %s, Id: %i, ", faninName[f].c_str(), faninId[f]);
        printf("unateness: %i \n", faninUnate[f]);
      }

      /// print result
      printf("node %s:\n", Abc_ObjName(pObj));
      /// print positive unate
      int a;
      int a_count = 0;
      Abc_ObjForEachFanin(pObj, pFanin, a) {
        int negation = (negateFlag == 0) ? 1 : 2;
        if (unateness[a] == negation) {
          if (a_count == 0) {
            printf("+unate inputs: %s", Abc_ObjName(pFanin));
            a_count++;
          }
          else {
            printf(",%s", Abc_ObjName(pFanin)); 
          }
        }
      }
      if (a_count == 1) printf("\n");
      /// print negative unate
      int b;
      int b_count = 0;
      Abc_ObjForEachFanin(pObj, pFanin, b) {
        int negation = (negateFlag == 0) ? 2 : 1;
        if (unateness[b] == negation) {
          if (b_count == 0) {
            printf("-unate inputs: %s", Abc_ObjName(pFanin));
            b_count++;
          }
          else {
            printf(",%s", Abc_ObjName(pFanin)); 
          }
        }
      }
      if (b_count == 1) printf("\n");
      /// print binate
      int c;
      int c_count = 0;
      Abc_ObjForEachFanin(pObj, pFanin, c) {
        if (unateness[c] == 3) {
          if (c_count == 0) {
            printf("binate inputs: %s", Abc_ObjName(pFanin));
            c_count++;
          }
          else {
            printf(",%s", Abc_ObjName(pFanin)); 
          }
        }
      }
      if (c_count == 1) printf("\n");
      /// free variable
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
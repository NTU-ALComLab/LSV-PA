#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <vector>
#include <stdlib.h>
#include <algorithm>

bool comp(std::pair<unsigned, char*>& a, std::pair<unsigned, char*>& b) {
  return a.first < b.first;  
}

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_sopunate", Lsv_CommandPrintNodes, 0);
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
    Abc_Obj_t* pFanin;
    int j;
    std::vector<std::pair<unsigned, char*> > fanin_name;
    Abc_ObjForEachFanin(pObj, pFanin, j) {
      std::pair<unsigned, char*> p(Abc_ObjId(pFanin), Abc_ObjName(pFanin));
      fanin_name.push_back(p);
    }

    if (Abc_NtkHasSop(pNtk)) {
      int faninNum = Abc_ObjFaninNum(pObj);
      if(faninNum) printf("node %s:\n", Abc_ObjName(pObj));
      else return;

      char* pCube;
      int* unate;
      unate = new int[faninNum];
      for(int n = 0 ; n < faninNum ; n++) unate[n] = 0;

      bool offset = false;
      if( ((char*)pObj-> pData)[faninNum+1] == 48 ) offset = true;
      
      Abc_SopForEachCube((char*)pObj->pData, faninNum, pCube) {
        int k, value;
        Abc_CubeForEachVar(pCube, value, k) {
          if(value == 49) {  // 1
            if(unate[k] == 0) unate[k] = 1;  // +
            else if(unate[k] == -1) unate[k] = 2;  // bi
          }
          if(value == 48) {  // 0
            if(unate[k] == 0) unate[k] = -1;  // -
            else if(unate[k] == 1) unate[k] = 2;  // bi
          }
        }
      }

      std::vector<std::pair<unsigned, char*> > positive_unate_var;
      std::vector<std::pair<unsigned, char*> > negative_unate_var;
      std::vector<std::pair<unsigned, char*> > binate_var;
      for(int n = 0 ; n < faninNum ; n++) {
        if(offset) {
          if(unate[n] == -1) positive_unate_var.push_back(fanin_name[n]);
          if(unate[n] == 1) negative_unate_var.push_back(fanin_name[n]);
        }
        else {  // onset minterm
          if(unate[n] == 1) positive_unate_var.push_back(fanin_name[n]);
          if(unate[n] == -1) negative_unate_var.push_back(fanin_name[n]);
        }
        if(unate[n] == 0) {
          positive_unate_var.push_back(fanin_name[n]);
          negative_unate_var.push_back(fanin_name[n]);
        }
        if(unate[n] == 2) binate_var.push_back(fanin_name[n]);
      }
      sort(positive_unate_var.begin(), positive_unate_var.end(), comp);
      sort(negative_unate_var.begin(), negative_unate_var.end(), comp);
      sort(binate_var.begin(), binate_var.end(), comp);

      for(int n = 0 ; n < positive_unate_var.size() ; n++) {
        if(n == 0) {
          printf("+unate inputs: ");
          printf("%s", positive_unate_var[n].second);
        }
        else printf(",%s", positive_unate_var[n].second);
      }
      if(!positive_unate_var.empty()) printf("\n");

      for(int n = 0 ; n < negative_unate_var.size() ; n++) {
        if(n == 0) {
          printf("-unate inputs: ");
          printf("%s", negative_unate_var[n].second);
        }
        else printf(",%s", negative_unate_var[n].second);
      }
      if(!negative_unate_var.empty()) printf("\n");

      for(int n = 0 ; n < binate_var.size() ; n++) {
        if(n == 0) {
          printf("binate inputs: ");
          printf("%s", binate_var[n].second);
        }
        else printf(",%s", binate_var[n].second);
      }
      if(!binate_var.empty()) printf("\n");

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
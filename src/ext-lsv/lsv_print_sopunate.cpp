#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <vector>
#include <algorithm>

namespace {


bool Fanin_idxcmp (Abc_Obj_t i, Abc_Obj_t j) { return (i.Id < j.Id); }


static int Lsv_CommandPrintSopunate(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_sopunate", Lsv_CommandPrintSopunate, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager1 {
  PackageRegistrationManager1() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager1;

void Lsv_NtkPrintSopunate(Abc_Ntk_t* pNtk) {
  char* data;
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i) {
    int FaninNum = Abc_ObjFaninNum(pObj);
    int minnum;
    int linenum;

    int *state = new int[pObj->vFanins.nSize];
    int eflag[3] = {0};
    bool first;
    bool isOffset;
    for (int l = 0; l < pObj->vFanins.nSize; l++) {
        state[l] = 0;
    }

    if (Abc_NtkHasSop(pNtk)) {
      data = (char*)pObj->pData;
      linenum = pObj->vFanins.nSize + 3;
      minnum = strlen(data)/linenum;
      if (strlen(data) == 3)
      {
        continue;
      }
      
      for (int m = 0; m < minnum; m++) {
          if (data[linenum - 2 + m * linenum] == '0') isOffset = true;
          else isOffset = false;
          for (int n = 0; n < pObj->vFanins.nSize; n++) {
            if ((!isOffset && data[n + m * linenum] == '0') || (isOffset && data[n + m * linenum] == '1' )) {
                if (state[n] == 2) {
                    eflag[0]--;
                    eflag[2]++;
                    state[n] = 3;
                } else if (state[n] == 0){
                    eflag[1]++;
                    state[n] = 1;
                }
            } else if ((!isOffset && data[n + m * linenum] == '1') || (isOffset && data[n + m * linenum] == '0')) {
                if (state[n] == 1) {
                    eflag[1]--;
                    eflag[2]++;
                    state[n] = 3;
                } else if (state[n] == 0){
                    eflag[0]++;
                    state[n] = 2;
                }
            } 
          }
      }
      if (eflag[0] != 0 || eflag[1] != 0 || eflag[2] != 0) printf("node %s:\n", Abc_ObjName(pObj));
      for (int m = 0; m < 3; m++) {
        Abc_Obj_t* cFanin; 
        if (eflag[0] != 0 && m == 0) {
            std::vector<Abc_Obj_t> pos_vector;           
            printf("+unate inputs: ");
            for (int n = 0; n < FaninNum; n++) {
              if (state[n] == 2) {
                  cFanin = Abc_ObjFanin(pObj, n);
                  pos_vector.push_back(*cFanin);
              }
            }
            std::sort(pos_vector.begin(), pos_vector.end(), Fanin_idxcmp); 
            for (int it = 0; it < pos_vector.size(); ++it) {
              cFanin = &pos_vector[it];
              if (it == 0) printf("%s", Abc_ObjName(cFanin));
              else printf(",%s", Abc_ObjName(cFanin));
            }
            printf("\n");                      
        }
        first = false;
        if (eflag[1] != 0 && m == 1) {
            std::vector<Abc_Obj_t> neg_vector;           
            printf("-unate inputs: ");
            for (int n = 0; n < FaninNum; n++) {
              if (state[n] == 1) {
                  cFanin = Abc_ObjFanin(pObj, n);
                  neg_vector.push_back(*cFanin);
              }
            }
            std::sort(neg_vector.begin(), neg_vector.end(), Fanin_idxcmp); 
            for (int it = 0; it < neg_vector.size(); ++it) {
              cFanin = &neg_vector[it];
              if (it == 0) printf("%s", Abc_ObjName(cFanin));
              else printf(",%s", Abc_ObjName(cFanin));
            }  
            printf("\n");                      
        }
        if (eflag[2] != 0 && m == 2) {
            std::vector<Abc_Obj_t> bi_vector;           
            printf("binate inputs: ");
            for (int n = 0; n < FaninNum; n++) {
              if (state[n] == 3) {
                  cFanin = Abc_ObjFanin(pObj, n);
                  bi_vector.push_back(*cFanin);
              }
            }
            std::sort(bi_vector.begin(), bi_vector.end(), Fanin_idxcmp); 
            for (int it = 0; it < bi_vector.size(); ++it) {
              cFanin = &bi_vector[it];
              if (it == 0) printf("%s", Abc_ObjName(cFanin));
              else printf(",%s", Abc_ObjName(cFanin));              
            }
            printf("\n");             
        }
               
      }
    }
  }
}

int Lsv_CommandPrintSopunate(Abc_Frame_t* pAbc, int argc, char** argv) {
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
  Abc_Print(-2, "\t        prints the Sop unate in the network\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}
}
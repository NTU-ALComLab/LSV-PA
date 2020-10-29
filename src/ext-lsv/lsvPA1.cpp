#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <algorithm>

static int Lsv_CommandPrintUnates(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_sopunate", Lsv_CommandPrintUnates, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

int cmp(Abc_Obj_t* obj1, Abc_Obj_t* obj2){
  if (Abc_ObjId(obj1) < Abc_ObjId(obj2))
    return -1;
  else if (Abc_ObjId(obj1) == Abc_ObjId(obj2)) 
    return 0;
  else 
    return 1;
}

void Lsv_NtkPrintUnates(Abc_Ntk_t* pNtk){
  Abc_Obj_t* pObj;
  Abc_Obj_t* pFanin;
  int i, j;

  Abc_NtkForEachNode(pNtk, pObj, i) {
    // printf("Current node: %s\n", Abc_ObjName(pObj));

    char* sop;
    // get node SOP
    if (Abc_NtkHasSop(pNtk)){
      sop = (char*)pObj->pData;
    } else {
      printf("Network does not have SOP.\n\n");
      return;
    }
    // printf("%s\n", sop);
    // Some properties & variables
    int N_fanin = Abc_ObjFaninNum(pObj);
    if (N_fanin == 0) continue; // ignore nodes without fanin

    int row_len = N_fanin + 3;
    int N_clause = strlen(sop) / row_len; //Each row(clause): len("01-0 1\n")=N_fanin + len(" 1\n")
    int N_pos_unate = 0;
    int N_neg_unate = 0;
    int N_binate = 0;
    bool normal_SOP = (sop[N_fanin + 1] == '1');

    Abc_Obj_t* pos_unates[N_fanin];
    Abc_Obj_t* neg_unates[N_fanin];
    Abc_Obj_t* binates[N_fanin];

    Abc_ObjForEachFanin(pObj, pFanin, j){
      // Count 1 and 0 of the j-th Fanin in each clauses
      int pos_cnt = 0;
      int neg_cnt = 0;
      for (int k = 0; k < N_clause; ++k){
        int idx = j + k * row_len;
        if (sop[idx] == '1')
          pos_cnt += 1;
        if (sop[idx] == '0')
          neg_cnt += 1;
      }

      // determine unate/binate
      if (normal_SOP){
        if (pos_cnt == 0){
          neg_unates[N_neg_unate] = pFanin;
          N_neg_unate += 1;
        } 
        if (neg_cnt == 0){
          pos_unates[N_pos_unate] = pFanin;
          N_pos_unate += 1;
        }
        if (pos_cnt > 0 && neg_cnt > 0){
          binates[N_binate] = pFanin;
          N_binate += 1;
        }
      } else { // normal_SOP == False
        if (neg_cnt == 0){
          neg_unates[N_neg_unate] = pFanin;
          N_neg_unate += 1;
        } 
        if (pos_cnt == 0){
          pos_unates[N_pos_unate] = pFanin;
          N_pos_unate += 1;
        }
        if (pos_cnt > 0 && neg_cnt > 0){
          binates[N_binate] = pFanin;
          N_binate += 1;
        }
      }
    }
    
    // Sorting & output
    printf("node %s:\n", Abc_ObjName(pObj));
    // Sort unate/binate Fanins of the i-th node
    if (N_pos_unate){
      // std::sort(pos_unates, pos_unates + N_pos_unate, cmp);

      printf("+unate inputs: %s", Abc_ObjName(pos_unates[0]));
      for (int k = 1; k < N_pos_unate; k ++){
        printf(",%s", Abc_ObjName(pos_unates[k]));
      }
      printf("\n");
    }
    if (N_neg_unate){
      // std::sort(neg_unates, neg_unates + N_neg_unate, cmp);

      printf("-unate inputs: %s", Abc_ObjName(neg_unates[0]));
      for (int k = 1; k < N_neg_unate; k ++){
        printf(",%s", Abc_ObjName(neg_unates[k]));
      }
      printf("\n");

    }
    if(N_binate){
      // std::sort(binates, binates + N_binate, cmp);

      printf("binate inputs: %s", Abc_ObjName(binates[0]));
      for (int k = 1; k < N_binate; k++){
        printf(",%s", Abc_ObjName(binates[k]));
      }
      printf("\n");
    }
  }
}

int Lsv_CommandPrintUnates(Abc_Frame_t* pAbc, int argc, char** argv) {
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
  Lsv_NtkPrintUnates(pNtk);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_print_sopunate [-h]\n");
  Abc_Print(-2, "\t        prints the unate nodes in the network\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}
#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

#include "./lsvCut.h"

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintMOCut(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocut", Lsv_CommandPrintMOCut, 0);
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





int Lsv_FindCut(Abc_Obj_t* pObj, int k, Cut_t*** k_cut, int& kcut_size, int* id_to_index, int* num_cut_per_obj) {
  int nodeID = Abc_ObjId(pObj);
  int index = find_index(id_to_index, kcut_size, nodeID);
  if(index != -1) { // found
    return index;
  }
  index = kcut_size;
  kcut_size++;
  id_to_index[nodeID] = nodeID;

  int fanin_num = Abc_ObjFaninNum(pObj);
  if(fanin_num == 0) {
    k_cut[index] = (Cut_t**)malloc(sizeof(Cut_t*));
    k_cut[index][0] = new_cut(&nodeID, 1);
    num_cut_per_obj[index] = 1;
    return index;
  }
  int cut_accumulate_size = 1;
  Cut_t** cut_accumulate = NULL;

  Abc_Obj_t* pFanin;
  int i;
  Abc_ObjForEachFanin(pObj, pFanin, i) {
    int fanin_index = Lsv_FindCut(pFanin, k, k_cut, kcut_size, id_to_index, num_cut_per_obj);
    Cut_t** fanin_cut = k_cut[fanin_index];
    // merge cut_accumulate and fanin_cut
    Cut_t** cut_temp = (Cut_t**)malloc(sizeof(Cut_t*) * (cut_accumulate_size * num_cut_per_obj[fanin_index] + 1));
    if(cut_accumulate != NULL){
      for(int j=0; j<cut_accumulate_size; j++){
        for(int k=0; k<num_cut_per_obj[fanin_index]; k++){
          cut_temp[j*num_cut_per_obj[fanin_index]+k] = new_cut(cut_accumulate[j], fanin_cut[k]);
        }
      }
      free_cuts(cut_accumulate, cut_accumulate_size);
    }
    else{ // first fanin
      for(int j=0; j<num_cut_per_obj[fanin_index]; j++){
        cut_temp[j] = copy_cut(fanin_cut[j]);
      }
    }
    // update cut_accumulate
    cut_accumulate_size *= num_cut_per_obj[fanin_index];
    cut_sort_and_eliminate(cut_temp, cut_accumulate_size, k);
    cut_accumulate = cut_temp;
  }
  
  return index;
}

void Lsv_NtkPrintMOCut(Abc_Ntk_t* pNtk, int k, int l) {

  int NtkObjNum = Abc_NtkObjNum(pNtk);
  int kcut_size = 0;
  int* id_to_index = (int*)malloc(sizeof(int) * NtkObjNum);
  int* num_cut_per_obj = (int*)malloc(sizeof(int) * NtkObjNum);
  Cut_t*** k_cut = (Cut_t***)malloc(sizeof(Cut_t**) * NtkObjNum);

  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i) {
    // step1. Find k-cut for each node
    int index = Lsv_FindCut(pObj, k, k_cut, kcut_size, id_to_index, num_cut_per_obj);
    printf("hi");
    for(int j=0; j<num_cut_per_obj[index]; j++){
      // printf("%d: ", Abc_ObjId(pObj));
      print_cut(k_cut[index][j]);
    }
    // step2. count each cut's output num

    // step3. if output num >= l(?), print the cut
    // for(int j=0; j<num_cut_per_obj[index]; j++) {
    //   // 
    //   printf("%d: ", Abc_ObjId(pObj));
    //   print_cut(k_cut[index][j]);
    // }
    // for(int i=0; i<kcut_size; i++){
    //   free_cuts(k_cut[i], num_cut_per_obj[i]);
    // }
    return;
  }
}

int Lsv_CommandPrintMOCut(Abc_Frame_t* pAbc, int argc, char** argv) {
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
  if(argc != 3) {
    Abc_Print(-1, "Wrong number of arguments.\n");
    Abc_Print(-2, "usage: lsv_printmocut <k> <l> [-h]\n");
    Abc_Print(-2, "\t-h    : print the command usage\n");
    return 1;
  }
  if(strlen(argv[1]) != 1 || argv[1][0] < '3' || argv[1][0] > '6') {
    Abc_Print(-1, "Invalid k value.\n");
    Abc_Print(-2, "usage: lsv_printmocut <k> <l>\n");
    Abc_Print(-2, "\t        only accept 3<=k<=6\n");
    return 1;
  }
  if(strlen(argv[1]) != 1 || argv[2][0] < '1' || argv[2][0] > '4') {
    Abc_Print(-1, "Invalid l value.\n");
    Abc_Print(-2, "usage: lsv_printmocut <k> <l>\n");
    Abc_Print(-2, "\t        only accept 1<=l<=4\n");
    return 1;
  }

  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  Lsv_NtkPrintMOCut(pNtk, argv[1][0]-'0', argv[2][0]-'0');
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_printmocut <k> <l>[-h]\n");
  Abc_Print(-2, "\t        prints the inputs and outputs of every k-l multi-output cut\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}
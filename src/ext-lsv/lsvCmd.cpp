#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

#include "./lsvCut.h"

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintCut(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandSDC(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_printcut", Lsv_CommandPrintCut, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_sdc", Lsv_CommandSDC, 0);
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
  return;
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

int * My_Abc_NtkVerifySimulatePattern( Abc_Ntk_t * pNtk, int * pModel )
{
    Abc_Obj_t * pNode;
    int * pValues, Value0, Value1, i;
    int fStrashed = 0;
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        pNtk = Abc_NtkStrash(pNtk, 0, 0, 0);
        fStrashed = 1;
    }

    // increment the trav ID
    Abc_NtkIncrementTravId( pNtk );
    // set the CI values
    Abc_AigConst1(pNtk)->pCopy = (Abc_Obj_t *)1;
    Abc_NtkForEachCi( pNtk, pNode, i )
        pNode->pCopy = (Abc_Obj_t *)(ABC_PTRINT_T)pModel[i];
    // simulate in the topological order
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        Value0 = ((int)(ABC_PTRINT_T)Abc_ObjFanin0(pNode)->pCopy);
        Value1 = ((int)(ABC_PTRINT_T)Abc_ObjFanin1(pNode)->pCopy);
        Value0 = Abc_ObjFaninC0(pNode) ? ~Value0 : Value0;
        Value1 = Abc_ObjFaninC1(pNode) ? ~Value1 : Value1;
        pNode->pCopy = (Abc_Obj_t *)(ABC_PTRINT_T)(Value0 & Value1);
    }
    // fill the output values
    pValues = ABC_ALLOC( int, Abc_NtkCoNum(pNtk) );
    Abc_NtkForEachCo( pNtk, pNode, i ){
        pValues[i] = ((int)(ABC_PTRINT_T)Abc_ObjFanin0(pNode)->pCopy);
        pValues[i] = Abc_ObjFaninC0(pNode) ? ~pValues[i] : pValues[i];
    }
    if ( fStrashed )
        Abc_NtkDelete( pNtk );
    return pValues;
}

void Lsv_sdc(Abc_Ntk_t* pNtk, Abc_Obj_t* pObj) {
  // Abc_Ntk_t* transFanin = Abc_NtkCreateCone(pNtk, pObj, "test", 0);
  Vec_Ptr_t* v_roots = Vec_PtrAlloc(5);

  Abc_Obj_t* pFanin;
  int i;
  Abc_ObjForEachFanin(pObj, pFanin, i) {
    Vec_PtrPush(v_roots, pFanin);
  }

  Abc_Ntk_t* transFanin = Abc_NtkCreateConeArray(pNtk, v_roots, 0);

  int* pModel = (int*)malloc(sizeof(int) * Abc_NtkCiNum(transFanin));
  for(i = 0; i < Abc_NtkCiNum(transFanin); i++){
    pModel[i] = 0;
  }
  
  if(Abc_NtkCiNum(transFanin) <= 5){
    for(i = 0; i < Abc_NtkCiNum(transFanin); i++){
      switch(i){
        case 0:
          pModel[i] = 0x55555555;
          break;
        case 1:
          pModel[i] = 0x33333333;
          break;
        case 2:
          pModel[i] = 0x0f0f0f0f;
          break;
        case 3:
          pModel[i] = 0x00ff00ff;
          break;
        case 4:
          pModel[i] = 0x0000ffff;
          break;
        default:
          pModel[i] = 0;
          printf("Error: too many CI\n");
          break;
      }
    }
  }
  else{

  }

  int* pSimInfo = My_Abc_NtkVerifySimulatePattern(transFanin, pModel);

  if(Abc_ObjFaninC0(pObj)){
    pSimInfo[0] = ~pSimInfo[0];
  }
  if(Abc_ObjFaninC1(pObj)){
    pSimInfo[1] = ~pSimInfo[1];
  }
  
  Abc_NtkForEachCo(transFanin, pFanin, i){
    printf("CO: Id = %d, name = %s\n", Abc_ObjId(pFanin), Abc_ObjName(pFanin));
  }
  
  int pSimInfo_bool[4];
  int masked_SimInfo[4];
  masked_SimInfo[0] = ~(pSimInfo[0] ^ 0x00000000);
  masked_SimInfo[1] = ~(pSimInfo[1] ^ 0x00000000);
  masked_SimInfo[2] = ~(pSimInfo[0] ^ 0xffffffff);
  masked_SimInfo[3] = ~(pSimInfo[1] ^ 0xffffffff);
  pSimInfo_bool[0] = masked_SimInfo[0] & masked_SimInfo[1];
  pSimInfo_bool[1] = masked_SimInfo[0] & masked_SimInfo[3];
  pSimInfo_bool[2] = masked_SimInfo[2] & masked_SimInfo[1];
  pSimInfo_bool[3] = masked_SimInfo[2] & masked_SimInfo[3];

  for(i = 0; i < 4; i++){
    printf("pSimInfo_bool[%d] = %d\n", i, pSimInfo_bool[i]);
  }

  // Abc_Obj_t* pObj_CO;
  // // int i;
  // Abc_NtkForEachPo(transFanin, pObj_CO, i) {
  //   printf("CO: Id = %d, name = %s\n", Abc_ObjId(pObj_CO), Abc_ObjName(pObj_CO));
  //   Abc_Obj_t* pFanin;
  //   int j;
  //   Abc_ObjForEachFanin(pObj_CO, pFanin, j) {
  //     printf("  Fanin-%d: Id = %d, name = %s\n", j, Abc_ObjId(pFanin), Abc_ObjName(pFanin));
  //   }
  // }

  // Abc_Obj_t* pObj_new;
  // // int i;
  // Abc_NtkForEachNode(transFanin, pObj_new, i){
  //   char* name = Abc_ObjName(pObj_new);
  //   printf("in lsv_sdc %s\n", name);
  //   Abc_Obj_t* pFanin;
  //   int j;
  //   Abc_ObjForEachFanin(pObj_new, pFanin, j){
  //     printf("  Fanin-%d: Id = %d, name = %s\n", j, Abc_ObjId(pFanin), Abc_ObjName(pFanin));
  //   }
  // }
  
  return;
}

int Lsv_CommandSDC(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  
  if(argc != 2) {
    Abc_Print(-1, "Wrong number of arguments.\n");
    Abc_Print(-2, "usage: lsv_sdc <n>\n");
    Abc_Print(-2, "\t        prints all k-feasible cuts for all nodes in the network\n");
    return 1;
  }
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }

  Abc_Obj_t* pObj;
  int i;
  int found_node = 0;
  Abc_NtkForEachNode(pNtk, pObj, i){
    char* name = Abc_ObjName(pObj);
    printf("%s\n", name);
    
    if(strcmp(name+1, argv[1]) == 0){
      printf("find node %s\n", name);
      found_node = 1;
      Lsv_sdc(pNtk, pObj);
      break;
    }
  }

  if(!found_node){
    Abc_Print(-1, "Node not found.\n");
    return 1;
  }
  return 0;
}


int find_index(int* id_to_index, int array_size, int node_id) {
  int index = -1;
  for(int i=array_size - 1; i>=0; i--){
    if(id_to_index[i] == node_id){
      index = i;
      break;
    }
  }
  return index;
}

// return index of the node
int Lsv_find_cut(Abc_Obj_t* pObj, const int k_feasible, Cut_t*** k_cut, int& kcut_size, int* id_to_index, int* num_cut_per_obj) {
  int nodeID = Abc_ObjId(pObj);
  int index = find_index(id_to_index, kcut_size, nodeID);
  // printf("nodeID = %d, index = %d, kcut_size = %d\n", nodeID, index, kcut_size);
  if(index != -1){
    return index;
  }

  index = kcut_size;
  kcut_size++;
  id_to_index[index] = nodeID;
  // printf("nodeID = %d, index = %d, kcut_size = %d\n", nodeID, index, kcut_size);

  int fanin_num = Abc_ObjFaninNum(pObj);
  // printf("fanin_num = %d\n", fanin_num);
  if(fanin_num == 0){
    num_cut_per_obj[index] = 1;
    k_cut[index] = (Cut_t**)malloc(sizeof(Cut_t*) * 1);
    // printf("nodeID = %d, pcut = %p\n", nodeID, k_cut[index]);
    k_cut[index][0] = cut_new(&nodeID, 1);
    return index;
  }
  
  int cut_accumulate_size = 1;
  Cut_t** cut_accumulate = NULL;
  // cut_accumulate[0] = cut_new(&nodeID, 1);

  Abc_Obj_t* pFanin;
  int i;
  Abc_ObjForEachFanin(pObj, pFanin, i) {
    int faninID = (int)Abc_ObjId(pFanin);
    int fanin_index = Lsv_find_cut(pFanin, k_feasible, k_cut, kcut_size, id_to_index, num_cut_per_obj);
    // printf("faninID = %d, fanin_index = %d\n", faninID, fanin_index);
    // printf("num_cut_per_obj[fanin_index] = %d\n", num_cut_per_obj[fanin_index]);
    
    Cut_t** fanin_cut = k_cut[fanin_index];
    // printf("fanin_cut[0] = %p\n", fanin_cut[0]);
    // printf("malloc size = %d\n", (cut_accumulate_size * num_cut_per_obj[fanin_index] + 1));
    // merge cut_accumulate and fanin_cut
    Cut_t** cut_temp = (Cut_t**)malloc(sizeof(Cut_t*) * (cut_accumulate_size * num_cut_per_obj[fanin_index] + 1));
    // if(cut_temp == NULL){
    //   printf("cut_temp == NULL\n");
    // }
    // printf("cut_temp = %p, %d\n", cut_temp, cut_temp);
    if(cut_accumulate != NULL){
      // printf("cut_accumulate != NULL\n");
      for(int j=0; j<cut_accumulate_size; j++){
        for(int k=0; k<num_cut_per_obj[fanin_index]; k++){
          // printf("j %d: ", cut_accumulate[j]->cut_size);
          // print_cut(cut_accumulate[j]);
          // printf("k %d: ", fanin_cut[k]->cut_size);
          // print_cut(fanin_cut[k]);
          cut_temp[j*num_cut_per_obj[fanin_index]+k] = cut_new(cut_accumulate[j], fanin_cut[k]);
        }
      }
      cuts_free(cut_accumulate, cut_accumulate_size);
    }
    else{
      for(int j=0; j<num_cut_per_obj[fanin_index]; j++){
        cut_temp[j] = cut_copy(fanin_cut[j]);
      }
    }
    cut_accumulate_size *= num_cut_per_obj[fanin_index];
    // printf("cut_accumulate_size = %d\n", cut_accumulate_size);
    cut_sort_and_eliminate(cut_temp, cut_accumulate_size, k_feasible);
    cut_accumulate = cut_temp;
  }

  if(cut_accumulate == NULL){
    num_cut_per_obj[index] = 1;
    k_cut[index] = (Cut_t**)malloc(sizeof(Cut_t*) * 1);
    // printf("nodeID = %d, pcut = %p\n", nodeID, k_cut[index]);
    k_cut[index][0] = cut_new(&nodeID, 1);
    return index;
  }

  cut_accumulate[cut_accumulate_size++] = cut_new(&nodeID, 1);
  num_cut_per_obj[index] = cut_accumulate_size;
  k_cut[index] = cut_accumulate;
  // printf("nodeID = %d, pcut = %p\n", nodeID, k_cut[index]);
  return index;
}

int Lsv_NtkPrintCut(Abc_Ntk_t* pNtk, int k_feasible) {
  
  int NtkObjNum = Abc_NtkObjNum(pNtk);
  int kcut_size = 0;
  int* id_to_index = (int*)malloc(sizeof(int) * NtkObjNum);
  int* num_cut_per_obj = (int*)malloc(sizeof(int) * NtkObjNum);
  Cut_t*** k_cut = (Cut_t***)malloc(sizeof(Cut_t**) * NtkObjNum);
  
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i) {
    int nodeID = Abc_ObjId(pObj);
    int index = Lsv_find_cut(pObj, k_feasible, k_cut, kcut_size, id_to_index, num_cut_per_obj);
    for(int j=0; j<num_cut_per_obj[index]; j++){
      printf("%d: ", nodeID);
      print_cut(k_cut[index][j]);
    }
  }

  for(int i=0; i<kcut_size; i++){
    // printf("Node %d\n", id_to_index[i]);
    cuts_free(k_cut[i], num_cut_per_obj[i]);
  }
  return 0;
}

// Parse the command line arguments and call the function to print the cuts
int Lsv_CommandPrintCut(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  
  if(argc != 2) {
    Abc_Print(-1, "Wrong number of arguments.\n");
    Abc_Print(-2, "usage: lsv_printcut <k> [-h]\n");
    Abc_Print(-2, "\t        prints all k-feasible cuts for all nodes in the network\n");
    Abc_Print(-2, "\t-h    : print the command usage\n");
    return 1;
  }
  if(strlen(argv[1]) != 1 || argv[1][0] < '3' || argv[1][0] > '6') {
    Abc_Print(-1, "Invalid k value.\n");
    Abc_Print(-2, "usage: lsv_printcut <k>\n");
    Abc_Print(-2, "\t        only accept 3<=k<=6\n");
    return 1;
  }

  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  
  int k_feasible = argv[1][0] - '0';
  Lsv_NtkPrintCut(pNtk, k_feasible);

  return 0;
}
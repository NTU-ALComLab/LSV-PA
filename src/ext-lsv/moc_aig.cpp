#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

static int Lsv_PrintMOCuts(Abc_Frame_t* pAbc, int argc, char** argv);
static Vec_Wec_t* Lsv_computeNodeInputs(Abc_Ntk_t* pNtk, Abc_Obj_t * pNode, int max_input);
static int Lsv_printExample(Abc_Ntk_t* pNtk);

// Function additions for vectors of int 

static inline void Vec_WecPush_vecint(Vec_Wec_t* p, Vec_Int_t* a);
static inline int Vec_WecCompare(Vec_Wec_t* p, Vec_Int_t* a);
static Vec_Wec_t* Vec_WecRemoveSizeOver(Vec_Wec_t* p, int size);

void init_moc(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocut", Lsv_PrintMOCuts, 0);
}

void destroy_moc(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer_moc = {init_moc, destroy_moc};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer_moc); }
} PackageRegistrationManager_moc;

/// @brief Adds a vector of int in a new level to a vector of vector
/// @param p vector of vector
/// @param a vector of int
static inline void Vec_WecPush_vecint(Vec_Wec_t* p, Vec_Int_t* a) {
  int level = Vec_WecSize(p);
  for (int i=0; i<Vec_IntSize(a); i++) {
    Vec_WecPush(p, level, Vec_IntGetEntry(a, i));
  }
}

/// @brief Returns 1 if the vector of int is already in the vector of vector
/// @param p vector of vector
/// @param a vector of int
/// @return 
static inline int Vec_WecCompare(Vec_Wec_t* p, Vec_Int_t* a) {
  for (int i=0; i<Vec_WecSize(p); i++){
    Vec_Int_t* b = Vec_WecEntry(p, i);
    if (Vec_IntEqual(a, b)) {
      return 1;
    }
  }
  return -1;
}

/// @brief Creates a new Vec_Wec with only vectors that are bellow the size constraint
/// @param node_input 
/// @param max_input 
static Vec_Wec_t* Vec_WecRemoveSizeOver(Vec_Wec_t* p, int size) {
  Vec_Wec_t* new_vec = Vec_WecStart(0); 
  for (int i=0; i<Vec_WecSize(p); i++){
    Vec_Int_t* b = Vec_WecEntry(p, i);
    if (Vec_IntSize(b)<=size) {
      Vec_WecPush_vecint(new_vec, b);
    }
  }
  Vec_WecFreeP(&p);
  return new_vec;
}



int Lsv_PrintMOCuts(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c;
  int K, L;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "klh")) != EOF) {
    switch (c) {
      case 'h':
        goto usage;
      default:
        goto usage;
    }
  }
  if ( argc == globalUtilOptind + 2 )
  {
      K = atoi(argv[globalUtilOptind]);
      globalUtilOptind++;
      L = atoi(argv[globalUtilOptind]);
  }
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "This command require an AIG strash network.\n");
    return 1;
  }
  if (!Lsv_printExample(pNtk)) {
    Abc_Print(-1, "The computation of the cuts failed.\n");
    return 1;
  }
  return 1;

usage:
  Abc_Print(-2, "usage: lsv_printmocut <k> <l> [-h]\n");
  Abc_Print(-2, "\t          prints the nodes in the network\n");
  Abc_Print(-2, "\t<k>     : maximum number of nodes in a cut (2 < k < 7)\n");
  Abc_Print(-2, "\t<l>     : minimum number of output nodes of a cut (0 < l < 5)\n");
  Abc_Print(-2, "\t-h      : print the command usage\n");
  return 1;
}

static Vec_Wec_t* Lsv_computeNodeInputs(Abc_Ntk_t* pNtk, Abc_Obj_t * pNode, int max_input) {
  assert(Abc_ObjIsNode(pNode)==1);
  int input_set_pointer = 0;
  Vec_Wec_t* node_input = Vec_WecStart(0);
  Vec_Int_t* input_set = Vec_IntStart(0);
  for (int j=0; j<Abc_ObjFaninNum(pNode); j++) {
    Abc_Obj_t* pFanin = Abc_ObjFanin(pNode, j);
    Vec_IntPush(input_set, Abc_ObjId(pFanin));
  }
  if (Vec_IntSize(input_set)<=max_input) {
    Vec_WecPush_vecint(node_input, input_set);
  }
  while (true) {
    for (int i=0; i<Vec_IntSize(Vec_WecEntry(node_input, input_set_pointer)); i++) {
      Abc_Obj_t* pNextNode = Abc_NtkObj(pNtk, Vec_IntEntry(Vec_WecEntry(node_input, input_set_pointer),i));
      if (Abc_ObjIsNode(pNextNode)) {
        Vec_Int_t* next_input_set = Vec_IntStart(0);
        for (int j=0; j<Vec_IntSize(Vec_WecEntry(node_input, input_set_pointer)); j++) {
          if (j!=i) {
            Vec_IntPush(next_input_set, Vec_IntEntry(Vec_WecEntry(node_input, input_set_pointer),j));
          }
        }
        for (int j=0; j<Abc_ObjFaninNum(pNextNode); j++) {
          Abc_Obj_t* pFanin = Abc_ObjFanin(pNextNode, j);
          if (Vec_IntFind(next_input_set, Abc_ObjId(pFanin))==-1) {
            Vec_IntPush(next_input_set, Abc_ObjId(pFanin));
          }
        }
        if (Vec_IntSize(next_input_set)>0) {
          Vec_IntSort(next_input_set, 0);
          if (Vec_WecCompare(node_input,next_input_set)==-1) {
            Vec_WecPush_vecint(node_input, next_input_set);
          }
        }
      }
    }
    input_set_pointer++;
    if (input_set_pointer > Vec_WecSize(node_input) - 1) {
      break;
    }
  }
  Vec_Wec_t* final_node_inputs = Vec_WecRemoveSizeOver(node_input, max_input);
  Vec_WecPrint(final_node_inputs, 0);
  return final_node_inputs;
}

static int Lsv_printExample(Abc_Ntk_t* pNtk) {
  Abc_Print(1, "Number of Primary inputs : %d.\n", Abc_NtkPiNum(pNtk ));
  Abc_Print(1, "Number of Nodes : %d.\n", Abc_NtkNodeNum(pNtk ));
  Abc_Print(1, "Number of Objects : %d.\n", Abc_NtkObjNum(pNtk ));
  Abc_Print(1, "Number of Primary outputs : %d.\n", Abc_NtkPoNum(pNtk ));
  for (int i=1; i<Abc_NtkObjNum(pNtk ); i++) {
    Abc_Obj_t * pObj = Abc_NtkObj(pNtk, i);
    Abc_Print(1, "------------------%d------------------\n", i);
    Abc_Print(1, "Is object a node ? : %d.\n", Abc_ObjIsNode(pObj ));
    Abc_Print(1, "Is object a PI ? : %d.\n", Abc_ObjIsPi(pObj ));
    Abc_Print(1, "Is object a PO ? : %d.\n", Abc_ObjIsPo(pObj ));
    if (Abc_ObjIsNode(pObj ) or Abc_ObjIsPo(pObj )) {
      Abc_Print(1, "Number of object fanin : %d.\n", Abc_ObjFaninNum(pObj ));
      for (int j=0; j<Abc_ObjFaninNum(pObj ); j++) {
        Abc_Print(1, "Id of fanin %d node : %d.\n", j, Abc_ObjFaninId(pObj, j));
      }
    }
    if (Abc_ObjIsNode(pObj ) or Abc_ObjIsPi(pObj )) {
      Abc_Print(1, "Number of object fanout : %d.\n", Abc_ObjFanoutNum(pObj ));
      for (int j=0; j<Abc_ObjFanoutNum(pObj ); j++) {
        Abc_Obj_t * pFanout = Abc_ObjFanout(pObj, j);
        Abc_Print(1, "Id of fanout %d node : %d.\n", j, Abc_ObjId(pFanout));
      }
    }
    if (Abc_ObjIsNode(pObj )) {
      Vec_Wec_t* a = Lsv_computeNodeInputs(pNtk, pObj, 3);
    }
    Abc_Print(1, "------------------%d------------------\n\n", i);
  }
  return 1;
}
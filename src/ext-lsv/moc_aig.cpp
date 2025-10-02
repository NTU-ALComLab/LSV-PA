#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <pthread.h>

// Number of threads to use for the parrallelism
#define NUM_THREADS 12

// Structure for computation parrallelism
typedef struct {
  Abc_Ntk_t* pNtk;
  Vec_Wec_t** all_inputs_nodes;
  int offset;
  int max_input;
  int total_nodes;
  int* shared_index;
  pthread_mutex_t* shared_mutex;
} ThreadArgs_t;

static int LSV_MOCuts_init(Abc_Frame_t* pAbc, int argc, char** argv);
static Vec_Wec_t* LSV_computeNodeInputs(Abc_Ntk_t* pNtk, Abc_Obj_t * pNode, int max_input);
void* compute_inputs_worker(void* arg);
static int LSV_printDebug(Abc_Ntk_t* pNtk);
static int LSV_MOCuts(Abc_Ntk_t* pNtk, int max_inputs, int min_outputs, int debug);
static Vec_Wec_t* LSV_singleVectorInputs(Vec_Vec_t* all_nodes_inputs);
static Vec_Wec_t* LSV_combineInputsVec(Vec_Wec_t** p, int size);
static void LSV_printMOCuts(Vec_Wec_t* p);
static Vec_Wec_t* LSV_filterMOCuts(Vec_Wec_t* p);

// Function additions for vectors of int 

static inline void Vec_WecPush_vecint(Vec_Wec_t* p, Vec_Int_t* a);
static inline int Vec_WecCompare(Vec_Wec_t* p, Vec_Int_t* a);
static Vec_Wec_t* Vec_WecRemoveSizeOver(Vec_Wec_t* p, int size);
static inline void Vec_WecPrint_multiples(Vec_Wec_t** p, int size);

void init_moc(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocut", LSV_MOCuts_init, 0);
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

/// @brief 
/// @param p 
static inline void Vec_WecPrint_multiples(Vec_Wec_t** p, int size) {
  for (int i=0; i<size; i++) {
    printf("Node %d :\n", i);
    Vec_WecPrint(p[i], 0);
  }
}



int LSV_MOCuts_init(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c;
  int K, L;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "hds")) != EOF) {
    switch (c) {
      case 'd':
        goto debug;
      case 's':
        goto stats;
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
  if (!LSV_MOCuts(pNtk, K, L, 0)) {
    Abc_Print(-1, "The multi-output cut computation failed.\n");
    return 1;
  }
  return 1;

debug:
  if (!LSV_MOCuts(pNtk, K, L, 1)) {
    Abc_Print(-1, "The multi-output cut computation failed.\n");
    return 1;
  }
  return 1;

stats:
  LSV_printDebug(pNtk);
  return 1;

usage:
  Abc_Print(-2, "usage: lsv_printmocut <k> <l> [-h]\n");
  Abc_Print(-2, "\t          prints the nodes in the network\n");
  Abc_Print(-2, "\t<k>     : maximum number of nodes in a cut (2 < k < 7)\n");
  Abc_Print(-2, "\t<l>     : minimum number of output nodes of a cut (0 < l < 5)\n");
  Abc_Print(-2, "\t-d      : debug mode\n");
  Abc_Print(-2, "\t-s      : stats mode, show a few important informations about the circuit\n");
  Abc_Print(-2, "\t-h      : print the command usage\n");
  return 1;
}

static Vec_Wec_t* LSV_computeNodeInputs(Abc_Ntk_t* pNtk, Abc_Obj_t * pNode, int max_input) {
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
        if (Vec_IntSize(next_input_set)>0 and Vec_IntSize(next_input_set)<(2*max_input)) {
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
  return final_node_inputs;
}

static int LSV_printDebug(Abc_Ntk_t* pNtk) {
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
      Vec_Wec_t* pNode_inputs = LSV_computeNodeInputs(pNtk, pObj, 3);
      Vec_WecPrint(pNode_inputs, 0);
    }
    Abc_Print(1, "------------------%d------------------\n\n", i);
  }
  return 1;
}

static int LSV_MOCuts(Abc_Ntk_t* pNtk, int max_inputs, int min_outputs, int debug) {
  // First part, create the nodes combination of inputs vectors
  Vec_Wec_t* all_inputs_nodes[Abc_NtkNodeNum(pNtk)];
  int offset = Abc_NtkPiNum(pNtk) + Abc_NtkPoNum(pNtk) + 1;
  int total_nodes = Abc_NtkObjNum(pNtk);
  int shared_index = offset;
  pthread_mutex_t shared_mutex = PTHREAD_MUTEX_INITIALIZER;
  pthread_t threads[NUM_THREADS];
  ThreadArgs_t thread_args[NUM_THREADS];
  for (int t = 0; t < NUM_THREADS; t++) {
    thread_args[t].pNtk = pNtk;
    thread_args[t].all_inputs_nodes = all_inputs_nodes;
    thread_args[t].offset = offset;
    thread_args[t].max_input = max_inputs;
    thread_args[t].total_nodes = total_nodes;
    thread_args[t].shared_index = &shared_index;
    thread_args[t].shared_mutex = &shared_mutex;
    pthread_create(&threads[t], NULL, compute_inputs_worker, &thread_args[t]);
  }
  for (int t = 0; t < NUM_THREADS; t++) {
    pthread_join(threads[t], NULL);
  }
  if (debug) {Vec_WecPrint_multiples(all_inputs_nodes, Abc_NtkNodeNum(pNtk));}
  Vec_Wec_t* combined_unique_inputs = LSV_combineInputsVec(all_inputs_nodes, Abc_NtkNodeNum(pNtk));
  if (debug) {
    Abc_Print(1, "Combined Vector of all inputs : \n");
    Vec_WecPrint(combined_unique_inputs, 0);
  }
  // Second part, computes all of the multiple outputs
  Vec_Wec_t* unfiltered_mocuts = Vec_WecStart(0);
  for (int i=0; i<Vec_WecSize(combined_unique_inputs); i++) {
    Vec_Int_t* current_inputs = Vec_WecEntry(combined_unique_inputs, i);
    Vec_Int_t* modified_current_inputs = Vec_IntDup(current_inputs);
    int number_outputs = 0;
    for (int j=0; j<Abc_NtkNodeNum(pNtk); j++) {
      if (Vec_WecCompare(all_inputs_nodes[j], current_inputs)==1) {
        number_outputs++;
        Vec_IntPush(modified_current_inputs, j+offset);
      }
    }
    if (number_outputs>=min_outputs) {
      Vec_IntPushFirst(modified_current_inputs, number_outputs);
      Vec_IntPushFirst(modified_current_inputs, Vec_IntSize(current_inputs));
      Vec_WecPush_vecint(unfiltered_mocuts, modified_current_inputs);
    }
  }
  Vec_WecFreeP(&combined_unique_inputs);
  if (debug) {
    Abc_Print(1, "Unfiltered multi-output cuts : \n");
    LSV_printMOCuts(unfiltered_mocuts);
  }
  // Third part, filtering of the subsets of cuts
  Vec_Wec_t* filtered_mocuts = LSV_filterMOCuts(unfiltered_mocuts);

  // Finalisation, printing of the multi-output cuts
  if (debug) {
    Abc_Print(1, "Filtered multi-output cuts : \n");
  }
  LSV_printMOCuts(filtered_mocuts);
  return 1;
}

static Vec_Wec_t* LSV_combineInputsVec(Vec_Wec_t** p, int size) {
  Vec_Wec_t* comb = Vec_WecStart(0);
  for (int i=0; i<size; i++) {
    Vec_Wec_t* current_node = p[i];
    for (int j=0; j<Vec_WecSize(current_node);j++) {
      if (Vec_WecCompare(comb, Vec_WecEntry(current_node, j))==-1) {
        Vec_WecPush_vecint(comb, Vec_WecEntry(current_node, j));
      }
    }
  }
  return comb;
}

static void LSV_printMOCuts(Vec_Wec_t* p) {
  for (int i=0; i<Vec_WecSize(p); i++) {
    Vec_Int_t* cut = Vec_WecEntry(p, i);
    for (int input=0; input<Vec_IntEntry(cut,0); input++) {
      Abc_Print(1, "%d ", Vec_IntEntry(cut, input+2));
    }
    Abc_Print(1, ": ");
    for (int output=0; output<Vec_IntEntry(cut,1); output++) {
      Abc_Print(1, "%d ", Vec_IntEntry(cut, Vec_IntEntry(cut,0)+output+2));
    }
    Abc_Print(1, "\n");
  }
}

void* compute_inputs_worker(void* arg) {
  ThreadArgs_t* args = (ThreadArgs_t*)arg;
  int local_idx;
  while (1) {
    pthread_mutex_lock(args->shared_mutex);
    if (*(args->shared_index) >= args->total_nodes) {
      pthread_mutex_unlock(args->shared_mutex);
      break;
    }
    local_idx = *(args->shared_index);
    (*(args->shared_index))++;
    pthread_mutex_unlock(args->shared_mutex);
    Abc_Obj_t* pNode = Abc_NtkObj(args->pNtk, local_idx);
    if (!Abc_ObjIsNode(pNode)) continue;
    args->all_inputs_nodes[local_idx - args->offset] =
        LSV_computeNodeInputs(args->pNtk, pNode, args->max_input);
  }
  return NULL;
}

static Vec_Wec_t* LSV_filterMOCuts(Vec_Wec_t* p) {
  Vec_Wec_t* filtered = Vec_WecStart(0);
  Vec_Wec_t* filtered_outputs = Vec_WecStart(0);
  for (int i=0; i<Vec_WecSize(p); i++) {
    int is_valid = 1;
    Vec_Int_t* a = Vec_WecEntry(p,i);
    Vec_Int_t* a_outputs = Vec_IntDup(a);
    Vec_IntRemove(a_outputs, Vec_IntEntry(a, 0));
    Vec_IntRemove(a_outputs, Vec_IntEntry(a, 1));
    for (int j=0; j<Vec_IntEntry(a,0); j++) {
      Vec_IntRemove(a_outputs, Vec_IntEntry(a, j+2));
    }
    for (int j=i+1; j<Vec_WecSize(p); j++) {
      Vec_Int_t* b = Vec_WecEntry(p,j);
      Vec_Int_t* b_outputs = Vec_IntDup(b);
      Vec_IntRemove(b_outputs, Vec_IntEntry(b, 0));
      Vec_IntRemove(b_outputs, Vec_IntEntry(b, 1));
      for (int k=0; k<Vec_IntEntry(b,0); k++) {
        Vec_IntRemove(b_outputs, Vec_IntEntry(b, k+2));
      }
      if (Vec_IntEqual(a_outputs,b_outputs)==0) {
        break;
      }
      if (Vec_IntEntry(a,1+Vec_IntEntry(a,0)) < Vec_IntEntry(b,1+Vec_IntEntry(b,0))) {
        is_valid = 0;
        break;
      } else if (Vec_IntEntry(a,1+Vec_IntEntry(a,0)) == Vec_IntEntry(b,1+Vec_IntEntry(b,0))) {
        if (Vec_IntEntry(a,0) > Vec_IntEntry(b,0)) {
          is_valid = 0;
          break;
        }
      }
    }
    if (is_valid and Vec_WecCompare(filtered_outputs, a_outputs)==-1) {
      Vec_WecPush_vecint(filtered, a);
      Vec_WecPush_vecint(filtered_outputs, a_outputs);
    }
  }
  return filtered;
}
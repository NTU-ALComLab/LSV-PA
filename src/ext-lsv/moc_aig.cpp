#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

static int Lsv_PrintMOCuts(Abc_Frame_t* pAbc, int argc, char** argv);

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
  return 1;

usage:
  Abc_Print(-2, "usage: lsv_printmocut <k> <l> [-h]\n");
  Abc_Print(-2, "\t          prints the nodes in the network\n");
  Abc_Print(-2, "\t<k>     : maximum number of nodes in a cut (2 < k < 7)\n");
  Abc_Print(-2, "\t<l>     : minimum number of output nodes of a cut (0 < l < 5)\n");
  Abc_Print(-2, "\t-h      : print the command usage\n");
  return 1;
}
#include <stdint.h>
#include <algorithm>
#include <iterator>
#include <set>
#include <vector>
#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "aig/aig/aig.h"

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandCutTT(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandCutBDDsize(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_cut_tt", Lsv_CommandCutTT, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_cut_bddsize", Lsv_CommandCutBDDsize, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

// ---------------------------------------------------------------
// lsv_print_nodes
// ---------------------------------------------------------------
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

// ---------------------------------------------------------------
// programming assignment 1
// ---------------------------------------------------------------
typedef std::vector<int> Lsv_Cut;
typedef std::vector<Lsv_Cut> Lsv_Cuts;
typedef std::vector<Lsv_Cuts> Lsv_NodeCuts;

static Lsv_NodeCuts Lsv_EnumerateCuts(Abc_Ntk_t* pNtk, int k){
  Lsv_NodeCuts cuts(Abc_NtkObjNumMax(pNtk));

  Abc_Obj_t* pObj;
  int i;

  // Constant-1 node has the empty cut.
  Abc_Obj_t* pConst1 = Abc_AigConst1(pNtk);
  cuts[Abc_ObjId(pConst1)].push_back(Lsv_Cut());

  // Each CI has its trivial cut {itself}.
  Abc_NtkForEachCi(pNtk, pObj, i){
    int id = Abc_ObjId(pObj);
    cuts[id].push_back(Lsv_Cut(1, id));
  }

  // Since pNtk is strashed, each internal node is an AIG AND node.
  Abc_AigForEachAnd(pNtk, pObj, i){
    int nodeId = Abc_ObjId(pObj);
    Lsv_Cuts& nodeCuts = cuts[nodeId];

    // Trivial cut {node itself}
    nodeCuts.push_back(Lsv_Cut(1, nodeId));

    std::set<Lsv_Cut> seen;
    seen.insert(nodeCuts.front());

    int fanin0Id = Abc_ObjId(Abc_ObjFanin0(pObj));
    int fanin1Id = Abc_ObjId(Abc_ObjFanin1(pObj));

    const Lsv_Cuts& left  = cuts[fanin0Id];
    const Lsv_Cuts& right = cuts[fanin1Id];

    for(size_t a = 0; a < left.size(); ++a){
      for(size_t b = 0; b < right.size(); ++b){
        Lsv_Cut merged;
        std::set_union(left[a].begin(), left[a].end(), right[b].begin(), right[b].end(),std::back_inserter(merged));

        if(merged.size() <= static_cast<size_t>(k) && seen.insert(merged).second){
          nodeCuts.push_back(merged);
        }
      }
    }
  }
  return cuts;
}

static bool Lsv_CheckCutArgs(Abc_Ntk_t* pNtk, int argc, char** argv, int& k){
  char* end = NULL;
  long value = argc == 2 ? strtol(argv[1], &end, 10) : 0;
  if(argc != 2 || end == argv[1] || *end != '\0' || value < 2 || value > 6){
    Abc_Print(-1, "usage: %s <k> (2 <= k <= 6)\n", argv[0]);
    return false;
  }
  if(!pNtk || !Abc_NtkIsStrash(pNtk)){
    Abc_Print(-1, "Read a network and run strash first.\n");
    return false;
  }
  k = static_cast<int>(value);
  return true;
}

static int Lsv_FindLeafIndex(int nodeId, const int leafIds[], int nLeaves){
  for(int i = 0; i < nLeaves; i++){
    if(leafIds[i] == nodeId)
      return i;
  }
  return -1;
}

// ---------------------------------------------------------------
// lsv_cut_tt
// ---------------------------------------------------------------
static int Lsv_EvalCut_rec(Abc_Obj_t* pObj, const int leafIds[], int nLeaves, int assignment){
  int nodeId = Abc_ObjId(pObj);
  int leafIndex = Lsv_FindLeafIndex(nodeId, leafIds, nLeaves);

  if(leafIndex != -1){
    return (assignment >> (nLeaves - 1 - leafIndex)) & 1;
  }

  // Constant-1
  if(pObj == Abc_AigConst1(Abc_ObjNtk(pObj)))
    return 1;

  int value0 = Lsv_EvalCut_rec(
    Abc_ObjFanin0(pObj),
    leafIds,
    nLeaves,
    assignment
  );

  int value1 = Lsv_EvalCut_rec(
    Abc_ObjFanin1(pObj),
    leafIds,
    nLeaves,
    assignment
  );

  if(Abc_ObjFaninC0(pObj))
    value0 = !value0;

  if(Abc_ObjFaninC1(pObj))
    value1 = !value1;

  return value0 & value1;
}

static uint64_t Lsv_BuildTruthTable(Abc_Obj_t* pRoot, const int leafIds[], int nLeaves){
  uint64_t truth = 0;
  int nAssignments = 1 << nLeaves;
  for(int assignment = 0; assignment < nAssignments; assignment++){
    int output = Lsv_EvalCut_rec(pRoot, leafIds, nLeaves, assignment);
    if(output){
      truth |= ((uint64_t)1 << assignment);
    }
  }
  return truth;
}

void Lsv_KCut(Abc_Ntk_t* pNtk, int k){
  Lsv_NodeCuts cuts = Lsv_EnumerateCuts(pNtk, k);
  Abc_Obj_t* pObj;
  int i;
  Abc_AigForEachAnd(pNtk, pObj, i){
    int nodeId = Abc_ObjId(pObj);
    const Lsv_Cuts& nodeCuts = cuts[nodeId];
    for(size_t j = 0; j < nodeCuts.size(); ++j){
      const Lsv_Cut& cut = nodeCuts[j];
      const int* leafIds = cut.empty() ? NULL : &cut[0];
      uint64_t truth = Lsv_BuildTruthTable(pObj, leafIds, cut.size());

      // ORIGINAL ABC OBJECT ID
      printf("%d: ", Abc_ObjId(pObj));
      for(size_t m = 0; m < cut.size(); ++m){
        printf("%s%d", m ? " " : "",cut[m]);
      }

      printf(": %llX\n", (unsigned long long)truth);
    }
  }
}

int Lsv_CommandCutTT(Abc_Frame_t* pAbc, int argc, char** argv){
  int k;
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  if (!Lsv_CheckCutArgs(pNtk, argc, argv, k)) return 1;
  Lsv_KCut(pNtk, k);
  return 0;
}

// ---------------------------------------------------------------
// lsv_cut_bddsize
// ---------------------------------------------------------------
static DdNode* Lsb_BuildCutBDD(DdManager* dd, Abc_Obj_t* pObj, const int* leafIds, int nLeaves){
  int nodeId = Abc_ObjId(pObj);
  int leafIndex = Lsv_FindLeafIndex(nodeId, leafIds, nLeaves);
  if(leafIndex != -1){
    DdNode* var = Cudd_bddIthVar(dd, leafIndex);
    Cudd_Ref(var);
    return var;
  }

  // Constant-1
  if(pObj == Abc_AigConst1(Abc_ObjNtk(pObj))){
    DdNode* one = Cudd_ReadOne(dd);
    Cudd_Ref(one);
    return one;
  }

  DdNode* bdd0 = Lsb_BuildCutBDD(dd, Abc_ObjFanin0(pObj), leafIds, nLeaves);

  if(bdd0 == NULL)
    return NULL;

  DdNode* bdd1 = Lsb_BuildCutBDD(dd, Abc_ObjFanin1(pObj), leafIds, nLeaves);

  if(bdd1 == NULL) {
    Cudd_RecursiveDeref(dd, bdd0);
    return NULL;
  }

  DdNode* input0 = Abc_ObjFaninC0(pObj) ? Cudd_Not(bdd0) : bdd0;
  DdNode* input1 = Abc_ObjFaninC1(pObj) ? Cudd_Not(bdd1) : bdd1;
  DdNode* result = Cudd_bddAnd( dd, input0, input1);

  if(result == NULL){
    Cudd_RecursiveDeref(dd, bdd0);
    Cudd_RecursiveDeref(dd, bdd1);
    return NULL;
  }

  Cudd_Ref(result);
  Cudd_RecursiveDeref(dd, bdd0);
  Cudd_RecursiveDeref(dd, bdd1);
  return result;
}

void Lsv_CountBDDsize(Abc_Ntk_t* pNtk, int k){
  Lsv_NodeCuts cuts = Lsv_EnumerateCuts(pNtk, k);
  DdManager* dd = Cudd_Init(k, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);

  Abc_Obj_t* pObj;
  int i;
  Abc_AigForEachAnd(pNtk, pObj, i){
    int nodeId = Abc_ObjId(pObj);
    const Lsv_Cuts& nodeCuts = cuts[nodeId];
    for(size_t j = 0; j < nodeCuts.size(); ++j){
      const Lsv_Cut& cut = nodeCuts[j];
      const int* leafIds = cut.empty() ? NULL : &cut[0];
      DdNode* bdd = Lsb_BuildCutBDD(dd, pObj, leafIds, cut.size());
      printf("%d: ",Abc_ObjId(pObj));
      for(size_t m = 0; m < cut.size(); ++m){
        printf("%s%d", m ? " " : "", cut[m]);
      }
      printf(": %d\n", Cudd_DagSize(bdd));
      Cudd_RecursiveDeref(dd, bdd);
    }
  }
  Cudd_Quit(dd);
}

int Lsv_CommandCutBDDsize(Abc_Frame_t* pAbc, int argc, char** argv){
  int k;
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  if(!Lsv_CheckCutArgs(pNtk, argc, argv, k)) 
    return 1;
  Lsv_CountBDDsize(pNtk, k);
  return 0;
}
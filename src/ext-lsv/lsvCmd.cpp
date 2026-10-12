#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "bdd/cudd/cudd.h"

#include <cerrno>
#include <climits>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>

typedef struct Lsv_Cut_t_ {
  int nLeaves;
  int* pLeaves;
} Lsv_Cut_t;

typedef struct Lsv_CutList_t_ {
  int nCuts;
  int nCapacity;
  Lsv_Cut_t* pCuts;
} Lsv_CutList_t;

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandCut(Abc_Frame_t* pAbc, int argc, char** argv);

static void Lsv_CutListInit(Lsv_CutList_t* pList);
static void Lsv_CutListFree(Lsv_CutList_t* pList);
static void Lsv_CutListGrow(Lsv_CutList_t* pList);
static int Lsv_CutIsSubset(const int* pSmall, int nSmall,
                           const int* pLarge, int nLarge);
static void Lsv_CutListAdd(Lsv_CutList_t* pList,
                           const int* pLeaves, int nLeaves);
static int Lsv_CutMerge(const Lsv_Cut_t* pCut0,
                        const Lsv_Cut_t* pCut1,
                        int k, int* pMerged);
static Lsv_CutList_t* Lsv_EnumerateCuts(Abc_Ntk_t* pNtk, int k);
static void Lsv_FreeAllCuts(Lsv_CutList_t* pCutLists, int nObjects);

static int Lsv_CutFindLeaf(const Lsv_Cut_t* pCut, int objId);
static int Lsv_EvalCut_rec(Abc_Ntk_t* pNtk, Abc_Obj_t* pObj,
                           const Lsv_Cut_t* pCut,
                           unsigned assignment, int* pValues);
static uint64_t Lsv_ComputeCutTruth(Abc_Ntk_t* pNtk,
                                    Abc_Obj_t* pRoot,
                                    const Lsv_Cut_t* pCut);
static void Lsv_PrintCutPrefix(Abc_Obj_t* pRoot,
                               const Lsv_Cut_t* pCut);
static void Lsv_PrintCutTruthTables(Abc_Ntk_t* pNtk, int k);

static DdNode* Lsv_BuildBdd_rec(DdManager* pDd, uint64_t truth,
                                int nRemaining, int variableIndex);
static int Lsv_TruthBddSize(uint64_t truth, int nVariables);
static void Lsv_PrintCutBddSizes(Abc_Ntk_t* pNtk, int k);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv", Lsv_CommandCut, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes",
                 Lsv_CommandPrintNodes, 0);
}

void destroy(Abc_Frame_t* pAbc) {
  (void)pAbc;
}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() {
    Abc_FrameAddInitializer(&frame_initializer);
  }
} lsvPackageRegistrationManager;

static void Lsv_CutListInit(Lsv_CutList_t* pList) {
  pList->nCuts = 0;
  pList->nCapacity = 0;
  pList->pCuts = NULL;
}

static void Lsv_CutListFree(Lsv_CutList_t* pList) {
  int i;

  for (i = 0; i < pList->nCuts; ++i) {
    free(pList->pCuts[i].pLeaves);
  }
  free(pList->pCuts);

  pList->nCuts = 0;
  pList->nCapacity = 0;
  pList->pCuts = NULL;
}

static void Lsv_CutListGrow(Lsv_CutList_t* pList) {
  Lsv_Cut_t* pNewCuts;
  int newCapacity;

  if (pList->nCuts < pList->nCapacity) {
    return;
  }

  newCapacity = pList->nCapacity == 0 ? 4 : 2 * pList->nCapacity;
  pNewCuts = static_cast<Lsv_Cut_t*>(
      realloc(pList->pCuts, sizeof(Lsv_Cut_t) * newCapacity));

  if (pNewCuts == NULL) {
    fprintf(stderr, "Out of memory while growing a cut list.\n");
    exit(1);
  }

  pList->pCuts = pNewCuts;
  pList->nCapacity = newCapacity;
}

/* Both arrays must be sorted in ascending order. */
static int Lsv_CutIsSubset(const int* pSmall, int nSmall,
                           const int* pLarge, int nLarge) {
  int i = 0;
  int j = 0;

  if (nSmall > nLarge) {
    return 0;
  }

  while (i < nSmall && j < nLarge) {
    if (pSmall[i] == pLarge[j]) {
      ++i;
      ++j;
    } else if (pSmall[i] > pLarge[j]) {
      ++j;
    } else {
      return 0;
    }
  }

  return i == nSmall;
}

/*
 * Adds a cut while removing duplicates and dominated cuts.
 * No ABC cut package or cut-specific API is used here.
 */
static void Lsv_CutListAdd(Lsv_CutList_t* pList,
                           const int* pLeaves, int nLeaves) {
  int i;
  int j;
  Lsv_Cut_t* pNew;

  /* An existing subset makes the candidate duplicate or dominated. */
  for (i = 0; i < pList->nCuts; ++i) {
    if (Lsv_CutIsSubset(pList->pCuts[i].pLeaves,
                        pList->pCuts[i].nLeaves,
                        pLeaves, nLeaves)) {
      return;
    }
  }

  /* The candidate may dominate cuts that were inserted earlier. */
  i = 0;
  while (i < pList->nCuts) {
    if (Lsv_CutIsSubset(pLeaves, nLeaves,
                        pList->pCuts[i].pLeaves,
                        pList->pCuts[i].nLeaves)) {
      free(pList->pCuts[i].pLeaves);
      for (j = i; j + 1 < pList->nCuts; ++j) {
        pList->pCuts[j] = pList->pCuts[j + 1];
      }
      --pList->nCuts;
      continue;
    }
    ++i;
  }

  Lsv_CutListGrow(pList);
  pNew = &pList->pCuts[pList->nCuts++];
  pNew->nLeaves = nLeaves;
  pNew->pLeaves = NULL;

  if (nLeaves > 0) {
    pNew->pLeaves = static_cast<int*>(malloc(sizeof(int) * nLeaves));
    if (pNew->pLeaves == NULL) {
      fprintf(stderr, "Out of memory while storing a cut.\n");
      exit(1);
    }
    memcpy(pNew->pLeaves, pLeaves, sizeof(int) * nLeaves);
  }
}

/* Returns the merged cut size, or -1 if the union has more than k leaves. */
static int Lsv_CutMerge(const Lsv_Cut_t* pCut0,
                        const Lsv_Cut_t* pCut1,
                        int k, int* pMerged) {
  int i = 0;
  int j = 0;
  int nMerged = 0;
  int leaf;

  while (i < pCut0->nLeaves || j < pCut1->nLeaves) {
    if (j == pCut1->nLeaves ||
        (i < pCut0->nLeaves && pCut0->pLeaves[i] < pCut1->pLeaves[j])) {
      leaf = pCut0->pLeaves[i++];
    } else if (i == pCut0->nLeaves ||
               pCut1->pLeaves[j] < pCut0->pLeaves[i]) {
      leaf = pCut1->pLeaves[j++];
    } else {
      leaf = pCut0->pLeaves[i];
      ++i;
      ++j;
    }

    if (nMerged >= k) {
      return -1;
    }
    pMerged[nMerged++] = leaf;
  }

  return nMerged;
}

static Lsv_CutList_t* Lsv_EnumerateCuts(Abc_Ntk_t* pNtk, int k) {
  const int nObjects = Abc_NtkObjNumMax(pNtk);
  Lsv_CutList_t* pCutLists;
  Abc_Obj_t* pObj;
  Abc_Obj_t* pFanin0;
  Abc_Obj_t* pFanin1;
  Abc_Obj_t* pConst1;
  int* pMerged;
  int objectIndex;
  int cutIndex0;
  int cutIndex1;
  int id;
  int nMerged;

  pCutLists = static_cast<Lsv_CutList_t*>(
      malloc(sizeof(Lsv_CutList_t) * nObjects));
  pMerged = static_cast<int*>(malloc(sizeof(int) * k));

  if (pCutLists == NULL || pMerged == NULL) {
    fprintf(stderr, "Out of memory while enumerating cuts.\n");
    free(pCutLists);
    free(pMerged);
    return NULL;
  }

  for (id = 0; id < nObjects; ++id) {
    Lsv_CutListInit(&pCutLists[id]);
  }

  /* The constant-one AIG object has the empty cut. */
  pConst1 = Abc_AigConst1(pNtk);
  if (pConst1 != NULL) {
    Lsv_CutListAdd(&pCutLists[Abc_ObjId(pConst1)], NULL, 0);
  }

  /* Every PI starts with its elementary cut {PI}. */
  Abc_NtkForEachPi(pNtk, pObj, objectIndex) {
    id = Abc_ObjId(pObj);
    Lsv_CutListAdd(&pCutLists[id], &id, 1);
  }

  /* AIG nodes are visited in topological order. */
  Abc_NtkForEachNode(pNtk, pObj, objectIndex) {
    id = Abc_ObjId(pObj);

    /* The trivial cut is always included. */
    Lsv_CutListAdd(&pCutLists[id], &id, 1);

    pFanin0 = Abc_ObjFanin0(pObj);
    pFanin1 = Abc_ObjFanin1(pObj);

    for (cutIndex0 = 0;
         cutIndex0 < pCutLists[Abc_ObjId(pFanin0)].nCuts;
         ++cutIndex0) {
      for (cutIndex1 = 0;
           cutIndex1 < pCutLists[Abc_ObjId(pFanin1)].nCuts;
           ++cutIndex1) {
        nMerged = Lsv_CutMerge(
            &pCutLists[Abc_ObjId(pFanin0)].pCuts[cutIndex0],
            &pCutLists[Abc_ObjId(pFanin1)].pCuts[cutIndex1],
            k, pMerged);

        if (nMerged >= 0) {
          Lsv_CutListAdd(&pCutLists[id], pMerged, nMerged);
        }
      }
    }
  }

  free(pMerged);
  return pCutLists;
}

static void Lsv_FreeAllCuts(Lsv_CutList_t* pCutLists, int nObjects) {
  int id;

  if (pCutLists == NULL) {
    return;
  }

  for (id = 0; id < nObjects; ++id) {
    Lsv_CutListFree(&pCutLists[id]);
  }
  free(pCutLists);
}

static int Lsv_CutFindLeaf(const Lsv_Cut_t* pCut, int objId) {
  int low = 0;
  int high = pCut->nLeaves - 1;

  while (low <= high) {
    int middle = low + (high - low) / 2;
    if (pCut->pLeaves[middle] == objId) {
      return middle;
    }
    if (pCut->pLeaves[middle] < objId) {
      low = middle + 1;
    } else {
      high = middle - 1;
    }
  }

  return -1;
}

static int Lsv_EvalCut_rec(Abc_Ntk_t* pNtk, Abc_Obj_t* pObj,
                           const Lsv_Cut_t* pCut,
                           unsigned assignment, int* pValues) {
  const int objId = Abc_ObjId(pObj);
  const int leafPosition = Lsv_CutFindLeaf(pCut, objId);
  int value0;
  int value1;

  if (leafPosition >= 0) {
    /* The smallest leaf ID is the leftmost (most significant) input. */
    return (assignment >> (pCut->nLeaves - 1 - leafPosition)) & 1U;
  }

  if (pValues[objId] >= 0) {
    return pValues[objId];
  }

  if (pObj == Abc_AigConst1(pNtk)) {
    pValues[objId] = 1;
    return 1;
  }

  /* A valid cut should stop every path before an unlisted PI is reached. */
  if (Abc_ObjIsPi(pObj)) {
    pValues[objId] = 0;
    return 0;
  }

  value0 = Lsv_EvalCut_rec(pNtk, Abc_ObjFanin0(pObj),
                           pCut, assignment, pValues);
  value1 = Lsv_EvalCut_rec(pNtk, Abc_ObjFanin1(pObj),
                           pCut, assignment, pValues);

  if (Abc_ObjFaninC0(pObj)) {
    value0 = !value0;
  }
  if (Abc_ObjFaninC1(pObj)) {
    value1 = !value1;
  }

  pValues[objId] = value0 & value1;
  return pValues[objId];
}

static uint64_t Lsv_ComputeCutTruth(Abc_Ntk_t* pNtk,
                                    Abc_Obj_t* pRoot,
                                    const Lsv_Cut_t* pCut) {
  const int nObjects = Abc_NtkObjNumMax(pNtk);
  const unsigned nAssignments = 1U << pCut->nLeaves;
  int* pValues = static_cast<int*>(malloc(sizeof(int) * nObjects));
  uint64_t truth = 0;
  unsigned assignment;

  if (pValues == NULL) {
    fprintf(stderr, "Out of memory while computing a truth table.\n");
    exit(1);
  }

  for (assignment = 0; assignment < nAssignments; ++assignment) {
    memset(pValues, 0xFF, sizeof(int) * nObjects);
    if (Lsv_EvalCut_rec(pNtk, pRoot, pCut, assignment, pValues)) {
      truth |= UINT64_C(1) << assignment;
    }
  }

  free(pValues);
  return truth;
}

static void Lsv_PrintCutPrefix(Abc_Obj_t* pRoot,
                               const Lsv_Cut_t* pCut) {
  int leafIndex;

  printf("%d:", Abc_ObjId(pRoot));
  for (leafIndex = 0; leafIndex < pCut->nLeaves; ++leafIndex) {
    printf(" %d", pCut->pLeaves[leafIndex]);
  }
  printf(": ");
}

static void Lsv_PrintCutTruthTables(Abc_Ntk_t* pNtk, int k) {
  const int nObjects = Abc_NtkObjNumMax(pNtk);
  Lsv_CutList_t* pCutLists = Lsv_EnumerateCuts(pNtk, k);
  Abc_Obj_t* pObj;
  int objectIndex;
  int cutIndex;

  if (pCutLists == NULL) {
    return;
  }

  Abc_NtkForEachNode(pNtk, pObj, objectIndex) {
    Lsv_CutList_t* pList = &pCutLists[Abc_ObjId(pObj)];
    for (cutIndex = 0; cutIndex < pList->nCuts; ++cutIndex) {
      uint64_t truth = Lsv_ComputeCutTruth(pNtk, pObj,
                                           &pList->pCuts[cutIndex]);
      Lsv_PrintCutPrefix(pObj, &pList->pCuts[cutIndex]);
      printf("%llX\n", static_cast<unsigned long long>(truth));
    }
  }

  Lsv_FreeAllCuts(pCutLists, nObjects);
}

/*
 * Builds a BDD directly from our truth table by Shannon expansion.
 * variableIndex increases with the sorted leaf order, so smaller node IDs
 * are tested closer to the BDD root.
 */
static DdNode* Lsv_BuildBdd_rec(DdManager* pDd, uint64_t truth,
                                int nRemaining, int variableIndex) {
  DdNode* pLow;
  DdNode* pHigh;
  DdNode* pResult;
  DdNode* pVariable;
  unsigned halfAssignments;
  uint64_t mask;
  uint64_t lowTruth;
  uint64_t highTruth;

  if (nRemaining == 0) {
    pResult = (truth & UINT64_C(1))
                  ? Cudd_ReadOne(pDd)
                  : Cudd_ReadLogicZero(pDd);
    Cudd_Ref(pResult);
    return pResult;
  }

  halfAssignments = 1U << (nRemaining - 1);
  mask = (UINT64_C(1) << halfAssignments) - UINT64_C(1);
  lowTruth = truth & mask;
  highTruth = (truth >> halfAssignments) & mask;

  pLow = Lsv_BuildBdd_rec(pDd, lowTruth,
                           nRemaining - 1, variableIndex + 1);
  pHigh = Lsv_BuildBdd_rec(pDd, highTruth,
                            nRemaining - 1, variableIndex + 1);
  pVariable = Cudd_bddIthVar(pDd, variableIndex);

  pResult = Cudd_bddIte(pDd, pVariable, pHigh, pLow);
  if (pResult == NULL) {
    Cudd_RecursiveDeref(pDd, pLow);
    Cudd_RecursiveDeref(pDd, pHigh);
    return NULL;
  }

  Cudd_Ref(pResult);
  Cudd_RecursiveDeref(pDd, pLow);
  Cudd_RecursiveDeref(pDd, pHigh);
  return pResult;
}

static int Lsv_TruthBddSize(uint64_t truth, int nVariables) {
  DdManager* pDd;
  DdNode* pRoot;
  int size;

  pDd = Cudd_Init(nVariables, 0,
                  CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);
  if (pDd == NULL) {
    fprintf(stderr, "Could not initialize CUDD.\n");
    return -1;
  }

  pRoot = Lsv_BuildBdd_rec(pDd, truth, nVariables, 0);
  if (pRoot == NULL) {
    Cudd_Quit(pDd);
    fprintf(stderr, "Could not build a BDD.\n");
    return -1;
  }

  size = Cudd_DagSize(pRoot);
  Cudd_RecursiveDeref(pDd, pRoot);
  Cudd_Quit(pDd);
  return size;
}

static void Lsv_PrintCutBddSizes(Abc_Ntk_t* pNtk, int k) {
  const int nObjects = Abc_NtkObjNumMax(pNtk);
  Lsv_CutList_t* pCutLists = Lsv_EnumerateCuts(pNtk, k);
  Abc_Obj_t* pObj;
  int objectIndex;
  int cutIndex;

  if (pCutLists == NULL) {
    return;
  }

  Abc_NtkForEachNode(pNtk, pObj, objectIndex) {
    Lsv_CutList_t* pList = &pCutLists[Abc_ObjId(pObj)];
    for (cutIndex = 0; cutIndex < pList->nCuts; ++cutIndex) {
      const Lsv_Cut_t* pCut = &pList->pCuts[cutIndex];
      uint64_t truth = Lsv_ComputeCutTruth(pNtk, pObj, pCut);
      int size = Lsv_TruthBddSize(truth, pCut->nLeaves);

      if (size < 0) {
        Lsv_FreeAllCuts(pCutLists, nObjects);
        return;
      }

      Lsv_PrintCutPrefix(pObj, pCut);
      printf("%d\n", size);
    }
  }

  Lsv_FreeAllCuts(pCutLists, nObjects);
}

void Lsv_NtkPrintNodes(Abc_Ntk_t* pNtk) {
  Abc_Obj_t* pObj;
  int i;

  Abc_NtkForEachNode(pNtk, pObj, i) {
    Abc_Obj_t* pFanin;
    int j;

    printf("Object Id = %d, name = %s\n",
           Abc_ObjId(pObj), Abc_ObjName(pObj));

    Abc_ObjForEachFanin(pObj, pFanin, j) {
      printf("  Fanin-%d: Id = %d, name = %s\n",
             j, Abc_ObjId(pFanin), Abc_ObjName(pFanin));
    }

    if (Abc_NtkHasSop(pNtk)) {
      printf("The SOP of this node:\n%s", (char*)pObj->pData);
    }
  }
}

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc,
                                 int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c;

  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
      case 'h':
      default:
        goto usage;
    }
  }

  if (pNtk == NULL) {
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

static int Lsv_ParseK(const char* pText, int* pK) {
  char* pEnd = NULL;
  long value;

  errno = 0;
  value = strtol(pText, &pEnd, 10);

  if (errno != 0 || pEnd == pText || *pEnd != '\0' ||
      value < 2 || value > 6 || value > INT_MAX) {
    return 0;
  }

  *pK = static_cast<int>(value);
  return 1;
}

static int Lsv_CommandCut(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int k;

  if (argc != 4 || strcmp(argv[1], "cut") != 0 ||
      (strcmp(argv[2], "tt") != 0 &&
       strcmp(argv[2], "bddsize") != 0) ||
      !Lsv_ParseK(argv[3], &k)) {
    goto usage;
  }

  if (pNtk == NULL) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }

  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1,
              "The current network is not a structurally hashed AIG.\n");
    Abc_Print(-1, "Run \"strash\" before this command.\n");
    return 1;
  }

  if (strcmp(argv[2], "tt") == 0) {
    Lsv_PrintCutTruthTables(pNtk, k);
  } else {
    Lsv_PrintCutBddSizes(pNtk, k);
  }

  return 0;

usage:
  Abc_Print(-2, "usage: lsv cut <tt|bddsize> <k>\n");
  Abc_Print(-2, "\ttt       : print hexadecimal cut truth tables\n");
  Abc_Print(-2, "\tbddsize  : print ROBDD sizes using Cudd_DagSize\n");
  Abc_Print(-2, "\tk        : maximum cut size (2 through 6)\n");
  return 1;
}

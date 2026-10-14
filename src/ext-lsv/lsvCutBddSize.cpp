#include "lsvCuts.h"

#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "bdd/cudd/cudd.h"

#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <vector>

static int Lsv_FindCutVariable(
    const Lsv_Cut& cut,
    int nodeId) {
  std::vector<int>::const_iterator it =
      std::lower_bound(
          cut.begin(),
          cut.end(),
          nodeId);

  if (it == cut.end() || *it != nodeId) {
    return -1;
  }

  return static_cast<int>(
      it - cut.begin());
}

static DdNode* Lsv_BddBuildNode(
    DdManager* pDd,
    Abc_Obj_t* pNode,
    const Lsv_Cut& cut,
    const std::vector<DdNode*>& variables);

static DdNode* Lsv_BddBuildLiteral(
    DdManager* pDd,
    Abc_Obj_t* pLiteral,
    const Lsv_Cut& cut,
    const std::vector<DdNode*>& variables) {
  Abc_Obj_t* pRegular =
      Abc_ObjRegular(pLiteral);

  DdNode* result =
      Lsv_BddBuildNode(
          pDd,
          pRegular,
          cut,
          variables);

  if (result == nullptr) {
    return nullptr;
  }

  if (Abc_ObjIsComplement(pLiteral)) {
    DdNode* complemented =
        Cudd_Not(result);

    Cudd_Ref(complemented);
    Cudd_RecursiveDeref(pDd, result);

    return complemented;
  }

  return result;
}

static DdNode* Lsv_BddBuildNode(
    DdManager* pDd,
    Abc_Obj_t* pNode,
    const Lsv_Cut& cut,
    const std::vector<DdNode*>& variables) {
  Abc_Obj_t* pRegular =
      Abc_ObjRegular(pNode);

  int nodeId =
      Abc_ObjId(pRegular);

  // If the node is a cut leaf, it becomes a BDD variable
  int varIndex =
      Lsv_FindCutVariable(cut, nodeId);

  if (varIndex >= 0) {
    DdNode* variable =
        variables[varIndex];

    Cudd_Ref(variable);
    return variable;
  }

  // Constant-one node
  if (pRegular->Type == ABC_OBJ_CONST1) {
    DdNode* one =
        Cudd_ReadOne(pDd);

    Cudd_Ref(one);
    return one;
  }

  // Internal AIG node
  if (Abc_ObjIsNode(pRegular)) {
    if (Abc_ObjFaninNum(pRegular) != 2) {
      DdNode* zero =
          Cudd_ReadLogicZero(pDd);

      Cudd_Ref(zero);
      return zero;
    }

    DdNode* left =
        Lsv_BddBuildLiteral(
            pDd,
            Abc_ObjFanin(pRegular, 0),
            cut,
            variables);

    DdNode* right =
        Lsv_BddBuildLiteral(
            pDd,
            Abc_ObjFanin(pRegular, 1),
            cut,
            variables);

    if (left == nullptr || right == nullptr) {
      if (left != nullptr) {
        Cudd_RecursiveDeref(pDd, left);
      }

      if (right != nullptr) {
        Cudd_RecursiveDeref(pDd, right);
      }

      return nullptr;
    }

    DdNode* result =
        Cudd_bddAnd(
            pDd,
            left,
            right);

    if (result != nullptr) {
      Cudd_Ref(result);
    }

    Cudd_RecursiveDeref(pDd, left);
    Cudd_RecursiveDeref(pDd, right);

    return result;
  }

  // Prevent reaching an unhandled object if valid cut
  DdNode* zero =
      Cudd_ReadLogicZero(pDd);

  Cudd_Ref(zero);
  return zero;
}
static int Lsv_GetCutBddSize(
    Abc_Obj_t* pRoot,
    const Lsv_Cut& cut) {
  DdManager* pDd =
      Cudd_Init(
          static_cast<unsigned>(cut.size()),
          0,
          CUDD_UNIQUE_SLOTS,
          CUDD_CACHE_SLOTS,
          0);

  if (pDd == nullptr) {
    return -1;
  }

  std::vector<DdNode*> variables;
  variables.reserve(cut.size());

  for (unsigned i = 0;
       i < cut.size();
       ++i) {

    // cut[0] has the smallest node ID
    // CUDD variable index 0.
    DdNode* variable =
        Cudd_bddIthVar(
            pDd,
            static_cast<int>(i));

    variables.push_back(variable);
  }

  DdNode* root =
      Lsv_BddBuildNode(
          pDd,
          pRoot,
          cut,
          variables);

  if (root == nullptr) {
    Cudd_Quit(pDd);
    return -1;
  }

  int size =
      Cudd_DagSize(root);

  Cudd_RecursiveDeref(
      pDd,
      root);

  Cudd_Quit(pDd);

  return size;
}
int Lsv_CutBddSize(
    Abc_Frame_t* pAbc,
    int argc,
    char** argv) {
  Abc_Ntk_t* pNtk =
      Abc_FrameReadNtk(pAbc);

  if (pNtk == nullptr) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }

  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(
        -1,
        "The current network is not an AIG. "
        "Run strash first.\n");
    return 1;
  }

  if (argc != 2) {
    Abc_Print(
        -2,
        "usage: lsv_cut_bddsize <k>\n");
    return 1;
  }

  char* end = nullptr;

  long kLong =
      std::strtol(
          argv[1],
          &end,
          10);

  if (end == argv[1] ||
      *end != '\0' ||
      kLong < 1 ||
      kLong > 6) {
    Abc_Print(
        -1,
        "Error: k must be in the range 1..6.\n");
    return 1;
  }

  int k =
      static_cast<int>(kLong);

  int maxObjectId =
      Abc_NtkObjNumMax(pNtk);

  Lsv_AllCuts allCuts(maxObjectId);
  std::vector<char> computed(
      maxObjectId,
      0);

  Abc_Obj_t* pNode;
  int i;

  Abc_NtkForEachNode(
      pNtk,
      pNode,
      i) {
    const Lsv_CutList& cuts =
        Lsv_ComputeCuts(
            pNode,
            k,
            allCuts,
            computed);

    for (const Lsv_Cut& cut : cuts) {
      int bddSize =
          Lsv_GetCutBddSize(
              pNode,
              cut);

      if (bddSize < 0) {
        Abc_Print(
            -1,
            "Could not construct BDD for node %d.\n",
            Abc_ObjId(pNode));

        return 1;
      }

      std::printf(
          "%d:",
          Abc_ObjId(pNode));

      for (int leafId : cut) {
        std::printf(" %d", leafId);
      }

      std::printf(
          ": %d\n",
          bddSize);
    }
  }

  return 0;
}

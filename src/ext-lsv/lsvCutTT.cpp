#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <vector>

#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "bdd/cudd/cudd.h"


typedef std::vector<int> Cut;

static int Lsv_CommandCutTT(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandCutBddSize(Abc_Frame_t* pAbc, int argc, char** argv);

void Lsv_CutTT_Init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_cut_tt", Lsv_CommandCutTT, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_cut_bddsize", Lsv_CommandCutBddSize, 0);
}

// ===========================================================================
// Part 1: finding the cuts
// ===========================================================================

static bool Lsv_MergeCuts(const Cut& a, const Cut& b, int k, Cut& out) {
  out.clear();
  int i = 0;  
  int j = 0;  

  while (i < (int)a.size() && j < (int)b.size()) {
    if (a[i] < b[j]) {        
      out.push_back(a[i]);
      i++;
    } else if (a[i] > b[j]) {  
      out.push_back(b[j]);
      j++;
    } else {                  
      out.push_back(a[i]);
      i++;
      j++;
    }
  }

  while (i < (int)a.size()) {
    out.push_back(a[i]);
    i++;
  }
  while (j < (int)b.size()) {
    out.push_back(b[j]);
    j++;
  }

  if ((int)out.size() <= k) {
    return true;
  } else {
    return false;
  }
}

static bool Lsv_HasCut(const std::vector<Cut>& list, const Cut& c) {
  for (int i = 0; i < (int)list.size(); i++) {
    if (list[i] == c) {
      return true;
    }
  }
  return false;
}

static void Lsv_EnumerateCuts(Abc_Ntk_t* pNtk, int k,
                              std::vector<std::vector<Cut>>& cuts) {

  cuts.clear();
  cuts.resize(Abc_NtkObjNumMax(pNtk));

  Abc_Obj_t* pObj;
  int i;

  Abc_NtkForEachPi(pNtk, pObj, i) {
    int id = Abc_ObjId(pObj);
    Cut self;
    self.push_back(id);
    cuts[id].push_back(self);
  }


  Abc_NtkForEachNode(pNtk, pObj, i) {
    int id = Abc_ObjId(pObj);

    Cut self;
    self.push_back(id);
    cuts[id].push_back(self);

    int leftId = Abc_ObjFaninId0(pObj);
    int rightId = Abc_ObjFaninId1(pObj);

    for (int a = 0; a < (int)cuts[leftId].size(); a++) {
      for (int b = 0; b < (int)cuts[rightId].size(); b++) {
        Cut merged;
        bool fits = Lsv_MergeCuts(cuts[leftId][a], cuts[rightId][b], k, merged);
        if (fits && !Lsv_HasCut(cuts[id], merged)) {
          cuts[id].push_back(merged);
        }
      }
    }
  }
}


static int Lsv_ReadK(Abc_Ntk_t* pNtk, int argc, char** argv,
                     const char* cmdName) {
  if (pNtk == NULL) {
    Abc_Print(-1, "Empty network.\n");
    return -1;
  }
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "Run strash first.\n");
    return -1;
  }
  if (argc != 2) {
    Abc_Print(-2, "usage: %s <k>\n", cmdName);
    return -1;
  }
  int k = atoi(argv[1]);
  if (k < 1 || k > 6) {
    Abc_Print(-1, "k must be between 1 and 6.\n");
    return -1;
  }
  return k;
}

static void Lsv_PrintCutStart(int id, const Cut& c) {
  printf("%d:", id);
  for (int i = 0; i < (int)c.size(); i++) {
    printf(" %d", c[i]);
  }
  printf(": ");
}

// ===========================================================================
// Part 2: truth table (lsv_cut_tt)
// ===========================================================================

static uint64_t Lsv_ComputeTT(Abc_Obj_t* pObj, std::vector<uint64_t>& value,
                              std::vector<int>& known, std::vector<int>& used,
                              uint64_t mask) {
  int id = Abc_ObjId(pObj);

  if (known[id] == 1) {
    return value[id];
  }

  if (Abc_AigNodeIsConst(pObj)) {
    return mask;
  }


  uint64_t left = Lsv_ComputeTT(Abc_ObjFanin0(pObj), value, known, used, mask);
  uint64_t right = Lsv_ComputeTT(Abc_ObjFanin1(pObj), value, known, used, mask);


  if (Abc_ObjFaninC0(pObj)) {
    left = ~left & mask;
  }
  if (Abc_ObjFaninC1(pObj)) {
    right = ~right & mask;
  }

  uint64_t result = left & right;

  value[id] = result;
  known[id] = 1;
  used.push_back(id);
  return result;
}


static uint64_t Lsv_CutTruthTable(Abc_Obj_t* pRoot, const Cut& cut,
                                  std::vector<uint64_t>& value,
                                  std::vector<int>& known,
                                  std::vector<int>& used) {
  int n = (int)cut.size();  

  // Number of rows = 2^n
  int nRows = 1;
  for (int i = 0; i < n; i++) {
    nRows = nRows * 2;
  }


  uint64_t mask;
  if (n == 6) {
    mask = ~0ULL;  
  } else {
    mask = (1ULL << nRows) - 1;
  }

  for (int i = 0; i < n; i++) {
    int bit = n - 1 - i;  
    uint64_t column = 0;
    for (int row = 0; row < nRows; row++) {
      if ((row >> bit) & 1) {  
        column = column | (1ULL << row);
      }
    }
    value[cut[i]] = column;
    known[cut[i]] = 1;
    used.push_back(cut[i]);
  }

  uint64_t result = Lsv_ComputeTT(pRoot, value, known, used, mask);

  for (int i = 0; i < (int)used.size(); i++) {
    known[used[i]] = 0;
  }
  used.clear();

  return result;
}

static int Lsv_CommandCutTT(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int k = Lsv_ReadK(pNtk, argc, argv, "lsv_cut_tt");
  if (k < 0) {
    return 1;
  }

  std::vector<std::vector<Cut>> cuts;
  Lsv_EnumerateCuts(pNtk, k, cuts);

  int size = Abc_NtkObjNumMax(pNtk);
  std::vector<uint64_t> value(size, 0);
  std::vector<int> known(size, 0);
  std::vector<int> used;

  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i) {
    int id = Abc_ObjId(pObj);
    for (int c = 0; c < (int)cuts[id].size(); c++) {
      uint64_t tt = Lsv_CutTruthTable(pObj, cuts[id][c], value, known, used);
      Lsv_PrintCutStart(id, cuts[id][c]);
      printf("%llX\n", (unsigned long long)tt);
    }
  }
  return 0;
}

// ===========================================================================
// Part 3: BDD size (lsv_cut_bddsize)
// ===========================================================================
//

static DdNode* Lsv_BuildBdd(DdManager* dd, Abc_Obj_t* pObj,
                            std::vector<DdNode*>& value,
                            std::vector<int>& known, std::vector<int>& used) {
  int id = Abc_ObjId(pObj);

  if (known[id] == 1) {
    return value[id];
  }

  if (Abc_AigNodeIsConst(pObj)) {
    return Cudd_ReadOne(dd);
  }

  DdNode* left = Lsv_BuildBdd(dd, Abc_ObjFanin0(pObj), value, known, used);
  DdNode* right = Lsv_BuildBdd(dd, Abc_ObjFanin1(pObj), value, known, used);

  if (Abc_ObjFaninC0(pObj)) {
    left = Cudd_Not(left);
  }
  if (Abc_ObjFaninC1(pObj)) {
    right = Cudd_Not(right);
  }

  DdNode* result = Cudd_bddAnd(dd, left, right);
  Cudd_Ref(result);  

  value[id] = result;
  known[id] = 1;
  used.push_back(id);
  return result;
}


static int Lsv_CutBddSize(DdManager* dd, Abc_Obj_t* pRoot, const Cut& cut,
                          std::vector<DdNode*>& value, std::vector<int>& known,
                          std::vector<int>& used) {
  for (int i = 0; i < (int)cut.size(); i++) {
    DdNode* var = Cudd_bddIthVar(dd, i);
    Cudd_Ref(var);
    value[cut[i]] = var;
    known[cut[i]] = 1;
    used.push_back(cut[i]);
  }

  DdNode* root = Lsv_BuildBdd(dd, pRoot, value, known, used);
  int bddSize = Cudd_DagSize(root);


  for (int i = 0; i < (int)used.size(); i++) {
    Cudd_RecursiveDeref(dd, value[used[i]]);
    known[used[i]] = 0;
  }
  used.clear();

  return bddSize;
}

static int Lsv_CommandCutBddSize(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int k = Lsv_ReadK(pNtk, argc, argv, "lsv_cut_bddsize");
  if (k < 0) {
    return 1;
  }

  std::vector<std::vector<Cut>> cuts;
  Lsv_EnumerateCuts(pNtk, k, cuts);

  DdManager* dd = Cudd_Init(k, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);

  int size = Abc_NtkObjNumMax(pNtk);
  std::vector<DdNode*> value(size, NULL);
  std::vector<int> known(size, 0);
  std::vector<int> used;

  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i) {
    int id = Abc_ObjId(pObj);
    for (int c = 0; c < (int)cuts[id].size(); c++) {
      int bddSize = Lsv_CutBddSize(dd, pObj, cuts[id][c], value, known, used);
      Lsv_PrintCutStart(id, cuts[id][c]);
      printf("%d\n", bddSize);
    }
  }

  Cudd_Quit(dd);
  return 0;
}
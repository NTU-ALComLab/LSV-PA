#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#ifdef ABC_USE_CUDD
#include "bdd/cudd/cudd.h"
#endif
#include "sat/cnf/cnf.h"
#include "sat/bsat/satSolver.h"
#include <algorithm>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include <string>
#include <cstring>

extern "C" {
  Aig_Man_t* Abc_NtkToDar(Abc_Ntk_t* pNtk, int fExors, int fRegisters);
}

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintMocut(Abc_Frame_t* pAbc, int argc, char** argv);
#ifdef ABC_USE_CUDD
static int Lsv_CommandUnateBdd(Abc_Frame_t* pAbc, int argc, char** argv);
#endif
static int Lsv_CommandUnateSat(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocut", Lsv_CommandPrintMocut, 0);
#ifdef ABC_USE_CUDD
  Cmd_CommandAdd(pAbc, "LSV", "lsv_unate_bdd", Lsv_CommandUnateBdd, 0);
#endif
  Cmd_CommandAdd(pAbc, "LSV", "lsv_unate_sat", Lsv_CommandUnateSat, 0);
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

// -------------------- Multi-output k-feasible cut enumeration --------------------

namespace {

// Performance cap to prevent explosion on large designs
static const size_t LSV_MAX_CUTS_PER_NODE = 512;

// Memoization of reachability queries: fromId -> targetId
static std::unordered_map<unsigned long long, char> gReachMemo;

// Helper: DFS to check if target is in transitive fanin of from.
static bool Lsv_IsInTransitiveFanin(Abc_Obj_t* from, Abc_Obj_t* target) {
  if (from == target) return true;
  if (Abc_ObjIsCi(from)) return false;
  std::vector<Abc_Obj_t*> stack;
  stack.push_back(from);
  std::unordered_set<int> visited;
  while (!stack.empty()) {
    Abc_Obj_t* cur = stack.back();
    stack.pop_back();
    int id = Abc_ObjId(cur);
    if (visited.find(id) != visited.end()) continue;
    visited.insert(id);
    if (cur == target) return true;
    if (Abc_ObjIsCi(cur)) continue;
    Abc_Obj_t* pFanin; int k;
    Abc_ObjForEachFanin(cur, pFanin, k) stack.push_back(pFanin);
  }
  return false;
}

// Reduce redundant leaves: remove any leaf that is in transitive fanin of another leaf
static void Lsv_ReduceIrredundant(std::vector<int>& leaves, Abc_Ntk_t* pNtk) {
  if (leaves.size() <= 1) return;
  std::sort(leaves.begin(), leaves.end());
  leaves.erase(std::unique(leaves.begin(), leaves.end()), leaves.end());
  std::vector<int> keep;
  keep.reserve(leaves.size());
  for (size_t i = 0; i < leaves.size(); ++i) {
    bool dominated = false;
    Abc_Obj_t* leaf_i = Abc_NtkObj(pNtk, leaves[i]);
    for (size_t j = 0; j < leaves.size() && !dominated; ++j) {
      if (i == j) continue;
      Abc_Obj_t* leaf_j = Abc_NtkObj(pNtk, leaves[j]);
      unsigned long long key = (((unsigned long long)Abc_ObjId(leaf_j)) << 32) | (unsigned long long)Abc_ObjId(leaf_i);
      auto it = gReachMemo.find(key);
      bool reach = false;
      if (it != gReachMemo.end()) reach = (it->second != 0);
      else {
        reach = Lsv_IsInTransitiveFanin(leaf_j, leaf_i);
        gReachMemo.emplace(key, reach ? 1 : 0);
      }
      if (reach) dominated = true;
    }
    if (!dominated) keep.push_back(leaves[i]);
  }
  leaves.swap(keep);
}

static std::string Lsv_LeavesKey(const std::vector<int>& leaves) {
  std::string s;
  s.reserve(leaves.size() * 6);
  for (size_t i = 0; i < leaves.size(); ++i) {
    if (i) s.push_back(' ');
    s += std::to_string(leaves[i]);
  }
  return s;
}

}  // namespace

static int Lsv_CommandPrintMocut(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  if (!pNtk) { Abc_Print(-1, "Empty network.\n"); return 1; }
  if (!Abc_NtkIsStrash(pNtk)) { Abc_Print(-1, "The current network is not an AIG (strashed). Run 'strash' first.\n"); return 1; }

  int c; int k = 0, l = 0;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
      case 'h':
        Abc_Print(-2, "usage: lsv_printmocut <k> <l> [-h]\n");
        Abc_Print(-2, "\t        enumerate k-l multi-output cuts (3<=k<=6, 1<=l<=4)\n");
        Abc_Print(-2, "\t-h    : print the command usage\n");
        return 1;
      default:
        Abc_Print(-2, "usage: lsv_printmocut <k> <l> [-h]\n");
        Abc_Print(-2, "\t        enumerate k-l multi-output cuts (3<=k<=6, 1<=l<=4)\n");
        Abc_Print(-2, "\t-h    : print the command usage\n");
        return 1;
    }
  }
  if (argc < 3) {
    Abc_Print(-2, "usage: lsv_printmocut <k> <l> [-h]\n");
    Abc_Print(-2, "\t        enumerate k-l multi-output cuts (3<=k<=6, 1<=l<=4)\n");
    Abc_Print(-2, "\t-h    : print the command usage\n");
    return 1;
  }
  k = atoi(argv[1]); l = atoi(argv[2]);
  if (k < 3 || k > 6 || l < 1 || l > 4) { Abc_Print(-1, "Parameter out of range. Require 3 <= k <= 6 and 1 <= l <= 4.\n"); return 1; }

  int nObjs = Abc_NtkObjNumMax(pNtk);
  std::vector<std::vector<std::vector<int>>> nodeCuts; nodeCuts.resize(nObjs);

  Abc_Obj_t* pObj; int i;
  Abc_NtkForEachCi(pNtk, pObj, i) {
    int id = Abc_ObjId(pObj);
    nodeCuts[id].push_back(std::vector<int>{id});
  }

  Vec_Ptr_t* vDfs = Abc_NtkDfs(pNtk, 0);
  int nDfs = Vec_PtrSize(vDfs);
  for (int idx = 0; idx < nDfs; ++idx) {
    Abc_Obj_t* pNode = (Abc_Obj_t*)Vec_PtrEntry(vDfs, idx);
    if (!Abc_ObjIsNode(pNode)) continue;
    Abc_Obj_t* pF0 = Abc_ObjFanin(pNode, 0);
    Abc_Obj_t* pF1 = Abc_ObjFanin(pNode, 1);
    int idNode = Abc_ObjId(pNode);
    int id0 = Abc_ObjId(pF0);
    int id1 = Abc_ObjId(pF1);

    if (Abc_ObjIsCi(pF0) && nodeCuts[id0].empty()) nodeCuts[id0].push_back(std::vector<int>{id0});
    if (Abc_ObjIsCi(pF1) && nodeCuts[id1].empty()) nodeCuts[id1].push_back(std::vector<int>{id1});

    std::unordered_set<std::string> seen;
    {
      std::vector<int> unit{ idNode };
      std::sort(unit.begin(), unit.end());
      std::string key = Lsv_LeavesKey(unit);
      if (seen.insert(key).second) nodeCuts[idNode].push_back(std::move(unit));
    }
    for (const auto& ca : nodeCuts[id0]) {
      for (const auto& cb : nodeCuts[id1]) {
        if (nodeCuts[idNode].size() >= LSV_MAX_CUTS_PER_NODE) break;
        std::vector<int> merged;
        merged.reserve(ca.size() + cb.size());
        merged.insert(merged.end(), ca.begin(), ca.end());
        merged.insert(merged.end(), cb.begin(), cb.end());
        std::sort(merged.begin(), merged.end());
        merged.erase(std::unique(merged.begin(), merged.end()), merged.end());
        if ((int)merged.size() > k) continue;
        if ((int)merged.size() > k || merged.empty()) continue;
        std::string key = Lsv_LeavesKey(merged);
        if (seen.insert(key).second) {
          nodeCuts[idNode].push_back(std::move(merged));
          if (nodeCuts[idNode].size() >= LSV_MAX_CUTS_PER_NODE) break;
        }
      }
      if (nodeCuts[idNode].size() >= LSV_MAX_CUTS_PER_NODE) break;
    }
  }

  std::unordered_map<std::string, std::vector<int>> cutToOutputs;

  // Per-node DP pruning: remove dominated cuts (subset dominance)
  for (int idx = 0; idx < nDfs; ++idx) {
    Abc_Obj_t* pNode = (Abc_Obj_t*)Vec_PtrEntry(vDfs, idx);
    if (!Abc_ObjIsNode(pNode)) continue;
    auto& cuts = nodeCuts[Abc_ObjId(pNode)];
    if (cuts.size() <= 1) continue;
    // sort by size then lex
    std::sort(cuts.begin(), cuts.end(), [](const std::vector<int>& a, const std::vector<int>& b){
      if (a.size() != b.size()) return a.size() < b.size();
      return a < b;
    });
    std::vector<char> removed(cuts.size(), 0);
    for (size_t i = 0; i < cuts.size(); ++i) {
      if (removed[i]) continue;
      for (size_t j = i + 1; j < cuts.size(); ++j) {
        if (removed[j]) continue;
        // since cuts[i] is not larger than cuts[j], check subset
        size_t pi = 0, pj = 0;
        const auto& A = cuts[i];
        const auto& B = cuts[j];
        while (pi < A.size() && pj < B.size()) {
          if (A[pi] == B[pj]) { ++pi; ++pj; }
          else if (A[pi] > B[pj]) { ++pj; }
          else break;
        }
        if (pi == A.size()) removed[j] = 1;
      }
    }
    std::vector<std::vector<int>> kept;
    kept.reserve(cuts.size());
    for (size_t t = 0; t < cuts.size(); ++t) if (!removed[t]) kept.push_back(std::move(cuts[t]));
    cuts.swap(kept);
  }

  Abc_NtkForEachCi(pNtk, pObj, i) {
    int id = Abc_ObjId(pObj);
    for (const auto& cut : nodeCuts[id]) {
      std::vector<int> leaves = cut;
      std::sort(leaves.begin(), leaves.end());
      std::string key = Lsv_LeavesKey(leaves);
      auto& outs = cutToOutputs[key];
      outs.push_back(id);
    }
  }

  for (int idx = 0; idx < nDfs; ++idx) {
    Abc_Obj_t* pNode = (Abc_Obj_t*)Vec_PtrEntry(vDfs, idx);
    if (!Abc_ObjIsNode(pNode)) continue;
    int idNode = Abc_ObjId(pNode);
    for (const auto& cut : nodeCuts[idNode]) {
      std::vector<int> leaves = cut;
      std::sort(leaves.begin(), leaves.end());
      std::string key = Lsv_LeavesKey(leaves);
      auto& outs = cutToOutputs[key];
      outs.push_back(idNode);
    }
  }

  for (auto& kv : cutToOutputs) {
    auto& outs = kv.second;
    std::sort(outs.begin(), outs.end());
    outs.erase(std::unique(outs.begin(), outs.end()), outs.end());
    if ((int)outs.size() < l) continue;
    const std::string& key = kv.first;
    printf("%s :", key.c_str());
    for (size_t t = 0; t < outs.size(); ++t) printf(" %d", outs[t]);
    printf("\n");
  }

  Vec_PtrFree(vDfs);
  return 0;
}

// -----------------------------------------------------------------------------
// Unateness Checking with BDD
// -----------------------------------------------------------------------------

#ifdef ABC_USE_CUDD

/**Function*************************************************************
  Synopsis    [Detects unate variables using BDD for a single output and input.]
  Description [Checks if output yk is unate in input xi using BDD.]
  SideEffects []
  SeeAlso     []
***********************************************************************/
static int Lsv_CommandUnateBdd(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk;
  Abc_Obj_t* pCo;
  DdManager* dd;
  DdNode* func;
  DdNode* bVar;
  DdNode* f1, * f0;
  DdNode* posDiff, * negDiff;
  char* pattern;
  int k, i;
  int nPis, nVars;
  int c;
  int hasPosViol, hasNegViol;
  int isPosUnate, isNegUnate;

  // Parse arguments
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
      case 'h':
        Abc_Print(-2, "usage: lsv_unate_bdd <k> <i>\n");
        Abc_Print(-2, "\t        checks if output k is unate in input i using BDD\n");
        Abc_Print(-2, "\t-k    : output index (0-based)\n");
        Abc_Print(-2, "\t-i    : input index (0-based)\n");
        return 1;
      default:
        Abc_Print(-2, "usage: lsv_unate_bdd <k> <i>\n");
        return 1;
    }
  }
  if (argc < 3) {
    Abc_Print(-2, "usage: lsv_unate_bdd <k> <i>\n");
    return 1;
  }

  // Get current network
  pNtk = Abc_FrameReadNtk(pAbc);
  if (pNtk == NULL) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }

  // Parse k and i
  k = atoi(argv[1]);
  i = atoi(argv[2]);
  if (k < 0 || k >= Abc_NtkCoNum(pNtk) || i < 0 || i >= Abc_NtkCiNum(pNtk)) {
    Abc_Print(-1, "Index out of range.\n");
    return 1;
  }

  // Build or get BDDs (support both AIG and BDD formats)
  int fNeedFree = 0;
  if (Abc_NtkIsBddLogic(pNtk)) {
    // Network is already in BDD format (from collapse command), use existing BDD manager
    dd = (DdManager*)pNtk->pManFunc;
    pCo = Abc_NtkCo(pNtk, k);
    func = (DdNode*)Abc_ObjFanin0(pCo)->pData;
    if (func == NULL) {
      Abc_Print(-1, "The selected output has no BDD.\n");
      return 1;
    }
    Cudd_Ref(func);
  } else {
    // Network is in AIG format, build global BDDs
    if (!Abc_NtkIsStrash(pNtk)) {
      Abc_Print(-1, "Network must be in AIG format (run \"strash\") or BDD format (run \"collapse\").\n");
      return 1;
    }
    dd = (DdManager*)Abc_NtkBuildGlobalBdds(pNtk, 10000000, 0, 1, 0, 0);
    if (dd == NULL) {
      Abc_Print(-1, "Failed to build global BDDs.\n");
      return 1;
    }
    fNeedFree = 1;
    pCo = Abc_NtkCo(pNtk, k);
    func = (DdNode*)Abc_ObjGlobalBdd(pCo);
    if (func == NULL) {
      Abc_Print(-1, "The selected output has no BDD.\n");
      Abc_NtkFreeGlobalBdds(pNtk, 1);
      return 1;
    }
    Cudd_Ref(func);
  }

  nPis = Abc_NtkCiNum(pNtk);
  nVars = Cudd_ReadSize(dd);
  
  // Get the BDD variable for input i
  // If PI is not in the support of the output function, it's independent
  Abc_Obj_t* pPiObj = Abc_NtkPi(pNtk, i);
  if (Abc_NtkIsBddLogic(pNtk)) {
    // In BDD format: use Abc_NodeGetFaninNames to find BDD variable
    Abc_Obj_t* pRoot = Abc_ObjFanin0(pCo);
    Vec_Ptr_t* vFaninNames = Abc_NodeGetFaninNames(pRoot);
    char** bdd2name_arr = (char**)vFaninNames->pArray;
    int bdd_num = Abc_ObjFaninNum(pRoot);
    const char* piName = Abc_ObjName(pPiObj);
    
    int bddLevel = -1;
    for (int j = 0; j < bdd_num; j++) {
      if (strcmp(bdd2name_arr[j], piName) == 0) {
        bddLevel = j;
        break;
      }
    }
    Abc_NodeFreeNames(vFaninNames);
    
    if (bddLevel < 0) {
      // PI is not in the support, output is independent of this input
      printf("independent\n");
      Cudd_RecursiveDeref(dd, func);
      return 0;
    }
    bVar = Cudd_bddIthVar(dd, bddLevel);
  } else {
    // In AIG format: use Abc_ObjGlobalBdd
    bVar = (DdNode*)Abc_ObjGlobalBdd(pPiObj);
    if (bVar == NULL) {
      // PI is not in the support, output is independent of this input
      printf("independent\n");
      Cudd_RecursiveDeref(dd, func);
      Abc_NtkFreeGlobalBdds(pNtk, 1);
      return 0;
    }
  }
  Cudd_Ref(bVar);

  // Step 2: Compute cofactors (standard BDD unateness checking)
  // f0 = f|xi=0, f1 = f|xi=1
  // Standard: f0 = Cudd_Cofactor(dd, f, NOT(xi_bdd))
  //           f1 = Cudd_Cofactor(dd, f, xi_bdd)
  f0 = Cudd_Cofactor(dd, func, Cudd_Not(bVar));  // f|xi=0
  f1 = Cudd_Cofactor(dd, func, bVar);             // f|xi=1
  Cudd_Ref(f0);
  Cudd_Ref(f1);

  // Step 3: Check unateness using implication (Cudd_bddLeq)
  // Positive unate: f0 <= f1 (f0 → f1, when xi: 0→1, f doesn't decrease)
  // Negative unate: f1 <= f0 (f1 → f0, when xi: 0→1, f doesn't increase)
  // Standard: pos = Cudd_bddLeq(dd, f0, f1)
  //           neg = Cudd_bddLeq(dd, f1, f0)
  isPosUnate = Cudd_bddLeq(dd, f0, f1);
  isNegUnate = Cudd_bddLeq(dd, f1, f0);

  // For binate case, we need to find witness patterns
  // posDiff = f0 & !f1 (cases where f0=1 but f1=0, violating positive unate)
  // negDiff = f1 & !f0 (cases where f1=1 but f0=0, violating negative unate)
  posDiff = Cudd_bddAnd(dd, f0, Cudd_Not(f1));
  negDiff = Cudd_bddAnd(dd, f1, Cudd_Not(f0));
  Cudd_Ref(posDiff);
  Cudd_Ref(negDiff);

  hasPosViol = (posDiff != Cudd_ReadLogicZero(dd));
  hasNegViol = (negDiff != Cudd_ReadLogicZero(dd));

  // Output results according to standard BDD unateness checking
  // pos==1 && neg==1 → independent (f0 == f1)
  // pos==1 && neg==0 → positive unate (f0 <= f1)
  // pos==0 && neg==1 → negative unate (f1 <= f0)
  // pos==0 && neg==0 → binate (neither holds)
  if (isPosUnate && isNegUnate) {
    // f0 == f1, independent of xi
    printf("independent\n");
  } else if (isPosUnate) {
    // f0 <= f1, positive unate
    printf("positive unate\n");
  } else if (isNegUnate) {
    // f1 <= f0, negative unate
    printf("negative unate\n");
  } else {
    // Both violations exist, it's binate
    printf("binate\n");

    // Build mapping from BDD variable level to original PI index
    std::vector<int> bddLevelToPi(nVars, -1);
    if (Abc_NtkIsBddLogic(pNtk)) {
      // In BDD network: use Abc_NodeGetFaninNames to get BDD variable names
      Abc_Obj_t* pRoot = Abc_ObjFanin0(pCo);
      Vec_Ptr_t* vFaninNames = Abc_NodeGetFaninNames(pRoot);
      char** bdd2name_arr = (char**)vFaninNames->pArray;
      int bdd_num = Abc_ObjFaninNum(pRoot);
      
      // Build mapping: for each BDD level, find corresponding original PI
      for (int bddLevel = 0; bddLevel < bdd_num; bddLevel++) {
        const char* bddName = bdd2name_arr[bddLevel];
        // Find original PI with this name
        Abc_Obj_t* pPi;
        int piIdx;
        Abc_NtkForEachPi(pNtk, pPi, piIdx) {
          if (strcmp(Abc_ObjName(pPi), bddName) == 0) {
            bddLevelToPi[bddLevel] = piIdx;
            break;
          }
        }
      }
      Abc_NodeFreeNames(vFaninNames);
    } else {
      // In global BDDs: BDD variable order matches PI order
      for (int t = 0; t < nPis && t < nVars; t++) {
        bddLevelToPi[t] = t;
      }
    }

    // Extract witness patterns
    pattern = ABC_ALLOC(char, nVars);
    
    // Pattern 1: from negDiff (corresponds to xi case)
    if (Cudd_bddPickOneCube(dd, negDiff, pattern)) {
      // Convert pattern to string format
      std::string pat1(nPis, '0');
      for (int t = 0; t < nPis; t++) {
        if (t == i) {
          pat1[t] = '-';
        } else {
          // Find BDD level for this PI
          int bddLevel = -1;
          for (int j = 0; j < nVars; j++) {
            if (bddLevelToPi[j] == t) {
              bddLevel = j;
              break;
            }
          }
          if (bddLevel >= 0 && bddLevel < nVars) {
            if (pattern[bddLevel] == 1) pat1[t] = '1';
            else if (pattern[bddLevel] == 0) pat1[t] = '0';
            else pat1[t] = '0';  // don't care -> 0
          } else {
            pat1[t] = '0';
          }
        }
      }
      printf("%s\n", pat1.c_str());
    }

    // Pattern 2: from posDiff (corresponds to !xi case)
    if (Cudd_bddPickOneCube(dd, posDiff, pattern)) {
      // Convert pattern to string format
      std::string pat2(nPis, '0');
      for (int t = 0; t < nPis; t++) {
        if (t == i) {
          pat2[t] = '-';
        } else {
          // Find BDD level for this PI
          int bddLevel = -1;
          for (int j = 0; j < nVars; j++) {
            if (bddLevelToPi[j] == t) {
              bddLevel = j;
              break;
            }
          }
          if (bddLevel >= 0 && bddLevel < nVars) {
            if (pattern[bddLevel] == 1) pat2[t] = '1';
            else if (pattern[bddLevel] == 0) pat2[t] = '0';
            else pat2[t] = '0';  // don't care -> 0
          } else {
            pat2[t] = '0';
          }
        }
      }
      printf("%s\n", pat2.c_str());
    }

    ABC_FREE(pattern);
  }

  // Cleanup BDD references
  Cudd_RecursiveDeref(dd, posDiff);
  Cudd_RecursiveDeref(dd, negDiff);
  Cudd_RecursiveDeref(dd, f0);
  Cudd_RecursiveDeref(dd, f1);
  Cudd_RecursiveDeref(dd, bVar);
  Cudd_RecursiveDeref(dd, func);
  if (fNeedFree) {
    Abc_NtkFreeGlobalBdds(pNtk, 1);
  }
  return 0;
}

#endif  // ABC_USE_CUDD

// -----------------------------------------------------------------------------
// Unateness Checking with SAT
// -----------------------------------------------------------------------------

/**Function*************************************************************
  Synopsis    [Detects unate variables using SAT for a single output and input.]
  Description [Checks if output yk is unate in input xi using SAT solver.]
  SideEffects []
  SeeAlso     []
***********************************************************************/
static int Lsv_CommandUnateSat(Abc_Frame_t* pAbc, int argc, char** argv) {
  //#0 Readin
  if (argc < 3) {
    Abc_Print(-2, "usage: lsv_unate_sat <k> <i>\n");
    Abc_Print(-2, "\t        checks if output k is unate in input i using SAT\n");
    Abc_Print(-2, "\t-k    : output index (0-based)\n");
    Abc_Print(-2, "\t-i    : input index (0-based)\n");
    return 1;
  }

  const int k = atoi(argv[1]);
  const int i = atoi(argv[2]);

  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  if (pNtk == NULL) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "The current network is not an AIG. Run 'strash' first.\n");
    return 1;
  }

  const int out_num = Abc_NtkCoNum(pNtk);
  const int inp_num = Abc_NtkCiNum(pNtk);
  if (k < 0 || k >= out_num || i < 0 || i >= inp_num) {
    Abc_Print(-1, "Index out of range.\n");
    return 1;
  }

  //#1 Pre-process
  Abc_Obj_t* output = Abc_NtkPo(pNtk, k);
  Abc_Ntk_t* cone = Abc_NtkCreateCone(pNtk, Abc_ObjFanin0(output), Abc_ObjName(output), 1/*int fUseAllCis*/);

  // Check if input i is in the cone
  Abc_Obj_t* pCiOrig = Abc_NtkCi(pNtk, i);
  Abc_Obj_t* pCiInCone = (Abc_Obj_t*)pCiOrig->pCopy;
  if (pCiInCone == NULL) {
    printf("independent\n");
    Abc_NtkDelete(cone);
    return 0;
  }

  Aig_Man_t* pAig = Abc_NtkToDar(cone, 0/*int fExors*/, 0/*int fRegisters*/);
  sat_solver* pSat = sat_solver_new();
  Cnf_Dat_t* pCnf = Cnf_Derive(pAig, Aig_ManCoNum(pAig));
  pSat = (sat_solver*)Cnf_DataWriteIntoSolverInt(pSat, pCnf, 1/*int nFrames*/, 0/*int fInit*/);
  Cnf_DataLift(pCnf, pCnf->nVars);
  pSat = (sat_solver*)Cnf_DataWriteIntoSolverInt(pSat, pCnf, 2/*int nFrames*/, 0/*int fInit*/);
  Cnf_DataLift(pCnf, -1 * pCnf->nVars/*-(nTimes-1) * pCnf->nVars*/);

  //#2 add clauses for input (unateness checking)
  int pLits[2];
  Aig_Obj_t* pObj;
  int iObj;
  int varXiA = -1, varXiB = -1;
  Aig_ManForEachCi(pAig, pObj, iObj) {
    if (iObj == i) {
      // Target input: don't add equivalence clauses, allow different values
      varXiA = pCnf->pVarNums[pObj->Id];
      varXiB = pCnf->pVarNums[pObj->Id] + pCnf->nVars;
      continue;
    }
    // For other inputs: v_A(t) == v_B(t), v_A <-> v_B
    // v_A + v_B'
    pLits[0] = toLitCond(pCnf->pVarNums[pObj->Id], 0/*conjugate*/);
    pLits[1] = toLitCond(pCnf->pVarNums[pObj->Id] + pCnf->nVars, 1/*conjugate*/);
    sat_solver_addclause(pSat, pLits, pLits + 2);
    // v_A' + v_B
    pLits[0] = toLitCond(pCnf->pVarNums[pObj->Id], 1/*conjugate*/);
    pLits[1] = toLitCond(pCnf->pVarNums[pObj->Id] + pCnf->nVars, 0/*conjugate*/);
    sat_solver_addclause(pSat, pLits, pLits + 2);
  }

  //#3 add clauses for output (unateness checking)
  // Get output variables
  Aig_Obj_t* pPoAig = Aig_ManCo(pAig, 0);
  int varFA = pCnf->pVarNums[pPoAig->Id];
  int varFB = pCnf->pVarNums[pPoAig->Id] + pCnf->nVars;
  int litFA1 = toLitCond(varFA, 0);  // fA = 1
  int litFA0 = toLitCond(varFA, 1);   // fA = 0
  int litFB1 = toLitCond(varFB, 0);   // fB = 1
  int litFB0 = toLitCond(varFB, 1);   // fB = 0

  //#4 solve by SAT
// Negative-unate violation: xiA=0, xiB=1, fA=0, fB=1
int assumptionsNeg[4];
assumptionsNeg[0] = toLitCond(varXiA, 1);   // xiA = 0
assumptionsNeg[1] = toLitCond(varXiB, 0);   // xiB = 1
assumptionsNeg[2] = litFA0;                 // fA = 0
assumptionsNeg[3] = litFB1;                 // fB = 1
int statusNeg = sat_solver_solve(pSat, assumptionsNeg, assumptionsNeg+4, 0,0,0,0);

// Positive-unate violation: xiA=0, xiB=1, fA=1, fB=0
int assumptionsPos[4];
assumptionsPos[0] = toLitCond(varXiA, 1);   // xiA = 0
assumptionsPos[1] = toLitCond(varXiB, 0);   // xiB = 1
assumptionsPos[2] = litFA1;                 // fA = 1
assumptionsPos[3] = litFB0;                 // fB = 0
int statusPos = sat_solver_solve(pSat, assumptionsPos, assumptionsPos+4, 0,0,0,0);


  //#5 Output results
  if (statusNeg != l_True && statusPos != l_True) {
    printf("independent\n");
  } else if (statusPos != l_True && statusNeg == l_True) {
    printf("negative unate\n");
  } else if (statusNeg != l_True && statusPos == l_True) {
    printf("positive unate\n");
  } else {
    // Both violations exist, it's binate
    printf("binate\n");

    // Extract counterexample patterns
    std::string patNeg, patPos;
    patNeg.assign(inp_num, '0');
    patPos.assign(inp_num, '0');

    // For negative violation pattern
    if (statusNeg == l_True) {
      sat_solver_solve(pSat, assumptionsNeg, assumptionsNeg + 4, 0, 0, 0, 0);
      Aig_ManForEachCi(pAig, pObj, iObj) {
        if (iObj == i) {
          patNeg[iObj] = '-';
        } else {
          int val = sat_solver_var_value(pSat, pCnf->pVarNums[pObj->Id]);
          patNeg[iObj] = val ? '1' : '0';
        }
      }
    }

    // For positive violation pattern
    if (statusPos == l_True) {
      sat_solver_solve(pSat, assumptionsPos, assumptionsPos + 4, 0, 0, 0, 0);
      Aig_ManForEachCi(pAig, pObj, iObj) {
        if (iObj == i) {
          patPos[iObj] = '-';
        } else {
          int val = sat_solver_var_value(pSat, pCnf->pVarNums[pObj->Id]);
          patPos[iObj] = val ? '1' : '0';
        }
      }
    }

    // Pattern 1: cofactor equals x_i (positive unate violation)
    // Pattern 2: cofactor equals ~x_i (negative unate violation)
    printf("%s\n", patPos.c_str());
    printf("%s\n", patNeg.c_str());
  }

  // Cleanup
  Cnf_DataFree(pCnf);
  sat_solver_delete(pSat);
  Aig_ManStop(pAig);
  Abc_NtkDelete(cone);
  return 0;
}
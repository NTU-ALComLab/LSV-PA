#ifndef LSV_CUT_H
#define LSV_CUT_H

#include "base/abc/abc.h"
#include <cstdint>
#include <vector>

#ifdef ABC_USE_CUDD
#include "bdd/cudd/cudd.h"
#endif

// 自己用一般 STL 容器表示 cuts，不使用 ABC 內建的 cut 資料結構。
using Cut = std::vector<int>;          // 一個 cut 的 leaf IDs，遞增且不重複
using CutList = std::vector<Cut>;      // 一個節點的所有 cuts
using CutTable = std::vector<CutList>; // cuts[nodeID]；大小由 Abc_NtkObjNumMax 決定

// 1. 合併兩個 cut；結果不超過 k 就寫入 result 並回傳 true。
bool mergeCuts(const Cut &left, const Cut &right, int k, Cut &result);

// 2. 初始化與列舉所有 internal nodes 的 cuts；完成回傳 true。
bool enumerateCuts(Abc_Ntk_t *pNtk, int k, CutTable &cuts);

// 3. 算一組 assignment 的邏輯值；cut[0] 對應輸入編號的最高位。
bool evaluate(Abc_Obj_t *node, const Cut &cut, unsigned assignment);

// 4. 將所有 assignments 的輸出組成最多 64-bit 的 truth table。
std::uint64_t computeTruthTable(Abc_Obj_t *root, const Cut &cut);

#ifdef ABC_USE_CUDD
// 5. 自行用 Shannon 展開建立 BDD。
// 第一次呼叫：remainingVariables = cut.size()，variableIndex = 0。
// 成功回傳的 BDD 持有一次引用，呼叫者須用 Cudd_RecursiveDeref 釋放。
// 失敗回傳 nullptr。
DdNode *buildBdd(DdManager *manager, std::uint64_t truth,
                 int remainingVariables, int variableIndex);
#endif

// 6、7. 與 lsvCmd.cpp 已註冊的指令入口銜接；完成回傳 true。
bool Lsv_RunCutTruthTables(Abc_Ntk_t *pNtk, int k);
bool Lsv_RunCutBddSizes(Abc_Ntk_t *pNtk, int k);

#endif

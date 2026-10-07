#ifndef LSV_CUT_H
#define LSV_CUT_H

#include "base/abc/abc.h"
#include "bdd/cudd/cudd.h"

#include <cstdint>
#include <map>
#include <vector>

// ===================== PA1 4.1: k-feasible cuts =====================

// 一個 cut
struct Cut
{
  std::vector<int> leaves; // leaf 的節點 ID，由小到大
  uint64_t sign = 0;       // 簽名：每個 leaf 打開第 (ID % 64) 個 bit，用來快速判斷合併後會不會太大

  bool operator<(const Cut &o) const { return leaves < o.leaves; } // 給 std::set 排序、找重複用
};

typedef std::map<int, std::vector<Cut>> CutTable; // cuts[ID] = 這個節點的所有 cut

// 合併兩個排好序的 cut（聯集）, 並且去掉重複的節點並且排序好，結果放進 u
void Lsv_CutMerge(const Cut &a, const Cut &b, Cut &u);

// 由下往上算出每個節點的所有 k-feasible cut（strash 之後才能用）
CutTable Lsv_NtkEnumCuts(Abc_Ntk_t *pNtk, int k);

// 算 pRoot 以 cut 為輸入的真值表（好方法：一次算一整欄）
uint64_t Lsv_CutTt(Abc_Obj_t *pRoot, const Cut &cut);

// lsv_cut_tt：印出每個 AND 節點的每個 cut 和它的真值表
void Lsv_NtkPrintCutTt(Abc_Ntk_t *pNtk, int k);

// ===================== PA1 4.2: cut BDD size =====================

// 建出 pRoot 以 cut 為輸入的 ROBDD，回傳 BDD 大小（Cudd_DagSize）
// 變數順序：cut 裡第 j 個 leaf（ID 由小到大）= 第 j 個 BDD 變數，ID 小的靠近 root
int Lsv_CutBddSize(DdManager *dd, Abc_Obj_t *pRoot, const Cut &cut);

// lsv_cut_bddsize：印出每個 AND 節點的每個 cut 和它的 BDD 大小
void Lsv_NtkPrintCutBddSize(Abc_Ntk_t *pNtk, int k);

#endif

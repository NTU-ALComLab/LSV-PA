#ifndef LSV_CUT_H
#define LSV_CUT_H

#include "base/abc/abc.h"

#include <cstdint>
#include <map>
#include <vector>

// ===================== PA1 4.1: k-feasible cuts =====================

typedef std::vector<int> Cut;                     // 一個 cut = 一串排好序的節點 ID
typedef std::map<int, std::vector<Cut>> CutTable; // cuts[ID] = 這個節點的所有 cut

// 合併兩個排好序的 cut（聯集）, 並且去掉重複的節點並且排序好
Cut Lsv_CutMerge(const Cut &a, const Cut &b);

// 由下往上算出每個節點的所有 k-feasible cut（strash 之後才能用）
CutTable Lsv_NtkEnumCuts(Abc_Ntk_t *pNtk, int k);

// 算 pRoot 以 cut 為輸入的真值表（好方法：一次算一整欄）
uint64_t Lsv_CutTt(Abc_Obj_t *pRoot, const Cut &cut);

// lsv_cut_tt：印出每個 AND 節點的每個 cut 和它的真值表
void Lsv_NtkPrintCutTt(Abc_Ntk_t *pNtk, int k);

#endif

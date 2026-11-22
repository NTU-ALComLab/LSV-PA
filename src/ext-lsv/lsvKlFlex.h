#ifndef LSV_KL_FLEX_H
#define LSV_KL_FLEX_H

#include "base/abc/abc.h"

#include <iostream>
#include <optional>
#include <string>
#include <vector>

// 一組 KL cut 的兩個邊界。ID 都屬於原始 AIG，並依升冪排列。
// 組成 leaf 或 root 的 bit 字串時，這個順序讓最小 ID 落在最高位。
struct KlCut
{
  std::vector<int> roots;  // V，這塊子電路提供給下游的訊號
  std::vector<int> leaves; // U，從 roots 往回追時停下來的輸入邊界
};

// 第一階段會在已 strash 的組合電路 pNtk 中，找出所有並列最大的 KL cuts。
// k 和 l 分別是 leaves 和 roots 的數量上限。大小是 root 數加上內部 AND 數。
// 找不到合法 cut 時回傳空的 vector。
std::vector<KlCut> Lsv_FindMaximumKlCuts(Abc_Ntk_t *pNtk, int k, int l);

// 第二階段會對 pNtk 中的一組合法 cut，算出每個 leaf 值 u 的允許 root 組合。
// 回傳值的第 u 格是大寫十六進位 mask。bit c 為 1 代表允許強制成 root 組合 c。
// 如果 AIG/CNF 轉換或 SAT 求解失敗，回傳 std::nullopt。
std::optional<std::vector<std::string>> Lsv_ComputeFlexMasks(Abc_Ntk_t *pNtk, const KlCut &cut);

#endif // LSV_KL_FLEX_H

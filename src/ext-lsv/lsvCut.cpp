#include "lsvCut.h"

#include <algorithm>
#include <cassert>
#include <iostream>
#include <iterator>

// 合併兩個排好序的 cut（聯集）, 並且去掉重複的節點並且排序好
Cut Lsv_CutMerge(const Cut &a, const Cut &b)
{
  Cut u;
  std::set_union(a.begin(), a.end(), b.begin(), b.end(), std::back_inserter(u));
  return u;
}

// 由下往上算出每個節點的所有 k-feasible cut
// strash 之後的網路，確保child 比 parent 早建立
CutTable Lsv_NtkEnumCuts(Abc_Ntk_t *pNtk, int k)
{
  CutTable cuts; // cuts[ID] = 這個節點的所有 cut
  Abc_Obj_t *pObj;
  int i;

  // initial input：只有自己
  // Abc_NtkForEachPi 是巨集（abc.h:516），會被替換成：
  //   for (i = 0; i < Abc_NtkPiNum(pNtk) && (pObj = Abc_NtkPi(pNtk, i), 1); i++)
  // 所以下面的 { } 就是 for 迴圈本體，每一輪 pObj 指向一個 PI
  Abc_NtkForEachPi(pNtk, pObj, i)
  {
    cuts[Abc_ObjId(pObj)].push_back(Cut{(int)Abc_ObjId(pObj)}); // 把自己算進cut裡面
  }

  // AND 節點：ID 由小到大，fanin 一定已經算好
  // Abc_NtkForEachNode 是巨集（abc.h:464），會被替換成：
  //   for (i = 0; i < 物件總數 && (pObj = Abc_NtkObj(pNtk, i), 1); i++)
  //     if (pObj == NULL || !Abc_ObjIsNode(pObj)) {} else { ...下面的 { } ... }
  // 照 ID 由小到大掃，不是 AND 節點（PI、PO、常數）就跳過，只有 AND 節點才會執行本體
  Abc_NtkForEachNode(pNtk, pObj, i)
  {
    int id = Abc_ObjId(pObj);                 // parent node id
    int id0 = Abc_ObjId(Abc_ObjFanin0(pObj)); // fanin0 node id (left child)
    int id1 = Abc_ObjId(Abc_ObjFanin1(pObj)); // fanin1 node id (right child)
    assert(id0 < id && id1 < id);             // child 一定比 parent 先算好（strash 後保證）
    std::vector<Cut> &my = cuts[id];

    my.push_back(Cut{id}); // trivial cut：自己

    for (const Cut &c0 : cuts[id0])
    {
      for (const Cut &c1 : cuts[id1])
      {
        Cut u = Lsv_CutMerge(c0, c1);
        if ((int)u.size() > k)
          continue; // 太大就丟
        if (std::find(my.begin(), my.end(), u) != my.end())
          continue; // 重複就丟
        my.push_back(u);
      }
    }
  }
  return cuts;
}

// 一次算一整欄
// 回傳 pObj 在這個 cut 下的「整欄」真值表（每個 bit 是一行）
// leafTt[ID] = cut 裡每個 leaf 的模式（例如 11110000）；碰到 leaf 就停
//  static，不放進 header
static uint64_t Lsv_NodeTt(Abc_Obj_t *pObj, std::map<int, uint64_t> &leafTt)
{
  auto it = leafTt.find(Abc_ObjId(pObj));
  if (it != leafTt.end())
    return it->second; // 是 leaf：直接回傳它的模式，不再往下

  assert(Abc_AigNodeIsAnd(pObj));                        // 不是 leaf 就一定是 AND（cut 會擋住所有往下的路）
  uint64_t t0 = Lsv_NodeTt(Abc_ObjFanin0(pObj), leafTt); // 左 child 的整欄
  uint64_t t1 = Lsv_NodeTt(Abc_ObjFanin1(pObj), leafTt); // 右 child 的整欄
  if (Abc_ObjFaninC0(pObj))
    t0 = ~t0; // 虛線：每一位都翻轉
  if (Abc_ObjFaninC1(pObj))
    t1 = ~t1;
  return t0 & t1; // 每一位各自 AND = 所有行一起算
}

// 算 pRoot 以 cut 為輸入的真值表
uint64_t Lsv_CutTt(Abc_Obj_t *pRoot, const Cut &cut)
{
  int m = cut.size(); // leaf 個數
  int nRows = 1 << m; // 2^m 行
  std::map<int, uint64_t> leafTt;

  // 第 1 步：組出每個 leaf 的模式（直著讀那一欄）
  // 第 j 個 leaf 在第 idx 行的值 = idx 的第 (m-1-j) 個 bit（ID 最小的是最高位）
  for (int j = 0; j < m; j++)
  {
    uint64_t pat = 0;
    for (int idx = 0; idx < nRows; idx++)
      if ((idx >> (m - 1 - j)) & 1) // 看第 (m-1-j) 個 bit 是不是 1
        pat |= (uint64_t)1 << idx;  // 這一行是 1 → 打開第 idx 位
    leafTt[cut[j]] = pat;
  }

  // 第 2 步：從 root 往下遞迴，一次算完
  uint64_t tt = Lsv_NodeTt(pRoot, leafTt);

  // 第 3 步：清掉 ~ 造成的高位垃圾，只留 2^m 位（m=6 時 1<<64 不合法，直接全留）(和 m個1 的mask做AND)
  uint64_t mask = (nRows == 64) ? ~(uint64_t)0 : (((uint64_t)1 << nRows) - 1);
  return tt & mask;
}

// lsv_cut_tt：印出每個 AND 節點的每個 cut 和它的真值表
void Lsv_NtkPrintCutTt(Abc_Ntk_t *pNtk, int k)
{
  CutTable cuts = Lsv_NtkEnumCuts(pNtk, k);
  Abc_Obj_t *pObj;
  int i;

  Abc_NtkForEachNode(pNtk, pObj, i)
  {
    int id = Abc_ObjId(pObj);
    for (const Cut &c : cuts[id])
    {
      std::cout << id << ":";
      for (const int &x : c)
        std::cout << " " << x;
      // hex + uppercase：印成 2A 這種格式；印完切回 dec，不然下一行的 ID 也會變 hex
      std::cout << ": " << std::hex << std::uppercase << Lsv_CutTt(pObj, c)
                << std::dec << std::endl;
    }
  }
}

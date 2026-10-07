#include "lsvCut.h"
#include "bdd/cudd/cuddInt.h" // Cudd_Not / Cudd_NotCond 用到的 ptrint 型別定義在這裡

#include <algorithm>
#include <cassert>
#include <iostream>
#include <iterator>
#include <set>

// 只有一個 leaf 的 cut（PI 和 trivial cut 用）
static Cut Lsv_CutSingle(int id)
{
  Cut c;
  c.leaves.push_back(id);
  c.sign = (uint64_t)1 << (id % 64);
  return c;
}

// 合併兩個排好序的 cut（聯集）, 並且去掉重複的節點並且排序好
// 結果放進 u（重複使用同一個 vector，不用每次都向系統要新的記憶體）
void Lsv_CutMerge(const Cut &a, const Cut &b, Cut &u)
{
  u.leaves.clear();
  std::set_union(a.leaves.begin(), a.leaves.end(), b.leaves.begin(), b.leaves.end(),
                 std::back_inserter(u.leaves));
  u.sign = a.sign | b.sign; // 聯集的簽名 = 兩邊簽名 OR 起來
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
    cuts[Abc_ObjId(pObj)].push_back(Lsv_CutSingle(Abc_ObjId(pObj))); // 把自己算進cut裡面
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

    my.push_back(Lsv_CutSingle(id)); // trivial cut：自己
    std::set<Cut> seen;    // 這個節點已經有的 cut，用來檢查重複

    Cut u; // 放在迴圈外面重複使用
    for (const Cut &c0 : cuts[id0])
    {
      for (const Cut &c1 : cuts[id1])
      {
        // 簽名快速篩選：兩個簽名 OR 起來，數有幾個 1（popcount）
        // 超過 k 個 → 合併後一定超過 k 個 leaf，連合併都不用做
        //（不同 ID 可能撞到同一個 bit，1 的個數只會少算、不會多算，所以不會誤刪）
        if (__builtin_popcountll(c0.sign | c1.sign) > k)
          continue;
        Lsv_CutMerge(c0, c1, u);
        if ((int)u.leaves.size() > k)
          continue; // 太大就丟
        if (!seen.insert(u).second)
          continue; // 重複就丟（insert 失敗代表已經有了）
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
  int m = cut.leaves.size(); // leaf 個數
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
    leafTt[cut.leaves[j]] = pat;
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
      for (const int &x : c.leaves)
        std::cout << " " << x;
      // hex + uppercase：印成 2A 這種格式；印完切回 dec，不然下一行的 ID 也會變 hex
      std::cout << ": " << std::hex << std::uppercase << Lsv_CutTt(pObj, c)
                << std::dec << "\n"; // 用 "\n" 不用 endl：endl 每行都強制寫出，幾百萬行會很慢
    }
  }
  std::cout << std::flush; // 最後一次寫出，避免跟 ABC 用 printf 印的東西順序錯亂
}

// ===================== PA1 4.2: cut BDD size =====================

// 跟 Lsv_NodeTt 一樣的遞迴，只是把 uint64_t 換成 BDD
// memo[ID] = 這個節點的 BDD；一開始只放 cut 的 leaf，碰到就停
// 算過的節點也存進 memo，同一個節點被走到第二次時直接拿，不重算
// memo 裡的每個 BDD 都有 Cudd_Ref，用完由呼叫的人統一 Deref
// all bdd nodes, aig nodes, id->bdd node mapping
static DdNode *Lsv_NodeBdd(DdManager *dd, Abc_Obj_t *pObj, std::map<int, DdNode *> &memo)
{
  auto it = memo.find(Abc_ObjId(pObj));
  if (it != memo.end())
    return it->second; // 是 leaf 或已經算過：直接回傳

  assert(Abc_AigNodeIsAnd(pObj));                          // 不是 leaf 就一定是 AND（cut 會擋住所有往下的路）
  DdNode *f0 = Lsv_NodeBdd(dd, Abc_ObjFanin0(pObj), memo); // 左 child 的 BDD
  DdNode *f1 = Lsv_NodeBdd(dd, Abc_ObjFanin1(pObj), memo); // 右 child 的 BDD
  f0 = Cudd_NotCond(f0, Abc_ObjFaninC0(pObj));             // 虛線：反相（CUDD 的 complemented edge，不用建新節點）
  f1 = Cudd_NotCond(f1, Abc_ObjFaninC1(pObj));

  DdNode *f = Cudd_bddAnd(dd, f0, f1); // AND = ite(f0, f1, 0)，CUDD 內部會自動化簡成 ROBDD
  Cudd_Ref(f);                         // 告訴 CUDD「我還要用」，避免被回收
  memo[Abc_ObjId(pObj)] = f;
  return f;
}

// 建出 pRoot 以 cut 為輸入的 ROBDD，回傳 BDD 大小
int Lsv_CutBddSize(DdManager *dd, Abc_Obj_t *pRoot, const Cut &cut)
{
  std::map<int, DdNode *> memo;

  // 第 1 步：cut 裡第 j 個 leaf → 第 j 個 BDD 變數
  // 沒有開 reordering，所以變數 j 就在第 j 層：ID 小的 j 小，靠近 root
  for (int j = 0; j < (int)cut.leaves.size(); j++)
  {
    DdNode *v = Cudd_bddIthVar(dd, j);
    Cudd_Ref(v); // 跟其他 BDD 一樣 Ref，最後才能統一 Deref
    memo[cut.leaves[j]] = v;
  }

  // 第 2 步：從 root 往下遞迴建 BDD
  DdNode *f = Lsv_NodeBdd(dd, pRoot, memo);

  // 第 3 步：數節點（變數節點 + 1 個終端節點）
  int size = Cudd_DagSize(f);

  // 第 4 步：釋放這個 cut 用到的所有 BDD
  for (auto &p : memo)
    Cudd_RecursiveDeref(dd, p.second);
  return size;
}

// lsv_cut_bddsize：印出每個 AND 節點的每個 cut 和它的 BDD 大小
void Lsv_NtkPrintCutBddSize(Abc_Ntk_t *pNtk, int k)
{
  CutTable cuts = Lsv_NtkEnumCuts(pNtk, k);
  // 整個指令共用一個 BDD manager（工作空間），每個 cut 用完就 Deref，不用每次重開
  DdManager *dd = Cudd_Init(0, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);
  Abc_Obj_t *pObj;
  int i;

  Abc_NtkForEachNode(pNtk, pObj, i)
  {
    int id = Abc_ObjId(pObj);
    for (const Cut &c : cuts[id])
    {
      std::cout << id << ":";
      for (const int &x : c.leaves)
        std::cout << " " << x;
      std::cout << ": " << Lsv_CutBddSize(dd, pObj, c) << "\n";
    }
  }
  std::cout << std::flush;

  assert(Cudd_CheckZeroRef(dd) == 0); // 每個 Ref 都有對應的 Deref，沒有漏掉的記憶體
  Cudd_Quit(dd);
}

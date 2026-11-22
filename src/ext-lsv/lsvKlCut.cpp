#include "lsvKlFlex.h"
#include "lsvCut.h"

#include <algorithm>
#include <map>
#include <utility>

// 驗證一組候選 cut 分成四步，由 GetKlCutSize 依序呼叫：
//   1. WalkCutBoundary     K2，並收集 interior，同時留下走訪標記
//   2. AllLeavesReached    K3 第一段，讀第 1 步的走訪標記
//   3. IsFanoutFree        K4，讀第 1 步的走訪標記
//   4. AllLeavesNecessary  K3 第二段，會重新走訪並換掉走訪編號
// 第 2、3 步依賴第 1 步的標記，所以第 4 步一定要排在最後。

// 沿 pNtk 的 fanin 從 roots 往回走，遇到 leaves 就停，藉此驗證 K2。
// 若有路走到尚未被 leaf 擋住的 PI，回傳 false，否則回傳 true。
// 若有傳入 interior，就把看到的內部 AND ID 加進去，供後續 K4 和計算大小用。
static bool WalkCutBoundary(Abc_Ntk_t *pNtk, const std::vector<int> &roots,
                     const std::vector<int> &leaves, std::vector<int> *interior = nullptr)
{
  // 開啟新的走訪編號。同一輪 DFS 看到共用節點時可以跳過，下一輪會重新走。
  // pending 是待處理的 ID 堆疊。先放所有 roots，之後每次加入目前節點的 fanins。
  Abc_NtkIncrementTravId(pNtk);
  std::vector<int> pending = roots;
  while (!pending.empty())
  {
    int id = pending.back();
    pending.pop_back();
    Abc_Obj_t *node = Abc_NtkObj(pNtk, id);
    if (Abc_NodeIsTravIdCurrent(node))
      continue;
    // 先標記再判斷 leaf，K3 才知道這一輪實際碰到了哪些 leaves。
    Abc_NodeSetTravIdCurrent(node);
    if (std::binary_search(leaves.begin(), leaves.end(), id))
      continue;
    if (Abc_ObjIsPi(node))
      return false;
    if (Abc_AigNodeIsConst(node))
      continue;

    // 一個 root 可以是另一個 root 的上游，所以也要穿過它繼續走。
    // 只有介在 root 和 leaf 之間的 AND 會列進 interior，常數本身沒有 fanin。
    if (interior && !std::binary_search(roots.begin(), roots.end(), id))
      interior->push_back(id);
    Abc_Obj_t *fanin;
    int i;
    Abc_ObjForEachFanin(node, fanin, i)
        pending.push_back(Abc_ObjId(fanin));
  }
  return true;
}

// K3 第一段：每個 leaf 都要被 WalkCutBoundary 碰到。如果剛才的 DFS 碰不到某個 leaf，
// 代表其他 leaves 已經擋住通往它的所有路徑。這個 leaf 可以拿掉，因此 cut 無效。
static bool AllLeavesReached(Abc_Ntk_t *pNtk, const std::vector<int> &leaves)
{
  for (int id : leaves)
    if (!Abc_NodeIsTravIdCurrent(Abc_NtkObj(pNtk, id)))
      return false;
  return true;
}

// K4：每條從 interior 出發的線都要接到 interior 或 roots。
// WalkCutBoundary 標記過的節點正好是 roots、interior 和碰到的 leaves，
// 所以「有標記且不是 leaf」就等於在 roots 或 interior 裡，不必另外排序再二分搜尋。
// PO 不會被走訪標記，所以 interior 直接驅動 PO 時也會在這裡被擋下。
// leaf 那一項不能省：leaf 的 fanin 可能是 interior 節點，這時 leaf 有標記，但不在 cut 內。
static bool IsFanoutFree(Abc_Ntk_t *pNtk, const std::vector<int> &leaves,
                         const std::vector<int> &interior)
{
  for (int id : interior)
  {
    Abc_Obj_t *fanout;
    int i;
    Abc_ObjForEachFanout(Abc_NtkObj(pNtk, id), fanout, i)
    {
      if (!Abc_NodeIsTravIdCurrent(fanout) ||
          std::binary_search(leaves.begin(), leaves.end(), Abc_ObjId(fanout)))
        return false;
    }
  }
  return true;
}

// K3 第二段：逐一確認每個 leaf 都是必要的。
// 走到的 PI leaf 本身就是路徑終點，可以直接判定為必要（前提是 AllLeavesReached 已經通過）。
// 若 leaf 是 AND，先用 remaining 暫時移除它，再跑一次 K2。如果仍然擋住
// 所有到 PI 的路，它就是多餘的。確認必要後放回原位，remaining 因此保持排序。
static bool AllLeavesNecessary(Abc_Ntk_t *pNtk, const KlCut &cut)
{
  std::vector<int> remaining = cut.leaves;
  for (std::size_t i = 0; i < cut.leaves.size(); ++i)
  {
    if (Abc_ObjIsPi(Abc_NtkObj(pNtk, cut.leaves[i])))
      continue;
    remaining.erase(remaining.begin() + i);
    if (WalkCutBoundary(pNtk, cut.roots, remaining))
      return false;
    remaining.insert(remaining.begin() + i, cut.leaves[i]);
  }
  return true;
}

// 驗證已通過 K1 的 cut。違規回傳 -1，合法時回傳 roots 數量加 interior 數量。
// 呼叫順序見檔案開頭：前三步共用同一次走訪的標記，會重新走訪的 K3 第二段放最後。
static int GetKlCutSize(Abc_Ntk_t *pNtk, const KlCut &cut)
{
  std::vector<int> interior;
  if (!WalkCutBoundary(pNtk, cut.roots, cut.leaves, &interior)) // K2
    return -1;
  if (!AllLeavesReached(pNtk, cut.leaves)) // K3 第一段
    return -1;
  if (!IsFanoutFree(pNtk, cut.leaves, interior)) // K4
    return -1;
  if (!AllLeavesNecessary(pNtk, cut)) // K3 第二段
    return -1;
  return static_cast<int>(cut.roots.size() + interior.size());
}

// 一組 U 候選，以及它的 cone 總和。cone(r, C) 是從 root r 走到 PA1 cut C 為止經過的 AND 數
// （不含 r）。U 由每個已選 root r 的某個 cut C_r 聯集而成，而 interior 的每個節點都是從
// 某個 root r 沿著不經過 U（因此也不經過 C_r）的路走到的，所以 interior 落在這些 cone 的
// 聯集裡。因此 |V| + cone 總和是這組 cut 大小的上界。同一個 U 可能由不同組合產生，
// 每一組算出的都是合法上界，所以保留最小的那個。
typedef std::map<Cut, int> LeafUnions;

// 只保留包含關係上最小的 U，比它大的 U 連同往下的整棵子樹都不必展開。
// 每個 U 都是各 root 的 PA1 cut 的聯集，所以一定是 V 的 cut。若 U1 ⊊ U2，往下加入 root r
// 和它的 cut C 時，U1 ∪ C 也是新 roots 的 cut，而且包含於 U2 ∪ C：
//   - 若 U2 ∪ C 比較大，它多出來的 leaf 拿掉後仍是 cut，違反 K3，一定不合法。
//   - 若兩者相等，從 U1 也會產生同一個 U，不會漏。
// U1 ∪ C 是 U2 ∪ C 的子集，所以 leaf 上限、signature、K1 這些篩選它也一定通過。
// 歸納下去，每組合法 cut 的 U 都還會在對應那組 roots 的候選裡出現。
// 依 leaf 數由小到大處理，只和已保留的 U 比對就夠了：被刪掉的 U 本身也包含某個保留的 U。
static void KeepMinimalUnions(LeafUnions &unions)
{
  std::vector<LeafUnions::iterator> bySize;
  for (auto it = unions.begin(); it != unions.end(); ++it)
    bySize.push_back(it);
  std::stable_sort(bySize.begin(), bySize.end(),
                   [](LeafUnions::iterator a, LeafUnions::iterator b)
                   { return a->first.leaves.size() < b->first.leaves.size(); });

  std::vector<const Cut *> kept;
  for (LeafUnions::iterator it : bySize)
  {
    const Cut &u = it->first;
    bool hasSubset = false;
    for (const Cut *s : kept)
    {
      // 一樣大的不可能是真子集。signature 有 u 沒有的位元，代表 s 有 u 沒有的 leaf。
      if (s->leaves.size() < u.leaves.size() && !(s->sign & ~u.sign) &&
          std::includes(u.leaves.begin(), u.leaves.end(), s->leaves.begin(), s->leaves.end()))
      {
        hasSubset = true;
        break;
      }
    }
    if (hasSubset)
      unions.erase(it);
    else
      kept.push_back(&u);
  }
}

// 搜尋的資料集中放在同一份 search，遞迴時用參考傳下去。
// singleRootCuts、andIds 和 coneSizes 是進入搜尋前準備好的資料，roots 則會隨分支增減。
struct KlCutSearch
{
  Abc_Ntk_t *pNtk = nullptr;
  int k = 0;                              // leaf 數量上限
  int l = 0;                              // root 數量上限
  CutTable singleRootCuts;                // PA1 查表，key 是單一 root 的 ID
  std::vector<int> andIds;                // 可選 root 的 ID，已按升冪排列
  std::vector<std::vector<int>> coneSizes; // coneSizes[index][j]：andIds[index] 第 j 個 PA1 cut 的 cone 大小
  std::vector<int> roots;                 // 目前這條分支選了哪些 roots
  int maximumSize = 0;                    // 到目前為止最大的合法 cut 大小
  std::vector<KlCut> maximumCuts;         // 所有和 maximumSize 並列的合法 cuts
};

// 在目前的 roots 後再試選一個 root。start 是下一個可選的 andIds 索引。
// leafUnions 是加入新 root 前的 U 候選。函式把找到的答案更新到 search。
static void EnumerateKlCuts(KlCutSearch &search, std::size_t start,
                            const LeafUnions &leafUnions)
{
  for (std::size_t index = start; index < search.andIds.size(); ++index)
  {
    int root = search.andIds[index];
    search.roots.push_back(root);

    // options 是新 root 自己的 PA1 cuts，cones 是它們各自的 cone 大小。
    // nextUnions 只收這組新 V 對應的 U。
    const std::vector<Cut> &options = search.singleRootCuts.at(root);
    const std::vector<int> &cones = search.coneSizes[index];
    LeafUnions nextUnions;
    Cut merged;
    for (const auto &[leaves, coneSum] : leafUnions)
    {
      if (std::binary_search(leaves.leaves.begin(), leaves.leaves.end(), root))
        continue;
      for (std::size_t j = 0; j < options.size(); ++j)
      {
        const Cut &option = options[j];
        // 先用 signature 快篩，再算精確聯集。merged 是獨立的暫存，
        // 因為 Lsv_CutMerge 會先清空它的內容。
        if (__builtin_popcountll(leaves.sign | option.sign) > search.k)
          continue;
        Lsv_CutMerge(leaves, option, merged);
        if (merged.leaves.size() > static_cast<std::size_t>(search.k))
          continue;

        // K1 要求 U 和 V 分開。逐個查已選 root 是否混進合併後的 leaves。
        // 例如新 root 的 trivial cut {root} 會在這裡被過濾。
        bool overlapsRoot = false;
        for (int selectedRoot : search.roots)
        {
          if (std::binary_search(merged.leaves.begin(), merged.leaves.end(), selectedRoot))
          {
            overlapsRoot = true;
            break;
          }
        }
        if (overlapsRoot)
          continue;

        // 同一組 roots 下，同一份 U 只驗證一次。重複出現時只把 cone 總和更新成較小值，
        // 讓下一層的上界更緊。
        int bound = coneSum + cones[j];
        auto [it, inserted] = nextUnions.emplace(merged, bound);
        if (!inserted)
        {
          it->second = std::min(it->second, bound);
          continue;
        }

        // 上界剪枝：|V| + cone 總和已經小於目前最大值，這組 cut 不可能被印出，不必驗證。
        // 用嚴格小於，因為大小並列的 cut 也要印。它已經在 nextUnions 裡，下一層加了
        // root 之後仍可能長大，所以只跳過驗證，不跳過遞迴。
        if (static_cast<int>(search.roots.size()) + bound < search.maximumSize)
          continue;

        // 遇到更大的合法 cut 就清空舊答案，大小並列的則一起留下。
        KlCut candidate{search.roots, merged.leaves};
        int size = GetKlCutSize(search.pNtk, candidate);
        if (size > search.maximumSize)
        {
          search.maximumSize = size;
          search.maximumCuts.clear();
        }
        if (size == search.maximumSize)
          search.maximumCuts.push_back(std::move(candidate));
      }
    }

    // 往下一層只挑後面的 ID，讓同一組 roots 只按一種順序產生。
    // nextUnions 包含所有通過 K1 的 U。加一個 root 可能修復原先的 K4 違規。
    // 展開前先刪掉非最小的 U，理由見 KeepMinimalUnions。
    if (search.roots.size() < static_cast<std::size_t>(search.l) && !nextUnions.empty())
    {
      KeepMinimalUnions(nextUnions);
      EnumerateKlCuts(search, index + 1, nextUnions);
    }

    // 這個 root 的分支試完，撤回選擇，再讓 for 嘗試同層的下一個 root。
    search.roots.pop_back();
  }
}

// 先取得 PA1 的單 root cuts 和所有可選的 AND，再開始遞迴。
// k 和 l 分別是 leaf 與 root 的上限，回傳所有最大且合法的 cut。
std::vector<KlCut> Lsv_FindMaximumKlCuts(Abc_Ntk_t *pNtk, int k, int l)
{
  if (l == 0)
    return {};

  KlCutSearch search;
  search.pNtk = pNtk;
  search.k = k;
  search.l = l;
  search.singleRootCuts = Lsv_NtkEnumCuts(pNtk, k);

  Abc_Obj_t *node;
  int i;
  Abc_AigForEachAnd(pNtk, node, i)
    search.andIds.push_back(Abc_ObjId(node));

  // 預先算好每個 (root, PA1 cut) 的 cone 大小，給上界剪枝用。
  // 同時把單一 root 的合法 cut 都驗證一次，得到起始的 maximumSize。這些 cut 的 |V| = 1 ≤ l，
  // 所以真正的最大值至少是它；有了它，遞迴一開始就能剪枝，不必等到碰巧走到大的 cut。
  // maximumCuts 先保持空的：完整搜尋會重新產生這些 cut，大小並列時才放進答案，不會重複。
  for (int root : search.andIds)
  {
    std::vector<int> &cones = search.coneSizes.emplace_back();
    for (const Cut &option : search.singleRootCuts.at(root))
    {
      std::vector<int> interior;
      WalkCutBoundary(pNtk, {root}, option.leaves, &interior);
      cones.push_back(static_cast<int>(interior.size()));
      if (std::binary_search(option.leaves.begin(), option.leaves.end(), root))
        continue; // trivial cut {root} 違反 K1
      search.maximumSize = std::max(search.maximumSize,
                                    GetKlCutSize(pNtk, KlCut{{root}, option.leaves}));
    }
  }

  // 從沒有選任何 root 的狀態開始，起始的 U 候選只有一個空集合，cone 總和為 0。
  EnumerateKlCuts(search, 0, {{Cut{}, 0}});
  return std::move(search.maximumCuts);
}

#include "lsvKlFlex.h"
#include "lsvCut.h"

#include <algorithm>
#include <set>
#include <utility>

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

// 驗證已通過 K1 的 cut。先用 K2 找出 interior，再檢查 leaf 的必要性和外部 fanout。
// 違規回傳 -1，合法時回傳 roots 數量加 interior 數量。
static int GetKlCutSize(Abc_Ntk_t *pNtk, const KlCut &cut)
{
  std::vector<int> interior;
  if (!WalkCutBoundary(pNtk, cut.roots, cut.leaves, &interior))
    return -1;

  // K3 先確認哪些 leaf 被走訪到。如果剛才的 DFS 碰不到某個 leaf，代表其他 leaves 已經擋住
  // 通往它的所有路徑。這個 leaf 可以拿掉，因此 cut 無效。
  // 要在下一次 DFS 開始前讀取走訪標記，因為下一輪會換走訪編號。
  for (int id : cut.leaves)
    if (!Abc_NodeIsTravIdCurrent(Abc_NtkObj(pNtk, id)))
      return -1;

  // K4 要求每條從 interior 出發的線都接到 interior 或 roots。
  // target 是 fanout 的 ID。如果接到 PO 或 cut 外的 AND，這組 cut 就無效。
  // 先排序 interior，後面可以用 binary_search 判斷 target 是否在裡面。
  std::sort(interior.begin(), interior.end());
  for (int id : interior)
  {
    Abc_Obj_t *fanout;
    int i;
    Abc_ObjForEachFanout(Abc_NtkObj(pNtk, id), fanout, i)
    {
      int target = Abc_ObjId(fanout);
      if (!std::binary_search(interior.begin(), interior.end(), target) &&
          !std::binary_search(cut.roots.begin(), cut.roots.end(), target))
        return -1;
    }
  }

  // K3 接著逐一確認必要性。走到的 PI leaf 本身就是路徑終點，可以直接判定為必要。
  // 若 leaf 是 AND，先用 remaining 暫時移除它，再跑一次 K2。如果仍然擋住
  // 所有到 PI 的路，它就是多餘的。確認必要後放回原位，下一輪只測另一個 leaf。
  std::vector<int> remaining = cut.leaves;
  for (std::size_t i = 0; i < cut.leaves.size(); ++i)
  {
    if (Abc_ObjIsPi(Abc_NtkObj(pNtk, cut.leaves[i])))
      continue;
    remaining.erase(remaining.begin() + i);
    if (WalkCutBoundary(pNtk, cut.roots, remaining))
      return -1;
    remaining.insert(remaining.begin() + i, cut.leaves[i]);
  }
  return static_cast<int>(cut.roots.size() + interior.size());
}

// 搜尋的資料集中放在同一份 search，遞迴時用參考傳下去。
// singleRootCuts 和 andIds 是進入搜尋前準備好的資料，roots 則會隨分支增減。
struct KlCutSearch
{
  Abc_Ntk_t *pNtk = nullptr;
  int k = 0;                        // leaf 數量上限
  int l = 0;                        // root 數量上限
  CutTable singleRootCuts;          // PA1 查表，key 是單一 root 的 ID
  std::vector<int> andIds;          // 可選 root 的 ID，已按升冪排列
  std::vector<int> roots;           // 目前這條分支選了哪些 roots
  int maximumSize = 0;              // 到目前為止最大的合法 cut 大小
  std::vector<KlCut> maximumCuts;   // 所有和 maximumSize 並列的合法 cuts
};

// 在目前的 roots 後再試選一個 root。start 是下一個可選的 andIds 索引。
// leafUnions 是加入新 root 前的 U 候選。函式把找到的答案更新到 search。
static void EnumerateKlCuts(KlCutSearch &search, std::size_t start,
                            const std::set<Cut> &leafUnions)
{
  for (std::size_t index = start; index < search.andIds.size(); ++index)
  {
    int root = search.andIds[index];
    search.roots.push_back(root);

    // options 是新 root 自己的 PA1 cuts。nextUnions 只收這組新 V 對應的 U。
    const std::vector<Cut> &options = search.singleRootCuts.at(root);
    std::set<Cut> nextUnions;
    Cut merged;
    for (const Cut &leaves : leafUnions)
    {
      if (std::binary_search(leaves.leaves.begin(), leaves.leaves.end(), root))
        continue;
      for (const Cut &option : options)
      {
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

        // 同一組 roots 下，同一份 U 只驗證一次。遇到更大的合法 cut
        // 就清空舊答案，大小並列的則一起留下。
        if (!nextUnions.insert(merged).second)
          continue;
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
    if (search.roots.size() < static_cast<std::size_t>(search.l) && !nextUnions.empty())
      EnumerateKlCuts(search, index + 1, nextUnions);

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

  // 從沒有選任何 root 的狀態開始，起始的 U 候選只有一個空集合。
  EnumerateKlCuts(search, 0, {Cut{}});
  return std::move(search.maximumCuts);
}

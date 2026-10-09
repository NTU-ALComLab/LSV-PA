#include "lsvCut.h"
#include <algorithm>
#include <cinttypes>

#ifdef ABC_USE_CUDD
// 配合 ABC 內附 CUDD 的 Cudd_Not 巨集所需的 ptrint 定義。
#include "bdd/cudd/cuddInt.h"
#endif

// 最基本的待實作骨架：依照 1 到 7 的順序完成。
// 目前的 return 都只是佔位值，不代表演算法已完成。
// 只能使用一般 ABC network API 與一般 CUDD 操作；
// cut 結構、列舉、truth table 與 BDD 建構流程必須自己寫。

// 1. mergeCuts：合併兩個 cut
bool mergeCuts(const Cut &left, const Cut &right, int k, Cut &result)
{
  //    不需要 ABC API。
  //    將兩邊 leaves 放在一起，排序、去重；數量超過 k 就不保留。
  //    可用一般迴圈，或 std::sort / std::unique（需 <algorithm>）。
  //    只有完全相同的 leaf 集合才是重複 cut。

  // TODO：在這裡實作，並替換下面的佔位回傳值。
  int i_left = 0, i_right = 0;
  result.clear();
  while (i_left < left.size() && i_right < right.size())
  {
    if (left[i_left] < right[i_right])
    {
      result.push_back(left[i_left]);
      i_left++;
    }
    else if (left[i_left] > right[i_right])
    {
      result.push_back(right[i_right]);
      i_right++;
    }
    else
    {
      result.push_back(left[i_left]);
      i_left++;
      i_right++;
    }
  }
  while (i_left < left.size())
  {
    result.push_back(left[i_left]);
    i_left++;
  }
  while (i_right < right.size())
  {
    result.push_back(right[i_right]);
    i_right++;
  }
  if (result.size() > k)
  {
    result.clear();
    return false;
  }
  return true;
}

// 2. enumerateCuts：初始化與列舉放在同一個函式即可
bool enumerateCuts(Abc_Ntk_t *pNtk, int k, CutTable &cuts)
{
  //    a. cuts 的大小設為 Abc_NtkObjNumMax(pNtk)，使用 cuts[nodeID] 存取。
  //    b. 用 Abc_NtkForEachCi 走訪輸入，以 Abc_ObjId 取得 ID。
  //       每個輸入的 cut list 先加入一個 {自己的 ID}。
  //       用 Abc_AigConst1 取得常數；它的 list 放一個空 cut，表示沒有變數。
  //    c. 用 Abc_NtkDfs(pNtk, 1) 取得 fanins 先於目前節點的順序。
  //       用 Vec_PtrForEachEntry 走訪結果，最後用 Vec_PtrFree 釋放向量。
  //    d. 每個 internal node 先加入 trivial cut {自己的 ID}。
  //       用 Abc_ObjFanin0 / Abc_ObjFanin1 取得兩個 fanins。
  //       兩層迴圈組合 fanin cut lists，呼叫自己的 mergeCuts。
  //       結果不超過 k 且尚未存在，就加入 cuts[nodeID]。
  //    不設 cut 數量上限，也不要照搬內建的 dominance filtering。
  //    反相邊不影響 leaf 集合，求值時再處理。

  // TODO：在這裡實作，並替換下面的佔位回傳值。
  cuts.clear();
  cuts.resize(Abc_NtkObjNumMax(pNtk));
  Abc_Obj_t *pCi;
  int i;
  Abc_NtkForEachCi(pNtk, pCi, i)
  {
    int id = Abc_ObjId(pCi);
    cuts[id].push_back({id});
  }

  Abc_Obj_t *pConst1 = Abc_AigConst1(pNtk);
  int const1_id = Abc_ObjId(pConst1);
  cuts[const1_id].push_back({});

  Vec_Ptr_t *dfs_nodes = Abc_NtkDfs(pNtk, 1);
  Abc_Obj_t *pNode;

  Vec_PtrForEachEntry(Abc_Obj_t *, dfs_nodes, pNode, i)
  {
    int node_id = Abc_ObjId(pNode);
    if (!Abc_ObjIsCi(pNode) && !Abc_AigNodeIsConst(pNode))
    {
      cuts[node_id].push_back({node_id});
      Abc_Obj_t *pFanin0 = Abc_ObjFanin0(pNode);
      Abc_Obj_t *pFanin1 = Abc_ObjFanin1(pNode);
      int fanin0_id = Abc_ObjId(pFanin0);
      int fanin1_id = Abc_ObjId(pFanin1);
      for (const Cut &cut0 : cuts[fanin0_id])
      {
        for (const Cut &cut1 : cuts[fanin1_id])
        {
          Cut merged_cut;
          if (mergeCuts(cut0, cut1, k, merged_cut))
          {
            if (std::find(cuts[node_id].begin(), cuts[node_id].end(), merged_cut) == cuts[node_id].end())
            {
              cuts[node_id].push_back(merged_cut);
            }
          }
        }
      }
    }
  }
  Vec_PtrFree(dfs_nodes);
  return true;
}

// 3. evaluate：自行遞迴計算一組 assignment
bool evaluate(Abc_Obj_t *node, const Cut &cut, unsigned assignment)
{
  //    a. 用 Abc_ObjId 判斷 node 是否在 cut 中。
  //       如果是 cut[j]，回傳 assignment 的第 (m-1-j) 位，不再展開。
  //       m 是實際 leaf 數；第一個（最小 ID）leaf 對應較高的輸入位元。
  //    b. 不是 leaf 時，用 Abc_AigNodeIsConst 判斷常數，const1 回傳 true。
  //    c. 用 Abc_ObjFanin0 / Abc_ObjFanin1 取得 fanins，遞迴算兩邊的值。
  //       用 Abc_ObjFaninC0 / Abc_ObjFaninC1 判斷反相，再做 AND。
  //    有效 cut 不應走到未列在 leaves 中的 CI，可用 Abc_ObjIsCi 檢查。
  //    必須先判斷 leaf，再判斷它是 PI 或 internal node。

  const int nodeId = Abc_ObjId(node);
  for (std::size_t j = 0; j < cut.size(); ++j)
  {
    if (cut[j] == nodeId)
      return ((assignment >> (cut.size() - 1 - j)) & 1) != 0;
    if (cut[j] > nodeId)
      break;
  }

  if (Abc_AigNodeIsConst(node))
    return true;
  if (Abc_ObjIsCi(node))
    return false;

  const bool left = ((evaluate(Abc_ObjFanin0(node), cut, assignment) != Abc_ObjFaninC0(node)) != 0);
  if (!left)
    return false;
  return ((evaluate(Abc_ObjFanin1(node), cut, assignment) != Abc_ObjFaninC1(node)) != 0);
}

// 4. computeTruthTable：逐組模擬，不需要位元平行最佳化
std::uint64_t computeTruthTable(Abc_Obj_t *root, const Cut &cut)
{
  //    不需要新的 ABC API，呼叫自己的 evaluate 即可。
  //    m = cut.size()，枚舉 assignment a=0 到 2^m-1。
  //    truth 從 0 開始；輸出為 1 時，設定 truth 的第 a 位。
  //    使用 std::uint64_t(1) << a。m 最大 6，所以 a 最大 63。
  //    不要執行移位 64 位的運算。
  //    例如 cut=[1,2]，函數 x1 AND NOT x2，truth 應為十六進位 4。
  //    trivial cut {root} 的 truth 必須是 2。

  std::uint64_t truth = 0;
  const unsigned assignmentCount = 1u << cut.size();
  for (unsigned assignment = 0; assignment < assignmentCount; ++assignment)
  {
    if (evaluate(root, cut, assignment))
      truth |= std::uint64_t(1) << assignment;
  }
  return truth;
}

#ifdef ABC_USE_CUDD
// 5. buildBdd：由自己的 truth table 自行做 Shannon 展開
DdNode *buildBdd(DdManager *manager, std::uint64_t truth,
                 int remainingVariables, int variableIndex)
{
  //    不需要再走訪 AIG，也不使用 ABC 的 truth-table-to-BDD 函式。
  //    a. remainingVariables=0 時，truth 只有一個有效 bit。
  //       用 Cudd_ReadOne 取得常數 1，常數 0 可用 Cudd_Not(one)。
  //    b. 其他情況，最前面的變數是目前 variableIndex。
  //       truth 的低半部對應此變數=0，高半部對應此變數=1。
  //       分割時使用 64-bit 值；最大只需移位 32 位。
  //    c. 遞迴建立 low / high，remainingVariables 減一、variableIndex 加一。
  //       用 Cudd_bddIthVar(manager, variableIndex) 取得變數。
  //       用 Cudd_bddIte(manager, variable, high, low) 組合。
  //    d. 每個成功回傳的 BDD 都持有一次 Cudd_Ref。
  //       low 建好後須有引用保護，才能安全地繼續建 high。
  //       保護目前結果後，用 Cudd_RecursiveDeref 釋放 low / high 的引用。
  //       即使 low 和 high 相同，也要釋放各自持有的引用；失敗也要清理。
  //    這是自己寫建構流程，只使用允許的一般 CUDD 操作。
  //    ABC 此版本的 Cudd_Not 需要 ptrint 定義；使用時可在本 .cpp 的
  //    #ifdef ABC_USE_CUDD 中 include "bdd/cudd/cuddInt.h"。

  if (remainingVariables == 0)
  {
    DdNode *result = Cudd_ReadOne(manager);
    if ((truth & 1) == 0)
      result = Cudd_Not(result);
    Cudd_Ref(result);
    return result;
  }

  const unsigned halfBits = 1u << (remainingVariables - 1);
  const std::uint64_t lowMask = (std::uint64_t(1) << halfBits) - 1;
  DdNode *low = buildBdd(manager, truth & lowMask,
                         remainingVariables - 1, variableIndex + 1);
  if (!low)
    return nullptr;

  DdNode *high = buildBdd(manager, truth >> halfBits,
                          remainingVariables - 1, variableIndex + 1);
  if (!high)
  {
    Cudd_RecursiveDeref(manager, low);
    return nullptr;
  }

  DdNode *variable = Cudd_bddIthVar(manager, variableIndex);
  DdNode *result = variable ? Cudd_bddIte(manager, variable, high, low) : nullptr;
  if (result)
    Cudd_Ref(result);
  Cudd_RecursiveDeref(manager, low);
  Cudd_RecursiveDeref(manager, high);
  return result;
}
#endif

// 6. Lsv_RunCutTruthTables：接上 lsv_cut_tt
bool Lsv_RunCutTruthTables(Abc_Ntk_t *pNtk, int k)
{
  //    呼叫自己的 enumerateCuts。
  //    用 Abc_NtkForEachNode 走訪 internal nodes，以 Abc_ObjId 取得 ID。
  //    對每個 cut 呼叫 computeTruthTable，再用 printf 輸出：
  //    <node ID>: <leaf IDs，空格分隔>: <十六進位 truth table>
  //    uint64_t 可用 PRIX64 格式（需 <cinttypes>），不加 0x。
  //    包含 internal node 的 trivial cut，不印 PI / PO 的 cuts。
  //    成功回傳 true，失敗回傳 false。

  CutTable cuts;
  if (!enumerateCuts(pNtk, k, cuts))
    return false;

  Abc_Obj_t *node;
  int i;
  Abc_NtkForEachNode(pNtk, node, i)
  {
    const int nodeId = Abc_ObjId(node);
    for (const Cut &cut : cuts[nodeId])
    {
      printf("%d:", nodeId);
      for (int leafId : cut)
        printf(" %d", leafId);
      printf(": %" PRIX64 "\n", computeTruthTable(node, cut));
    }
  }
  return true;
}

// 7. Lsv_RunCutBddSizes：接上 lsv_cut_bddsize
bool Lsv_RunCutBddSizes(Abc_Ntk_t *pNtk, int k)
{
  //    共用 enumerateCuts，走訪方式與 truth table 指令相同。
  //    每個 cut 先用自己的 computeTruthTable 取得 truth。
  //    用 Cudd_Init 建立 manager，變數數為 cut.size()。
  //    用 Cudd_AutodynDisable 保持變數順序；variableIndex 從 0 開始。
  //    呼叫自己的 buildBdd，再用 Cudd_DagSize 取得大小，不扣除 terminal。
  //    用 printf 輸出：<node ID>: <leaf IDs，空格分隔>: <十進位 BDD size>
  //    用 Cudd_RecursiveDeref 釋放 root BDD，再用 Cudd_Quit 關閉 manager。
  //    成功與失敗路徑都要清理。CUDD 實作放在 #ifdef ABC_USE_CUDD 中。
  //    trivial cut 的 BDD size 應為 2。

#ifdef ABC_USE_CUDD
  CutTable cuts;
  if (!enumerateCuts(pNtk, k, cuts))
    return false;

  Abc_Obj_t *node;
  int i;
  Abc_NtkForEachNode(pNtk, node, i)
  {
    const int nodeId = Abc_ObjId(node);
    for (const Cut &cut : cuts[nodeId])
    {
      const std::uint64_t truth = computeTruthTable(node, cut);
      DdManager *manager = Cudd_Init(static_cast<unsigned>(cut.size()), 0,
                                     CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);
      if (!manager)
        return false;
      Cudd_AutodynDisable(manager);

      DdNode *root = buildBdd(manager, truth, static_cast<int>(cut.size()), 0);
      if (!root)
      {
        Cudd_Quit(manager);
        return false;
      }

      const int size = Cudd_DagSize(root);
      printf("%d:", nodeId);
      for (int leafId : cut)
        printf(" %d", leafId);
      printf(": %d\n", size);

      Cudd_RecursiveDeref(manager, root);
      Cudd_Quit(manager);
    }
  }
  return true;
#else
  Abc_Print(-1, "lsv_cut_bddsize requires CUDD support.\n");
  return false;
#endif
}

// 先用 lsv/pa1/example.blif 對照 PDF，再測 mul.blif。
// 檢查 k=2..6、反相邊、trivial cut、leaf ID 順序及 64-bit 邊界。
// 這份基本方法以容易理解為主；大型 benchmarks 的效能可在正確後再處理。

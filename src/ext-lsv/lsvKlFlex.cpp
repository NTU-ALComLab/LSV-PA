#include "lsvKlFlex.h"
#include "lsvCut.h"

#include "sat/bsat/satSolver.h"
#include "sat/cnf/cnf.h"

#include <limits>
#include <memory>

// ABC 的 C 函式。將 miter 的 strashed 網路轉成 Cnf_Derive 使用的 AIG，
// 保留 PI/PO 索引。兩個旗標在這題都使用 0，處理的是組合電路。
extern "C" Aig_Man_t *Abc_NtkToDar(Abc_Ntk_t *pNtk, int fExors, int fRegisters);

// 讀 obj 的第 index 條輸入線。從 copy 找到舊 driver 在新圖的訊號，
// 再套用舊線的反相標記。複製 AND 的 fanin 和 PO 都會用到。
static Abc_Obj_t *CopyMiterFanin(const std::vector<Abc_Obj_t *> &copy,
                                Abc_Obj_t *obj, int index)
{
  int id = Abc_ObjId(Abc_ObjFanin(obj, index));
  return Abc_ObjNotCond(copy[id], Abc_ObjFaninC(obj, index));
}

// 依 pNtk 和指定的 cut 建立 miter，也就是比較原版和強制版輸出的 AIG。
// 回傳新網路由呼叫端釋放。PI 接腳順序是 [原始 PIs][強制用 PIs]，
// PO 接腳順序是 [原版 leaves][diff]，這個索引順序會用在後續 CNF 轉換。
static Abc_Ntk_t *BuildKlMiter(Abc_Ntk_t *pNtk, const KlCut &cut)
{
  Abc_Ntk_t *miter = Abc_NtkAlloc(ABC_NTK_STRASH, ABC_FUNC_AIG, 1);
  miter->pName = Extra_UtilStrsav("lsv_kl_flex_miter");
  // manager 是新 AIG 的管理器，AND/XOR 等操作都在這張圖上建節點。
  // original[id] 與 forced[id] 記錄原始節點 id 在兩份電路對應的訊號。
  auto *manager = static_cast<Abc_Aig_t *>(miter->pManFunc);
  std::vector<Abc_Obj_t *> original(Abc_NtkObjNumMax(pNtk), nullptr);
  std::vector<Abc_Obj_t *> forced(original.size(), nullptr);

  int constant = Abc_ObjId(Abc_AigConst1(pNtk));
  original[constant] = forced[constant] = Abc_AigConst1(miter);

  // 原本一個 PI 只建一次，兩個版本都接同一條線，確保比較時使用同一組 PI。
  // 後面按 root ID 各加一個 PI，這些才是 SAT 查詢時指定的強制值 p。
  Abc_Obj_t *node;
  int i;
  Abc_NtkForEachPi(pNtk, node, i)
    original[Abc_ObjId(node)] = forced[Abc_ObjId(node)] = Abc_NtkCreatePi(miter);
  for (int root : cut.roots)
    forced[root] = Abc_NtkCreatePi(miter);

  // nodes 依拓撲順序存原網路的內部 AND。走到一個 AND 時，它的兩個
  // fanin 已經對應到新 miter 的訊號，可以直接接起來。
  Vec_Ptr_t *nodes = Abc_NtkDfs(pNtk, 1);
  Vec_PtrForEachEntry(Abc_Obj_t *, nodes, node, i)
  {
    int id = Abc_ObjId(node);
    original[id] = Abc_AigAnd(manager, CopyMiterFanin(original, node, 0), CopyMiterFanin(original, node, 1));
    // forced[id] 若已有值，代表它是 root，剛才已接到指定用的 p。
    // 即使這個 root 的上游還有另一個 root，這裡也保留自己的 p。
    if (!forced[id])
      forced[id] = Abc_AigAnd(manager, CopyMiterFanin(forced, node, 0), CopyMiterFanin(forced, node, 1));
  }
  Vec_PtrFree(nodes);

  // pairs 依序放原版 PO0、強制版 PO0、原版 PO1、強制版 PO1，依此類推。
  // Abc_AigMiter 對每對做 XOR，再把結果 OR 起來，任一原本的 PO 不同就有 diff=1。
  Vec_Ptr_t *pairs = Vec_PtrAlloc(2 * Abc_NtkPoNum(pNtk));
  Abc_NtkForEachPo(pNtk, node, i)
  {
    Vec_PtrPush(pairs, CopyMiterFanin(original, node, 0));
    Vec_PtrPush(pairs, CopyMiterFanin(forced, node, 0));
  }
  Abc_Obj_t *diff = Abc_AigMiter(manager, pairs, 0);
  Vec_PtrFree(pairs);

  // 先把原版 leaf 值接到 PO，讓 SAT 能約束 U=u。若某個 leaf 依賴被強制
  // 的 root，兩份電路的 leaf 可能不同，所以這裡取 original[leaf]。
  // diff 放在最後一個 PO，和前面只供查詢 leaf 的接腳分開。
  for (int leaf : cut.leaves)
    Abc_ObjAddFanin(Abc_NtkCreatePo(miter), original[leaf]);
  Abc_ObjAddFanin(Abc_NtkCreatePo(miter), diff);
  return miter;
}

// 把 value 的各個 bit 轉成 SAT literals，追加到本次查詢的 assumptions。
// variables 按原始節點 ID 排列，所以用 value 的最高位對應第一個變數。
static void AppendAssumptions(std::vector<lit> &assumptions,
                              const std::vector<int> &variables, std::size_t value)
{
  // 例如 value=011 且有三個 variables，會依序加上 var0=0、var1=1、var2=1。
  // Abc_Var2Lit 的第二個參數代表取反，因此固定成 0 時要傳 true。
  for (std::size_t i = 0; i < variables.size(); ++i)
  {
    bool bit = (value >> (variables.size() - 1 - i)) & 1;
    assumptions.push_back(Abc_Var2Lit(variables[i], !bit));
  }
}

// 將低位在前的 nibbles 轉成大寫十六進位字串。每個 nibble 是四個 mask bits，
// 其值 0 到 15 可直接當作 digits 的索引。全為 0 時回傳 "0"。
static std::string HexMask(const std::vector<unsigned char> &nibbles)
{
  const char digits[] = "0123456789ABCDEF";
  std::string result;
  // 十六進位字串從高位往低位寫。看到第一個非零位之前都跳過，
  // 因此會省略前導零。用 nibble 陣列也能存超過 64 bits 的 mask。
  for (auto it = nibbles.rbegin(); it != nibbles.rend(); ++it)
    if (*it || !result.empty())
      result += digits[*it];
  return result.empty() ? "0" : result;
}

// originalRoots[u] 是 leaf 值為 u 時，roots 原本會算出的組合，編號方式和 root 組合 c 相同。
// 由 K2，roots 的值完全由 leaves 決定，所以用 PA1 的真值表從 leaves 模擬到 roots 即可。
// PA1 的真值表也是最小 ID 的 leaf 在最高位，和 u 的編號一致。
// 真值表用 64 位元，leaf 超過 6 個時回傳空 vector，呼叫端就不使用這個捷徑。
static std::vector<std::size_t> OriginalRootValues(Abc_Ntk_t *pNtk, const KlCut &cut)
{
  std::vector<std::size_t> values;
  if (cut.leaves.size() > 6)
    return values;
  Cut leaves;
  leaves.leaves = cut.leaves;
  std::vector<uint64_t> tables;
  for (int root : cut.roots)
    tables.push_back(Lsv_CutTt(Abc_NtkObj(pNtk, root), leaves));
  values.assign(std::size_t{1} << cut.leaves.size(), 0);
  for (std::size_t u = 0; u < values.size(); ++u)
    for (uint64_t table : tables)
      values[u] = (values[u] << 1) | ((table >> u) & 1); // 最小 ID 的 root 先放，最後落在最高位
  return values;
}

// 用同一個 solver 求解一次。assumptions 是這次才生效的 literals，
// 回傳 l_True、l_False 或 l_Undef。最後四個 0 表示未設定求解上限。
static int SolveKlSat(sat_solver *solver, std::vector<lit> &assumptions)
{
  lit *begin = assumptions.data();
  return sat_solver_solve(solver, begin, begin + assumptions.size(), 0, 0, 0, 0);
}

// 對一組最大 cut 計算 flexibility。masks[u] 是 leaf 值 u 對應的 mask，
// 其中 bit c 為 1 表示 root 組合 c 在所有符合 U=u 的情況下都安全。
// 建圖、轉 CNF 或 SAT 查詢若失敗，回傳 nullopt 交給指令入口回報。
std::optional<std::vector<std::string>> Lsv_ComputeFlexMasks(Abc_Ntk_t *pNtk, const KlCut &cut)
{
  // 每種 u、c 都用整數編號，下面會以 1 左移節點個數來算總數。
  // 先確認位移的位數在 size_t 能表示的範圍。
  if (cut.leaves.size() >= std::numeric_limits<std::size_t>::digits ||
      cut.roots.size() >= std::numeric_limits<std::size_t>::digits)
  {
    Abc_Print(-1, "Too many cut nodes to index all assignments.\n");
    return std::nullopt;
  }

  // 一個 cut 只建一張 miter。aig 是供 CNF 轉換的 ABC 表示法，cnf 是
  // SAT solver 使用的布林公式。給 Cnf_Derive 全部的 PO 數量，讓每個 PO
  // 都保留為可約束的變數。第一次查 U=u 時，diff 必須還能自由取值。
  // unique_ptr 搭配 ABC 的釋放函式，成功或提早返回時都會清理這些資源。
  const std::unique_ptr<Abc_Ntk_t, decltype(&Abc_NtkDelete)> miter(BuildKlMiter(pNtk, cut), Abc_NtkDelete);
  const std::unique_ptr<Aig_Man_t, decltype(&Aig_ManStop)> aig(Abc_NtkToDar(miter.get(), 0, 0), Aig_ManStop);
  if (!aig)
    return std::nullopt;
  const std::unique_ptr<Cnf_Dat_t, decltype(&Cnf_DataFree)> cnf(Cnf_Derive(aig.get(), Aig_ManCoNum(aig.get())), Cnf_DataFree);
  if (!cnf)
    return std::nullopt;
  const std::unique_ptr<sat_solver, decltype(&sat_solver_delete)> solver(
    static_cast<sat_solver *>(Cnf_DataWriteIntoSolver(cnf.get(), 1, 0)), sat_solver_delete);
  if (!solver)
    return std::nullopt;

  // leafVars 是原版 leaves 的 CNF 變數，rootVars 是強制輸入 p 的變數，
  // diffVar 是最後那個比較位元。先依 miter 接腳的建立順序找到轉換後的
  // CI/CO，才用它的新 ID 查 pVarNums。這裡不能直接用原始電路的 node ID。
  std::vector<int> leafVars;
  for (int i = 0; i < static_cast<int>(cut.leaves.size()); ++i)
    leafVars.push_back(cnf->pVarNums[Aig_ManCo(aig.get(), i)->Id]);
  std::vector<int> rootVars;
  int firstForcingPi = Abc_NtkPiNum(pNtk);
  for (int i = 0; i < static_cast<int>(cut.roots.size()); ++i)
    rootVars.push_back(cnf->pVarNums[Aig_ManCi(aig.get(), firstForcingPi + i)->Id]);
  int diffVar = cnf->pVarNums[Aig_ManCo(aig.get(), static_cast<int>(leafVars.size()))->Id];

  // leafPatterns 是要輸出的列數，rootPatterns 是每列要試幾組強制值。
  // 每四個 bit 用一個 nibble 儲存，allAllowed 是所有選項都允許時的字串。
  const std::size_t leafPatterns = std::size_t{1} << leafVars.size();
  const std::size_t rootPatterns = std::size_t{1} << rootVars.size();
  const std::size_t nibbleCount = (rootPatterns + 3) / 4;
  const std::string allAllowed = rootPatterns == 2 ? "3" : std::string(nibbleCount, 'F');
  std::vector<std::string> masks;
  std::vector<lit> assumptions;
  assumptions.reserve(leafVars.size() + rootVars.size() + 1);
  const std::vector<std::size_t> originalRoots = OriginalRootValues(pNtk, cut);

  for (std::size_t u = 0; u < leafPatterns; ++u)
  {
    // 第一道查詢只固定 U=u，判斷原始 PI 是否能產生這組 leaf 值。
    assumptions.clear();
    AppendAssumptions(assumptions, leafVars, u);
    int reachable = SolveKlSat(solver.get(), assumptions);
    if (reachable == l_False)
    {
      // 若 U=u 是 UNSAT，實際電路用不到這一列，所有 root 組合都允許。
      masks.push_back(allAllowed);
      continue;
    }
    if (reachable != l_True)
      return std::nullopt;

    std::vector<unsigned char> nibbles(nibbleCount, 0);
    for (std::size_t c = 0; c < rootPatterns; ++c)
    {
      // c 就是 roots 原本的值時，強制成 c 等於什麼都沒改，輸出不可能變，一定允許。
      // 這種查詢一定是 UNSAT，但 SAT 要證明兩份電路完全等價，在大型算術電路上可能要好幾分鐘。
      if (!originalRoots.empty() && c == originalRoots[u])
      {
        nibbles[c / 4] |= 1U << (c % 4);
        continue;
      }
      // 保留前面的 U=u，換掉上一輪的 p=c，再加上 diff=1 來找反例。
      assumptions.resize(leafVars.size());
      AppendAssumptions(assumptions, rootVars, c);
      assumptions.push_back(Abc_Var2Lit(diffVar, 0));
      // SAT 代表找到一組 PI 會讓輸出改變，所以 c 的 bit 留 0。
      // UNSAT 代表找不到反例，才把 c 的 bit 設成 1。c/4 是十六進位位址，
      // c%4 是該位址內的哪個 bit。求解結果不明時，回傳錯誤而不寫入 mask。
      int counterexample = SolveKlSat(solver.get(), assumptions);
      if (counterexample == l_False)
        nibbles[c / 4] |= 1U << (c % 4);
      else if (counterexample != l_True)
        return std::nullopt;
    }
    masks.push_back(HexMask(nibbles));
  }
  return masks;
}

# LSV PA1 — Exercise 4: k-feasible Cuts

R15921090 Tse-Chuan Yang

## 檔案

| 檔案 | 內容 |
|---|---|
| `lsvCmd.cpp` | 註冊 ABC 指令（`init`），以及各指令的入口：檢查參數、確認網路已經 `strash` |
| `lsvCut.h` | `Cut`、`CutTable` 型別與 cut 相關函式的宣告 |
| `lsvCut.cpp` | cut enumeration、truth table（4.1）、BDD size（4.2）的計算與輸出 |
| `module.make` | 把 `lsvCmd.cpp`、`lsvCut.cpp` 加進 ABC 的編譯清單 |

## 編譯與執行

```bash
make -j8
./abc
```

```
abc 01> read lsv/pa1/example.blif
abc 02> strash
abc 03> lsv_cut_tt 3
abc 04> lsv_cut_bddsize 3
```

## 指令

### `lsv_cut_tt <k>`（4.1）

列出每個 AND 節點的所有 k-feasible cut，並印出該 cut 的真值表（hex）。

```
<node>: <cut 的節點 ID，由小到大>: <truth table>
```

範例（題目 Fig. 1，`lsv/pa1/example.blif`）：

```
5: 5: 2
5: 1 2: 4
6: 6: 2
6: 2 3: 8
7: 7: 2
7: 5 6: 4
7: 2 3 5: 2A
7: 1 2 6: 10
7: 1 2 3: 30
```

### `lsv_cut_bddsize <k>`（4.2）

列出每個 AND 節點的所有 k-feasible cut，並印出該 cut 的 ROBDD 大小（`Cudd_DagSize`）。
BDD 變數順序依 node ID：ID 小的變數靠近 root。

```
<node>: <cut 的節點 ID，由小到大>: <BDD size>
```

範例（題目 Fig. 1）：

```
5: 5: 2
5: 1 2: 3
6: 6: 2
6: 2 3: 3
7: 7: 2
7: 5 6: 3
7: 2 3 5: 4
7: 1 2 6: 4
7: 1 2 3: 3
```

## 演算法

### Cut enumeration — `Lsv_NtkEnumCuts`

由下往上（bottom-up）計算，結果存在 `CutTable cuts`（`cuts[ID]` = 該節點的所有 cut）：

1. PI：只有 trivial cut `{自己}`。
2. AND 節點 n（fanin 為 n0、n1），依 ID 由小到大處理：
   - 先加入 trivial cut `{n}`；
   - 對 `cuts[n0] × cuts[n1]` 的每一對 cut 取聯集（`Lsv_CutMerge`）；
   - 大小超過 k 的丟掉，重複的丟掉。

strash 後的 AIG 中，fanin 的 ID 一定小於節點本身（新節點的 ID = 目前物件數，見
`src/base/abc/abcObj.c`），所以照 ID 順序走時 fanin 的 cut 一定已經算好；程式中以
`assert(id0 < id && id1 < id)` 檢查。

每個 cut 的 leaf 以排序好的 `std::vector<int>` 表示，`std::set_union` 合併後仍保持排序，
因此輸出直接符合「由小到大」的格式。

### Truth table — `Lsv_CutTt`

使用 bit-parallel simulation，一個 `uint64_t` 的第 idx 個 bit 代表真值表第 idx 行，
一次算完全部 2^m 行（m = cut 大小，m ≤ 6）。

1. **Leaf 的模式**：cut 中第 j 個 leaf（ID 由小到大）在第 idx 行的值為
   `(idx >> (m-1-j)) & 1`，也就是 ID 最小的 leaf 對應 assignment 的最高位。
   以 m = 3 為例，三個 leaf 的模式分別是 `0xF0`、`0xCC`、`0xAA`。
2. **往下遞迴**（`Lsv_NodeTt`）：從 root 開始，碰到 leaf 就回傳它的模式；
   否則計算兩個 fanin，complemented edge 取 `~`，再做 `&`。
   cut 擋住了 root 往 PI 的所有路徑，所以遞迴一定停在 leaf。
3. **Mask**：`~` 會把超過 2^m 的高位設成 1，最後和 `(1 << 2^m) - 1` 做 AND。
   m = 6 時 `1 << 64` 是 undefined behavior，所以直接用全 1。

例：node 7、cut `{2, 3, 5}`

```
n6 = x1 & x2   = 0xF0 & 0xCC  = 0xC0
n7 = n5 & ~n6  = 0xAA & ~0xC0 = 0x2A
```

### BDD size — `Lsv_CutBddSize`

與 truth table 相同的遞迴架構，只是每個節點的值從 `uint64_t` 換成 CUDD 的 BDD。
只使用 CUDD 的基本運算（`Cudd_bddIthVar`、`Cudd_bddAnd`、`Cudd_NotCond`），
沒有呼叫 ABC 內建的 BDD 建構函式。

1. **Leaf → 變數**：cut 中第 j 個 leaf 對應 `Cudd_bddIthVar(dd, j)`。沒有開啟 dynamic
   reordering，變數 j 固定在第 j 層，所以 ID 最小的 leaf 在最上面，符合題目要求的順序。
2. **往下遞迴**（`Lsv_NodeBdd`）：碰到 leaf 就回傳它的變數；否則計算兩個 fanin，
   complemented edge 用 `Cudd_NotCond`（只翻轉指標的最低位，不建新節點），
   再用 `Cudd_bddAnd` 合併。CUDD 會自動化簡成 ROBDD。
   算過的節點存在 `memo`（AIG node ID → BDD），同一個節點不重算。
3. **大小**：`Cudd_DagSize`。CUDD 使用 complemented edge，只有一個終端節點，
   所以大小 = 變數節點數 + 1。例如 `7: 1 2 3` 的函數化簡後是 x0·x1'，
   x2 被化簡掉，大小為 3。
4. **記憶體**：`memo` 裡每個 BDD 都 `Cudd_Ref` 一次，cut 處理完後全部
   `Cudd_RecursiveDeref`。整個指令共用一個 `DdManager`，結束前以
   `assert(Cudd_CheckZeroRef(dd) == 0)` 確認沒有漏掉的 reference，再 `Cudd_Quit`。

`Cudd_NotCond` 用到的 `ptrint` 型別定義在 `bdd/cudd/cuddInt.h`，因此 `lsvCut.cpp`
額外 include 了這個檔案。

## 優化

為了加速，每個 cut 是一個 `struct Cut`，除了 leaf 之外多存一個簽名：

```cpp
struct Cut
{
  std::vector<int> leaves; // leaf 的節點 ID，由小到大
  uint64_t sign = 0;       // 簽名
};
```

一個節點的候選 cut 數是兩個 fanin 的 cut 數相乘，大電路在 k = 6 時一個節點可能有
上萬對要合併，但**絕大多數合併後都超過 k、會被丟掉**。初版每一對都要建一個新的
vector、完整合併、再檢查大小，log2 需要約 2 小時。優化後的流程：

1. **簽名篩選**：每個 cut 帶一個 64 位元簽名 `sign`，每個 leaf 打開第 `ID % 64` 個 bit
   （聯集的簽名 = 兩邊簽名 OR 起來）。合併前先算 `popcount(c0.sign | c1.sign)`，
   大於 k 就代表合併後一定超過 k 個 leaf，**不用合併直接跳過**。
   不同 ID 可能撞到同一個 bit，這只會讓 1 的個數少算、不會多算，所以不會誤刪合法的 cut。
   大部分配對在這一步就被淘汰，是效果最大的優化。
2. **重複使用暫存的 cut**：合併結果放進迴圈外的 `Cut u`，`clear()` 後再填，
   不用每次都配置新的記憶體。
3. **用 `std::set` 檢查重複**：原本用 `std::find` 和已有的 cut 逐一比較，
   改成 `std::set::insert` 的回傳值判斷。

對應的程式（`Lsv_NtkEnumCuts` 的雙層迴圈）：

```cpp
Cut u; // 放在迴圈外面重複使用（優化 2）
for (const Cut &c0 : cuts[id0])
{
  for (const Cut &c1 : cuts[id1])
  {
    if (__builtin_popcountll(c0.sign | c1.sign) > k)
      continue; // 簽名就知道太大，不用合併（優化 1）
    Lsv_CutMerge(c0, c1, u);
    if ((int)u.leaves.size() > k)
      continue; // 太大就丟
    if (!seen.insert(u).second)
      continue; // 重複就丟（優化 3，seen 是 std::set<Cut>）
    my.push_back(u);
  }
}
```

以 log2、k = 6 為例，`lsv_cut_tt` 從約 2 小時降到約 16 秒。

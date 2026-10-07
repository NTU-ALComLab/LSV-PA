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

每個 cut 以排序好的 `std::vector<int>` 表示，`std::set_union` 合併後仍保持排序，
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

## 驗證

- `example.blif`：兩個指令的輸出都與題目範例逐行相同。
- `lsv/pa1/benchmarks/` 中的 adder、int2float、router、mem_ctrl，k = 2、4、6：
  與另外寫的 Python 檢查程式結果完全一致。`lsv_cut_bddsize` 另外也驗證了 sqrt。
  - truth table：逐行代入 2^m 種輸入（brute force），不使用 bit-parallel。
  - BDD size：由 truth table 直接計算 ROBDD 節點數（相異且非常數的子函數個數，
    f 與 f' 算同一個，再加 1 個終端），不使用 CUDD。

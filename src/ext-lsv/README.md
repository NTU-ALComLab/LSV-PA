# PA1：各函式的實作方向

目前 `lsvCut.h` 已有資料結構與宣告，`lsvCut.cpp` 是待實作骨架。裡面的 `return false`、`return 0`、`return nullptr` 都只是佔位值。

目標是完成兩個 ABC 指令：

```text
read lsv/pa1/example.blif
strash
lsv_cut_tt 3
lsv_cut_bddsize 3
```

兩個指令共用 cut enumeration。第一個計算 truth table；第二個由你自己算出的 truth table 建立 BDD，再取得大小。

## 資料結構

| 型別       | 意義                               | 例子                           |
| ---------- | ---------------------------------- | ------------------------------ |
| `Cut`      | 一個 cut 的 leaf IDs，遞增且不重複 | `{1, 2}`                       |
| `CutList`  | 一個節點的所有 cuts                | `{{5}, {1, 2}}`                |
| `CutTable` | 以 node ID 索引各節點的 cuts       | `cuts[5]` 是節點 5 的 cut list |

Cut leaf 是這次計算的輸入邊界，可以是 PI，也可以是 internal node。遇到 leaf 時，應將它視為獨立變數，停止往下展開。

每個 internal node 也要包含 trivial cut `{自己的 ID}`。它表示將整個節點當成一個輸入變數，因此 truth table 是 `2`，BDD size 是 `2`。

## 1. `mergeCuts(left, right, k, result)`

**目的：**計算兩個 leaf 集合的聯集，判斷是否不超過 `k`。

高階演算法：

1. 將 `left` 和 `right` 的 IDs 放進暫存容器。
2. 排序，再移除重複的 IDs。
3. 若數量大於 `k`，回傳 `false`。
4. 否則將結果存入 `result`，回傳 `true`。

例如 `{1, 2}` 與 `{2, 3}` 合併成 `{1, 2, 3}`；`k=3` 時接受，`k=2` 時拒絕。結果數量可以小於 `k`。

**使用的 API：**不需要 ABC；一般迴圈或 `std::sort`、`std::unique` 即可。使用 `std::unique` 後，還需要移除容器尾端不再使用的元素。

## 2. `enumerateCuts(pNtk, k, cuts)`

**目的：**由輸入往輸出方向，計算每個 internal node 的所有 cuts，存進 `cuts[nodeID]`。

高階演算法：

1. 清除舊資料，將 `cuts` 大小設定為 node ID 所需的範圍。
2. 每個 CI 的 cut list 放入 singleton cut `{自己的 ID}`。純組合電路的 CI 就是 PI。
3. 常數 1 節點的 cut list 放入「一個空 cut」，表示沒有輸入變數。這與「沒有任何 cut」不同；空 list 會使後面的組合無法進行。
4. 取得 fanins 在目前節點之前的拓樸順序。
5. 對每個 internal node，先加入 trivial cut。
6. 取得兩個 fanins，從各自的 cut list 各取一個 cut，考慮每一對組合。
7. 呼叫自己的 `mergeCuts`；合法且尚未存在的結果就加入目前節點的 list。
8. 完成所有節點後釋放暫存走訪向量，回傳 `true`。

這個方法能由下往上計算，是因為處理目前節點時，兩個 fanins 的 cuts 都已經準備好。

**使用的 ABC API：**

| API                                  | 用途                                         |
| ------------------------------------ | -------------------------------------------- |
| `Abc_NtkObjNumMax`                   | 決定 ID 索引陣列大小；不是有效節點數量       |
| `Abc_NtkForEachCi`、`Abc_ObjId`      | 初始化輸入 cuts                              |
| `Abc_AigConst1`                      | 取得常數節點                                 |
| `Abc_NtkDfs(pNtk, 1)`                | 取得走訪順序，也包含 dangling internal nodes |
| `Vec_PtrForEachEntry`、`Vec_PtrFree` | 走訪並釋放 DFS 結果                          |
| `Abc_ObjFanin0`、`Abc_ObjFanin1`     | 取得目前節點的兩個 fanins                    |

只將完全相同的 leaf 集合視為重複。不自行設定 cut 數量上限，也不照搬 ABC 內建的 dominance filtering。反相邊不影響 leaf 集合。

## 3. `evaluate(node, cut, assignment)`

**目的：**對一組指定的 leaf 輸入值，遞迴算出目前節點的 Boolean 值。回傳 `false` 是邏輯 0，`true` 是邏輯 1。

高階演算法：

1. 先檢查目前節點是否在 `cut` 裡。
2. 若是第 `j` 個 leaf，就回傳它在 `assignment` 中的輸入值，不再展開 fanins。
3. 若不是 leaf，但它是常數 1，就回傳 `true`。
4. 否則遞迴求兩個 fanins 的值。
5. 根據兩條邊的反相標記，各自翻轉對應的值。
6. 將兩個值做 AND，回傳結果。

假設 `cut=[1, 2]`，輸入順序必須是：

| `assignment` | 節點 1 的值 | 節點 2 的值 |
| ------------ | ----------- | ----------- |
| 0（`00`）    | 0           | 0           |
| 1（`01`）    | 0           | 1           |
| 2（`10`）    | 1           | 0           |
| 3（`11`）    | 1           | 1           |

也就是 `cut[j]` 對應 assignment 的第 `m-1-j` 位，`m` 是實際 leaf 數。

**使用的 ABC API：**`Abc_ObjId`、`Abc_AigNodeIsConst`、`Abc_ObjFanin0/1`、`Abc_ObjFaninC0/1`。必要時用 `Abc_ObjIsCi` 檢查是否遇到未列入 cut 的輸入；有效的 cut 不應發生這種情況。

## 4. `computeTruthTable(root, cut)`

**目的：**把所有輸入組合的輸出值，組成一個 `std::uint64_t`。

高階演算法：

1. 令 `m=cut.size()`，將 truth table 初始化為 0。
2. 從 assignment 0 枚舉到 `2^m-1`。
3. 每組呼叫自己的 `evaluate(root, cut, assignment)`。
4. 若輸出為 1，就設定 truth table 中第 assignment 個 bit。
5. 回傳組好的整數。

例如 `x1 AND NOT x2` 在 `00, 01, 10, 11` 的輸出依序是 `0, 0, 1, 0`。按 MSB 到 LSB 寫是 `0100`，十六進位為 `4`。

**使用的 API：**不需要新的 ABC API，只呼叫自己的 `evaluate`。設定 bit 時使用 64-bit 無號值；`m=6` 時最高會設定第 63 位，不能執行移位 64 位的運算。

## 5. `buildBdd(manager, truth, remainingVariables, variableIndex)`

**目的：**自行用 Shannon 展開，把已算好的 truth table 建立成 BDD。

第一次呼叫時，`remainingVariables=cut.size()`、`variableIndex=0`。變數 0 對應最小的 leaf ID，變數 1 對應下一個 leaf，以此類推。

高階演算法：

1. 若沒有剩餘變數，truth table 只剩一個有效 bit，直接回傳常數 0 或 1 的 BDD。
2. 否則將有效的 truth bits 分成相等的兩半：低半部是目前變數為 0 的函數，高半部是目前變數為 1 的函數。
3. 遞迴建立 `low` 和 `high`；剩餘變數減一，變數索引加一。
4. 取得目前變數 `x`，用 `ITE(x, high, low)` 組合兩個分支。
5. 保護結果的引用，再釋放兩個分支各自持有的引用，回傳結果。

例如 `truth=0100` 的兩個分支是 `low=00`、`high=01`。它們分別表示第一個 leaf 固定為 0、1 時，第二個 leaf 的 truth table。

你負責寫分割與遞迴流程；一般 CUDD 操作負責共用節點與 BDD reduction。

**使用的 CUDD API：**`Cudd_ReadOne`、`Cudd_Not`、`Cudd_bddIthVar`、`Cudd_bddIte`、`Cudd_Ref`、`Cudd_RecursiveDeref`。

**引用約定：**每次成功回傳都持有一次引用。`low` 必須受保護，才能繼續建立 `high`；即使它們指向相同 BDD，也要釋放各自持有的引用。失敗回傳 `nullptr`，並清理已建立的分支。

## 6. `Lsv_RunCutTruthTables(pNtk, k)`

**目的：**串起 cut enumeration、truth table 計算與輸出。

高階演算法：

1. 呼叫自己的 `enumerateCuts`。
2. 走訪 internal nodes，取得 `cuts[nodeID]`。
3. 每個 cut 呼叫 `computeTruthTable`。
4. 印出 node ID、排序後的 leaf IDs，以及十六進位 truth table。
5. 全部完成回傳 `true`；流程失敗回傳 `false`。

格式範例：

```text
5: 5: 2
5: 1 2: 4
```

**使用的 API：**`Abc_NtkForEachNode`、`Abc_ObjId`、一般 `printf`。64-bit 十六進位可使用 `<cinttypes>` 的 `PRIX64`，不加 `0x`。PI、PO 的 cuts 不需要印。

## 7. `Lsv_RunCutBddSizes(pNtk, k)`

**目的：**串起 cut enumeration、BDD 建構、大小計算與輸出。

高階演算法：

1. 呼叫同一份 `enumerateCuts`，走訪所有 internal roots 的 cuts。
2. 每個 cut 先用自己的 `computeTruthTable` 取得函數。
3. 建立變數數量等於 leaf 數的 CUDD manager，停用自動重排。
4. 呼叫自己的 `buildBdd`，讓變數索引與排序後的 leaf IDs 一致。
5. 用 `Cudd_DagSize` 取得大小，印出 node ID、leaves 和十進位大小。
6. 釋放 root BDD 的引用，再關閉 manager。成功與失敗路徑都要清理。
7. 全部完成回傳 `true`；流程失敗回傳 `false`。

**使用的 API：**`Abc_NtkForEachNode`、`Abc_ObjId`、`Cudd_Init`、`Cudd_AutodynDisable`、`Cudd_DagSize`、`Cudd_RecursiveDeref`、`Cudd_Quit`。

直接使用 `Cudd_DagSize` 的結果，不扣 terminal。trivial cut 的大小應是 `2`。CUDD 功能放在 `ABC_USE_CUDD` 條件區塊中。

## 指令入口與實作順序

`lsvCmd.cpp` 已處理指令註冊、`k` 的解析、空 network 與 `strash` 檢查。`Lsv_CommandCutTt` 呼叫 `Lsv_RunCutTruthTables`；`Lsv_CommandCutBddSize` 呼叫 `Lsv_RunCutBddSizes`。

建議先完成 1 到 4，再完成第 6 個函式，確認 truth table 指令符合 PDF。接著完成 5 與 7，確認 BDD size。

先測 `example.blif`，再測 `mul.blif`。至少檢查 trivial cut、反相邊、重複 leaves、變數順序，以及 `k=6` 的 64-bit 邊界。

這份基本方法以容易理解為主；效能可在正確後再改善。作業要求的 cut 結構、列舉、truth table 與 cut BDD 建構流程都必須自行撰寫，不能呼叫、複製或重用 ABC 內建的 cut-specific 功能。一般 ABC 網路 API 與題目允許的一般 CUDD 操作可以使用。

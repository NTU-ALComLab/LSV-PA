# HW1 Exercise 4 解題說明

## 完成內容與使用方式

實作放在 `src/ext-lsv/`，兩個 ABC 指令是：

```text
lsv_cut_tt <k>
lsv_cut_bddsize <k>
```

`k` 必須是 2 到 6 的整數。先 `read` 再 `strash`，兩個指令只分析目前的 AIG，不修改網路；只印內部 AND 節點，不印 PI、PO 或常數節點。

Ubuntu 執行：

```bash
cd ~/LSV-PA
make -j4
./abc -c "read lsv/pa1/ex4_sample.blif; strash; lsv_cut_tt 3"
./abc -c "read lsv/pa1/ex4_sample.blif; strash; lsv_cut_bddsize 3"
python3 lsv/pa1/test_ex4.py --abc ./abc
```

檔案分工：

- `lsvCmd.cpp`：註冊指令、解析 k、檢查網路類型，呼叫共同分析入口。
- `lsvCut.h`：宣告 `Lsv_PrintCuts`。
- `lsvCut.cpp`：列舉 cut、計算 truth table、建立 BDD 並輸出大小。
- `module.make`：把兩個 `.cpp` 納入 ABC 編譯。

## 1. 理解 AIG 與 cut

AIG 的內部節點是二輸入 AND，反相以邊上的 complement bit 表示。不能只取 fanin 的函數相 AND，必須先讀取 `Abc_ObjFaninC0/C1`，再依需要取反。

root 的 cut 是一組邊界節點：以它們當作獨立輸入，就能評估 root 的函數。k-feasible 表示這組葉子不超過 k 個，並不是每個 cut 都恰好 k 個輸入。

每個內部節點還有 trivial cut `{root}`，其函數就是該變數本身，因此 truth table 是 `2`，BDD size 是 `2`。

葉子 ID 按遞增順序儲存，以便集合合併、重複檢查及固定變數順序。不同 cut 的葉子是不同的獨立變數，即使葉子本身在原電路中有邏輯關係，也不能把這些關係帶入 cut 的輸入 assignment。

## 2. 用動態規劃列舉 cut

令 `Cuts(v)` 表示節點 v 的 cut 集合。初始化：

```text
Cuts(PI) = {{PI}}
Cuts(constant 1) = {empty set}
```

對內部節點 `v = AND(a,b)`：

```text
Cuts(v) = {{v}}
for each A in Cuts(a):
    for each B in Cuts(b):
        C = sorted_union(A, B)
        if |C| <= k and C has not appeared:
            append C to Cuts(v)
```

`Merge` 用兩個索引掃過排序後的葉子集合，遇到相同 ID 只放一次；一旦超過 k，立即放棄這個候選。`std::set<Cut>` 只用來刪掉完全相同的集合。

例如題目範例的 root 7 有兩個 fanin 5、6，且：

```text
Cuts(5) = {{5}, {1,2}}
Cuts(6) = {{6}, {2,3}}
```

兩兩聯集，加上 `{7}`，得到：

```text
{7}, {5,6}, {2,3,5}, {1,2,6}, {1,2,3}
```

最後一組是 `{1,2} union {2,3}`，共同輸入 2 只算一次，所以是 3-feasible。

**不做 dominance pruning。** 在 technology mapping 中常會刪除某個較小 cut 的超集合；本題要求所有 cut，所以保留。重收斂時，兩個 fanin 的 cut 聯集可能同時包含某節點與它的祖先，造成冗餘變數，也保留這種合法聯集。

處理順序必須保證 fanin 比 root 早完成。`ConeOrder` 使用明確的 stack 做 DFS postorder，而非假設 ID 就是拓樸順序；也避免深電路造成 C++ 遞迴 stack overflow。以 stamp 標記已走訪的節點，每次分析新 cone 不必清空整個標記陣列。

## 3. 建立每個 cut 的 truth table

對一個有 m 個葉子的 cut，實際真值表有 `2^m` 個 bit。因為 `m <= k <= 6`，一個 `uint64_t` 就能容納。

假设排序後的 cut 是 `[c0,c1,...,c(m-1)]`。assignment 用二進位遞增：第一個變數是 assignment 的最高有效位元；assignment 的整數值 t 對應 truth table 的第 t 個 bit。

```text
value(cj, t) = (t >> (m-1-j)) & 1
TT = sum(output(t) << t), t = 0..2^m-1
```

例如兩輸入時：

| assignment | c0 | c1 | 真值表 bit |
|---|---:|---:|---:|
| 00 | 0 | 0 | 0 |
| 01 | 0 | 1 | 1 |
| 10 | 1 | 0 | 2 |
| 11 | 1 | 1 | 3 |

所以 c0 的表是 `0xC`，c1 是 `0xA`；`c0 & !c1` 的表是 `0x4`。

`Variable` 產生每個葉子的整張真值表。之後不是對每個 assignment 重新走電路，而是一次用 64-bit bitwise AND 同時評估所有 assignments：

```text
a = TT(fanin0)
b = TT(fanin1)
if fanin0 edge is complemented: a ^= mask
if fanin1 edge is complemented: b ^= mask
TT(node) = a & b
```

`mask` 的低 `2^m` 個 bit 是 1，避免取反污染有效範圍之外的 bit。m=6 時不能計算 `1ULL << 64`，這是 undefined behavior；實作直接使用 `uint64_t` 最大值。

計算 cone 時遇到 cut 葉子就停止往下走。這點很重要：cut 葉子要被當作變數，而不是繼續展開原本的函數。遇到 constant 1 就填 mask；若遇到未包含在 cut 裡的 PI，表示邊界無效，回報失敗。結果以大寫 hexadecimal 印出，不加 `0x`。

## 4. 建立 ROBDD 並取得大小

BDD 與 truth table 分別由 AIG cone 建立，BDD 不依賴 truth table 的結果，也沒有呼叫 ABC 內建 cut 列舉或 cut BDD 產生器。

建立獨立的 CUDD manager，並關閉 dynamic reordering。對排序後的 cut，把最小 ID 葉子對應到 BDD variable 0，下一個對應 variable 1，依此類推。因此 smaller ID 永遠在較前面的 decision level。

逐節點的建構規則：

```text
BDD(cut leaf j) = Cudd_bddIthVar(manager, j)
BDD(constant 1) = Cudd_ReadOne(manager)
BDD(node) = Cudd_bddAnd(manager, edgeAdjustedBDD(a), edgeAdjustedBDD(b))
```

反相邊透過 `Cudd_Not` 處理。CUDD 自動維持固定變數順序下的 reduced、shared BDD；最後以題目指定的 `Cudd_DagSize(rootBDD)` 取得大小。

**大小包含可達的終端節點。** CUDD 以 complemented edge 表示反相，因此 0 與 1 共用一個實體終端；不能直接拿「兩個終端都算」的普通 BDD 節點數來比。例如單一變數是 1 個 decision node 加 1 個實體 terminal，所以 size=2。

每次得到 BDD pointer 都 `Cudd_Ref`，評估該 cut 後逐一 `Cudd_RecursiveDeref`。即使兩個節點共用同一個函數，reference 和 dereference 次數仍平衡。全部分析完成後 `Cudd_Quit`；CUDD 配置失敗時也會清理已建立的 reference。

## 5. 題目範例

`ex4_sample.blif` 對應：

```text
5 = x0 & !x1
6 = x1 & x2
7 = 5 & !6
```

`lsv_cut_tt 3` 輸出應為：

```text
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

例如 cut `[1,2,3]` 的函數化簡成 `x0 & !x1`，x2 不影響輸出。只有 assignments `100` 和 `101` 輸出為 1，所以 bit 4、5 是 1，得到 `0x30`。

BDD size 輸出：

```text
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

最後一列有三個 cut 輸入，但 x2 不影響結果，ROBDD 會消掉它，留下 x0、x1 的 decision nodes 及一個 terminal，size=3。

## 6. 驗證方法與結果

Ubuntu 使用 g++ 13、C++17 與 ABC 原本的 CUDD 成功編譯。

`test_ex4.py` 使用 ABC `write_dot` 匯出的原始節點 ID 與實線／虛線邊，建立獨立 oracle：

1. 窮舉 ancestor 節點子集合，再检查該集合是否能由各個路徑上的停止選擇形成 cut；重收斂路徑允許不同停止選擇。
2. 對每個 cut 逐筆枚舉所有 assignment，用 scalar boolean simulation 計算 truth table。
3. 用 Shannon expansion 建立具有 complement edges 的 ROBDD，合併相同節點、消除相同分支，再數 root 可達節點；不呼叫 CUDD。
4. 與兩個指令的所有輸出逐筆比較，並檢查重複 cut。

實際測試包含題目範例、六輸入 AND、常數／直接 PI 輸出、重收斂電路、20 個固定 seed 的隨機電路及原本的 two-bit multiplier。對每個電路跑 k=2..6，**共核對 2,726 筆 truth table 和 2,726 筆 BDD size，全部通過**。另檢查缺少參數、非整數、越界 k、空網路、未 strash，以及同一個 process 連續執行分析。

這些是自行建立的驗證，並不等同助教隱藏測試。測試輸出保存在 Windows 工作區的 `ex4-tests.log`，編譯輸出在 `ex4-build.log`。

## 7. 成本與限制

若節點 v 的兩個 fanin 各有 A、B 個 cut，該節點最多考慮 A*B 個聯集，每個聯集掃描 O(k) 個葉子，另加集合去重成本。全列舉不限制 cut 數量，所以 cut 很多的電路可能花費較多記憶體與時間，不能套用只保留固定數量 cut 的近似方法。

單個 cut 的 truth table 評估成本約是 cone 節點数乘上固定的 64-bit 操作；產生 m 個變數表需要 O(m*2^m)。BDD 建構成本取決於 CUDD 的 AND 運算與中間 BDD 大小。

## 8. 提交來源

實際可執行的 checkout 是 Ubuntu `/home/cwlu/LSV-PA`；Windows `E:\LSV\LSV-PA` 留有相同 ex4 原始碼與說明。後續建議以 Ubuntu checkout 為準，避免兩份程式碼分歧。

交作業需要的實作檔是 `src/ext-lsv/lsvCmd.cpp`、`lsvCut.cpp`、`lsvCut.h`、`module.make`。先在 Ubuntu 檢查 `git diff`，再 commit、push 到自己的 fork，最後開 PR 到課程 repository 中以自己學號命名的分支。這次只完成實作與本機驗證，尚未 push 或提交 PR。

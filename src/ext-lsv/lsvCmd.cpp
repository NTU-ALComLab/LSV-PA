#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <vector>
#include <algorithm>
#include <iostream>
#include <cstdint>
#include "bdd/cudd/cudd.h"
#include "bdd/cudd/cuddInt.h"

// 定義 Cut 與 CutSet 的資料結構
typedef std::vector<int> Lsv_Cut_t;
typedef std::vector<Lsv_Cut_t> Lsv_CutSet_t;

// 提前宣告介面函數，讓 init() 認得它們
static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandCutTt(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandCutBdd(Abc_Frame_t* pAbc, int argc, char** argv);

// ==================== 以下為助教原始架構 (請勿更動) ====================
void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_cut_tt", Lsv_CommandCutTt, 0); 
  Cmd_CommandAdd(pAbc, "LSV", "lsv_cut_bddsize", Lsv_CommandCutBdd, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

void Lsv_NtkPrintNodes(Abc_Ntk_t* pNtk) {
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i) {
    printf("Object Id = %d, name = %s\n", Abc_ObjId(pObj), Abc_ObjName(pObj));
    Abc_Obj_t* pFanin;
    int j;
    Abc_ObjForEachFanin(pObj, pFanin, j) {
      printf("  Fanin-%d: Id = %d, name = %s\n", j, Abc_ObjId(pFanin),
             Abc_ObjName(pFanin));
    }
    if (Abc_NtkHasSop(pNtk)) {
      printf("The SOP of this node:\n%s", (char*)pObj->pData);
    }
  }
}

int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
      case 'h':
        goto usage;
      default:
        goto usage;
    }
  }
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  Lsv_NtkPrintNodes(pNtk);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_print_nodes [-h]\n");
  Abc_Print(-2, "\t        prints the nodes in the network\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}
// ==================== 助教原始架構結束 ====================


// ==================== PA1 Ex4: 自訂函數區 ====================

// 輔助函數：將兩個 Cut 取聯集，如果大小超過 k 就回傳空集合
Lsv_Cut_t MergeCuts(const Lsv_Cut_t& cutA, const Lsv_Cut_t& cutB, int k) {
    Lsv_Cut_t result;
    // 使用 std::set_union 合併兩個有序陣列，並自動剔除重複的 Node ID
    std::set_union(cutA.begin(), cutA.end(),
                   cutB.begin(), cutB.end(),
                   std::back_inserter(result));
    
    // 如果合併後的 Cut 數量大於 k，代表不合法 (Not k-feasible)
    if (result.size() > (size_t)k) {
        result.clear(); 
    }
    return result;
}

// 核心函數：利用位元平行運算計算 Truth Table
uint64_t computeTruthTable_rec(Abc_Obj_t * pObj, const Lsv_Cut_t& cut,
                               std::vector<uint64_t>& memo, std::vector<int>& visited, int global_gen,
                               const std::vector<uint64_t>& masks) {
    // 1. 檢查是否已經抵達 Cut 的邊界 (Cut 內的節點即為輸入變數)
    for (size_t i = 0; i < cut.size(); ++i) {
        if (Abc_ObjId(pObj) == cut[i]) {
            return masks[i]; // 回傳對應的魔法遮罩
        }
    }
    
    // 2. 特殊情況：如果走到常數 1 節點
    if (Abc_ObjFaninNum(pObj) == 0) {
        return ~(uint64_t)0; // 回傳全為 1 的 64-bit 整數
    }
    
    // 3. Memorization (記憶化)：如果這回合已經算過這個節點，直接拿答案，避免重複計算
    if (visited[Abc_ObjId(pObj)] == global_gen) {
        return memo[Abc_ObjId(pObj)];
    }
    
    // 4. 遞迴往下尋找子節點
    Abc_Obj_t * pFanin0 = Abc_ObjFanin0(pObj);
    Abc_Obj_t * pFanin1 = Abc_ObjFanin1(pObj);
    
    uint64_t val0 = computeTruthTable_rec(pFanin0, cut, memo, visited, global_gen, masks);
    if (Abc_ObjFaninC0(pObj)) val0 = ~val0; // 如果是虛線 (NOT edge)，就把 0/1 反轉
    
    uint64_t val1 = computeTruthTable_rec(pFanin1, cut, memo, visited, global_gen, masks);
    if (Abc_ObjFaninC1(pObj)) val1 = ~val1;
    
    // 5. AIG 節點本身一定是 AND gate
    uint64_t result = val0 & val1;
    
    // 6. 紀錄運算結果
    memo[Abc_ObjId(pObj)] = result;
    visited[Abc_ObjId(pObj)] = global_gen;
    
    return result;
}

// 核心演算法：找出所有的 k-feasible cuts
void Lsv_NtkFindCuts(Abc_Ntk_t * pNtk, int k) {
    // 開啟一個足夠大的陣列，讓每個節點 ID 都能有自己的 Cut 集合
    std::vector<Lsv_CutSet_t> allCuts(Abc_NtkObjNumMax(pNtk));
    Abc_Obj_t * pObj;
    int i;

    // 1. 處理邊界條件：Primary Inputs (PI) 的 Cut 只有自己
    Abc_NtkForEachPi(pNtk, pObj, i) {
        Lsv_Cut_t trivialCut;
        trivialCut.push_back(Abc_ObjId(pObj));
        allCuts[Abc_ObjId(pObj)].push_back(trivialCut);
    }

    // 2. 依照拓撲順序走訪 AIG 的內部節點 (Internal Nodes)
    Abc_NtkForEachNode(pNtk, pObj, i) {
        // 每一個節點的第一個 Cut，永遠是「它自己」(Trivial Cut)
        Lsv_Cut_t trivialCut;
        trivialCut.push_back(Abc_ObjId(pObj));
        allCuts[Abc_ObjId(pObj)].push_back(trivialCut);

        // 取得左子節點 (Fanin0) 與右子節點 (Fanin1)
        Abc_Obj_t * pFanin0 = Abc_ObjFanin0(pObj);
        Abc_Obj_t * pFanin1 = Abc_ObjFanin1(pObj);

        // 如果兩個來源都存在，將兩邊的 Cuts 進行兩兩交配 (Cartesian Product)
        if (pFanin0 != NULL && pFanin1 != NULL) {
            Lsv_CutSet_t & cuts0 = allCuts[Abc_ObjId(pFanin0)];
            Lsv_CutSet_t & cuts1 = allCuts[Abc_ObjId(pFanin1)];

            for (size_t c0 = 0; c0 < cuts0.size(); ++c0) {
                for (size_t c1 = 0; c1 < cuts1.size(); ++c1) {
                    Lsv_Cut_t merged = MergeCuts(cuts0[c0], cuts1[c1], k);
                    
                    if (!merged.empty()) {
                        // 檢查是否已經存在相同的 Cut，避免重複收集
                        if (std::find(allCuts[Abc_ObjId(pObj)].begin(), allCuts[Abc_ObjId(pObj)].end(), merged) == allCuts[Abc_ObjId(pObj)].end()) {
                            allCuts[Abc_ObjId(pObj)].push_back(merged);
                        }
                    }
                }
            }
        }
    }
    
    // 這裡我們成功收集完所有 Cuts 了！
    // 準備 Memorization 需要的陣列
    std::vector<uint64_t> memo(Abc_NtkObjNumMax(pNtk), 0);
    std::vector<int> visited(Abc_NtkObjNumMax(pNtk), 0);
    int global_gen = 0; // 用來標記每一次的計算回合，這招可以省去清空陣列的 O(N) 時間
    
    // 定義 Truth Table 的魔法遮罩
    std::vector<uint64_t> masks = {
        0xAAAAAAAAAAAAAAAA, // var 0
        0xCCCCCCCCCCCCCCCC, // var 1
        0xF0F0F0F0F0F0F0F0, // var 2
        0xFF00FF00FF00FF00, // var 3
        0xFFFF0000FFFF0000, // var 4
        0xFFFFFFFF00000000  // var 5
    };

    // 走訪並列印 (排除 PI 與 PO，作業要求只印 Internal Node)
    Abc_NtkForEachNode(pNtk, pObj, i) {
        if (!Abc_ObjIsNode(pObj)) continue;
        
        for (const auto& cut : allCuts[Abc_ObjId(pObj)]) {
            // 列印節點 ID 與 Cut 內容 (完全對齊助教要求的空格格式)
            printf("%d:", Abc_ObjId(pObj));
            for (int n : cut) {
                printf(" %d", n);
            }
            
            // 計算 Truth Table
            global_gen++;
            uint64_t tt = computeTruthTable_rec(pObj, cut, memo, visited, global_gen, masks);
            
            // 裁切遮罩：我們只需要用到 2^c 個 bit，把多餘的高位元歸零
            int c_size = cut.size();
            uint64_t final_mask = (c_size == 6) ? ~(uint64_t)0 : ((1ULL << (1 << c_size)) - 1);
            tt &= final_mask;
            
            // 印出大寫 16 進位 (%lX 代表 64-bit unsigned hex)
            printf(": %lX\n", tt);
        }
    }
}
//=====================================================================================//
// 接收終端機指令的介面
static int Lsv_CommandCutTt(Abc_Frame_t * pAbc, int argc, char ** argv) {
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int k = 0;

    Extra_UtilGetoptReset();
    while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
        switch (c) {
            case 'h':
                goto usage;
            default:
                goto usage;
        }
    }

    if (pNtk == NULL) {
        Abc_Print(-1, "Empty network.\n");
        return 1;
    }

    if (argc != 2) {
        Abc_Print(-1, "Expected exactly 1 argument for k.\n");
        goto usage;
    }
    k = atoi(argv[1]);

    if (k < 2 || k > 6) {
        Abc_Print(-1, "k must be between 2 and 6.\n");
        return 1;
    }

    // 呼叫你的核心演算法
    Lsv_NtkFindCuts(pNtk, k);
    return 0;

usage:
    Abc_Print(-2, "usage: lsv_cut_tt [-h] <k>\n");
    Abc_Print(-2, "\t        enumerates k-feasible cuts and truth tables\n");
    Abc_Print(-2, "\t-h    : print the command usage\n");
    return 1;
}

// ==================== PA1 Ex4.2: k-feasible Cut BDD Generation ====================

// 輔助遞迴函式：透過走訪 AIG 來建立 BDD
DdNode* computeBdd_rec(DdManager* dd, Abc_Obj_t* pObj, const Lsv_Cut_t& cut,
                       std::vector<DdNode*>& memo, std::vector<int>& visited, int global_gen) {
    // 1. 檢查是否抵達 Cut 的邊界 (Cut 內的輸入變數)
    for (size_t i = 0; i < cut.size(); ++i) {
        if (Abc_ObjId(pObj) == cut[i]) {
            // 向 CUDD 要求第 i 個變數的 BDD，並增加參考計數
            DdNode* varBdd = Cudd_bddIthVar(dd, i);
            Cudd_Ref(varBdd); 
            return varBdd;
        }
    }
    
    // 2. 特殊情況：如果走到沒有子節點的節點 (常數 1)
    if (Abc_ObjFaninNum(pObj) == 0) {
        DdNode* const1 = Cudd_ReadOne(dd);
        Cudd_Ref(const1);
        return const1;
    }
    
    // 3. Memoization (記憶化)：避免重複走訪相同的節點
    if (visited[Abc_ObjId(pObj)] == global_gen) {
        DdNode* cachedBdd = memo[Abc_ObjId(pObj)];
        // 從備忘錄拿出來用，也要增加一次參考計數！
        Cudd_Ref(cachedBdd); 
        return cachedBdd;
    }
    
    // 4. 遞迴往下尋找子節點的 BDD
    Abc_Obj_t * pFanin0 = Abc_ObjFanin0(pObj);
    Abc_Obj_t * pFanin1 = Abc_ObjFanin1(pObj);
    
    DdNode* val0 = computeBdd_rec(dd, pFanin0, cut, memo, visited, global_gen);
    if (Abc_ObjFaninC0(pObj)) {
        // 如果是虛線 (NOT edge)，對 BDD 進行反轉，並替換原本的指標
        DdNode* notVal0 = Cudd_Not(val0);
        // Cudd_Not 只是對指標做 bit-flip，不需要額外 Ref/Deref
        val0 = notVal0; 
    }
    
    DdNode* val1 = computeBdd_rec(dd, pFanin1, cut, memo, visited, global_gen);
    if (Abc_ObjFaninC1(pObj)) {
        DdNode* notVal1 = Cudd_Not(val1);
        val1 = notVal1;
    }
    
    // 5. 將左右子迷宮進行 AND 運算，合併成大迷宮
    DdNode* resultBdd = Cudd_bddAnd(dd, val0, val1);
    Cudd_Ref(resultBdd); // resultBdd 是新建立的，必須增加參考計數
    
    // 6. 歸還子迷宮的參考計數 (非常重要，不然會 Memory Leak)
    Cudd_RecursiveDeref(dd, val0);
    Cudd_RecursiveDeref(dd, val1);
    
    // 7. 紀錄運算結果到備忘錄
    memo[Abc_ObjId(pObj)] = resultBdd;
    visited[Abc_ObjId(pObj)] = global_gen;
    // 存進備忘錄代表這個 BDD 被 memo 擁有，再加一次參考計數
    Cudd_Ref(resultBdd); 
    
    return resultBdd;
}

// 接收終端機指令的介面函式
static int Lsv_CommandCutBdd(Abc_Frame_t * pAbc, int argc, char ** argv) {
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int k = 0;

    Extra_UtilGetoptReset();
    while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
        switch (c) {
            case 'h':
                goto usage;
            default:
                goto usage;
        }
    }

    if (pNtk == NULL) {
        Abc_Print(-1, "Empty network.\n");
        return 1;
    }

    if (argc != 2) {
        Abc_Print(-1, "Expected exactly 1 argument for k.\n");
        goto usage;
    }
    k = atoi(argv[1]);

    if (k < 2 || k > 6) {
        Abc_Print(-1, "k must be between 2 and 6.\n");
        return 1;
    }

    {

    // 這裡我們借用 4.1 寫好的 Lsv_NtkFindCuts 來幫我們找好所有的 Cut
    // 但因為原本的 Lsv_NtkFindCuts 裡面已經包含了列印 Truth Table 的邏輯，
    // 為了避免同時印出兩種格式，我們需要稍微調整一下架構。
    
    // 策略：我們可以把尋找 Cut 的邏輯（迴圈與 MergeCuts）打包起來，
    // 或是為了這題，我們在這邊重寫一次精簡版的收集迴圈。
    // 為了清晰起見，這裡我們再跑一次找 Cut 的迴圈，然後直接算 BDD Size！

    std::vector<Lsv_CutSet_t> allCuts(Abc_NtkObjNumMax(pNtk));
    Abc_Obj_t * pObj;
    int i;

    // 收集 PI 的 Cut
    Abc_NtkForEachPi(pNtk, pObj, i) {
        Lsv_Cut_t trivialCut;
        trivialCut.push_back(Abc_ObjId(pObj));
        allCuts[Abc_ObjId(pObj)].push_back(trivialCut);
    }

    // 收集 Internal Nodes 的 Cuts
    Abc_NtkForEachNode(pNtk, pObj, i) {
        if (!Abc_ObjIsNode(pObj)) continue;
        
        Lsv_Cut_t trivialCut;
        trivialCut.push_back(Abc_ObjId(pObj));
        allCuts[Abc_ObjId(pObj)].push_back(trivialCut);

        Abc_Obj_t * pFanin0 = Abc_ObjFanin0(pObj);
        Abc_Obj_t * pFanin1 = Abc_ObjFanin1(pObj);

        if (pFanin0 != NULL && pFanin1 != NULL) {
            Lsv_CutSet_t & cuts0 = allCuts[Abc_ObjId(pFanin0)];
            Lsv_CutSet_t & cuts1 = allCuts[Abc_ObjId(pFanin1)];

            for (size_t c0 = 0; c0 < cuts0.size(); ++c0) {
                for (size_t c1 = 0; c1 < cuts1.size(); ++c1) {
                    Lsv_Cut_t merged = MergeCuts(cuts0[c0], cuts1[c1], k);
                    if (!merged.empty()) {
                        if (std::find(allCuts[Abc_ObjId(pObj)].begin(), allCuts[Abc_ObjId(pObj)].end(), merged) == allCuts[Abc_ObjId(pObj)].end()) {
                            allCuts[Abc_ObjId(pObj)].push_back(merged);
                        }
                    }
                }
            }
        }
    }

    // 開始建構 BDD 並計算 Size
    std::vector<DdNode*> memo(Abc_NtkObjNumMax(pNtk), NULL);
    std::vector<int> visited(Abc_NtkObjNumMax(pNtk), 0);
    int global_gen = 0;

    Abc_NtkForEachNode(pNtk, pObj, i) {
        if (Abc_ObjIsPi(pObj) || Abc_ObjIsPo(pObj) || Abc_ObjFaninNum(pObj) == 0) continue;
        if (!Abc_ObjIsNode(pObj)) continue;
        
        for (const auto& cut : allCuts[Abc_ObjId(pObj)]) {
            // 列印前半部：節點 ID 與 Cut 內容
            printf("%d:", Abc_ObjId(pObj));
            for (int n : cut) {
                printf(" %d", n);
            }
            
            // 針對每一個 Cut，初始化一個全新的 CUDD 經理人
            // 變數數量剛好就是這個 Cut 的大小
            DdManager * dd = Cudd_Init(cut.size(), 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);
            
            global_gen++;
            DdNode* bdd = computeBdd_rec(dd, pObj, cut, memo, visited, global_gen);
            
            // 呼叫 CUDD 內建函式取得 BDD 的總節點數 (DAG Size)
            int bdd_size = Cudd_DagSize(bdd);
            printf(": %d\n", bdd_size); // 印出 BDD Size
            
            // 清理這回合的 Reference Count (包含回傳的 bdd 以及備忘錄裡面的)
            Cudd_RecursiveDeref(dd, bdd);
            for (size_t m = 0; m < memo.size(); ++m) {
                if (visited[m] == global_gen && memo[m] != NULL) {
                    Cudd_RecursiveDeref(dd, memo[m]);
                }
            }
            
            // 開除這個經理人，徹底釋放這個 Cut 的 BDD 記憶體
            Cudd_Quit(dd); 
        }
    }

    }
    return 0;

usage:
    Abc_Print(-2, "usage: lsv_cut_bddsize [-h] <k>\n");
    Abc_Print(-2, "\t        enumerates k-feasible cuts and builds BDDs\n");
    Abc_Print(-2, "\t-h    : print the command usage\n");
    return 1;
}
#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "bdd/cudd/cudd.h"
#include "bdd/cudd/cuddInt.h"
#include <vector>
#include <set>
#include <algorithm>
#include <iostream>
#include <iomanip>
#include <cstdint>

using namespace std;

#define My_ObjIsConstant(pObj) ((pObj)->Type == ABC_OBJ_CONST1)

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandCutTt(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandCutBdd(Abc_Frame_t* pAbc, int argc, char** argv);

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

struct Cut {
    vector<int> nodes;
    bool operator<(const Cut& other) const {
        if (nodes.size() != other.nodes.size()) return nodes.size() < other.nodes.size();
        return nodes < other.nodes;
    }
    bool operator==(const Cut& other) const {
        return nodes == other.nodes;
    }
};

vector<Cut> MergeCuts(const vector<Cut>& c0, const vector<Cut>& c1, int k) {
    vector<Cut> res;
    for (const auto& cut0 : c0) {
        for (const auto& cut1 : c1) {
            Cut c_new;
            set_union(cut0.nodes.begin(), cut0.nodes.end(), 
                      cut1.nodes.begin(), cut1.nodes.end(), 
                      back_inserter(c_new.nodes));
            if (c_new.nodes.size() <= k) {
                res.push_back(c_new);
            }
        }
    }
    sort(res.begin(), res.end());
    res.erase(unique(res.begin(), res.end()), res.end());
    
    vector<Cut> final_cuts;
    for (const auto& c : res) {
        bool dominated = false;
        for (const auto& other : res) {
            if (other.nodes.size() < c.nodes.size() && includes(c.nodes.begin(), c.nodes.end(), other.nodes.begin(), other.nodes.end())) {
                dominated = true;
                break;
            }
        }
        if (!dominated) {
            final_cuts.push_back(c);
        }
    }
    return final_cuts;
}

vector<Cut> ComputeCutsRec(Abc_Obj_t* pObj, int k, vector<vector<Cut>>& all_cuts) {
    int id = Abc_ObjId(pObj);
    if (!all_cuts[id].empty()) return all_cuts[id]; 
    
    if (Abc_ObjIsCi(pObj) || My_ObjIsConstant(pObj)) {
        all_cuts[id].push_back({{id}});
        return all_cuts[id];
    }
    
    vector<Cut> c0 = ComputeCutsRec(Abc_ObjFanin0(pObj), k, all_cuts);
    vector<Cut> c1 = ComputeCutsRec(Abc_ObjFanin1(pObj), k, all_cuts);
    
    vector<Cut> res = MergeCuts(c0, c1, k);
    res.push_back({{id}}); 
    
    sort(res.begin(), res.end());
    res.erase(unique(res.begin(), res.end()), res.end());
    
    vector<Cut> final_cuts;
    for (const auto& c : res) {
        bool dominated = false;
        for (const auto& other : res) {
            if (other.nodes.size() < c.nodes.size() && includes(c.nodes.begin(), c.nodes.end(), other.nodes.begin(), other.nodes.end())) {
                dominated = true;
                break;
            }
        }
        if (!dominated) {
            final_cuts.push_back(c);
        }
    }
    all_cuts[id] = final_cuts;
    return final_cuts;
}

uint64_t ComputeTtRec(Abc_Obj_t* pObj, const Cut& cut, vector<uint64_t>& tt_map, vector<bool>& visited, vector<int>& visited_nodes) {
    int id = Abc_ObjId(pObj);
    if (visited[id]) return tt_map[id];
    
    auto it = find(cut.nodes.begin(), cut.nodes.end(), id);
    if (it != cut.nodes.end()) {
        visited[id] = true;
        visited_nodes.push_back(id);
        int j = distance(cut.nodes.begin(), it); 
        int m = cut.nodes.size();
        uint64_t mask = 0;
        for (int idx = 0; idx < (1 << m); ++idx) {
            int bit_pos = m - 1 - j;
            if (idx & (1 << bit_pos)) {
                mask |= (1ULL << idx);
            }
        }
        return tt_map[id] = mask;
    }
    
    if (Abc_ObjIsCi(pObj) || My_ObjIsConstant(pObj)) {
        visited[id] = true;
        visited_nodes.push_back(id);
        return tt_map[id] = 0; 
    }
    
    Abc_Obj_t* pFanin0 = Abc_ObjFanin0(pObj);
    Abc_Obj_t* pFanin1 = Abc_ObjFanin1(pObj);
    
    uint64_t tt0 = ComputeTtRec(pFanin0, cut, tt_map, visited, visited_nodes);
    uint64_t tt1 = ComputeTtRec(pFanin1, cut, tt_map, visited, visited_nodes);
    
    if (Abc_ObjFaninC0(pObj)) tt0 = ~tt0;
    if (Abc_ObjFaninC1(pObj)) tt1 = ~tt1;
    
    uint64_t tt = tt0 & tt1;
    
    visited[id] = true;
    visited_nodes.push_back(id);
    return tt_map[id] = tt;
}

uint64_t ComputeTruthTable(Abc_Obj_t* pRoot, const Cut& cut, vector<uint64_t>& tt_map, vector<bool>& visited, vector<int>& visited_nodes) {
    visited_nodes.clear();
    uint64_t tt = ComputeTtRec(pRoot, cut, tt_map, visited, visited_nodes);
    
    int m = cut.nodes.size();
    uint64_t final_mask;
    if (m == 6) {
        final_mask = ~0ULL;
    } else {
        final_mask = (1ULL << (1 << m)) - 1;
    }
    tt &= final_mask;
    
    for (int id : visited_nodes) {
        visited[id] = false;
    }
    return tt;
}

DdNode* ComputeBddRec(DdManager* dd, Abc_Obj_t* pObj, const Cut& cut, vector<DdNode*>& bdd_map, vector<bool>& visited, vector<int>& visited_nodes) {
    int id = Abc_ObjId(pObj);
    if (visited[id]) return bdd_map[id];
    
    auto it = find(cut.nodes.begin(), cut.nodes.end(), id);
    if (it != cut.nodes.end()) {
        visited[id] = true;
        visited_nodes.push_back(id);
        int j = distance(cut.nodes.begin(), it); 
        DdNode* var = Cudd_bddIthVar(dd, j);
        Cudd_Ref(var);
        return bdd_map[id] = var;
    }
    
    if (Abc_ObjIsCi(pObj) || My_ObjIsConstant(pObj)) {
        visited[id] = true;
        visited_nodes.push_back(id);
        DdNode* zero = (DdNode*)((uintptr_t)(Cudd_ReadOne(dd)) ^ 1);
        Cudd_Ref(zero);
        return bdd_map[id] = zero;
    }
    
    Abc_Obj_t* pFanin0 = Abc_ObjFanin0(pObj);
    Abc_Obj_t* pFanin1 = Abc_ObjFanin1(pObj);
    
    DdNode* bdd0 = ComputeBddRec(dd, pFanin0, cut, bdd_map, visited, visited_nodes);
    DdNode* bdd1 = ComputeBddRec(dd, pFanin1, cut, bdd_map, visited, visited_nodes);
    
    if (Abc_ObjFaninC0(pObj)) bdd0 = (DdNode*)((uintptr_t)(bdd0) ^ 1);
    if (Abc_ObjFaninC1(pObj)) bdd1 = (DdNode*)((uintptr_t)(bdd1) ^ 1);
    
    DdNode* bdd = Cudd_bddAnd(dd, bdd0, bdd1);
    Cudd_Ref(bdd);
    
    visited[id] = true;
    visited_nodes.push_back(id);
    return bdd_map[id] = bdd;
}

int ComputeBddSize(DdManager* dd, Abc_Obj_t* pRoot, const Cut& cut, vector<DdNode*>& bdd_map, vector<bool>& visited, vector<int>& visited_nodes) {
    visited_nodes.clear();
    
    DdNode* bdd = ComputeBddRec(dd, pRoot, cut, bdd_map, visited, visited_nodes);
    Cudd_Ref(bdd);
    
    int size = Cudd_DagSize(bdd);
    
    Cudd_RecursiveDeref(dd, bdd);
    for (int id : visited_nodes) {
        if (bdd_map[id]) {
            Cudd_RecursiveDeref(dd, bdd_map[id]);
            bdd_map[id] = nullptr;
        }
        visited[id] = false;
    }
    return size;
}

int Lsv_CommandCutTt(Abc_Frame_t* pAbc, int argc, char** argv) {
    Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
    if (!pNtk) {
        Abc_Print(-1, "Empty network.\n");
        return 1;
    }
    if (!Abc_NtkIsStrash(pNtk)) {
        Abc_Print(-1, "Only works for AIG.\n");
        return 1;
    }
    if (argc != 2) {
        Abc_Print(-1, "usage: lsv_cut_tt <k>\n");
        return 1;
    }
    int k = atoi(argv[1]);
    if (k < 1 || k > 6) {
        Abc_Print(-1, "Cut size must be between 1 and 6.\n");
        return 1;
    }
    
    vector<vector<Cut>> all_cuts(Abc_NtkObjNumMax(pNtk));
    Abc_Obj_t* pObj;
    int i;
    Abc_NtkForEachCi(pNtk, pObj, i) {
        all_cuts[(int)Abc_ObjId(pObj)].push_back({{(int)Abc_ObjId(pObj)}});
    }
    Abc_NtkForEachNode(pNtk, pObj, i) {
        ComputeCutsRec(pObj, k, all_cuts);
    }
    
    Abc_NtkForEachNode(pNtk, pObj, i) {
        if (Abc_ObjIsCi(pObj) || Abc_ObjIsCo(pObj) || My_ObjIsConstant(pObj)) continue;
        
        int node_id = Abc_ObjId(pObj);
        for (const auto& cut : all_cuts[node_id]) {
            if (cut.nodes.size() == 0) continue;
            uint64_t tt = ComputeTruthTable(pObj, cut, tt_map, visited, visited_nodes);
            
            cout << node_id << ":";
            for (int var : cut.nodes) cout << " " << var;
            
            if (tt == 0) {
                cout << ": 0\n";
            } else {
                cout << ": " << hex << uppercase << tt << dec << "\n";
            }
        }
    }
    return 0;
}

int Lsv_CommandCutBdd(Abc_Frame_t* pAbc, int argc, char** argv) {
    Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
    if (!pNtk) {
        Abc_Print(-1, "Empty network.\n");
        return 1;
    }
    if (!Abc_NtkIsStrash(pNtk)) {
        Abc_Print(-1, "Only works for AIG.\n");
        return 1;
    }
    if (argc != 2) {
        Abc_Print(-1, "usage: lsv_cut_bddsize <k>\n");
        return 1;
    }
    int k = atoi(argv[1]);
    if (k < 1) {
        Abc_Print(-1, "Cut size must be at least 1.\n");
        return 1;
    }
    
    vector<vector<Cut>> all_cuts(Abc_NtkObjNumMax(pNtk));
    Abc_Obj_t* pObj;
    int i;
    Abc_NtkForEachCi(pNtk, pObj, i) {
        all_cuts[(int)Abc_ObjId(pObj)].push_back({{(int)Abc_ObjId(pObj)}});
    }
    Abc_NtkForEachNode(pNtk, pObj, i) {
        ComputeCutsRec(pObj, k, all_cuts);
    }
    
    DdManager* dd = Cudd_Init(0, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);
    vector<DdNode*> bdd_map(Abc_NtkObjNumMax(pNtk), nullptr);
    vector<bool> visited(Abc_NtkObjNumMax(pNtk), false);
    vector<int> visited_nodes;
    
    Abc_NtkForEachNode(pNtk, pObj, i) {
        if (Abc_ObjIsCi(pObj) || Abc_ObjIsCo(pObj) || My_ObjIsConstant(pObj)) continue;
        
        int node_id = Abc_ObjId(pObj);
        for (const auto& cut : all_cuts[node_id]) {
            if (cut.nodes.size() == 0) continue;
            int size = ComputeBddSize(dd, pObj, cut, bdd_map, visited, visited_nodes);
            
            cout << node_id << ":";
            for (int var : cut.nodes) cout << " " << var;
            cout << ": " << size << "\n";
        }
    }
    Cudd_Quit(dd);
    return 0;
}
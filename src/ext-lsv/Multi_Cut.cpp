#include "Multi_Cut.h"
#include <iostream>
#include <vector>
#include <set>
#include <unordered_set>
#include <algorithm>
using namespace std;
extern "C" {
    #include "base/abc/abc.h"
    #include "aig/aig/aig.h"
}

using Cut    = vector<unsigned>;               
using CutSet = vector<Cut>;                    
struct CutGroup{
    Cut cut;
    set<unsigned> nodes;
};
static inline bool IsConst1(Abc_Obj_t* x) {
    return x == Abc_AigConst1(Abc_ObjNtk(x));
}
static int FindCutIndex(const vector<CutGroup>& result, const Cut& c) {
    for (size_t i = 0; i < result.size(); i++){
        if(result[i].cut == c){
            return i; 
        }
    }
    return -1;
}

static bool CanGoToPI(Abc_Obj_t* node , const Cut& cut, const Abc_Ntk_t* pNtk) {
    unordered_set<unsigned> S;
    for(int i = 0; i < cut.size(); i++){
        S.insert(cut[i]);
    }

    vector<Abc_Obj_t*> nodes;
    nodes.push_back(node);
    unordered_set<unsigned> visited;

    while (!nodes.empty()) {
        Abc_Obj_t* temp = nodes.back(); 
        nodes.pop_back();

        unsigned temp_id = Abc_ObjId(temp);
        if (visited.find(temp_id) != visited.end()){
            continue;
        }
        visited.insert(temp_id);

        if (S.find(temp_id) != S.end()){
            continue;
        }
        if (Abc_ObjIsCi(temp)) { //Is PI -> Can go to PI
            return false;
        }
        if(Abc_ObjIsPo(temp)){
            nodes.push_back(Abc_ObjFanin0(temp)); // only one fanin
        }
        else if(IsConst1(temp)){
            continue;
        }
        else if (Abc_ObjIsNode(temp)) {
            nodes.push_back(Abc_ObjFanin0(temp));
            nodes.push_back(Abc_ObjFanin1(temp));
            continue;
        }
        return false;
    }
    return true;
}

// check irredundancy: removing any leaf should fail to block output
static bool IsIrredundant(Abc_Obj_t* node, const Cut& cut, const Abc_Ntk_t* pNtk) {
    if (!CanGoToPI(node, cut, pNtk)){
        return false;
    }
    if (cut.size() <= 1) {
        return true;
    }
    for (int i = 0; i < cut.size(); i++) {
        Cut temp;
        for (int j = 0; j < cut.size(); j++){
            if (j != i) temp.push_back(cut[j]);
        }
        // ex: {3,5,7} -> {3,5}
        if (CanGoToPI(node, temp, pNtk)) return false;
    }
    return true;
}


static bool ComCuts(const Cut& a, const Cut& b, int K, Cut& out) {
    // back_inserter can use push_back
    set_union(a.begin(), a.end(), b.begin(), b.end(), back_inserter(out));
    if(out.size() <= K){
        return true;
    }
    else{
        return false;
    }
}

static void EnumerateCuts(Abc_Obj_t* node, int K,const vector<CutSet>& Cuts, CutSet & node_Cuts,
    const Abc_Ntk_t* pNtk)
{
    node_Cuts.clear();
    if (Abc_ObjIsCi(node)) {
        // PI -> only itself
        Cut temp = {Abc_ObjId(node)};
        node_Cuts.push_back(temp);
        return;
    }
    //And node
    Abc_Obj_t* a = Abc_ObjFanin0(node);
    Abc_Obj_t* b = Abc_ObjFanin1(node);
    const CutSet a_Cuts = Cuts[Abc_ObjId(a)];
    const CutSet b_Cuts = Cuts[Abc_ObjId(b)];

    set<vector<unsigned>> unique_map;

    for (const auto & s1 : a_Cuts) {
        for (const auto & s2 : b_Cuts) {
            Cut combine;
            if (!ComCuts(s1, s2, K, combine)){
                continue;
            }
            if (!IsIrredundant(node, combine, pNtk)){
                continue;
            }
            if(unique_map.count(combine) == 0){
                unique_map.insert(combine);
                node_Cuts.push_back(combine);
            }
        }
    }
}
static vector<CutGroup> MultiCuts(Abc_Ntk_t* pNtk, int K, int L) {
    int num_Objs = Abc_NtkObjNumMax(pNtk) + 1;
    vector<CutSet> Cuts(num_Objs);

    Abc_Obj_t* temp_Obj;
    int i;
    // Find All Node's Cut
    Abc_NtkForEachObj(pNtk, temp_Obj, i) {
        if (!(Abc_ObjIsCi(temp_Obj) || Abc_ObjIsNode(temp_Obj))) {
            continue;
        }
        EnumerateCuts(temp_Obj, K, Cuts, Cuts[i], pNtk);
    }

    vector<CutGroup> result;
    // Record cut for what node
    Abc_NtkForEachObj(pNtk, temp_Obj, i) {
        if (!Abc_ObjIsNode(temp_Obj)){
            continue;
        }
        const CutSet& temp_cutset = Cuts[i];
        for (const Cut& c : temp_cutset) {
            int idx = FindCutIndex(result, c);
            if (idx == -1) {
                CutGroup cg;
                cg.cut = c;
                cg.nodes.insert((unsigned)(i));
                result.push_back(cg);
            } else {
                result[idx].nodes.insert((unsigned)(i));
            }
        }
    }
    return result;
}

static void print_result(const vector<CutGroup>& result, int L){
    for (const auto& cg : result) {
        if ((int)cg.nodes.size() < L) continue;

        // print cut
        for (size_t t = 0; t < cg.cut.size(); ++t) {
            if (t) Abc_Print(1, " ");
            Abc_Print(1, "%u", cg.cut[t]);
        }
        Abc_Print(1, " : ");

        // print node IDs
        bool first = true;
        for (unsigned id : cg.nodes) {
            if (!first) Abc_Print(1, " ");
            Abc_Print(1, "%u", id);
            first = false;
        }
        Abc_Print(1, "\n");
    }
}
static void Readme() {
    Abc_Print(-2, "lsv_printmocut <K> <L>\n");
    Abc_Print(-2, "K: 3 ~ 6   L: 1 ~ 4\n");
}
int Abc_CommandLsvPrintMoCut(Abc_Frame_t* pAbc, int argc, char** argv) {
    if (argc != 3) { 
        Readme(); 
        return 1; 
    }
    int K = atoi(argv[1]);
    int L = atoi(argv[2]);
    if (K < 3 || K > 6 || L < 1 || L > 4) { 
        Readme(); 
        return 1; 
    }

    Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
    if (!pNtk) { // NO read
        Abc_Print(-1,"Empty Network\n");
        return 1; 
    }
    if (!Abc_NtkIsStrash(pNtk)){ // NO strash
        Abc_Print(-1,"Pleast starsh First.\n");
        return 1;
    }

    auto result = MultiCuts(pNtk, K, L);
    print_result(result,L);
    return 0;
}

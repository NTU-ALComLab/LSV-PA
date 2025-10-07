// 檔案: src/ext-lsv/lsvMocut.cpp

#include <vector>
#include <map>
#include <set>
#include <algorithm>
#include <iostream>

#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

using namespace std;

extern "C" int Lsv_CommandMocut(Abc_Frame_t *pAbc, int argc, char **argv);

bool Lsv_ConeHitsCut_Recursive(Abc_Obj_t *pNode, map<int, bool> &memo, const set<int> &cutIds)
{
    int nodeId = Abc_ObjId(pNode);
    if (cutIds.count(nodeId))
        return true;
    if (Abc_ObjIsPi(pNode))
        return false;
    if (memo.count(nodeId))
        return memo[nodeId];

    if (!Lsv_ConeHitsCut_Recursive(Abc_ObjFanin0(pNode), memo, cutIds))
        return memo[nodeId] = false;
    if (!Lsv_ConeHitsCut_Recursive(Abc_ObjFanin1(pNode), memo, cutIds))
        return memo[nodeId] = false;

    return memo[nodeId] = true;
}
bool Lsv_IsCutOfNode(Abc_Obj_t *pNode, const vector<int> &vCut)
{
    map<int, bool> memo;
    set<int> cutIds(vCut.begin(), vCut.end());
    return Lsv_ConeHitsCut_Recursive(pNode, memo, cutIds);
}
bool Lsv_IsIrredKFeasibleCut(Abc_Obj_t *pNode, const vector<int> &vCut, int k)
{
    if (vCut.empty() || vCut.size() > (size_t)k)
        return false;
    if (!Lsv_IsCutOfNode(pNode, vCut))
        return false;

    for (size_t i = 0; i < vCut.size(); ++i)
    {
        vector<int> tempCut = vCut;
        tempCut.erase(tempCut.begin() + i);
        if (Lsv_IsCutOfNode(pNode, tempCut))
        {
            return false;
        }
    }
    return true;
}

extern "C" int Lsv_CommandMocut(Abc_Frame_t *pAbc, int argc, char **argv)
{

    if (argc != 3)
    {
        Abc_Print(1, "Usage: lsv_printmocut <k> <l>\n");
        return 1;
    }
    int k = atoi(argv[1]);
    int l = atoi(argv[2]);
    if (k < 3 || k > 6 || l < 1 || l > 4)
    {
        Abc_Print(1, "Usage: lsv_printmocut <k:3..6> <l:1..4>\n");
        return 1;
    }
    Abc_Ntk_t *pNtk = Abc_FrameReadNtk(pAbc);
    if (!pNtk || !Abc_NtkIsStrash(pNtk))
    {
        Abc_Print(1, "Please read a network and run \"strash\" first.\n");
        return 1;
    }

    vector<vector<vector<int>>> nodeCuts(Abc_NtkObjNumMax(pNtk) + 1);
    map<vector<int>, vector<int>> multiOutputCuts;
    Abc_Obj_t *pObj;
    int i;

    Abc_NtkForEachPi(pNtk, pObj, i) { nodeCuts[Abc_ObjId(pObj)].push_back({(int)Abc_ObjId(pObj)}); }
    Abc_NtkForEachNode(pNtk, pObj, i)
    {
        set<vector<int>> candidates;
        Abc_Obj_t *pFanin0 = Abc_ObjFanin0(pObj);
        Abc_Obj_t *pFanin1 = Abc_ObjFanin1(pObj);
        for (const auto &c0 : nodeCuts[Abc_ObjId(pFanin0)])
        {
            for (const auto &c1 : nodeCuts[Abc_ObjId(pFanin1)])
            {
                vector<int> merged;
                merge(c0.begin(), c0.end(), c1.begin(), c1.end(), back_inserter(merged));
                merged.erase(unique(merged.begin(), merged.end()), merged.end());
                if (merged.size() <= (size_t)k)
                    candidates.insert(merged);
            }
        }
        candidates.insert({(int)Abc_ObjId(pObj)});
        auto &finalCuts = nodeCuts[Abc_ObjId(pObj)];
        for (const auto &cut : candidates)
        {
            if (Lsv_IsIrredKFeasibleCut(pObj, cut, k))
            {
                finalCuts.push_back(cut);
            }
        }
        for (const auto &cut : finalCuts)
        {
            multiOutputCuts[cut].push_back((int)Abc_ObjId(pObj));
        }
    }

    for (auto const &[cut, outputs] : multiOutputCuts)
    {
        if (outputs.size() >= (size_t)l)
        {
            vector<int> finalOutputs = outputs;
            sort(finalOutputs.begin(), finalOutputs.end());
            finalOutputs.erase(unique(finalOutputs.begin(), finalOutputs.end()), finalOutputs.end());
            for (size_t i = 0; i < cut.size(); ++i)
                Abc_Print(1, "%d%s", cut[i], (i + 1 == cut.size()) ? "" : " ");
            Abc_Print(1, " : ");
            for (size_t i = 0; i < finalOutputs.size(); ++i)
                Abc_Print(1, "%d%s", finalOutputs[i], (i + 1 == finalOutputs.size()) ? "" : " ");
            Abc_Print(1, "\n");
        }
    }
    return 0;
}
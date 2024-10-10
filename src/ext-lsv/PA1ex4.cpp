#include "base/abc/abc.h" 
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <vector>
#include <set>
#include <iostream>
#include <algorithm>

// Command function declaration
static int PA1_CommandPrintCut(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
    Cmd_CommandAdd(pAbc, "LSV", "lsv_printcut", PA1_CommandPrintCut, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
    PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

// Helper function to generate all possible subsets (combinations) of a set
void GenerateCombinations(const std::set<unsigned int>& inputSet, int k, std::vector<std::set<unsigned int>>& combinations) {
    std::vector<unsigned int> elements(inputSet.begin(), inputSet.end());
    int n = elements.size();
    std::vector<bool> select(n);

    std::fill(select.begin(), select.begin() + std::min(k, n), true);  // Ensure combinations are <= k

    do {
        std::set<unsigned int> subset;
        for (int i = 0; i < n; ++i) {
            if (select[i]) subset.insert(elements[i]);
        }
        combinations.push_back(subset);
    } while (std::prev_permutation(select.begin(), select.end()));
}

// �C�| k-feasible cuts�A�å]�t�Ҧ��i�઺�զX
void Lsv_EnumerateKFeasibleCuts(Abc_Obj_t* pNode, int k, std::vector<std::set<unsigned int>>& cuts) {

    std::set<unsigned int> currentCut;
    std::vector<std::set<unsigned int>> faninCuts;

    // Collect fan-ins
    for (int i = 0; i < Abc_ObjFaninNum(pNode); ++i) {
        Abc_Obj_t* pFanin = Abc_ObjFanin(pNode, i);
        currentCut.insert(Abc_ObjId(pFanin));
    }

    // Generate all combinations of fan-ins with size <= k
    GenerateCombinations(currentCut, k, cuts);
}

// ���� cut �����Y�Ӹ`�I�A�åͦ��scut
void SubstituteNodeWithFanin(Abc_Obj_t* pObj, const std::set<unsigned int>& originalCut, std::vector<std::set<unsigned int>>& expandedCuts, int k) {
    for (auto nodeId : originalCut) {
        Abc_Obj_t* pNode = Abc_NtkObj(pObj->pNtk, nodeId);
        if (pNode && Abc_ObjFaninNum(pNode) > 0) {
            std::set<unsigned int> newCut = originalCut;
            newCut.erase(nodeId);

            std::set<unsigned int> faninSet;
            for (int i = 0; i < Abc_ObjFaninNum(pNode); ++i) {
                faninSet.insert(Abc_ObjId(Abc_ObjFanin(pNode, i)));
            }

            // Combine new fanin nodes with the remaining cut
            for (auto faninId : faninSet) {
                newCut.insert(faninId);
            }

            // �u�B�z k-feasible �����p
            if (newCut.size() <= k) {
                expandedCuts.push_back(newCut);
            }
        }
    }
}

// Compute K-feasible cuts for a given node
Vec_Ptr_t* ComputeKFeasibleCuts(Abc_Obj_t* pObj, int k) {
    Vec_Ptr_t* cutsVec = Vec_PtrAlloc(100); // Allocate memory for the cuts
    std::vector<std::set<unsigned int>> cuts;
    
    Lsv_EnumerateKFeasibleCuts(pObj, k, cuts);  // ���j�C�| cuts
    
    for (const auto& cut : cuts) {
        Vec_Int_t* vCut = Vec_IntAlloc(cut.size());
        for (unsigned int id : cut) {
            Vec_IntPush(vCut, id);
        }
        Vec_PtrPush(cutsVec, vCut);
    }
    
    return cutsVec;
}

// Print node ID
void PrintNodeId(unsigned int nodeId) {
    std::cout << nodeId << ": ";
}

// Print each cut
void PrintCut(unsigned int nodeId, const std::set<unsigned int>& cut) {
    PrintNodeId(nodeId);
    bool first = true;
    for (auto id : cut) {
        if (!first) std::cout << " ";
        std::cout << id;
        first = false;
    }
    std::cout << "\n";
}

// Helper function to replace non-primary input cut with primary input
void ReplaceWithPrimaryInputs(Abc_Obj_t* pObj, std::set<unsigned int>& cut, std::set<unsigned int>& primaryInputs) {
    std::set<unsigned int> newCut;
    for (auto nodeId : cut) {
        Abc_Obj_t* pNode = Abc_NtkObj(pObj->pNtk, nodeId);
        if (Abc_ObjIsPi(pNode)) {
            newCut.insert(nodeId);  // �p�G�O primary input�A�[�J�s�� cut
        } else {
            // �N node ���Ҧ� fanins �[�J
            for (int i = 0; i < Abc_ObjFaninNum(pNode); ++i) {
                newCut.insert(Abc_ObjId(Abc_ObjFanin(pNode, i)));
            }
        }
    }

    // ��o�ӷs cut ���� primary inputs �v�@�[�J�A�קK����
    for (auto id : newCut) {
        primaryInputs.insert(id);
    }
}

void Lsv_PrintKFeasibleCuts(Abc_Ntk_t* pNtk, int k) {
    Abc_Obj_t* pObj;
    int i;
    std::set<std::set<unsigned int>> printedCuts;  // �Ψ��קK���ƿ�X

    Abc_NtkForEachObj(pNtk, pObj, i) {
        // �����`�Ƹ`�I
        if (pObj == Abc_AigConst1(pNtk)) continue;

        // ���� Primary output
        if (!Abc_ObjIsPi(pObj) && !Abc_AigNodeIsAnd(pObj)) continue;

        // Print the node itself as a single cut
        std::set<unsigned int> nodeItself = { Abc_ObjId(pObj) };
        if (printedCuts.insert(nodeItself).second) {
            // �p�G�o��cut�٨S����X�L�A�h��X
            PrintCut(Abc_ObjId(pObj), nodeItself);
        }

        // �p�� k-feasible cuts
        Vec_Ptr_t* cuts = ComputeKFeasibleCuts(pObj, k);
        Vec_Ptr_t* cut;
        int j;

        std::set<unsigned int> expandedPrimaryCut;
        std::set<unsigned int> printedPrimaryCut;  // �����O�_��X primary inputs

        Vec_PtrForEachEntry(Vec_Ptr_t *, cuts, cut, j) {
            Vec_Int_t* vCut = (Vec_Int_t*)cut;
            Vec_IntSort(vCut, 0);  // ��`�I�Ƨ�

            if(Abc_ObjIsPi(pObj))continue;
		    
            // �N cut �ഫ�� set �榡
            std::set<unsigned int> currentCut;
            int f;
            Vec_IntForEachEntry(vCut, f, j) {
                currentCut.insert(f);
            }

            // �p�G�o��cut�٨S����X�L�A�h��X
            if (printedCuts.insert(currentCut).second) {
                PrintCut(Abc_ObjId(pObj), currentCut);
            }

            // �s�W�G�P�_�O�_�i�H���� cut ���Y�Ӹ`�I�åͦ��scut
            std::vector<std::set<unsigned int>> expandedCuts;
            SubstituteNodeWithFanin(pObj, currentCut, expandedCuts, k);

            for (const auto& expandedCut : expandedCuts) {
                if (printedCuts.insert(expandedCut).second) {
                    PrintCut(Abc_ObjId(pObj), expandedCut);  // �L�X�����᪺ cut
                }
            }

            // Primary input combination
            ReplaceWithPrimaryInputs(pObj, currentCut, expandedPrimaryCut);

            // �p�G primary input ���զX�٨S����X�L�A�h��X
            if (!expandedPrimaryCut.empty() && printedPrimaryCut.empty()) {
                if (printedCuts.insert(expandedPrimaryCut).second) {
                    PrintCut(Abc_ObjId(pObj), expandedPrimaryCut);
                    printedPrimaryCut = expandedPrimaryCut;  // �T�O�u��X�@��
                }
            }
        }

        // ���� cuts �귽
        Vec_PtrFree(cuts);
    }
}

// Command to print cuts
int PA1_CommandPrintCut(Abc_Frame_t* pAbc, int argc, char** argv) {
    Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
    int k = 3;

    std::cout << "please input k (between 3 and 6): ";
    std::cin >> k;

    while (k < 3 || k > 6) {
        std::cerr << "k must be between 3 and 6\nPlease input again: ";
        std::cin >> k;
    }

    if (!pNtk) {
        std::cerr << "the network is empty\n";
        return 1;
    }

    Lsv_PrintKFeasibleCuts(pNtk, k);
    return 0;
}

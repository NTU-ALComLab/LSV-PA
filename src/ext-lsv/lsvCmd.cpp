#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

// include STL headers
#include <bits/stdc++.h>
using namespace std;
// #define LSV_DEBUG

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintSOPUnate(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
    Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
    Cmd_CommandAdd(pAbc, "LSV", "lsv_print_sopunate", Lsv_CommandPrintSOPUnate, 0);
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


void printSOPUnateness(Abc_Obj_t* pObj) {
    Abc_Obj_t* pFanin;
    char* sop   = (char*)pObj->pData;
    char type[3][10] = {"+unate", "-unate", "binate"};
    int cubeNum = Abc_SopGetCubeNum(sop);

    stringstream                ss(sop);            // input stream (sop form)
    vector<int>                 outputs(cubeNum);   // function outputs (only 0 and 1)
    vector<string>              inputs(cubeNum);    // function inputs (eg. 1-- or 010...)
    vector<vector<Abc_Obj_t*>>  unateness(3);       // 0: +unate, 1: -unate, 2: binate

    for (int i = 0; i < cubeNum; ++i) 
        ss >> inputs[i] >> outputs[i];

    int index = 0, j = 0;
    Abc_ObjForEachFanin(pObj, pFanin, index) {
        char flag = inputs[0][index];
        for (j = 0; j < cubeNum; ++j) {
            if (flag == '-') 
                flag = inputs[j][index];
            else {
                if (inputs[j][index] != '-' && inputs[j][index] != flag) {
                    flag = '2';
                    break;
                }
            }
        }

        if (flag != '-') {
            if (outputs[j - 1] == 1 && flag != '2')
                flag = (flag == '0') ? '1' : '0';
            unateness[flag - '0'].push_back(pFanin);
        }
    }

    if (!unateness[0].empty() || !unateness[1].empty() || !unateness[2].empty()) {
        cout << "node " << Abc_ObjName(pObj) << ":\n";
        for (int i = 0; i < 3; ++i) {
            if (!unateness[i].empty()) {
                sort(begin(unateness[i]), end(unateness[i]),
                    [&](auto& lhs, auto& rhs) {
                        return Abc_ObjId(lhs) < Abc_ObjId(rhs);
                    }
                );

                cout << type[i] << " inputs: " << Abc_ObjName(unateness[i][0]);
                for (int j = 1; j < unateness[i].size(); ++j)
                    cout << "," << Abc_ObjName(unateness[i][j]);
                cout << '\n';
            }
        }
    }
#ifdef LSV_DEBUG
    int j = 0;
    Abc_ObjForEachFanin(pObj, pFanin, j) {
        cout << Abc_ObjName(pFanin) << ' ';
    }
    cout << '\n';
    cout << sop << '\n';
#endif
}

void Lsv_NtkPrintSOPUnate(Abc_Ntk_t* pNtk) {
    int i = 0;
    Abc_Obj_t* pObj;
    Abc_NtkForEachNode(pNtk, pObj, i) {
        if (Abc_NtkHasSop(pNtk)) 
            printSOPUnateness(pObj);
    }
}

int Lsv_CommandPrintSOPUnate(Abc_Frame_t* pAbc, int argc, char** argv) {
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
    else if (!Abc_NtkHasSop(pNtk)) {
        Abc_Print(-1, "The node of logic network is not SOP.\n");
        return 1;
    }
    Lsv_NtkPrintSOPUnate(pNtk);
    return 0;

usage:
    Abc_Print(-2, "usage: lsv_print_sopunate [-h]\n");
    Abc_Print(-2, "\t        print the unate information for each node in the SOP form.\n");
    Abc_Print(-2, "\t-h    : print the command usage\n");
    return 1;
}
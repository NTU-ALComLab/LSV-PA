#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "sat/cnf/cnf.h"

// include STL headers
#include <bits/stdc++.h>
using namespace std;
// #define LSV_DEBUG

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintSOPUnate(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintPoUnate(Abc_Frame_t* pAbc, int argc, char** argv);

extern "C" Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );

void init(Abc_Frame_t* pAbc) {
    Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
    Cmd_CommandAdd(pAbc, "LSV", "lsv_print_sopunate", Lsv_CommandPrintSOPUnate, 0);
    Cmd_CommandAdd(pAbc, "LSV", "lsv_print_pounate", Lsv_CommandPrintPoUnate, 0);
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

void Lsv_vecPrint(Abc_Ntk_t* pNtk, vector<int>& PosUnate, vector<int>& NegUnate, vector<int>& BiUnate) {

    if (!PosUnate.empty()) {
        cout << "+unate inputs:";
        for (int i = 0; i < PosUnate.size(); ++i)
            cout << ", "[i == 0] << Abc_ObjName(Abc_NtkCi(pNtk, PosUnate[i]));
        cout << '\n';
    }

    if (!NegUnate.empty()) {
        cout << "-unate inputs:";
        for (int i = 0; i < NegUnate.size(); ++i)
            cout << ", "[i == 0] << Abc_ObjName(Abc_NtkCi(pNtk, NegUnate[i]));
        cout << '\n';
    }

    if (!BiUnate.empty()) {
        cout << "binate inputs:";
        for (int i = 0; i < BiUnate.size(); ++i)
            cout << ", "[i == 0] << Abc_ObjName(Abc_NtkCi(pNtk, BiUnate[i]));
        cout << '\n';
    }

    // if (!PosUnate.empty()) {
    //     printf("+unate inputs:");
    //     for (int i = 0; i < PosUnate.size(); ++i)
    //         if (i == 0) printf(" %s", Abc_ObjName(Abc_NtkCi(pNtk, PosUnate[i])));
    //         else        printf(",%s", Abc_ObjName(Abc_NtkCi(pNtk, PosUnate[i])));
    //     printf("\n");
    // }

    // if (!NegUnate.empty()) {
    //     printf("-unate inputs:");
    //     for (int i = 0; i < NegUnate.size(); ++i)
    //         if (i == 0) printf(" %s", Abc_ObjName(Abc_NtkCi(pNtk, NegUnate[i])));
    //         else        printf(",%s", Abc_ObjName(Abc_NtkCi(pNtk, NegUnate[i])));
    //     printf("\n");
    // }

    // if (!BiUnate.empty()) {
    //     printf("binate inputs:");
    //     for (int i = 0; i < BiUnate.size(); ++i)
    //         if (i == 0) printf(" %s", Abc_ObjName(Abc_NtkCi(pNtk, BiUnate[i])));
    //         else        printf(",%s", Abc_ObjName(Abc_NtkCi(pNtk, BiUnate[i])));
    //     printf("\n");
    // }
}

Abc_Ntk_t* Lsv_NtkPrintPoUnate(Abc_Ntk_t* pNtk) {
    Abc_Ntk_t  * pNtkNew;
    Abc_Obj_t  * pPo, * pPi, * pNode;

    Aig_Man_t  * pMan;
    Aig_Obj_t  * pObj, * pObjCo;

    Cnf_Dat_t  * pCnfPos, * pCnfNeg;
    sat_solver * pSat;

    int * assume = nullptr;
    int idx_pPo, offset, status, i, j;
    bool isComplment, isPosUnate, isNegUnate;

    vector<int> PosUnate, NegUnate, BiNate;
    unordered_map<string, int> nameMapping;

    Abc_NtkForEachPo(pNtk, pPo, idx_pPo) {
        assert( Abc_ObjFaninNum(pPo) == 1 );
        cout << "node " << Abc_ObjName(pPo) << ":\n";

        // create a single po cone circuit
        pNode   = Abc_ObjFanin0(pPo);
        pNtkNew = Abc_NtkCreateCone(pNtk, pNode, Abc_ObjName(pPo), 0);

        // convert single po Abc_Ntk_t into Aig_Man_t
        pMan = Abc_NtkToDar(pNtkNew, 0, 0);

        // get co pobj
        pObjCo = Aig_ManCo(pMan, 0);

        // derive CNF of function F
        pCnfPos = Cnf_Derive(pMan, Aig_ManCoNum(pMan)); // function F

        // check the phase of po
        // isComplment = (Aig_ObjPhase(Aig_ManCo(pMan, idx_pPo)) == 0);
        isComplment = Abc_ObjFaninC0(pPo);
        // cout << "[isComplment]: " << isComplment << '\n';
        
        // complment function F
        // Aig_ManFlipFirstPo(pMan);

        // derive CNF of function ~F
        // pCnfNeg = Cnf_Derive(pMan, Aig_ManCoNum(pMan)); // function ~F
        pCnfNeg = Cnf_DataDup(pCnfPos);

        // rename variables of function ~F
        Cnf_DataLift( pCnfNeg, pCnfPos->nVars );

        // Cnf_DataPrint(pCnfPos, 0);
        // cout << "\n";
        // Cnf_DataPrint(pCnfNeg, 0);
        
        // star a new sat solver
        pSat = sat_solver_new();
        sat_solver_setnvars(pSat, pCnfPos->nVars + pCnfNeg->nVars + Aig_ManCiNum(pMan));
        offset = pCnfPos->nVars + pCnfNeg->nVars;
        // cout << "Aig_ManCiNum(pMan): " << Aig_ManCiNum(pMan) << '\n';

        // add clauses of pCnfPos to sat solver
        for (j = 0; j < pCnfPos->nClauses; ++j)
            if (!sat_solver_addclause(pSat, pCnfPos->pClauses[j], pCnfPos->pClauses[j+1]))
                assert(0); // need to check tautology ???

        // add clauses of pCnfNeg to sat solver
        for (j = 0; j < pCnfNeg->nClauses; ++j)
            if (!sat_solver_addclause(pSat, pCnfNeg->pClauses[j], pCnfNeg->pClauses[j+1]))
                assert(0); // need to check tautology ???

        // adds clauses to assert the equivalence between two variables controlled by an enabling variable.
        assume = new int[Aig_ManCiNum(pMan) + 4]();
        Aig_ManForEachCi(pMan, pObj, i) {
            sat_solver_add_buffer_enable(pSat, pCnfPos->pVarNums[pObj->Id], pCnfNeg->pVarNums[pObj->Id], offset + i, 0);
            assume[i + 4] = toLitCond(offset + i , 0);

            // create a name mapping table
            nameMapping[Abc_ObjName(Abc_NtkCi(pNtkNew, i))] = i;
        }

        // Aig_ManForEachCi(pMan, pObj, i) {
        Abc_NtkForEachPi(pNtk, pPi, i) {
            isPosUnate = isNegUnate = true;

            auto it = nameMapping.find(Abc_ObjName(Abc_NtkCi(pNtk, i)));
            if (it != nameMapping.end()) {
                j = it->second;
                pObj = Aig_ManCi(pMan, j);

                // cofactor
                assume[0]     = toLitCond(pCnfPos->pVarNums[pObj->Id], 0);
                assume[1]     = toLitCond(pCnfNeg->pVarNums[pObj->Id], 1);

                // close enable variable
                assume[j + 4] = toLitCond(offset + j, 1);

                // pos-unate
                assume[2]     = toLitCond(pCnfPos->pVarNums[pObjCo->Id], 1);
                assume[3]     = toLitCond(pCnfNeg->pVarNums[pObjCo->Id], 0);
                
                status = sat_solver_solve(pSat, assume, assume + Aig_ManCiNum(pMan) + 4, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0);
                isPosUnate = (status == l_False) ;

                // neg-unate
                assume[2]     = toLitCond(pCnfPos->pVarNums[pObjCo->Id], 0);
                assume[3]     = toLitCond(pCnfNeg->pVarNums[pObjCo->Id], 1);
                status = sat_solver_solve(pSat, assume, assume + Aig_ManCiNum(pMan) + 4, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0);
                isNegUnate = (status == l_False) ;

                // reset
                assume[0]     = toLitCond(pCnfPos->pVarNums[pObj->Id], 0);
                assume[1]     = toLitCond(pCnfNeg->pVarNums[pObj->Id], 0);
                assume[j + 4] = toLitCond(offset + j, 0);
            }

            if (isComplment) swap(isPosUnate, isNegUnate);
            if (!isPosUnate && !isNegUnate) {
                BiNate.push_back(i);
            }
            else {
                if (isPosUnate) PosUnate.push_back(i);
                if (isNegUnate) NegUnate.push_back(i);
            }

            // if (isComplment)
            //     cout << Abc_ObjName(Abc_NtkCi(pNtk, i)) << " " << isNegUnate << " " << isPosUnate << '\n';
            // else
            //     cout << Abc_ObjName(Abc_NtkCi(pNtk, i)) << " " << isPosUnate << " " << isNegUnate << '\n';           
        }

        // print results
        Lsv_vecPrint(pNtk, PosUnate, NegUnate, BiNate);

        // free or reset data
        Cnf_DataFree(pCnfPos);
        Cnf_DataFree(pCnfNeg);
        sat_solver_delete(pSat);
        Aig_ManStop(pMan);
        if (assume) delete[] assume;
        assume = nullptr;

        BiNate.resize(0);
        PosUnate.resize(0);
        NegUnate.resize(0);
        nameMapping.clear();
        // break;
        // cout << '\n';
    }

    return nullptr;
    // return pNtkNew;
}

int Lsv_CommandPrintPoUnate(Abc_Frame_t* pAbc, int argc, char** argv) {
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
    else if (!Abc_NtkIsStrash(pNtk)) {
        Abc_Print( -1, "Currently only works for structurally hashed circuits.\n" );
        return 0;
    }

    Lsv_NtkPrintPoUnate(pNtk);

    // replace the current network
    // Abc_FrameReplaceCurrentNetwork(pAbc, Lsv_NtkPrintPoUnate(pNtk));
    return 0;

usage:
    Abc_Print(-2, "usage: lsv_print_sopunate [-h]\n");
    Abc_Print(-2, "\t        print the unate information for each primary output in terms of all primary inputs.\n");
    Abc_Print(-2, "\t-h    : print the command usage\n");
    return 1;
}
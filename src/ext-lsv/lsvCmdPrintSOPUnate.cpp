#include <vector>
#include <algorithm>
#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "lsvCmdPrintSOPUnate.h"
#include "lsvUtils.h"

using namespace std;

const int LSV_NO_UNATENESS = -1,
          LSV_NEGATIVE_UNATE = 0,
          LSV_POSITIVE_UNATE = 1,
          LSV_BINATE = 2;
const int LSV_UNATENESS_NUM = 3;
const char *UNATE_NAME[LSV_UNATENESS_NUM] = { "-unate", "+unate", "binate" };

void Lsv_NtkPrintSOPUnate(Abc_Ntk_t* pNtk) {
    Abc_Obj_t* pNode;
    int i;
    if (Abc_NtkHasSop(pNtk)) {
        Abc_NtkForEachNode(pNtk, pNode, i) {
            char *sop = (char*)pNode->pData;
            if (!(Abc_SopIsConst0(sop) || Abc_SopIsConst1(sop))) {
                printf("node %s:\n", Abc_ObjName(pNode));

                vector<Abc_Obj_t> unateness_vecs[LSV_UNATENESS_NUM];
                int tot_varnum = Abc_SopGetVarNum(sop);
                bool is_offset = (sop[tot_varnum + 1] == '0');

                for (int var_num = 0; var_num < tot_varnum; var_num++) {
                    int unateness = LSV_NO_UNATENESS;
                    for (char *var_lit = sop; *var_lit != '\0'; var_lit += (tot_varnum + 3)) {
                        if (var_lit[var_num] != '-') {
                            int var_value = var_lit[var_num] - '0';
                            if (unateness == LSV_NO_UNATENESS) {
                                unateness = var_value;
                            }
                            else {
                                if (unateness != var_value) {
                                    unateness = LSV_BINATE;
                                    break;
                                }
                            }
                        }
                    }
                    if (is_offset && unateness != LSV_BINATE) {
                        unateness = (int)(!unateness);
                    }
                    unateness_vecs[unateness].push_back(*Abc_ObjFanin(pNode, var_num));
                }
                int vec_order[] = { LSV_POSITIVE_UNATE, LSV_NEGATIVE_UNATE, LSV_BINATE };
                for(int n = 0; n < LSV_UNATENESS_NUM; n++) {
                    int vn = vec_order[n];
                    if (!unateness_vecs[vn].empty()) {
                        sort(unateness_vecs[vn].begin(), unateness_vecs[vn].end(), Lsv_CmpAbcObjId);
                        printf("%s inputs: ", UNATE_NAME[vn]);
                        Lsv_UtilPrintAbcObjVecs(unateness_vecs[vn]);
                        puts("");
                    }
                }
            }
        }
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
    Lsv_NtkPrintSOPUnate(pNtk);
    return 0;

usage:
    Abc_Print(-2, "usage: lsv_print_sopunate [-h]\n");
    Abc_Print(-2, "\t        print the unateness of all variables in the represent SOP onset\n");
    Abc_Print(-2, "\t-h    : print the command usage\n");
    return 1;
}
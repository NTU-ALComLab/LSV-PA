#include <iostream>
#include <set>
#include "ext-lsv/lsv.h"

void Lsv_NtkPrintUnate(Abc_Ntk_t *pNtk) {
    Abc_Obj_t* pObj;
    int i, j, value;
    auto cmp = [](Abc_Obj_t *o1, Abc_Obj_t *o2) { return Abc_ObjId(o1) < Abc_ObjId(o2); };
    std::set<Abc_Obj_t*, decltype(cmp)> positive_unate(cmp);
    std::set<Abc_Obj_t*, decltype(cmp)> negative_unate(cmp);
    std::set<Abc_Obj_t*, decltype(cmp)> binate(cmp);

    assert(Abc_NtkHasSop(pNtk));
    Abc_NtkForEachNode(pNtk, pObj, i) {
        positive_unate.clear();
        negative_unate.clear();
        binate.clear();
        std::cout << "node " << Abc_ObjName(pObj) << ":" << std::endl;
        char * sop = (char*)pObj->pData;
        if (Abc_SopIsConst0(sop) || Abc_SopIsConst1(sop)) continue;
        char *pCube;
        Abc_SopForEachCube(sop, Abc_ObjFaninNum(pObj), pCube) {
            bool inv = Abc_SopIsComplement(pCube);
            Abc_CubeForEachVar(pCube, value, j) {
                if (pCube[j] == '-') continue;
                bool isPostive = ((pCube[j] == '0') && inv) || ((pCube[j] == '1') && !inv);
                Abc_Obj_t *fanin = Abc_ObjFanin(pObj, j);
                if (binate.find(fanin) != binate.end()) {
                    continue;
                }

                if (isPostive) {
                    if (negative_unate.find(fanin) != negative_unate.end()) {
                        negative_unate.erase(fanin);
                        binate.insert(fanin);
                    } else {
                        positive_unate.insert(fanin);
                    }
                } else {
                    if (positive_unate.find(fanin) != positive_unate.end()) {
                        positive_unate.erase(fanin);
                        binate.insert(fanin);
                    } else {
                        negative_unate.insert(fanin);
                    }
                }
            }
        }
        Abc_Obj_t * pFanin;
        Abc_ObjForEachFanin(pObj, pFanin, j) {
            if (positive_unate.find(pFanin) == positive_unate.end() && negative_unate.find(pFanin) == negative_unate.end()) {
                binate.insert(pFanin);
            }
        }
        if (positive_unate.size() != 0) {
            std::cout << "+unate inputs: ";
            for (Abc_Obj_t* o: positive_unate) {
                if (o != *positive_unate.begin()) std::cout << ",";
                std::cout << Abc_ObjName(o);
            }
            std::cout << std::endl;
        }
        if (negative_unate.size() != 0) {
            std::cout << "-unate inputs: ";
            for (Abc_Obj_t* o: negative_unate) {
                if (o != *negative_unate.begin()) std::cout << ",";
                std::cout << Abc_ObjName(o);
            }
            std::cout << std::endl;
        }
        if (binate.size() != 0) {
            std::cout << "binate inputs: ";
            for (Abc_Obj_t* o: binate) {
                if (o != *binate.begin()) std::cout << ",";
                std::cout << Abc_ObjName(o);
            }
            std::cout << std::endl;
        }
    }
}

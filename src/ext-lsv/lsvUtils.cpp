#include <vector>
#include "lsvUtils.h"

void Lsv_UtilPrintAbcObjVecs(std::vector<Abc_Obj_t> &vec) {
    char *separator = ",";
    char *sep = "";
    for(int i = 0; i < vec.size(); i++) {
        printf("%s%s", sep, Abc_ObjName(&vec[i]));
        sep = separator;
    }
}

bool Lsv_CmpAbcObjId(Abc_Obj_t& a, Abc_Obj_t& b) {
    return Abc_ObjId(&a) < Abc_ObjId(&b);
}

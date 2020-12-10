#include "lsvUtils.h"

int Lsv_sortCompare(Abc_Obj_t ** a, Abc_Obj_t ** b) {
  return Abc_ObjId(*a) > Abc_ObjId(*b)? 1: -1;
}

void Lsv_printInputs(const char * str, Vec_Ptr_t * vec) {
  Abc_Obj_t * pEntry;
  int i, sz = Vec_PtrSize(vec);

  if (sz == 0) return;
  printf("%s: ", str);
  Vec_PtrForEachEntry( Abc_Obj_t *, vec, pEntry, i )
    printf("%s%c", Abc_ObjName(pEntry), i != sz-1? ',':'\n');
}


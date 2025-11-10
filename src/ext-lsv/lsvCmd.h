#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <unordered_set>
#include <set>
#include <map>
#include <vector>
#include <cstdlib>

extern void processNode(Abc_Obj_t* pObj, std::set<int>& visited, std::map<int, std::vector<std::set<int>>>& cutTable, int k);
extern void Lsv_NtkPrintNodes(Abc_Ntk_t* pNtk);
extern void Lsv_NtkPrintMocut(Abc_Ntk_t* pNtk, int k, int l);
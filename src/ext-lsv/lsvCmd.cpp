#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <vector>
#include <set>
#include <algorithm>
using namespace std; 

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintCut  (Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_printcut",    Lsv_CommandPrintCut,   0);
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

///////////////////////////////////////////////////////////////////////////////////////

void Lsv_NtkPrintCut(Abc_Ntk_t* pNtk, int k = 0) {
  Abc_Obj_t* pObj;
  int i, id;
  vector<set<set<int>>> v;

  // Initialization

  Abc_NtkForEachObj(pNtk, pObj, i) {
    v.push_back(set<set<int>>());
  }

  Abc_NtkForEachObj(pNtk, pObj, i) {
    // extracting information from the AIG
    id = Abc_ObjId(pObj);
    if (id == 0)
      continue;
    Abc_Obj_t* pFanin;
    int j;
    int fanInId[2]; 
    Abc_ObjForEachFanin(pObj, pFanin, j)
      fanInId[j] = Abc_ObjId(pFanin);
    
    // Building vector v
    if (j != 1)
      v[id].insert(set<int>{id});
    if (j == 2){
      for (const auto &s1 : v[fanInId[0]]) for (const auto &s2 : v[fanInId[1]]){
        set<int> merged_set = s1;
        merged_set.insert(s2.begin(), s2.end());
        if (merged_set.size() <= k){
          // Todo: maybe sort the set(?) here
          v[id].insert(merged_set);
        }
      }
    }
  }

  // Check if there is including relation
  for (i = 0; i < v.size(); i++) {
    set<set<int>>::iterator itr1 = v[i].begin(), itr2 = v[i].begin();
    while (itr1 != v[i].end()){
      while (itr2 != v[i].end()){
        if(itr1 != itr2 && includes((*itr1).begin(), (*itr1).end(), (*itr2).begin(), (*itr2).end()))
          itr1 = v[i].erase(itr1);
        else
          itr2++;
      }
      itr2 = v[i].begin();
      itr1++;
    }
  }

  // Printing out the result
  for (i = 0; i < v.size(); i++) {
    // printf("%d: {", i);
    for (const auto &s : v[i]) {                // v[i] is a set<vector<int>>
      printf("%d: ", i);
      for (const auto &e : s){                 // s in a set<int>
        printf("%d ", e);
      }
      printf("\n");
    }
    // printf("}\n");
  }
}

int Lsv_CommandPrintCut(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c, k = 0;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "kh")) != EOF) {
    switch (c) {
      case 'k': 
        if ( globalUtilOptind >= argc )
        {
            Abc_Print( -1, "Command line switch \"-k\" should be followed by an integer.\n" );
            goto usage;
        }
        k = atoi(argv[globalUtilOptind]);
        globalUtilOptind++;
        if ( k < 0 )
            goto usage;
        break;
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
  Lsv_NtkPrintCut(pNtk, k);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_print_nodes [-h]\n");
  Abc_Print(-2, "\t        prints the nodes in the network\n");
  Abc_Print(-2, "\t-k    : specifies k-feasible cuts\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}

#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <map>
#include <set>
#include <algorithm>

using namespace std;

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintMoCuts(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocuts", Lsv_CommandPrintMoCuts, 0);
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

void Lsv_NtkPrintMoCuts(Abc_Ntk_t* pNtk, int k, int l)
{
    Abc_Obj_t* pObj;
    int i;
    map<set<int>, set<int>> cutmap;
    Abc_NtkForEachObj(pNtk, pObj, i) {
        if(Abc_ObjIsPo(pObj)) continue;
        pObj->pData = new set<set<int>>();
        set<set<int>>& cutset = *(set<set<int>>*)pObj->pData;
        cutset.insert({Abc_ObjId(pObj)});
        Abc_Obj_t* pFanin;
        int j;
        void * cutset0 = NULL, * cutset1 = NULL;
        Abc_ObjForEachFanin(pObj, pFanin, j) {
            if (j == 0) cutset0 = pFanin->pData;
            else cutset1 = pFanin->pData;
        }
        if(cutset0 == NULL || cutset1 == NULL) continue;
        for(auto s0 : *(set<set<int>>*)cutset0) {
            for(auto s1 : *(set<set<int>>*)cutset1) {
                set<int> newset;
                set_union(s0.begin(), s0.end(), s1.begin(), s1.end(), inserter(newset, newset.begin()));
                if ((int)newset.size() <= k) {
                    cutset.insert(newset);
                    cutmap[newset].insert(Abc_ObjId(pObj));
                }
            }
        }
    }
    for (auto it = cutmap.begin(); it != cutmap.end(); it++) {
        if ((int)it->first.size() <= k && (int)it->second.size() >= l) {
            for (auto idit = it->first.begin(); idit != it->first.end(); idit++) {
                printf("%d ", *idit);
            }
            printf(":");
            for (auto idit = it->second.begin(); idit != it->second.end(); idit++) {
                printf(" %d", *idit);
            }
            printf("\n");
        }
    }
}

int Lsv_CommandPrintMoCuts(Abc_Frame_t* pAbc, int argc, char** argv)
{
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
    if (argc < 3) goto usage;
    Lsv_NtkPrintMoCuts(pNtk, atoi(argv[1]), atoi(argv[2]));
    return 0;

usage:
    Abc_Print(-2, "usage: lsv_print_mo_cuts [-h] <k> <l>\n");
    return 1;
}
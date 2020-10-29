#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <vector>
#include <string>
#include <sstream>
#include <iostream>
#include <algorithm>
#include <utility>

using namespace std;

static int Lsv_CommandPrintSopunate(Abc_Frame_t* pAbc, int argc, char** argv);

void Lsv_NtkPrintSopunate(Abc_Ntk_t* pNtk) {
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i) {
    Abc_Obj_t* pFanin;
    int j;
    vector<pair<unsigned int, string> > fanin, group[4];
    Abc_ObjForEachFanin(pObj, pFanin, j) {
      fanin.push_back(make_pair(Abc_ObjId(pFanin), Abc_ObjName(pFanin)));
    }
    if (!fanin.empty()) {
      printf("node %s:\n", Abc_ObjName(pObj));
      if (Abc_NtkHasSop(pNtk)) {
        stringstream ss((char*)pObj->pData);
        vector<int> types(fanin.size(), 0);
        string temp, gname[4] = {"", "+unate", "-unate", "binate"};
        ss >> temp;
        while (!ss.eof()) {
          for (int j = 0; j < fanin.size(); j++) if (temp[j] != '-') types[j] |= (1 << (temp[j] - '0'));
	  ss >> temp; ss >> temp;
        }
        for (int j = 0; j < fanin.size(); j++) group[types[j]].push_back(fanin[j]);
        if (temp[0] == '1') swap(group[1], group[2]);
        for (int j = 1; j < 4; j++) if (!group[j].empty()) {
          cout << gname[j] << " inputs: ";
	  sort(group[j].begin(), group[j].end());
	  for (int i0 = 0; i0 < group[j].size(); i0++) {
	    cout << group[j][i0].second << (i0 == group[j].size() - 1 ? '\n': ',');
	  }
        }
      }
    }
  }
}

int Lsv_CommandPrintSopunate(Abc_Frame_t* pAbc, int argc, char** argv) {
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
  Lsv_NtkPrintSopunate(pNtk);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_print_sopunate [-h]\n");
  Abc_Print(-2, "\t        prints the nodes in the network\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}

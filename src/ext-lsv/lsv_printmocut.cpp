#include <iostream>
#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <deque>
#include <map>
#include <algorithm>
#include <vector>
#include <string>
using namespace std;

vector<int> objToId(vector<Abc_Obj_t*> v){
  vector<int> ids;
  for(Abc_Obj_t* i : v){
    ids.push_back(Abc_ObjId(i));
  }
  sort(ids.begin(), ids.end());
  return ids;
}

vector<vector<Abc_Obj_t*>> getmorecut(vector<Abc_Obj_t*> cut){
  vector<vector<Abc_Obj_t*>> return_value;
  vector<Abc_Obj_t*> newcut;
  for(int i = 0; i < cut.size(); i++){
    newcut.clear();
    if(Abc_ObjIsPi(cut[i])){
      continue;
    }
    Abc_Obj_t* fanin;
    int j;
    Abc_ObjForEachFanin(cut[i], fanin, j){
      newcut.push_back(fanin);
    }
    for(int j = 0; j < cut.size(); j++){
      if(i != j){
        newcut.push_back(cut[j]);
      }
    }
    return_value.push_back(newcut);
  }
  return return_value;
}

int lsv_printmocut(Abc_Frame_t* pAbc, int argc, char** argv){
  if(argc != 3){
    Abc_Print( -1, "Usage: myfunc <number>\n" );
    return 1;
  }
  int k = atoi(argv[1]);
  int l = atoi(argv[2]);
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  Abc_Obj_t* pObj;
  map<vector<int>, vector<int>> allcut;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i){
    vector<Abc_Obj_t*> cut;
    Abc_Obj_t* fanin;
    int j;
    Abc_ObjForEachFanin(pObj, fanin, j){
      cut.push_back(fanin);
    }
    deque<vector<Abc_Obj_t*>> cuts;
    if(cut.size() < k){
      cuts.push_back(cut);
    }
    if(cut.size() <= k){
      vector<int> v = objToId(cut);
      allcut[v].push_back(Abc_ObjId(pObj));
    }
    while(!cuts.empty()){
      vector<Abc_Obj_t*> ncut = cuts.front();
      cuts.pop_front();
      vector<vector<Abc_Obj_t*>> morecut = getmorecut(ncut);
      for(vector<Abc_Obj_t*> cut2 : morecut){
        vector<int> v = objToId(cut2);
        allcut[v].push_back(Abc_ObjId(pObj));
        if(cut2.size() < k){
          cuts.push_back(cut2);
        }
      }
    }
  }
  for(const auto& cut : allcut){
    if(cut.second.size() >= l){
      for(int i : cut.first){
        cout << i << " ";
      }
      cout << ": ";
      for(int i : cut.second){
        cout << i << " ";
      }
      cout << "\n";
    }
  }
  usage:
  Abc_Print(-2, "usage: lsv_printmocut [-h]\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}




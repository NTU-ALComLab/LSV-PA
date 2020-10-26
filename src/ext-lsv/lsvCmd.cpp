#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <vector>
#include <iostream>
#include <sstream> 
#include <string>
#include <regex>
#include <assert.h>
#include <algorithm>

using namespace std;

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintSopunate(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_sopunate", Lsv_CommandPrintSopunate, 0);
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
bool compare(pair< Abc_Obj_t*, short> a, pair< Abc_Obj_t*, short> b) {
  return Abc_ObjId(a.first) < Abc_ObjId(b.first);
}
void Lsv_NtkPrintSopunate(Abc_Ntk_t* pNtk) {
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i) {
    Abc_Obj_t* pFanin;
    int j;
    vector< pair< Abc_Obj_t*, short>  > allFanin; // int==0 means neg, int==1 means pos, int==2 means bi, int==3 means error
    Abc_ObjForEachFanin(pObj, pFanin, j) {
      Abc_ObjForEachFanin(pObj, pFanin, j) {
        allFanin.push_back(make_pair(pFanin, 3));
      }
      if (Abc_NtkHasSop(pNtk)) {
        string s = (string)(char*)pObj->pData;
        regex newline{R"(\n+)"};
        regex whitespace{R"(\s+)"};
        sregex_token_iterator it{s.begin(), s.end(), newline, -1};
        vector<string> lines{it, {}};
        for ( string const str: lines){
          sregex_token_iterator it{str.begin(), str.end(), whitespace, -1};
          vector<string> toks{it, {}};
          assert( toks.size() == 2);
          bool on = 0; 
          stringstream sstr1( toks[1] ); 
          assert( toks[1].length() == 1);
          sstr1 >> on;
          assert( toks[0].length() == allFanin.size() );
          for( int i = 0; i < toks[0].length(); ++i){
            if ( toks[0][i] == '0' ){
              if ( allFanin[i].second == 3) allFanin[i].second = -1;
              else if ( allFanin[i].second == 1) allFanin[i].second = 2;
            }
            else if ( toks[0][i] == '1' ){
              if ( allFanin[i].second == 3) allFanin[i].second = 1;
              else if ( allFanin[i].second == -1) allFanin[i].second = 2;
            }
          }
          if ( !on )
            for ( auto& it: allFanin) it.second *= -1;
        }
      }
    }
    if (allFanin.size() == 0) return;
    sort(allFanin.begin(),allFanin.end(), compare);
    printf("node %s:\n", Abc_ObjName(pObj));
    vector<Abc_Obj_t*> Fanin2BPrinted;
    for ( short nateType: {1,-1,2}){
      Fanin2BPrinted.clear();
      for( auto& Fanin: allFanin)
        if ( Fanin.second == nateType) Fanin2BPrinted.push_back( Fanin.first);
      if ( Fanin2BPrinted.size() == 0) continue;
      else{
        if ( nateType == -1 ) cout << "-unate inputs: ";
        else if ( nateType == 1 ) cout << "+unate inputs: ";
        else if ( nateType == 2 ) cout << "binate inputs: ";
        cout << Abc_ObjName(Fanin2BPrinted[0]);
        Fanin2BPrinted.erase(Fanin2BPrinted.begin());
      }
      for( auto& Fanin: Fanin2BPrinted)
        cout << ',' << Abc_ObjName(Fanin);
      cout << '\n';
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

int Lsv_CommandPrintSopunate(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c;
  vector< int > vec_int;

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
  Abc_Print(-2, "usage: lsv_print_nodes [-h]\n");
  Abc_Print(-2, "\t        prints the nodes in the network\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}
#include <iostream>
#include <algorithm>
#include <string>
#include <vector>
#include <unordered_map>
#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

using namespace std;

// add new command
static int LSV_CommandPrintMSFC(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc)
{
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_msfc", LSV_CommandPrintMSFC, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = { init, destroy };

struct PackageRegistrationManager
{
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

// ** some useful function **
// abc.h --> Abc_ObjIsPi(pObj), Abc_ObjIsPo(pObj)
// abc.h --> Abc_ObjForEachFanin(), Abc_ObjForEachFanout()
// abc.h --> Abc_NtkForEachPi(), Abc_NtkForEachPo()

// ** msfc flag **
// default = global-1, traverse = global, (PI or multi-fanout) = global-2

// compare function
bool compareV(Abc_Obj_t* a, Abc_Obj_t* b)
{
  return Abc_ObjId(a) < Abc_ObjId(b);
}

bool compareVV(vector<Abc_Obj_t*>& a, vector<Abc_Obj_t*>& b)
{
  return Abc_ObjId(a[0]) < Abc_ObjId(b[0]);
}

// unordered map --> <const name, flag>
unordered_map<string, int> const_exist;

// traverse function
void Lsv_Traverse_MSFC(Abc_Ntk_t* pNtk, Abc_Obj_t* pNode, vector<Abc_Obj_t*>& find_msfc)
{
  // if meet multi-fanout --> return (count = 1 --> exist)
  if ((!Abc_NodeIsTravIdPrevious(pNode)) && (!Abc_NodeIsTravIdCurrent(pNode))) { return; }
  if (Abc_NodeIsTravIdCurrent(pNode)) { return; }
  if (Abc_NodeIsTravIdPrevious(pNode))
  {
    Abc_NodeSetTravIdCurrent(pNode); // marked as traversed 
    find_msfc.push_back(pNode);
  }
  // variable
  Abc_Obj_t* pFanin;
  int i;
  // recursively traverse each fanin
  Abc_ObjForEachFanin(pNode, pFanin, i) { Lsv_Traverse_MSFC(pNtk, pFanin, find_msfc); }

}

// main function
void Lsv_NtkPrintMSFC(Abc_Ntk_t* pNtk)
{
  // global variable
  Abc_Obj_t* PO;
  int i;
  vector<vector<Abc_Obj_t*>> msfc_pair;
  // default each node with flag=0 && find whether has "multi-fanout"
  Abc_Obj_t* pObj;
  int node;

  Abc_NtkIncrementTravId(pNtk);
  Abc_NtkIncrementTravId(pNtk);

  Abc_NtkForEachNode(pNtk, pObj, node) 
  {
    if (Abc_ObjFanoutNum(pObj) <= 1) { Abc_NodeSetTravIdPrevious(pObj); }
  }

  // check for each PO
  Abc_NtkForEachPo(pNtk, PO, i)
  {
    // variable
    Abc_Obj_t* pFanin;
    int j;
    // recursively traverse each fanin
    Abc_ObjForEachFanin(PO, pFanin, j)
    {
      // start from PO's fanin --> first round !
      vector<Abc_Obj_t*> first_find_msfc;
      if (Abc_NodeIsTravIdPrevious(pFanin))
      {
        Lsv_Traverse_MSFC(pNtk, pFanin, first_find_msfc);
        // sort internally
        sort(first_find_msfc.begin(), first_find_msfc.end(), compareV);
        msfc_pair.push_back(first_find_msfc);
      }
      // if const1 --> add (can only exist once)
      if (Abc_ObjFaninNum(pFanin) == 0)
      {
        if ((Abc_ObjType(pFanin) == 1) && (!const_exist.count(Abc_ObjName(pFanin))))
        {
          first_find_msfc.push_back(pFanin);
          msfc_pair.push_back(first_find_msfc);
          const_exist[Abc_ObjName(pFanin)] = 1;
        }
      }
    }
  }
  // second round ! find msfc from multi-fanout node 
  int count_multi = 0;
  Abc_Obj_t* pMulti;

  Abc_NtkForEachNode(pNtk, pMulti, count_multi) 
  {
    // if multi fanout
    if ((!Abc_NodeIsTravIdPrevious(pMulti)) && (!Abc_NodeIsTravIdCurrent(pMulti)))
    {
      // mark the root as flag = 0
      Abc_NodeSetTravIdPrevious(pMulti);
      vector<Abc_Obj_t*> second_find_msfc;
      // recursively traverse each fanin
      Lsv_Traverse_MSFC(pNtk, pMulti, second_find_msfc);
      // sort internally
      sort(second_find_msfc.begin(), second_find_msfc.end(), compareV);
      msfc_pair.push_back(second_find_msfc);
    }

  }

  // sort 
  sort(msfc_pair.begin(), msfc_pair.end(), compareVV);

  // output (print)
  int count_ans = 0;
  for (int k = 0 ; k < msfc_pair.size() ; ++k)
  {
    printf("MSFC %d: ", count_ans);
    for (int l = 0 ; l < msfc_pair[k].size() ; ++l)
    {
      printf("%s", Abc_ObjName(msfc_pair[k][l]));
      if (l == msfc_pair[k].size()-1) { printf("\n"); }
      else { printf(","); }
    }
    ++count_ans;
  }

}


// Define command function : LSV_CommandPrintMSFC
int LSV_CommandPrintMSFC(Abc_Frame_t* pAbc, int argc, char** argv)
{
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF)
  {
    switch (c)
    {
      case 'h':
        goto usage;
      default:
        goto usage;
    }
  }
  if (!pNtk)
  {
    Abc_Print(-1, "Empty network.\n");
    return -1;
  }
  // main function
  Lsv_NtkPrintMSFC(pNtk);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_print_msfc [-h]\n");
  Abc_Print(-2, "\t        prints the msfc in the network\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;

}
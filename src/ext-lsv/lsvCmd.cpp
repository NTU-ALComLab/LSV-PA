#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <vector>
#include <string>
#include <iostream>
#include <sstream>
#include <algorithm>

using namespace std;

static int Lsv_CommandPrintNodes(Abc_Frame_t *pAbc, int argc, char **argv);
static int Lsv_print_unatness(Abc_Frame_t *pAbc, int argc, char **argv);
void compute(vector<int> &, string &);

void init(Abc_Frame_t *pAbc)
{
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_sopunate", Lsv_print_unatness, 0);
}

void destroy(Abc_Frame_t *pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager
{
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

void Lsv_NtkPrintNodes(Abc_Ntk_t *pNtk)
{
  Abc_Obj_t *pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i)
  {
    printf("Object Id = %d, name = %s\n", Abc_ObjId(pObj), Abc_ObjName(pObj));
    Abc_Obj_t *pFanin;
    int j;
    Abc_ObjForEachFanin(pObj, pFanin, j)
    {
      printf("  Fanin-%d: Id = %d, name = %s\n", j, Abc_ObjId(pFanin),
             Abc_ObjName(pFanin));
    }
    if (Abc_NtkHasSop(pNtk))
    {
      printf("The SOP of this node:\n%s", (char *)pObj->pData);
    }
  }
}

int Lsv_CommandPrintNodes(Abc_Frame_t *pAbc, int argc, char **argv)
{
  Abc_Ntk_t *pNtk = Abc_FrameReadNtk(pAbc);
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

int Lsv_print_unatness(Abc_Frame_t *pAbc, int argc, char **argv)
{
  //original network
  Abc_Ntk_t *pNtk = Abc_FrameReadNtk(pAbc);
  Abc_Obj_t *pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i)
  {
    char *pSop = (char *)pObj->pData;
    std::vector<string> _negUnate;
    std::vector<string> _posUnate;
    std::vector<string> _binate;

    int nVars = Abc_SopGetVarNum(pSop);
    vector<int> index;
    index.resize(nVars, -1); //-1 as absent
    Abc_Obj_t *pFanin;
    int j;
    vector<string> _names;
    vector<int> _id;
    Abc_ObjForEachFanin(pObj, pFanin, j)
    {
      string id = Abc_ObjName(pFanin);
      _names.push_back(id);
      _id.push_back(Abc_ObjId(pFanin)); //record type for sorting
    }

    if (Abc_NtkHasSop(pNtk) && nVars != 0)
    {
      string sop = (char *)pObj->pData;
      compute(index, sop);
      printf("node %s:\n", Abc_ObjName(pObj));
      while (!_id.empty())
      {
        vector<int>::iterator it;
        it = min_element(_id.begin(), _id.end());
        int i = distance(_id.begin(), it);
        if (index[i] == -1)
        {
          _posUnate.push_back(_names[i]);
          _negUnate.push_back(_names[i]);
        }
        else if (index[i] == 0)
          _negUnate.push_back(_names[i]);
        else if (index[i] == 1)
          _posUnate.push_back(_names[i]);
        else if (index[i] == 2)
          _binate.push_back(_names[i]);
        swap(_id[i], _id[_id.size() - 1]);
        _id.pop_back();
        swap(index[i], index[index.size() - 1]);
        index.pop_back();
        swap(_names[i], _names[_names.size() - 1]);
        _names.pop_back();
      }
      if (_posUnate.size() != 0)
      {
        cout << "+unate inputs: ";
        for (unsigned int i = 0; i < _posUnate.size(); i++)
        {
          cout << _posUnate[i];
          if (i != _posUnate.size() - 1)
            cout << ",";
        }
        cout << endl;
      }
      if (_negUnate.size() != 0)
      {
        cout << "-unate inputs: ";
        for (unsigned int i = 0; i < _negUnate.size(); i++)
        {
          cout << _negUnate[i];
          if (i != _negUnate.size() - 1)
            cout << ",";
        }
        cout << endl;
      }
      if (_binate.size() != 0)
      {
        cout << "binate inputs: ";
        for (unsigned int i = 0; i < _binate.size(); i++)
        {
          cout << _binate[i];
          if (i != _binate.size() - 1)
            cout << ",";
        }
        cout << endl;
      }
    }
  }
  return 1;
}
void compute(vector<int> &index, string &sop)
{
  //SOP splitting
  vector<string> tmp;
  string result;
  stringstream input(sop);
  while (input >> result)
    tmp.push_back(result);
  bool flag = false;
  for (unsigned int i = 1; i < tmp.size(); i = i + 2)
  {
    string s = tmp[i - 1];
    //-1:absent, 0:neg, 1:pos, 2:binate
    for (unsigned int j = 0; j < s.size(); j++)
    {
      if (s[j] == '1')
      {
        if (index[j] == 0 || index[j] == 2)
          index[j] = 2;
        else
          index[j] = 1;
      }
      else if (s[j] == '0')
      {
        if (index[j] == 1 || index[j] == 2)
          index[j] = 2;
        else
          index[j] = 0;
      }
    }
    //inverse result
    if (tmp[i] == "0")
    {
      flag = true;
    }
  }
  if (flag)
  {
    for (unsigned int k = 0; k < index.size(); k++)
    {
      if (index[k] == 1)
        index[k] = 0;
      else if (index[k] == 0)
        index[k] = 1;
    }
  }
}
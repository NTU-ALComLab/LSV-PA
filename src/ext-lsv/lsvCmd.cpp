#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <unordered_map>
#include <vector>
#include <set>
#include <string>

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_commandPrintmocut(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocut", Lsv_commandPrintmocut, 0);
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

void generateCombination(
  const std::vector<std::set<std::set<int>>>& FaninCutList,
  int ListIndex,
  std::vector<std::set<int>>& CutListTemp,
  std::set<std::set<int>>& result,
  int valK
) 
{
  if(ListIndex == FaninCutList.size()){
    std::set<int> CutTemp;
    for(const auto& cut : CutListTemp){
      CutTemp.insert(cut.begin(), cut.end());
      if(CutTemp.size() > valK){
        return;
      }
    }
    result.insert(CutTemp);
    return;
  }

  for(const auto& CutList : FaninCutList[ListIndex]){
    CutListTemp.push_back(CutList);
    generateCombination(FaninCutList, ListIndex+1, CutListTemp, result, valK);
    CutListTemp.pop_back();
  }
}

void Lsv_NtkPrintmocut(Abc_Ntk_t* pNtk, int valK, int valL) {
  Abc_Obj_t* pObj;
  int i;
  std::unordered_map<int,std::set<std::set<int>>> Lsv_CutList; 
  std::set<int> Lsv_CutTemp;

  // printf("start cut generation\n");

  Abc_NtkForEachObj(pNtk, pObj, i) {
    if(Abc_ObjIsPi(pObj)){
      // printf("Object Id = %d, name = %s\n", Abc_ObjId(pObj), Abc_ObjName(pObj));
      Lsv_CutTemp = {int(Abc_ObjId(pObj))};
      Lsv_CutList[Abc_ObjId(pObj)].insert(Lsv_CutTemp);
      // printf("Cut num: %zu\n", Lsv_CutList[i].size());
    }else if(Abc_ObjIsNode(pObj)){
      // printf("Object Id = %d, name = %s\n", Abc_ObjId(pObj), Abc_ObjName(pObj));
      Lsv_CutTemp = {int(Abc_ObjId(pObj))};
      Lsv_CutList[Abc_ObjId(pObj)].insert(Lsv_CutTemp);

      // iterate through all the fanin
      Abc_Obj_t* pFanin;
      std::vector<std::set<std::set<int>>> LsvCutListComb;
      int j;
      Abc_ObjForEachFanin(pObj, pFanin, j) {
        LsvCutListComb.push_back(Lsv_CutList[Abc_ObjId(pFanin)]);
      }

      //Combine (remove large cut)
      std::vector<std::set<int>> CutListTemp;
      // std::set<std::set<int>> Lsv_CutResult;
      generateCombination(LsvCutListComb, 0, CutListTemp, Lsv_CutList[Abc_ObjId(pObj)], valK);
      // LsvCutList[i].insert(Lsv_CutResult.begin(), Lsv_CutResult.end());
      // printf("Cut num: %zu\n", Lsv_CutList[Abc_ObjId(pObj)].size());
    }
  }

  // printf("start cut counting\n");

  // count every cut (inverse the map)
  std::unordered_map<std::string, std::set<int>> Lsv_MocutList;
  std::string CutIndexTemp;
  for(const auto& [a, bSet] : Lsv_CutList) {
    for(const auto& b : bSet) {
      CutIndexTemp = "";
      for(int inId : b){
        CutIndexTemp += std::to_string(inId);
        CutIndexTemp += " ";
      }
      Lsv_MocutList[CutIndexTemp].insert(a);
    }
  }

  // printf("start the output\n");

  // output the result
  for(const auto& [cut, output] : Lsv_MocutList) {
    if(output.size() >= valL) {
      printf("%s", cut.c_str());
      printf(":");
      for(int outId : output) {
        printf(" %d", outId);
      }
      printf("\n");
    }
  }
}

int Lsv_commandPrintmocut(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c;
  int valL, valK;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
      case 'h':
        goto usage;
      case '?':
        goto usage;
    }
  }

  if (argc - globalUtilOptind < 2) {
      goto usage;
  }

  valK = atoi(argv[globalUtilOptind]);
  valL = atoi(argv[globalUtilOptind + 1]);

  // printf("k=%d, l=%d\n", valK, valL);

  // main function
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  Lsv_NtkPrintmocut(pNtk, valK, valL);
  return 0;
  usage:
    Abc_Print(-2, "usage: lsv_printmocut [-h] <k> <l>\n");
    Abc_Print(-2, "\t        prints the k-feasible cut shared between at least l output nodes (3 <= k <= 6, 1 <= l <= 4)\n");
    Abc_Print(-2, "\t-h    : print the command usage\n");
    return 1;
}

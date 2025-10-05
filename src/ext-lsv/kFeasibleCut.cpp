#include <algorithm>
#include <iostream>
#include <vector>

#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
// #include<fstream>

static int Lsv_CommandPrintCuts(Abc_Frame_t* pAbc, int argc, char** argv);
// extern int Abc_ObjFaninId( Abc_Obj_t* pObj, int i);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_printcut", Lsv_CommandPrintCuts, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

bool Including(std::vector<int>& smallCut, std::vector<int>& largeCut) {
  int smallCutSize = smallCut.size(), largeCutSize = largeCut.size();
  int i = 0;
  for (int j = 0; j < largeCutSize && i < smallCutSize; ++j) {
    if (smallCut[i] == largeCut[j])
      ++i;
    else if (smallCut[i] < largeCut[j])
      break;
  }
  if (i == smallCutSize)
    return true;
  return false;
}

void MergeTwoCuts(int node, std::vector<int>& cut0, std::vector<int>& cut1, std::vector<std::vector<std::vector<int>>>& Cuts, int k) {
  std::vector<int> newCut(cut0);
  // std::copy(cut0.begin(), cut0.end(), newCut.begin());
  //  for(auto& node0:cut0)
  //    newCut.emplace_back(node0);
  int i = 0;
  int cut0Size = cut0.size();
  int newCutSize = cut0Size;
  for (auto& node1 : cut1) {
    bool ifNewNode = true;
    for (; i < cut0Size; ++i) {
      if (node1 < cut0[i])
        break;
      if (node1 == cut0[i]) {
        ifNewNode = false;
        ++i;
        break;
      }
    }
    if (ifNewNode) {
      ++newCutSize;
      if (newCutSize > k)
        return;
      newCut.emplace_back(node1);
    }
  }

  std::sort(newCut.begin(), newCut.end());
  newCutSize = newCut.size();

  for (int j = 0; j < Cuts[node].size(); ++j) {
    // if(node==473)
    // {
    //   for(auto& dd:newCut)
    //     std::cout<<dd<<' ';
    //   std::cout<<std::endl;
    //   for(auto& dd:Cuts[node][l])
    //     std::cout<<dd<<' ';
    //   std::cout<<std::endl<<"===================================="<<Cuts[node].size()<<std::endl;
    // }
    int cutSize = Cuts[node][j].size();

    if (newCutSize > cutSize) {
      if (Including(Cuts[node][j], newCut)) {
        // std::cout<<"貓子"<<std::endl;
        //  if(node==473)
        //  {
        //    std::cout<<"貓子"<<std::endl;
        //    std::cout<<newCut<<' '<<Cuts[node][l]<<std::endl;
        //  }

        return;
      }

    } else if (newCutSize < cutSize) {
      if (Including(newCut, Cuts[node][j])) {
        // std::cout<<"狗子"<<std::endl;
        //  if(node==473)
        //  {
        //    std::cout<<"狗子"<<std::endl;
        //    std::cout<<newCut<<' '<<Cuts[node][l]<<std::endl;
        //  }

        // Cuts[node].erase(Cuts[node].begin()+j);
        Cuts[node][j] = Cuts[node].back();
        Cuts[node].pop_back();
        --j;
      }

    } else if (Cuts[node][j] == newCut)
      return;
  }
  Cuts[node].emplace_back(newCut);
  return;
}

void GetCuts(Abc_Ntk_t* pNtk, int node, std::vector<std::vector<std::vector<int>>>& Cuts, int k) {
  if (!Cuts[node].empty())
    return;
  Abc_Obj_t* pObj = Abc_NtkObj(pNtk, node);

  if (Abc_ObjIsNode(pObj)) {
    Cuts[node].emplace_back(std::vector<int>{node});
    int pFanin0 = Abc_ObjFaninId(pObj, 0);
    int pFanin1 = Abc_ObjFaninId(pObj, 1);
    GetCuts(pNtk, pFanin0, Cuts, k);
    GetCuts(pNtk, pFanin1, Cuts, k);
    for (auto& cut0 : Cuts[pFanin0]) {
      for (auto& cut1 : Cuts[pFanin1])
        MergeTwoCuts(node, cut0, cut1, Cuts, k);
    }
    return;
  } else if (Abc_ObjIsPo(pObj)) {
    int pFanin0 = Abc_ObjFaninId(pObj, 0);
    GetCuts(pNtk, pFanin0, Cuts, k);
    Cuts[node] = Cuts[pFanin0];
    Cuts[node].emplace_back(std::vector<int>{node});
    return;
  } else {
    Cuts[node].emplace_back(std::vector<int>{node});
    return;
  }
  // std::cout<<"Abc_ObjFaninId(pObj, 0)="<<Abc_ObjId(Abc_ObjFanin(pObj, 0))<<std::endl;
}

void Lsv_NtkPrintCuts(Abc_Ntk_t* pNtk, int k) {
  // std::cout<<"Lsv_NtkPrintCuts"<<std::endl;
  // std::cout<<"k= "<<k<<std::endl;
  std::vector<std::vector<std::vector<int>>> Cuts(Vec_PtrSize((pNtk)->vObjs));
  // std::cout<<"Vec_PtrSize((pNtk)->vObjs)="<<Vec_PtrSize((pNtk)->vObjs)<<std::endl;
  for (int i = 0; i < Vec_PtrSize((pNtk)->vObjs); ++i) {
    GetCuts(pNtk, i, Cuts, k);
    // std::cout<<"GetCuts "<<i<<" done"<<std::endl;
  }

  // std::cout<<"after GetCuts"<<std::endl;
  //  for (auto& cuts:Cuts)
  //  {
  //    std::sort(cuts.begin(), cuts.end(), [](const std::vector<int>& cut0, const std::vector<int>& cut1)
  //    {return cut0.size() < cut1.size();});
  //  }
  for (auto& cuts : Cuts) {
    std::sort(cuts.begin(), cuts.end(), [](const std::vector<int>& cut0, const std::vector<int>& cut1) {
      if (cut0.size() != cut1.size())
        return cut0.size() < cut1.size();
      return cut0 < cut1;
    });
  }

  for (int i = 0; i < Vec_PtrSize((pNtk)->vObjs); ++i) {
    for (auto& cut : Cuts[i]) {
      std::cout << i << ": ";
      for (auto& cutNode : cut)
        std::cout << cutNode << ' ';
      std::cout << '\n';
    }
  }
  // std::ofstream outFile("./output.txt");
  // for(int i=0;i<Vec_PtrSize((pNtk)->vObjs);++i)
  // {
  //   for(auto& cut:Cuts[i])
  //   {
  //     outFile<<i<<": ";
  //     for(auto& cutNode:cut)
  //       outFile<<cutNode<<' ';
  //     outFile<<'\n';
  //   }
  // }
  // outFile.close();
}

int Lsv_CommandPrintCuts(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  // int c, k;
  // std::cout<<argv[1]<<std::endl;
  int k = argv[1][0] - '0';

  // Extra_UtilGetoptReset();
  // while((c = Extra_UtilGetopt(argc, argv, "kh")) != EOF)
  // {
  //   std::cout<<"before switch"<<std::endl;
  //   switch(c)
  //   {
  //     case 'k':
  //     std::cout<<"33333"<<std::endl;
  //       if (globalUtilOptind >= argc)
  //       {
  //           Abc_Print(-1, "Command line switch \"-k\" should be followed by a int number.\n");
  //           goto usage;
  //       }
  //       std::cout<<"(int)atof(argv[globalUtilOptind])"<<(int)atof(argv[globalUtilOptind])<<std::endl;
  //       k = (int)atof(argv[globalUtilOptind]);
  //       ++globalUtilOptind;
  //       break;
  //     case 'h':
  //       goto usage;
  //     default:
  //       std::cout<<"default"<<std::endl;
  //       goto usage;
  //   }
  //}
  // std::cout<<"default"<<std::endl;
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  Lsv_NtkPrintCuts(pNtk, k);
  return 0;
  // usage:
  //   Abc_Print(-2, "usage: lsv_printcut [-h]\n");
  //   Abc_Print(-2, "\t        prints the cuts in the network\n");
  //   Abc_Print(-2, "\t-k int : sets the maximum cut size [default = %s]\n", k);
  //   Abc_Print(-2, "\t-h    : print the command usage\n");
  //   return 1;
}

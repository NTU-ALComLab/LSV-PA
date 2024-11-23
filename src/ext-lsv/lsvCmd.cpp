#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <vector>
#include <set>
#include <iostream>
#include <ostream>
#include <algorithm>
#include <iterator>
#include <random>
#include <unordered_map>
#include <stdio.h>
#include "sat/cnf/cnf.h"
#include "sat/bsat/satSolver.h"

extern "C"{
Aig_Man_t* Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
}

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);

static int Lsv_PrintCut(Abc_Frame_t* pAbc, int argc, char** argv);

static int Lsv_SDC(Abc_Frame_t* pAbc, int argc, char** argv);

static int Lsv_ODC(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_printcut", Lsv_PrintCut, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_sdc", Lsv_SDC, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_odc", Lsv_ODC, 0);
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

std::set<int> setUnion(const std::set<int> s1, const std::set<int> s2){
  std::set<int> result = s1;
  result.insert(s2.begin(), s2.end());
  return result;
}

void dominateCheck(std::pair<std::set<int>, bool>& s1, std::pair<std::set<int>, bool>& s2){
  std::set<int> diff1to2, diff2to1;
  std::set_difference(s1.first.begin(), s1.first.end(), s2.first.begin(), s2.first.end(), std::inserter(diff1to2, diff1to2.begin()));
  std::set_difference(s2.first.begin(), s2.first.end(), s1.first.begin(), s1.first.end(), std::inserter(diff2to1, diff2to1.begin()));
  // S1 dominates S2
  if(diff1to2.size()==0 && diff2to1.size()>0){
    s2.second = false;
  }
  // S2 dominates S1
  else if(diff1to2.size()>0 && diff2to1.size()==0){
    s1.second = false;
  }
}

int Lsv_PrintCut(Abc_Frame_t* pAbc, int argc, char** argv){
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

  // PI //
  if(argc==2){
    int k = argv[1][0]-'0';
    Abc_Obj_t *pObj;
    int i;
    std::vector<std::vector<std::set<int>>> eachNodeSet;
    eachNodeSet.resize(2*(Abc_NtkPiNum(pNtk)+Abc_NtkObjNum(pNtk)+Abc_NtkPoNum(pNtk)));

    Abc_NtkForEachPi(pNtk, pObj, i){
      // PIs
      if(Abc_ObjIsPi(pObj)){
        std::vector<std::set<int>> mySet;
        std::set<int> subset = {Abc_ObjId(pObj)};
        mySet.push_back(subset);
        eachNodeSet.at(Abc_ObjId(pObj)) = mySet;
        if(1<=k){
          printf("%d: %d\n", Abc_ObjId(pObj), Abc_ObjId(pObj));
        }
      }
    }

    // AND NODE //
    Abc_NtkForEachNode(pNtk, pObj, i){
      std::vector<std::pair<std::set<int>, bool>> naiveSet;
      std::pair<std::set<int>, bool> tmpPair;
      tmpPair.first = {Abc_ObjId(pObj)};
      tmpPair.second = true;
      naiveSet.push_back(tmpPair);
      // std::cout<<"NODE"<<pObj->Id<<" has "<<Abc_ObjFaninNum(pObj)<<" fanins."<<std::endl;
      Abc_Obj_t *fanin0 = Abc_ObjFanin0(pObj); 
      Abc_Obj_t *fanin1 = Abc_ObjFanin1(pObj);
      std::vector<std::set<int>> f0Set = eachNodeSet.at(fanin0->Id);
      std::vector<std::set<int>> f1Set = eachNodeSet.at(fanin1->Id);

      // First, union two fanins' sets without checking dominance.
      for(const auto& s1: f0Set){
        for(const auto& s2: f1Set){
          std::set<int> unionS = setUnion(s1, s2);
          // Check whether the set has been in naiveSet.
          if(unionS.size()<=k){
            bool rep = false;
            for(const auto& nS: naiveSet){
              if(unionS==nS.first){
                rep = true;
                break;
              }
            }
            if(!rep){
              tmpPair.first = unionS;
              tmpPair.second = true;
              naiveSet.push_back(tmpPair);
            }
          }
        }
      }

      // Domainance checking
      for(size_t i=0; i<naiveSet.size(); ++i){
        if(naiveSet[i].second==true){
          for(size_t j=i; j<naiveSet.size(); ++j){
            if(naiveSet[j].second==true){
              dominateCheck(naiveSet[i], naiveSet[j]);
            }
          }
        }
      }

      // Result
      for(const auto& s: naiveSet){
        if(s.second==true){
          eachNodeSet.at(Abc_ObjId(pObj)).push_back(s.first);
        }
      }

      // Print
      for(const auto& s: eachNodeSet.at(Abc_ObjId(pObj))){
          printf("%d:", Abc_ObjId(pObj));
          for(const auto& mem: s){
            printf(" %d", mem);
          }
          printf("\n");
      }
    }
  }
  else{
    printf("Please give a number k.\n");
  }

  return 0;

usage:
  Abc_Print(-2, "usage: lsv_printcut [-h]\n");
  Abc_Print(-2, "\tk       prints k-feasible cuts in the network\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}

void ExportNetworkToDot(Abc_Ntk_t* pConeNtk, const char* dotFileName) {
    if (!pConeNtk) {
        printf("Cone network is NULL.\n");
        return;
    }

    FILE* fp = fopen(dotFileName, "w");
    if (!fp) {
        printf("Failed to open file: %s\n", dotFileName);
        return;
    }

    fprintf(fp, "digraph G {\n"); // 開始 DOT 格式

    Abc_Obj_t* pObj;
    int i;

    // 遍歷所有節點
    Abc_NtkForEachObj(pConeNtk, pObj, i) {
        const char* name = Abc_ObjName(pObj) ? Abc_ObjName(pObj) : "Unnamed";
        int id = Abc_ObjId(pObj);

        // 根據節點類型設置圖形標籤
        if (Abc_ObjIsPi(pObj)) {
            fprintf(fp, "  n%d [label=\"%s\" shape=ellipse];\n", id, name); // PI 節點
        } else if (Abc_ObjIsPo(pObj)) {
            fprintf(fp, "  n%d [label=\"%s\" shape=box];\n", id, name); // PO 節點
        } else if (Abc_ObjIsNode(pObj)) {
            fprintf(fp, "  n%d [label=\"AND\" shape=diamond];\n", id); // AND 節點
        }
    }

    // 遍歷節點的扇入關係
    Abc_NtkForEachObj(pConeNtk, pObj, i) {
        if (Abc_ObjIsNode(pObj) || Abc_ObjIsPo(pObj)) {
            Abc_Obj_t* pFanin;
            int j;
            Abc_ObjForEachFanin(pObj, pFanin, j) {
                fprintf(fp, "  n%d -> n%d;\n", Abc_ObjId(pFanin), Abc_ObjId(pObj));
            }
        }
    }

    fprintf(fp, "}\n"); // 結束 DOT 格式
    fclose(fp);

    printf("DOT file saved to: %s\n", dotFileName);
}

void ExportAigToDot(Aig_Man_t* pAig, const char* dotFileName) {
    if (!pAig) {
        printf("AIG is NULL.\n");
        return;
    }

    FILE* fp = fopen(dotFileName, "w");
    if (!fp) {
        printf("Failed to open file: %s\n", dotFileName);
        return;
    }

    fprintf(fp, "digraph AIG {\n");

    Aig_Obj_t* pObj;
    int i;

    // 遍歷 AIG 節點並添加到 DOT 文件
    Aig_ManForEachObj(pAig, pObj, i) {
        int id = Aig_ObjId(pObj);
        if (Aig_ObjIsCi(pObj)) {
            fprintf(fp, "  n%d [label=\"PI%d\" shape=ellipse];\n", id, id);
        } else if (Aig_ObjIsCo(pObj)) {
            fprintf(fp, "  n%d [label=\"PO%d\" shape=box];\n", id, id);
        } else if (Aig_ObjIsNode(pObj)) {
            fprintf(fp, "  n%d [label=\"AND%d\" shape=diamond];\n", id, id);
        } else if (Aig_ObjIsConst1(pObj)) {
            fprintf(fp, "  n%d [label=\"CONST1\" shape=rectangle];\n", id);
        }
    }

    // 添加邊（連接關係）
    Aig_ManForEachObj(pAig, pObj, i) {
        if (Aig_ObjIsNode(pObj) || Aig_ObjIsCo(pObj)) {
            Aig_Obj_t* pFanin0 = Aig_ObjFanin0(pObj);
            Aig_Obj_t* pFanin1 = Aig_ObjFanin1(pObj);

            if (pFanin0) {
                fprintf(fp, "  n%d -> n%d [label=\"%s\"];\n",
                        Aig_ObjId(pFanin0), Aig_ObjId(pObj),
                        Aig_ObjFaninC0(pObj) ? "inv" : "");
            }

            if (pFanin1) {
                fprintf(fp, "  n%d -> n%d [label=\"%s\"];\n",
                        Aig_ObjId(pFanin1), Aig_ObjId(pObj),
                        Aig_ObjFaninC1(pObj) ? "inv" : "");
            }
        }
    }

    fprintf(fp, "}\n");
    fclose(fp);

    printf("AIG exported to DOT file: %s\n", dotFileName);
}

int Lsv_SDC(Abc_Frame_t* pAbc, int argc, char** argv){
  if(argc<2){
    Abc_Print(-1, "Usage: lsv_sdc <node_name>\n");
    return 0;
  }

  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  Abc_Obj_t* pNode = Abc_NtkObj(pNtk, atoi(argv[1]));
  
  // Check not PI/PO
  if((!pNode)||Abc_ObjIsPi(pNode)||Abc_ObjIsPo(pNode)){
    Abc_Print(-1, "Node must be an internal node.\n");
    return 0;
  }

  Abc_Obj_t* fanin0 = Abc_ObjFanin0(pNode);
  Abc_Obj_t* fanin1 = Abc_ObjFanin1(pNode);
  int fanin0_inverter = Abc_ObjFaninC0(pNode);
  int fanin1_inverter = Abc_ObjFaninC1(pNode);
  printf("fanin0_inverter:%d, fanin1_inverter:%d\n", fanin0_inverter, fanin1_inverter);
  if(!fanin0 || !fanin1){
    printf("Missing fanins...\n");
    return 0;
  }
  // Create fanin cone
  Vec_Ptr_t* rootFanins = Vec_PtrAlloc(2);
  Vec_PtrPush(rootFanins, Abc_ObjFanin0(pNode));
  Vec_PtrPush(rootFanins, Abc_ObjFanin1(pNode));
  Abc_Ntk_t* pConeNtk = Abc_NtkCreateConeArray(pNtk, rootFanins, 1); // Include PIs
  if(!pConeNtk) {
    Abc_Print(-1, "Failed to create fanin cone array.\n");
    return 0;
  }
  // ExportNetworkToDot(pConeNtk, "Cone.dot");

  // if(1){
  //   printf("Cone Network Information:\n");
  //   printf(" - Network Name: %s\n", Abc_NtkName(pConeNtk));
  //   printf(" - Number of PIs: %d\n", Abc_NtkPiNum(pConeNtk));
  //   printf(" - Number of POs: %d\n", Abc_NtkPoNum(pConeNtk));
  //   printf(" - Number of Nodes: %d\n", Abc_NtkNodeNum(pConeNtk)); 
  //   Abc_Obj_t* pObj;
  //   int i;
  //   Abc_NtkForEachObj(pConeNtk, pObj, i){
  //       const char* name = Abc_ObjName(pObj);
  //       printf("Node %d: ID = %d, Type = %d, Name = %s\n", i, 
  //              Abc_ObjId(pObj), 
  //              Abc_ObjType(pObj), 
  //              name ? name : "Unnamed");
  //   }
  // }
  
  // Turn cone to AIG
  Aig_Man_t* pAig = Abc_NtkToDar(pConeNtk, 0, 0);
  if(!pAig) {
    Abc_Print(-1, "Failed to create AIG.\n");
    return 0;
  }

  // ExportAigToDot(pAig, "Aig.dot");

  int y0ID=0, y1ID=0;
  Aig_Obj_t* pObjjj;
  int iii;
  Aig_ManForEachCo(pAig, pObjjj, iii) {
      // printf("  Node %d: ID = %d\n", iii, Aig_ObjId(pObjjj));
      if(iii==0){
        y0ID = Aig_ObjId(pObjjj);
      }
      else{
        y1ID = Aig_ObjId(pObjjj);
      }
  }

  sat_solver* pSat = sat_solver_new();
  Cnf_Dat_t* pCnf = Cnf_Derive(pAig, 2);
  std::vector<bool> UNSAT;
  bool noSDC = true;
  UNSAT.resize(4, false);

  Cnf_DataWriteIntoSolverInt(pSat, pCnf, 1, 0); 
  lit Lit[1], Lit2[1];
  printf("[CNF info]\n");
  Cnf_DataPrint(pCnf,1);

  Lit[0] = Abc_Var2Lit(pCnf->pVarNums[y0ID], 1);
  Lit2[0] = Abc_Var2Lit(pCnf->pVarNums[y1ID], 1);
  sat_solver_addclause(pSat, Lit, Lit+1);
  sat_solver_addclause(pSat, Lit2, Lit2+1);
  lbool status00 = sat_solver_solve(pSat, nullptr, nullptr, 0,0,0,0);
  if(status00==l_False){
    UNSAT[0] = true;
    noSDC = false;
  }

  sat_solver_restart(pSat);
  Cnf_DataWriteIntoSolverInt(pSat, pCnf, 1, 0); 
  Lit[0] = Abc_Var2Lit(pCnf->pVarNums[y0ID], 1);
  Lit2[0] = Abc_Var2Lit(pCnf->pVarNums[y1ID], 0);
  sat_solver_addclause(pSat, Lit, Lit+1);
  lbool status01 = sat_solver_solve(pSat, nullptr, nullptr, 0,0,0,0);
  if(status01==l_False){
    UNSAT[1] = true;
    noSDC = false;
  }

  sat_solver_restart(pSat);
  Cnf_DataWriteIntoSolverInt(pSat, pCnf, 1, 0); 
  Lit[0] = Abc_Var2Lit(pCnf->pVarNums[y0ID], 0);
  Lit2[0] = Abc_Var2Lit(pCnf->pVarNums[y1ID], 1);
  sat_solver_addclause(pSat, Lit, Lit+1);
  sat_solver_addclause(pSat, Lit2, Lit2+1);
  lbool status10 = sat_solver_solve(pSat, nullptr, nullptr, 0,0,0,0);
  if(status10==l_False){
    UNSAT[2] = true;
    noSDC = false;
  }
  
  sat_solver_restart(pSat);
  Cnf_DataWriteIntoSolverInt(pSat, pCnf, 1, 0); 
  Lit[0] = Abc_Var2Lit(pCnf->pVarNums[y0ID], 0);
  Lit2[0] = Abc_Var2Lit(pCnf->pVarNums[y1ID], 0);
  sat_solver_addclause(pSat, Lit, Lit+1);
  sat_solver_addclause(pSat, Lit2, Lit2+1);
  lbool status11 = sat_solver_solve(pSat, nullptr, nullptr, 0,0,0,0);
  if(status11==l_False){
    UNSAT[3] = true;
    noSDC = false;
  }

  // Delete the solver
  sat_solver_delete(pSat);

  // PRINT THE RESULT
  std::cout<<"[FINAL RESULT]"<<std::endl;
  if(UNSAT[0]){
    std::cout << ((fanin0_inverter)? 1: 0) << ((fanin1_inverter)? 1: 0) << std::endl;
  }
  if(UNSAT[1]){
    std::cout << ((fanin0_inverter)? 1: 0) << ((fanin1_inverter)? 0: 1) << std::endl;
  }
  if(UNSAT[2]){
    std::cout << ((fanin0_inverter)? 0: 1) << ((fanin1_inverter)? 1: 0) << std::endl;
  }
  if(UNSAT[3]){
    std::cout << ((fanin0_inverter)? 0: 1) << ((fanin1_inverter)? 0: 1) << std::endl;
  }
  if(noSDC){
    std::cout << "no sdc" << std::endl;
  }

  return 1;
}

int Lsv_ODC(Abc_Frame_t* pAbc, int argc, char** argv){

}
#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "sat/cnf/cnf.h"
#include <vector>
#include <algorithm>
#include <unordered_map>
#include <sstream>
#include <iterator>

extern "C"{
Aig_Man_t* Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
}

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandUnateBdd(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandUnateSat(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintMoCut(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocut", Lsv_CommandPrintMoCut, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_unate_bdd", Lsv_CommandUnateBdd, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_unate_sat", Lsv_CommandUnateSat, 0);
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

static std::string CutSig(const std::vector<int>& cut) {
  std::ostringstream oss;
  for (size_t i = 0; i < cut.size(); ++i) {
    if (i) oss << ' ';
    oss << cut[i];
  }
  return oss.str();
}

static bool IsSubset(const std::vector<int>& a, const std::vector<int>& b) {
  size_t i = 0, j = 0;
  while (i < a.size() && j < b.size()) {
    if (a[i] == b[j]) { ++i; ++j; }
    else if (a[i] > b[j]) { ++j; }
    else return false;
  }
  return i == a.size();
}

static void KeepIrredundant(std::vector<std::vector<int>>& cuts) {
  std::sort(cuts.begin(), cuts.end());
  cuts.erase(std::unique(cuts.begin(), cuts.end()), cuts.end());
  std::vector<char> rem(cuts.size(), 0);
  for (size_t i = 0; i < cuts.size(); ++i) {
    for (size_t j = 0; j < cuts.size(); ++j) {
      if (i == j) continue;
      if (cuts[j].size() < cuts[i].size() && IsSubset(cuts[j], cuts[i])) { rem[i] = 1; break; }
    }
  }
  std::vector<std::vector<int>> out; out.reserve(cuts.size());
  for (size_t i = 0; i < cuts.size(); ++i) if (!rem[i]) out.push_back(cuts[i]);
  cuts.swap(out);
}

static std::vector<std::vector<int>> MergeCuts(const std::vector<std::vector<int>>& a,
                                               const std::vector<std::vector<int>>& b,
                                               int k) {
  std::vector<std::vector<int>> res;
  for (const auto& ca : a) {
    for (const auto& cb : b) {
      std::vector<int> u;
      std::merge(ca.begin(), ca.end(), cb.begin(), cb.end(), std::back_inserter(u));
      u.erase(std::unique(u.begin(), u.end()), u.end());
      if ((int)u.size() <= k) res.push_back(u);
    }
  }
  return res;
}

static void EnumerateCuts(Abc_Ntk_t* pNtk, int k, std::vector<std::vector<std::vector<int>>>& vCuts) {
  int nObjs = Abc_NtkObjNum(pNtk);
  vCuts.assign(nObjs, {});
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachPi(pNtk, pObj, i) {
    int id = Abc_ObjId(pObj);
    vCuts[id] = { { id } };
  }
  Abc_NtkForEachNode(pNtk, pObj, i) {
    int id = Abc_ObjId(pObj);
    Abc_Obj_t* pF0 = Abc_ObjFanin0(pObj);
    Abc_Obj_t* pF1 = Abc_ObjFanin1(pObj);
    int id0 = Abc_ObjId(pF0);
    int id1 = Abc_ObjId(pF1);
    const auto& c0 = vCuts[id0];
    const auto& c1 = vCuts[id1];
    std::vector<std::vector<int>> cuts;
    cuts.push_back({ id });
    auto comb = MergeCuts(c0, c1, k);
    cuts.insert(cuts.end(), comb.begin(), comb.end());
    for (auto& c : cuts) std::sort(c.begin(), c.end());
    KeepIrredundant(cuts);
    vCuts[id] = cuts;
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
  Lsv_NtkPrintNodes(pNtk);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_print_nodes [-h]\n");
  Abc_Print(-2, "\t        prints the nodes in the network\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}

static int Lsv_CommandPrintMoCut(Abc_Frame_t* pAbc, int argc, char** argv) {
  int k = atoi(argv[1]);
  int l = atoi(argv[2]);
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  std::vector<std::vector<std::vector<int>>> vCuts;
  EnumerateCuts(pNtk, k, vCuts);
  std::unordered_map<std::string, std::vector<int>> cut2outs;
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachPi(pNtk, pObj, i) {
    int id = Abc_ObjId(pObj);
    for (const auto& cut : vCuts[id]) {
      if ((int)cut.size() > k) continue;
      auto sig = CutSig(cut);
      cut2outs[sig].push_back(id);
    }
  }
  Abc_NtkForEachNode(pNtk, pObj, i) {
    int id = Abc_ObjId(pObj);
    for (const auto& cut : vCuts[id]) {
      if ((int)cut.size() > k) continue;
      auto sig = CutSig(cut);
      cut2outs[sig].push_back(id);
    }
  }
  for (auto& kv : cut2outs) {
    auto& outs = kv.second;
    std::sort(outs.begin(), outs.end());
    outs.erase(std::unique(outs.begin(), outs.end()), outs.end());
    if ((int)outs.size() < l) continue;
    printf("%s :", kv.first.c_str());
    for (size_t j = 0; j < outs.size(); ++j) {
      printf(" %d", outs[j]);
    }
    printf("\n");
  }
  return 0;
}

static int Lsv_CommandUnateBdd(Abc_Frame_t* pAbc, int argc, char** argv) {
  int k = atoi(argv[1]);
  int i = atoi(argv[2]);
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  Abc_Obj_t* pPo = Abc_NtkPo(pNtk, k);
  Abc_Obj_t* pNode = Abc_ObjFanin0(pPo);
  Abc_Obj_t* pPi = Abc_NtkPi(pNtk, i);

  int varIndex = -1;
  Abc_Obj_t* pFanin;
  int j;
  Abc_ObjForEachFanin(pNode, pFanin, j) {
    if (pFanin == pPi) {
      varIndex = j;
      break;
    }
  }
  
  if (varIndex == -1) {
    printf("independent\n");
    return 0;
  }
  
  DdManager * dd = (DdManager *)pNtk->pManFunc;
  DdNode * f = (DdNode *)pNode->pData;
  DdNode * var = Cudd_bddIthVar(dd, varIndex);
  
  DdNode * f0 = Cudd_Cofactor(dd, f, Cudd_Not(var));
  Cudd_Ref(f0);
  DdNode * f1 = Cudd_Cofactor(dd, f, var);
  Cudd_Ref(f1);
  
  int isPos = Cudd_bddLeq(dd, f0, f1);
  int isNeg = Cudd_bddLeq(dd, f1, f0);
  
  if (isPos && isNeg) {
    printf("independent\n");
  } else if (isPos) {
    printf("positive unate\n");
  } else if (isNeg) {
    printf("negative unate\n");
  } else {
    DdNode * diff1 = Cudd_bddAnd(dd, Cudd_Not(f0), f1);
    Cudd_Ref(diff1);
    char * cube1 = new char[Cudd_ReadSize(dd)];
    Cudd_bddPickOneCube(dd, diff1, cube1);
    
    DdNode * diff2 = Cudd_bddAnd(dd, f0, Cudd_Not(f1));
    Cudd_Ref(diff2);
    char * cube2 = new char[Cudd_ReadSize(dd)];
    Cudd_bddPickOneCube(dd, diff2, cube2);
    
    printf("binate\n");
    
    std::vector<int> piToFanin(Abc_NtkPiNum(pNtk), -1);
    Abc_ObjForEachFanin(pNode, pFanin, j) {
      Abc_Obj_t* pPiCheck;
      int piIdx;
      Abc_NtkForEachPi(pNtk, pPiCheck, piIdx) {
        if (pPiCheck == pFanin) {
          piToFanin[piIdx] = j;
          break;
        }
      }
    }
    
    for (int p = 0; p < Abc_NtkPiNum(pNtk); ++p) {
        if (p == i) {
            printf("-");
            continue;
        }
        int fi = piToFanin[p];
        if (fi == -1) {
            printf("0");
        } else {
            int val = cube1[fi];
            if (val == 2) printf("0");
            else printf("%d", val);
        }
    }
    printf("\n");
    
    for (int p = 0; p < Abc_NtkPiNum(pNtk); ++p) {
        if (p == i) {
            printf("-");
            continue;
        }
        int fi = piToFanin[p];
        if (fi == -1) {
            printf("0");
        } else {
            int val = cube2[fi];
            if (val == 2) printf("0");
            else printf("%d", val);
        }
    }
    printf("\n");
    
    Cudd_RecursiveDeref(dd, diff1);
    Cudd_RecursiveDeref(dd, diff2);
    delete[] cube1;
    delete[] cube2;
  }
  
  Cudd_RecursiveDeref(dd, f0);
  Cudd_RecursiveDeref(dd, f1);
  return 0;
}

static int Lsv_CommandUnateSat(Abc_Frame_t* pAbc, int argc, char** argv) {
  int k = atoi(argv[1]);
  int i = atoi(argv[2]);
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  
  Abc_Obj_t* pPo = Abc_NtkPo(pNtk, k);
  
  Abc_Ntk_t* pCone = Abc_NtkCreateCone(pNtk, Abc_ObjFanin0(pPo), Abc_ObjName(pPo), 1);
  int origPOCompl = Abc_ObjFaninC0(pPo);

  Aig_Man_t* pMan = Abc_NtkToDar(pCone, 0, 0);
  sat_solver* pSat = sat_solver_new();
  Cnf_Dat_t* pCnf = Cnf_Derive(pMan, 1);
  
  
  Cnf_DataWriteIntoSolverInt(pSat, pCnf, 1, 0);
  
  int nVarsOrig = pCnf->nVars;
  Cnf_DataLift(pCnf, nVarsOrig);
  Cnf_DataWriteIntoSolverInt(pSat, pCnf, 1, 0);
  

  
  int nPis = Abc_NtkPiNum(pNtk);
  std::vector<int> Lits;
  Aig_Obj_t* pObjAig;
  int j;

  Aig_ManForEachCi(pMan, pObjAig, j) {
      int varB = pCnf->pVarNums[pObjAig->Id];           
      int varA = varB - nVarsOrig;                       
      if (j == i) {
          sat_solver_add_const(pSat, varA, 1);  
          sat_solver_add_const(pSat, varB, 0); 
      } else {
          Lits.clear();
          Lits.push_back(toLitCond(varA, 1));  
          Lits.push_back(toLitCond(varB, 0)); 
          sat_solver_addclause(pSat, Lits.data(), Lits.data() + Lits.size());
          Lits.clear();
          Lits.push_back(toLitCond(varB, 1));  
          Lits.push_back(toLitCond(varA, 0));  
          sat_solver_addclause(pSat, Lits.data(), Lits.data() + Lits.size());
      }
  }
  
  Aig_Obj_t* pObjPo = Aig_ManCo(pMan, 0);
  Aig_Obj_t* pObjPoDriver = Aig_ObjFanin0(pObjPo);
  int conePoCompl = Aig_ObjFaninC0(pObjPo);
  
  int outVarB = pCnf->pVarNums[pObjPoDriver->Id];     
  int outVarA = outVarB - nVarsOrig;                    
  
  int totalCompl = conePoCompl ^ origPOCompl;
  
  
  lit assumptions[2];
  int drvA_forPos = 1 ^ totalCompl;  
  int drvB_forPos = 0 ^ totalCompl;  
  
  assumptions[0] = toLitCond(outVarA, 1 - drvA_forPos);  
  assumptions[1] = toLitCond(outVarB, 1 - drvB_forPos);  
  
  int statusPos = sat_solver_solve(pSat, assumptions, assumptions + 2, 0, 0, 0, 0);
  bool isPosUnate = (statusPos == l_False);
  
  int drvA_forNeg = 0 ^ totalCompl;  
  int drvB_forNeg = 1 ^ totalCompl;  
  
  assumptions[0] = toLitCond(outVarA, 1 - drvA_forNeg); 
  assumptions[1] = toLitCond(outVarB, 1 - drvB_forNeg);  
  int statusNeg = sat_solver_solve(pSat, assumptions, assumptions + 2, 0, 0, 0, 0);
  bool isNegUnate = (statusNeg == l_False);
  
  if (isPosUnate && isNegUnate) {
      printf("independent\n");
  } else if (isPosUnate) {
      printf("positive unate\n");
  } else if (isNegUnate) {
      printf("negative unate\n");
  } else {
      printf("binate\n");

      assumptions[0] = toLitCond(outVarA, 1 - drvA_forPos);
      assumptions[1] = toLitCond(outVarB, 1 - drvB_forPos);
      sat_solver_solve(pSat, assumptions, assumptions + 2, 0, 0, 0, 0);
      
      for (int p = 0; p < nPis; ++p) {
          if (p == i) {
              printf("-");
              continue;
          }
          Aig_Obj_t* pObjC = Aig_ManCi(pMan, p);
          int varB = pCnf->pVarNums[pObjC->Id];
          int varA = varB - nVarsOrig;
          int val = sat_solver_var_value(pSat, varA);
          printf("%d", val);
      }
      printf("\n");

      assumptions[0] = toLitCond(outVarA, 1 - drvA_forNeg);
      assumptions[1] = toLitCond(outVarB, 1 - drvB_forNeg);
      sat_solver_solve(pSat, assumptions, assumptions + 2, 0, 0, 0, 0);
      
      for (int p = 0; p < nPis; ++p) {
          if (p == i) {
              printf("-");
              continue;
          }
          Aig_Obj_t* pObjC = Aig_ManCi(pMan, p);
          int varB = pCnf->pVarNums[pObjC->Id];
          int varA = varB - nVarsOrig;
          int val = sat_solver_var_value(pSat, varA);
          printf("%d", val);
      }
      printf("\n");
  }
  

  Cnf_DataFree(pCnf);
  sat_solver_delete(pSat);
  Aig_ManStop(pMan);
  Abc_NtkDelete(pCone);
  return 0;
}
/**
 * src/ext-lsv/lsvCmdPa2.cpp
 * LSV PA2 — Unateness Checking
 *
 * Commands:
 *   lsv_unate_bdd <k> <i>   // requires: collapse
 *   lsv_unate_sat <k> <i>   // works on cone(root = PO's fanin) + strash internally
 */

extern "C" {
#include "base/abc/abc.h"
#include "base/main/mainInt.h"
#include "sat/cnf/cnf.h"
}

#include <vector>
#include <string>
#include <unordered_map>
#include <algorithm>

// ===========================================================
// Small helpers
// ===========================================================
static inline int Var2Lit(int v, int s) { return (v << 1) ^ (s & 1); }
static void Sat_AddEquiv(sat_solver* pSat, int vA, int vB) {
    int c1[2] = { Var2Lit(vA,1), Var2Lit(vB,0) }; // (!a + b)
    int c2[2] = { Var2Lit(vA,0), Var2Lit(vB,1) }; // ( a + !b)
    sat_solver_addclause(pSat, c1, c1+2);
    sat_solver_addclause(pSat, c2, c2+2);
}

// ===========================================================
// BDD version (expects: collapse has been run)
// ===========================================================
static inline DdManager* ReadDdMan(Abc_Ntk_t* pNtk) {
    return (DdManager*)pNtk->pManFunc;
}
static inline Abc_Obj_t* NtkPo(Abc_Ntk_t* pNtk, int k){ return Abc_NtkPo(pNtk, k); }
static inline DdNode*    NodeFunc(Abc_Obj_t* pObj)     { return (DdNode*)pObj->pData; }

// Convert CUDD pick-one cube (char array '0','1','2') to a pattern in original PI order.
// Assume CUDD var order is PI order after collapse.
static bool BddPickOneCube(DdManager* dd, DdNode* f, int nPis, std::string& out, int xiIdx, char fillX) {
    int nVars = Cudd_ReadSize(dd);
    std::vector<char> a(nVars);
    if (!Cudd_bddPickOneCube(dd, f, a.data())) return false;

    out.resize(nPis);
    for (int idx = 0; idx < nPis; ++idx) {
        if (idx == xiIdx) { out[idx] = '-'; continue; }
        char c = a[idx];
        if (c != '0' && c != '1') c = fillX;
        out[idx] = c;
    }
    return true;
}

static int Lsv_UnateBdd(Abc_Frame_t* pAbc, int k, int i) {
    Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
    if (!pNtk) { Abc_Print(-1,"Error: no network.\n"); return 1; }

    int nPI = Abc_NtkPiNum(pNtk);
    int nPO = Abc_NtkPoNum(pNtk);
    if (k < 0 || k >= nPO || i < 0 || i >= nPI) {
        Abc_Print(-1,"Error: index out of range.\n");
        return 1;
    }

    // Must have global BDDs built by "collapse"
    DdManager* dd = ReadDdMan(pNtk);
    if (!dd) {
        Abc_Print(-1,"Error: run \"collapse\" first (no global BDD manager).\n");
        return 1;
    }

    Abc_Obj_t* pPo    = NtkPo(pNtk, k);
    Abc_Obj_t* pFanin = Abc_ObjFanin0(pPo);
    if (!pFanin) { Abc_Print(-1,"Error: PO has no fanin.\n"); return 1; }

    DdNode* f = NodeFunc(pFanin);
    if (!f) { Abc_Print(-1,"Error: PO fanin has no BDD. Did collapse succeed?\n"); return 1; }
    if (Abc_ObjFaninC0(pPo)) f = Cudd_Not(f);
    Cudd_Ref(f);

    // PI variable
    DdNode* xi = Cudd_bddIthVar(dd, i); Cudd_Ref(xi);

    // cofactors
    DdNode* f0 = Cudd_Cofactor(dd, f, Cudd_Not(xi)); Cudd_Ref(f0);
    DdNode* f1 = Cudd_Cofactor(dd, f, xi);           Cudd_Ref(f1);

    // independent if f0 XOR f1 == 0
    DdNode* diff = Cudd_bddXor(dd, f0, f1); Cudd_Ref(diff);
    if (diff == Cudd_ReadLogicZero(dd)) {
        Abc_Print(1,"independent\n");
        Cudd_RecursiveDeref(dd, diff);
        Cudd_RecursiveDeref(dd, f0);
        Cudd_RecursiveDeref(dd, f1);
        Cudd_RecursiveDeref(dd, xi);
        Cudd_RecursiveDeref(dd, f);
        return 0;
    }

    // violation sets
    DdNode* bad_pos = Cudd_bddAnd(dd, f0, Cudd_Not(f1)); Cudd_Ref(bad_pos); // violates positive
    DdNode* bad_neg = Cudd_bddAnd(dd, f1, Cudd_Not(f0)); Cudd_Ref(bad_neg); // violates negative

    bool has_pos = (bad_pos != Cudd_ReadLogicZero(dd));
    bool has_neg = (bad_neg != Cudd_ReadLogicZero(dd));

    if (!has_pos &&  has_neg)      Abc_Print(1,"positive unate\n");
    else if ( has_pos && !has_neg) Abc_Print(1,"negative unate\n");
    else if (!has_pos && !has_neg) Abc_Print(1,"independent\n");
    else {
        // binate: print two witnesses
        Abc_Print(1,"binate\n");
        std::string w1, w2;
        // f1 & !f0  -> xi
        if (!BddPickOneCube(dd, bad_neg, nPI, w1, i, '0')) w1.assign(nPI,'0'), w1[i]='-';
        // f0 & !f1  -> !xi
        if (!BddPickOneCube(dd, bad_pos, nPI, w2, i, '1')) w2.assign(nPI,'0'), w2[i]='-';
        Abc_Print(1, "%s\n", w1.c_str());
        Abc_Print(1, "%s\n", w2.c_str());
    }

    // cleanup
    Cudd_RecursiveDeref(dd, bad_pos);
    Cudd_RecursiveDeref(dd, bad_neg);
    Cudd_RecursiveDeref(dd, diff);
    Cudd_RecursiveDeref(dd, f0);
    Cudd_RecursiveDeref(dd, f1);
    Cudd_RecursiveDeref(dd, xi);
    Cudd_RecursiveDeref(dd, f);
    return 0;
}

extern "C" int Lsv_CommandUnateBdd(Abc_Frame_t* pAbc, int argc, char** argv) {
    if (argc != 3) { Abc_Print(-2,"usage: lsv_unate_bdd <k> <i>\n"); return 1; }
    return Lsv_UnateBdd(pAbc, atoi(argv[1]), atoi(argv[2]));
}

// ===========================================================
// SAT version (cone(root = PO's fanin) + strash, so polarity matches BDD)
// ===========================================================
extern "C" { Aig_Man_t* Abc_NtkToDar(Abc_Ntk_t*, int, int); }

// Build cone rooted at the PO's fanin (CO itself is not a legal cone root)
static Abc_Ntk_t* MakeConeOfPoFanin(Abc_Ntk_t* pNtk, int k) {
    Abc_Obj_t* pPo   = Abc_NtkPo(pNtk, k);
    Abc_Obj_t* pRoot = Abc_ObjFanin0(pPo);
    return Abc_NtkCreateCone(pNtk, pRoot, Abc_ObjName(pPo), 1); // single-PO cone
}

// Map original PI name to PI index in the cone
static int FindPiIndexByName(Abc_Ntk_t* pCone, const char* nm) {
    Abc_Obj_t* o; int i=0; Abc_NtkForEachPi(pCone,o,i) if (!strcmp(Abc_ObjName(o),nm)) return i; return -1;
}

// Build witness in original PI order from SAT model of copy A
static std::string BuildWitnessByName(
    Abc_Ntk_t* pNtkOrig, Abc_Ntk_t* pCone, Aig_Man_t* pAigCone, Cnf_Dat_t* pCnfA, sat_solver* pSat, int xiOrigIdx
){
    int nPisOrig = Abc_NtkPiNum(pNtkOrig);
    std::string s(nPisOrig, '0');

    std::unordered_map<std::string,int> name2orig;
    Abc_Obj_t* p; int i=0; Abc_NtkForEachPi(pNtkOrig, p, i) name2orig[Abc_ObjName(p)] = i;

    // gather CIs of the cone AIG in order
    std::vector<Aig_Obj_t*> vCi; Aig_Obj_t* a; int it=0; Aig_ManForEachCi(pAigCone, a, it) vCi.push_back(a);

    Abc_Obj_t* pc; int ic=0; Abc_NtkForEachPi(pCone, pc, ic) {
        auto f = name2orig.find(Abc_ObjName(pc));
        if (f == name2orig.end()) continue;
        int orig = f->second;
        if (orig == xiOrigIdx) continue;
        int varA = pCnfA->pVarNums[Aig_ObjId(vCi[ic])];
        int val  = (varA >= 0) ? sat_solver_var_value(pSat, varA) : 0;
        s[orig] = val ? '1' : '0';
    }
    if (0 <= xiOrigIdx && xiOrigIdx < nPisOrig) s[xiOrigIdx] = '-';
    return s;
}

static int Lsv_UnateSat(Abc_Frame_t* pAbc, int kOrig, int iOrig) {
    Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
    if (!pNtk) { Abc_Print(-1,"Error: no network.\n"); return 1; }

    int nPis = Abc_NtkPiNum(pNtk), nPos = Abc_NtkPoNum(pNtk);
    if (kOrig < 0 || kOrig >= nPos || iOrig < 0 || iOrig >= nPis) {
        Abc_Print(-1,"Error: index out of range.\n"); return 1;
    }

    // --- Build cone of PO's fanin to match BDD semantics ---
    Abc_Ntk_t* pCone = MakeConeOfPoFanin(pNtk, kOrig);
    if (!pCone) { Abc_Print(-1,"Error: cannot create cone.\n"); return 1; }

    const char* namePI = Abc_ObjName(Abc_NtkPi(pNtk, iOrig));
    int iCone = FindPiIndexByName(pCone, namePI);
    if (iCone < 0) {
        // xi not present in cone => independent
        Abc_Print(1,"independent\n");
        Abc_NtkDelete(pCone);
        return 0;
    }

    // strash the cone (1 PO)
    Abc_Ntk_t* pStr = Abc_NtkStrash(pCone, 0, 1, 0);
    Abc_NtkDelete(pCone);
    if (!pStr) { Abc_Print(-1,"Error: strash(cone) failed.\n"); return 1; }

    // to AIG + CNF (single CO)
    Aig_Man_t* pAig  = Abc_NtkToDar(pStr, 0, 0);
    Cnf_Dat_t* pCnfA = Cnf_Derive(pAig, 1);
    Cnf_Dat_t* pCnfB = Cnf_Derive(pAig, 1);
    int nVarsA = pCnfA->nVars; Cnf_DataLift(pCnfB, nVarsA);

    // SAT
    sat_solver* pSat = sat_solver_new();
    sat_solver_setnvars(pSat, pCnfA->nVars + pCnfB->nVars);
    Cnf_DataWriteIntoSolverInt(pSat, pCnfA, 1, 0);
    Cnf_DataWriteIntoSolverInt(pSat, pCnfB, 1, 0);

    // gather cone CI/COs
    std::vector<Aig_Obj_t*> vCi, vCo; Aig_Obj_t* o; int it=0;
    Aig_ManForEachCi(pAig, o, it) vCi.push_back(o);
    Aig_ManForEachCo(pAig, o, it) vCo.push_back(o); // size==1

    // equate all inputs except xi
    for (int t = 0; t < (int)vCi.size(); ++t) {
        if (t == iCone) continue;
        int vA = pCnfA->pVarNums[Aig_ObjId(vCi[t])];
        int vB = pCnfB->pVarNums[Aig_ObjId(vCi[t])];
        if (vA >= 0 && vB >= 0) Sat_AddEquiv(pSat, vA, vB);
    }

    // output literal helper (via fanin; cone has a single CO)
    auto out_lit = [&](Cnf_Dat_t* pCnf, Aig_Obj_t* pCo, int want1)->int {
        Aig_Obj_t* F = Aig_ObjFanin0(pCo);
        int var  = pCnf->pVarNums[Aig_ObjId(F)];
        int sign = (want1 ? 0 : 1) ^ (Aig_ObjFaninC0(pCo) ? 1 : 0);
        return Var2Lit(var, sign);
    };

    // Solve with assumptions: xiA=0, xiB=1; (yA,yB) = (1,0) is bad_pos; (0,1) is bad_neg
    auto solve_with = [&](int yA1, int yB1)->int {
        std::vector<int> as;
        int vXiA = pCnfA->pVarNums[Aig_ObjId(vCi[iCone])];
        int vXiB = pCnfB->pVarNums[Aig_ObjId(vCi[iCone])];
        if (vXiA >= 0 && vXiB >= 0) { as.push_back(Var2Lit(vXiA,1)); as.push_back(Var2Lit(vXiB,0)); }
        as.push_back(out_lit(pCnfA, vCo[0], yA1));
        as.push_back(out_lit(pCnfB, vCo[0], yB1));
        return sat_solver_solve(pSat, &as[0], &as[0]+(int)as.size(), 0,0,0,0);
    };

    int bad_pos = solve_with(1,0); // exists (yA=1,yB=0)
    int bad_neg = solve_with(0,1); // exists (yA=0,yB=1)

    if (bad_pos == l_False && bad_neg == l_False)      Abc_Print(1,"independent\n");
    else if (bad_pos == l_False)                       Abc_Print(1,"positive unate\n");
    else if (bad_neg == l_False)                       Abc_Print(1,"negative unate\n");
    else {
        Abc_Print(1,"binate\n");
        (void)solve_with(0,1);
        std::string w1 = BuildWitnessByName(pNtk, pStr, pAig, pCnfA, pSat, iOrig);
        Abc_Print(1, "%s\n", w1.c_str());
        (void)solve_with(1,0);
        std::string w2 = BuildWitnessByName(pNtk, pStr, pAig, pCnfA, pSat, iOrig);
        Abc_Print(1, "%s\n", w2.c_str());
    }

    // cleanup
    sat_solver_delete(pSat);
    Cnf_DataFree(pCnfA);
    Cnf_DataFree(pCnfB);
    Aig_ManStop(pAig);
    Abc_NtkDelete(pStr);
    return 0;
}

extern "C" int Lsv_CommandUnateSat(Abc_Frame_t* pAbc, int argc, char** argv) {
    if (argc != 3) { Abc_Print(-2,"usage: lsv_unate_sat <k> <i>\n"); return 1; }
    return Lsv_UnateSat(pAbc, atoi(argv[1]), atoi(argv[2]));
}

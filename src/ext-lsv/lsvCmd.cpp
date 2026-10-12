#include <stdio.h>
#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

#include <vector>
#include <map>
#include <set>
#include <algorithm>

#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
static int Lsv_CommandLsv(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
    Cmd_CommandAdd(pAbc, "LSV", "lsv", Lsv_CommandLsv, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;
typedef std::vector<int> Cut;
typedef std::vector<Cut> CutList;

static Cut MergeCuts(const Cut& a, const Cut& b)
{
    std::set<int> temp;

    for (int x : a)
        temp.insert(x);

    for (int x : b)
        temp.insert(x);

    return Cut(temp.begin(), temp.end());
}

static void AddCutUnique(CutList& cuts, Cut cut)
{
    std::sort(cut.begin(), cut.end());

    for (const Cut& oldCut : cuts) {
        if (oldCut == cut)
            return;
    }

    cuts.push_back(cut);
}
static CutList EnumerateCuts(
    Abc_Obj_t* pObj,
    int k,
    std::map<int, CutList>& memo)
{
    int id = Abc_ObjId(pObj);

    if (memo.count(id))
        return memo[id];

    CutList result;

    result.push_back(Cut{ id });

    
    if (Abc_ObjIsPi(pObj)) {
        memo[id] = result;
        return result;
    }

    Abc_Obj_t* pFanin0 = Abc_ObjFanin0(pObj);
    Abc_Obj_t* pFanin1 = Abc_ObjFanin1(pObj);

    CutList cuts0 = EnumerateCuts(pFanin0, k, memo);
    CutList cuts1 = EnumerateCuts(pFanin1, k, memo);

    for (const Cut& c0 : cuts0) {
        for (const Cut& c1 : cuts1) {

            Cut merged = MergeCuts(c0, c1);

            if ((int)merged.size() <= k)
                AddCutUnique(result, merged);
        }
    }

    memo[id] = result;
    return result;
}
static int EvaluateCut(
    Abc_Obj_t* pObj,
    const Cut& cut,
    uint64_t assignment)
{
    int id = Abc_ObjId(pObj);

    for (int i = 0; i < (int)cut.size(); ++i) {
        if (cut[i] == id) {
            int bitPos = (int)cut.size() - 1 - i;
            return (assignment >> bitPos) & 1ULL;
        }
    }

    if (Abc_ObjIsPi(pObj)) {
        return 0;
    }

    int value0 = EvaluateCut(
        Abc_ObjFanin0(pObj),
        cut,
        assignment);

    int value1 = EvaluateCut(
        Abc_ObjFanin1(pObj),
        cut,
        assignment);

    if (Abc_ObjFaninC0(pObj))
        value0 = !value0;

    if (Abc_ObjFaninC1(pObj))
        value1 = !value1;

    return value0 & value1;
}
static uint64_t ComputeTruthTable(
    Abc_Obj_t* pRoot,
    const Cut& cut)
{
    uint64_t truthTable = 0;

    uint64_t numAssignments =
        1ULL << cut.size();

    for (uint64_t assignment = 0;
         assignment < numAssignments;
         ++assignment)
    {
        int output =
            EvaluateCut(pRoot, cut, assignment);

        if (output) {
            truthTable |=
                (1ULL << assignment);
        }
    }

    return truthTable;
}
static DdNode* BuildBddFromTruthTable(
    DdManager* dd,
    uint64_t truthTable,
    int numVars)
{
    DdNode* function = Cudd_ReadLogicZero(dd);
    Cudd_Ref(function);

    uint64_t numAssignments = 1ULL << numVars;

    for (uint64_t assignment = 0;
         assignment < numAssignments;
         ++assignment)
    {
        if (((truthTable >> assignment) & 1ULL) == 0)
            continue;

        DdNode* cube = Cudd_ReadOne(dd);
        Cudd_Ref(cube);

        for (int i = 0; i < numVars; ++i)
        {
            int bitPos = numVars - 1 - i;
            int value = (assignment >> bitPos) & 1ULL;

            DdNode* var = Cudd_bddIthVar(dd, i);
            DdNode* literal = value ? var : Cudd_Not(var);

            DdNode* temp = Cudd_bddAnd(dd, cube, literal);
            Cudd_Ref(temp);

            Cudd_RecursiveDeref(dd, cube);
            cube = temp;
        }

        DdNode* temp =
            Cudd_bddOr(dd, function, cube);

        Cudd_Ref(temp);

        Cudd_RecursiveDeref(dd, function);
        Cudd_RecursiveDeref(dd, cube);

        function = temp;
    }

    return function;
}
static void Lsv_PrintBddSizes(
    Abc_Ntk_t* pNtk,
    int k)
{
    std::map<int, CutList> memo;

    Abc_Obj_t* pObj;
    int i;

    Abc_NtkForEachNode(pNtk, pObj, i)
    {
        CutList cuts =
            EnumerateCuts(pObj, k, memo);

        for (Cut cut : cuts)
        {
            std::sort(
                cut.begin(),
                cut.end());

            uint64_t truthTable =
                ComputeTruthTable(
                    pObj,
                    cut);

            int numVars =
                (int)cut.size();

            DdManager* dd =
                Cudd_Init(
                    numVars,
                    0,
                    CUDD_UNIQUE_SLOTS,
                    CUDD_CACHE_SLOTS,
                    0);

            DdNode* function =
                BuildBddFromTruthTable(
                    dd,
                    truthTable,
                    numVars);

            int bddSize =
                Cudd_DagSize(function);

            printf(
                "%d:",
                Abc_ObjId(pObj));

            for (int id : cut)
                printf(" %d", id);

            printf(
                ": %d\n",
                bddSize);

            Cudd_RecursiveDeref(
                dd,
                function);

            Cudd_Quit(dd);
        }
    }
}
static void Lsv_PrintCuts(Abc_Ntk_t* pNtk, int k)
{
    std::map<int, CutList> memo;

    Abc_Obj_t* pObj;
    int i;

    Abc_NtkForEachNode(pNtk, pObj, i) {

        CutList cuts =
            EnumerateCuts(pObj, k, memo);

        for (Cut cut : cuts) {

            std::sort(
                cut.begin(),
                cut.end());

            uint64_t truthTable =
                ComputeTruthTable(
                    pObj,
                    cut);

            printf(
                "%d:",
                Abc_ObjId(pObj));

            for (int id : cut) {
                printf(" %d", id);
            }

            printf(
                ": %llX\n",
                (unsigned long long)
                truthTable);
        }
    }
}

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

int Lsv_CommandLsv(Abc_Frame_t* pAbc, int argc, char** argv)
{
    Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);

    char* endptr = nullptr;
    long k = 0;

    if (!pNtk) {
        Abc_Print(-1, "Empty network.\n");
        return 1;
    }

    if (argc != 4) {
        goto usage;
    }

    if (strcmp(argv[1], "cut") != 0) {
        goto usage;
    }

    k = strtol(argv[3], &endptr, 10);

    if (*endptr != '\0' || k < 2 || k > 6) {
        Abc_Print(-1, "k must be an integer between 2 and 6.\n");
        return 1;
    }

    if (strcmp(argv[2], "tt") == 0) {
    Lsv_PrintCuts(pNtk, (int)k);
    return 0;
}

    if (strcmp(argv[2], "bddsize") == 0) {
    Lsv_PrintBddSizes(pNtk, (int)k);
    return 0;
}

usage:
    Abc_Print(-2, "usage: lsv cut <tt|bddsize> <k>\n");
    Abc_Print(-2, "       k must be between 2 and 6\n");
    return 1;
}

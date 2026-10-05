#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "bdd/cudd/cudd.h"
#include <cstdlib>
#include <set>
#include <vector>

static int Lsv_CommandPrintNodes(Abc_Frame_t *pAbc, int argc, char **argv);
static int Lsv_CommandCutTT(Abc_Frame_t *pAbc, int argc, char **argv);
static int Lsv_CommandCutBDD(Abc_Frame_t *pAbc, int argc, char **argv);

struct Lsv_CutTT_t
{
    std::set<int> cut_i;
    uint64_t TT;
};

struct Lsv_CutBDD_t
{
    std::set<int> cut_i;
    DdNode *pBDD;
};

void init(Abc_Frame_t *pAbc)
{
    Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
    Cmd_CommandAdd(pAbc, "LSV", "lsv_cut_tt", Lsv_CommandCutTT, 0);
    Cmd_CommandAdd(pAbc, "LSV", "lsv_cut_bddsize", Lsv_CommandCutBDD, 0);
}

void destroy(Abc_Frame_t *pAbc)
{
}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager
{
    PackageRegistrationManager()
    {
        Abc_FrameAddInitializer(&frame_initializer);
    }
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
            printf("  Fanin-%d: Id = %d, name = %s\n", j, Abc_ObjId(pFanin), Abc_ObjName(pFanin));
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

void Lsv_NtkCutTT(Abc_Ntk_t *pNtk, int k)
{
    Abc_Obj_t *pObj;
    std::vector<std::vector<Lsv_CutTT_t>> data(Abc_NtkObjNum(pNtk));
    int i;

    Abc_NtkForEachObj(pNtk, pObj, i)
    {
        // all nodes have a cut of itself
        data[i].push_back(Lsv_CutTT_t{{i}, 2});

        // filter out non-nodes/POs
        if (!(Abc_ObjIsNode(pObj) || Abc_ObjIsPo(pObj)) || Abc_ObjFanoutNum(pObj) == 0)
            continue;

        // fanin nodes
        int fId0 = Abc_ObjFaninId0(pObj);
        int fId1 = Abc_ObjFaninId1(pObj);
        int fComp0 = Abc_ObjFaninC0(pObj);
        int fComp1 = Abc_ObjFaninC1(pObj);

        for (const Lsv_CutTT_t &data0 : data[fId0])
        {
            for (const Lsv_CutTT_t &data1 : data[fId1])
            {
                // union of cut_i
                std::set<int> newCut = data0.cut_i;
                newCut.insert(data1.cut_i.begin(), data1.cut_i.end());
                int cutCount = newCut.size();

                // cutoff greater feasible cuts
                if (cutCount > k)
                    continue;

                // get mappings for TT
                int j = cutCount;
                std::set<int> mapIndex0;
                std::set<int> mapIndex1;
                for (int cut : newCut)
                {
                    --j;
                    if (data0.cut_i.count(cut))
                        mapIndex0.insert(j);
                    if (data1.cut_i.count(cut))
                        mapIndex1.insert(j);
                }

                // generate TT
                uint64_t newTT = 0;
                for (int iTT = 0; iTT < (1 << cutCount); ++iTT)
                {
                    int iFaninTT0 = 0, iFaninTT1 = 0;

                    for (int bit = 0, map0 = 0, map1 = 0; bit < cutCount; ++bit)
                    {
                        bool iTTBit = (iTT >> bit) & 1;
                        if (mapIndex0.count(bit))
                            iFaninTT0 |= (iTTBit << (map0++));
                        if (mapIndex1.count(bit))
                            iFaninTT1 |= (iTTBit << (map1++));
                    }

                    newTT |= ((((data0.TT >> iFaninTT0) & 1) != fComp0) && (((data1.TT >> iFaninTT1) & 1) != fComp1))
                             << iTT;
                }

                // record result
                data[i].push_back(Lsv_CutTT_t{newCut, newTT});
            }
        }

        // output result
        for (const Lsv_CutTT_t &result : data[i])
        {
            printf("%d : ", i);
            for (int cut : result.cut_i)
                printf("%d ", cut);
            printf(": %llX\n", result.TT);
        }
    }
}

int Lsv_CommandCutTT(Abc_Frame_t *pAbc, int argc, char **argv)
{
    Abc_Ntk_t *pNtk = Abc_FrameReadNtk(pAbc);
    if (argc != 2)
    {
        Abc_Print(-2, "usage: lsv_cut_tt <k>\n");
        Abc_Print(-2, "\t        generates the k-feasible cut truth table\n");
        Abc_Print(-2, "\t <k>  : k-feasible cut, must be a positive integer\n");
        return 1;
    }

    int k = std::atoi(argv[1]);

    if (k < 1)
    {
        Abc_Print(-1, "Must be a positive integer.\n");
        return 1;
    }
    if (k > 6)
    {
        Abc_Print(-1, "Unable to enumerate k greater than 6.\n");
        return 1;
    }
    if (!pNtk)
    {
        Abc_Print(-1, "Empty network.\n");
        return 1;
    }
    if (Abc_NtkIsStrash(pNtk) != 1)
    {
        Abc_Print(-1, "Network not strashed.\n");
        return 1;
    }

    Lsv_NtkCutTT(pNtk, k);
    return 0;
}

void Lsv_NtkCutBDD(Abc_Ntk_t *pNtk, int k)
{
    Abc_Obj_t *pObj;
    DdManager *dd = Cudd_Init(k, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);
    std::vector<std::vector<Lsv_CutBDD_t>> data(Abc_NtkObjNum(pNtk));
    int i;
    Cudd_AutodynDisable(dd);

    if (dd == NULL)
        return;

    Abc_NtkForEachObj(pNtk, pObj, i)
    {
        // all nodes have a cut of itself
        data[i].push_back(Lsv_CutBDD_t{{i}, Cudd_bddIthVar(dd, 0)});
        Cudd_Ref(data[i][0].pBDD);

        // filter out non-nodes/POs
        if (!(Abc_ObjIsNode(pObj) || Abc_ObjIsPo(pObj)) || Abc_ObjFanoutNum(pObj) == 0)
            continue;

        // fanin nodes
        int fId0 = Abc_ObjFaninId0(pObj);
        int fId1 = Abc_ObjFaninId1(pObj);
        int fComp0 = Abc_ObjFaninC0(pObj);
        int fComp1 = Abc_ObjFaninC1(pObj);

        for (const Lsv_CutBDD_t &data0 : data[fId0])
        {
            for (const Lsv_CutBDD_t &data1 : data[fId1])
            {
                // union of cut_i
                std::set<int> newCut = data0.cut_i;
                newCut.insert(data1.cut_i.begin(), data1.cut_i.end());
                int cutCount = newCut.size();

                // cutoff greater feasible cuts
                if (cutCount > k)
                    continue;

                // get mappings for TT
                int j = 0, m0 = 0, m1 = 0;
                int mapIndex0[k];
                int mapIndex1[k];
                for (int cut : newCut)
                {
                    if (data0.cut_i.count(cut))
                        mapIndex0[m0++] = j;
                    if (data1.cut_i.count(cut))
                        mapIndex1[m1++] = j;
                    ++j;
                }

                // generates BDD
                DdNode *bdd0 = Cudd_bddPermute(dd, data0.pBDD, mapIndex0);
                DdNode *bdd1 = Cudd_bddPermute(dd, data1.pBDD, mapIndex1);
                Cudd_Ref(bdd0);
                Cudd_Ref(bdd1);
                if (fComp0)
                    bdd0 = Cudd_Not(bdd0);
                if (fComp1)
                    bdd1 = Cudd_Not(bdd1);
                DdNode *newBdd = Cudd_bddAnd(dd, bdd0, bdd1);
                Cudd_Ref(newBdd);
                Cudd_RecursiveDeref(dd, Cudd_Regular(bdd0));
                Cudd_RecursiveDeref(dd, Cudd_Regular(bdd1));

                // register data
                data[i].push_back(Lsv_CutBDD_t{newCut, newBdd});
            }
        }

        // output result
        for (const Lsv_CutBDD_t &result : data[i])
        {
            printf("%d : ", i);
            for (int cut : result.cut_i)
                printf("%d ", cut);
            printf(" : %d\n", Cudd_DagSize(result.pBDD));
        }
    }

    Cudd_Quit(dd);
}

int Lsv_CommandCutBDD(Abc_Frame_t *pAbc, int argc, char **argv)
{
    Abc_Ntk_t *pNtk = Abc_FrameReadNtk(pAbc);
    if (argc != 2)
    {
        Abc_Print(-2, "usage: lsv_cut_bddsize <k>\n");
        Abc_Print(-2, "\t        generates the k-feasible cut bdd size\n");
        Abc_Print(-2, "\t <k>  : k-feasible cut, must be a positive integer\n");
        return 1;
    }

    int k = std::atoi(argv[1]);

    if (k < 1)
    {
        Abc_Print(-1, "Must be a positive integer.\n");
        return 1;
    }
    if (!pNtk)
    {
        Abc_Print(-1, "Empty network.\n");
        return 1;
    }
    if (Abc_NtkIsStrash(pNtk) != 1)
    {
        Abc_Print(-1, "Network not strashed.\n");
        return 1;
    }

    Lsv_NtkCutBDD(pNtk, k);
    return 0;
}

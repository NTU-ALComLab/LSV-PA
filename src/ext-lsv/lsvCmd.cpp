#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <cstdlib>
#include <set>
#include <vector>

static int Lsv_CommandPrintNodes(Abc_Frame_t *pAbc, int argc, char **argv);
static int Lsv_CommandCutTT(Abc_Frame_t *pAbc, int argc, char **argv);

struct Lsv_CutTT_t
{
    std::set<int> cut_i;
    uint64_t TT;
};

void init(Abc_Frame_t *pAbc)
{
    Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
    Cmd_CommandAdd(pAbc, "LSV", "lsv_cut_tt", Lsv_CommandCutTT, 0);
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

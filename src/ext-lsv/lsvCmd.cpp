#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <algorithm>
#include <vector>
#include "bdd/cudd/cudd.h"

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);

static int Debug_Print(int level, const char * format, ...);
static unsigned long long TTOfCut(Abc_Obj_t *pObj, const std::vector<unsigned int> &cut);
static unsigned long long TTOfProjection(unsigned int cut_size, const long &pos);
static int Print_Cut(std::__1::vector<std::__1::vector<unsigned int>> &cuts);
static std::__1::vector<std::__1::vector<std::__1::vector<unsigned int>>> CutEnumeration(Abc_Ntk_t *pNtk, int k);
static int Lsv_CommandCut_TT(Abc_Frame_t *pAbc, int argc, char **argv);
static DdNode* BddOfCut(DdManager *dd, Abc_Obj_t *pObj, const std::vector<unsigned int> &cut, int k);
static int Lsv_CommandCut_Bddsize(Abc_Frame_t * pAbc, int argc, char ** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_cut_tt", Lsv_CommandCut_TT, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_cut_bddsize", Lsv_CommandCut_Bddsize, 0);
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

int Lsv_CommandCut_TT(Abc_Frame_t *pAbc, int argc, char **argv)
{
    Abc_Ntk_t *pNtk = Abc_FrameReadNtk(pAbc);
    if (!pNtk) {
        Abc_Print(-1, "Empty network.\n");
        return 1;
    }

    if (argc != 2) {
        Abc_Print(-1, "Usage: lsv_cut_tt <k>\n");
        return 1;
    }

    int k = atoi(argv[1]);
    if (k <= 0) {
        Abc_Print(-1, "k must be a positive integer.\n");
        return 1;
    }

    // check if the network is an AIG
    if (!Abc_NtkIsStrash(pNtk)) {
        Abc_Print(-1, "The network is not an AIG.\n");
        return 1;
    }

    // cut enumeration for each node in the network
    const auto &cuts_of_node = CutEnumeration(pNtk, k);

    // Evaluate the truth table for each cut
    Abc_Obj_t *pObj;
    int i;
    Abc_NtkForEachNode(pNtk, pObj, i) {
        unsigned int id = Abc_ObjId(pObj);
        Debug_Print(2, "Evaluating truth tables for cuts of node %s (Id = %d)\n", Abc_ObjName(pObj), id);
        for (const auto &cut : cuts_of_node[id]) {
            unsigned long long tt = TTOfCut(pObj, cut);

            Abc_Print(2, "%d:", id);
            for (unsigned int cut_id : cut) {
                Abc_Print(2, " %d", cut_id);
            }
            Abc_Print(2, ": %llX\n", tt);
        }
    }

    return 0;
}

std::__1::vector<std::__1::vector<std::__1::vector<unsigned int>>> CutEnumeration(Abc_Ntk_t *pNtk, int k)
{
    std::__1::vector<std::__1::vector<std::__1::vector<unsigned int>>> cuts_of_node;
    cuts_of_node.resize(Abc_NtkObjNumMax(pNtk));

    Abc_Obj_t *pObj;
    int i;
    Abc_NtkForEachCi(pNtk, pObj, i)
    {
        // For each primary input, we can consider it as a cut of size 1
        unsigned int id = Abc_ObjId(pObj);
        Debug_Print(2, "Primary input: Id = %d, name = %s\n", id, Abc_ObjName(pObj));
        cuts_of_node[id].push_back({id});
    }

    Abc_NtkForEachNode(pNtk, pObj, i)
    {
        // perform cut enumeration for the node pObj within cut size k
        // and compute the truth table for each cut
        unsigned int id = Abc_ObjId(pObj);
        Abc_Obj_t *p0 = Abc_ObjFanin0(pObj);
        Abc_Obj_t *p1 = Abc_ObjFanin1(pObj);
        unsigned int id0 = Abc_ObjId(p0);
        unsigned int id1 = Abc_ObjId(p1);

        Debug_Print(2, "Performing cut enumeration for node %s (Id = %d) with fanins: %d, %d\n", Abc_ObjName(pObj), id, id0, id1);

        cuts_of_node[id].push_back({id});
        for (const auto &cut0 : cuts_of_node[id0])
        {
            for (const auto &cut1 : cuts_of_node[id1])
            {
                std::vector<unsigned int> merged_cut;

                std::set_union(cut0.begin(), cut0.end(),
                               cut1.begin(), cut1.end(),
                               std::back_inserter(merged_cut));

                // Only add the merged cut if its size is <= k and it's not already in the cuts_of_node[id]
                if (merged_cut.size() <= k &&
                    std::find(cuts_of_node[id].begin(), cuts_of_node[id].end(),
                              merged_cut) == cuts_of_node[id].end())
                {
                    cuts_of_node[id].push_back(merged_cut);
                }
            }
        }
        Debug_Print(2, "Total cuts found: %zu\n", cuts_of_node[id].size());
        Print_Cut(cuts_of_node[id]);
    }
    return cuts_of_node;
}

static unsigned long long TTOfCut(Abc_Obj_t *pObj, const std::vector<unsigned int> &cut) {
    Debug_Print(2, "Computing truth table for node %d (%s) with cut", Abc_ObjId(pObj), Abc_ObjName(pObj));
    for (unsigned int id : cut) {
        Debug_Print(2, " %d", id);
    }
    Debug_Print(2, "\n"); 
    // Base case: if the cut contains the current node, return the truth table for the primary input
    unsigned int cut_size = cut.size();
    const auto &it = std::find(cut.begin(), cut.end(), Abc_ObjId(pObj));
    if (it != cut.end()) {
        unsigned int pos = cut.end() - it - 1;
        Debug_Print(2, "Node %s (Id = %d) is in the cut at position %d. Returning truth table for primary input.\n", Abc_ObjName(pObj), Abc_ObjId(pObj), pos);
        return TTOfProjection(cut_size, pos);
    }

    // Recursive case: compute the truth table for the fanins
    Abc_Obj_t *p0 = Abc_ObjFanin0(pObj);
    Abc_Obj_t *p1 = Abc_ObjFanin1(pObj);
    Debug_Print(2, "Computing truth table for fanin 0: %s (Id = %d).\n", Abc_ObjName(p0), Abc_ObjId(p0));
    unsigned long long tt0 = TTOfCut(p0, cut);
    Debug_Print(2, "tt0 = %llX\n", tt0);
    Debug_Print(2, "Computing truth table for fanin 1: %s (Id = %d).\n", Abc_ObjName(p1), Abc_ObjId(p1));
    unsigned long long tt1 = TTOfCut(p1, cut);
    Debug_Print(2, "tt1 = %llX\n", tt1);

    // Combine the truth tables based on the type of gate (AND in this case)
    unsigned long long result_tt = (Abc_ObjFaninC0(pObj) ? ~tt0 : tt0) & (Abc_ObjFaninC1(pObj) ? ~tt1 : tt1);
    result_tt &= (1ULL << (1ULL << cut_size)) - 1; // Mask to keep only the relevant bits
    Debug_Print(2, "Combined truth table: %llX\n", result_tt);
    return result_tt;
}

static unsigned long long TTOfProjection(unsigned int cut_size, const long &pos)
{
    // (2,0) -> 1010
    // (2,1) -> 1100
    unsigned long long tt = 0;
    for (unsigned long long i = 0; i < (1ULL << cut_size); ++i) {
        if ((i >> pos) & 1) {
            tt |= (1ULL << i);
        }
    }
    return tt;
}

static int Debug_Print(int level, const char * format, ...) {
    if (level > 1) return 0; // Only print debug messages for level <= 2
    va_list args;
    va_start(args, format);
    std::vprintf(format, args);
    va_end(args);
    return 0;
}

static int Print_Cut(std::__1::vector<std::__1::vector<unsigned int>> &cuts)
{
    for (const auto &cut : cuts)
    {
        Debug_Print(2, "  Cut: ");
        for (unsigned int id : cut)
        {
            Debug_Print(2, "%d ", id);
        }
        Debug_Print(2, "\n");
    }
    return 0;
}

int Lsv_CommandCut_Bddsize(Abc_Frame_t *pAbc, int argc, char **argv)
{
    Abc_Ntk_t *pNtk = Abc_FrameReadNtk(pAbc);
    if (!pNtk) {
        Abc_Print(-1, "Empty network.\n");
        return 1;
    }

    if (argc != 2) {
        Abc_Print(-1, "Usage: lsv_cut_bddsize <k>\n");
        return 1;
    }

    int k = atoi(argv[1]);
    if (k <= 0) {
        Abc_Print(-1, "k must be a positive integer.\n");
        return 1;
    }

    // check if the network is an AIG
    if (!Abc_NtkIsStrash(pNtk)) {
        Abc_Print(-1, "The network is not an AIG.\n");
        return 1;
    }

    // cut enumeration for each node in the network
    const auto &cuts_of_node = CutEnumeration(pNtk, k);

    // Evaluate the BDD size for each cut
    Abc_Obj_t *pObj;
    int i;
    Abc_NtkForEachNode(pNtk, pObj, i) {
        unsigned int id = Abc_ObjId(pObj);
        Debug_Print(2, "Evaluating BDD sizes for cuts of node %s (Id = %d)\n", Abc_ObjName(pObj), id);
        for (const auto &cut : cuts_of_node[id]) {
            DdManager * dd = Cudd_Init(k, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);
            // Compute the BDD for the cut
            DdNode *f = BddOfCut(dd, pObj, cut, k);
            int bdd_size = Cudd_DagSize(f); 
            Cudd_RecursiveDeref(dd, f);
            Cudd_Quit(dd);
            
            Abc_Print(2, "%d:", id);
            for (unsigned int cut_id : cut) {
                Abc_Print(2, " %d", cut_id);
            }
            Abc_Print(2, ": %d\n", bdd_size);
        }
    }
    return 0;
}

static DdNode* BddOfCut(DdManager *dd, Abc_Obj_t *pObj, const std::vector<unsigned int> &cut, int k) {
    // Base case: if the cut contains the current node, return the BDD for the primary input
    const auto &it = std::find(cut.begin(), cut.end(), Abc_ObjId(pObj));
    if (it != cut.end()) {
        unsigned int pos = it - cut.begin();
        DdNode *var_bdd = Cudd_bddIthVar(dd, pos);
        Cudd_Ref(var_bdd);
        return var_bdd;
    }

    // Recursive case: compute the BDD for the fanins
    Abc_Obj_t *p0 = Abc_ObjFanin0(pObj);
    Abc_Obj_t *p1 = Abc_ObjFanin1(pObj);
    DdNode *f0 = BddOfCut(dd, p0, cut, k);
    DdNode *f1 = BddOfCut(dd, p1, cut, k);

    // Combine the BDDs of the fanins
    f0 = Abc_ObjFaninC0(pObj) ? Cudd_Not(f0) : f0;
    f1 = Abc_ObjFaninC1(pObj) ? Cudd_Not(f1) : f1;
    DdNode *f = Cudd_bddAnd(dd, f0, f1);
    Cudd_Ref(f);
    Cudd_RecursiveDeref(dd, f0);
    Cudd_RecursiveDeref(dd, f1);

    return f;
}
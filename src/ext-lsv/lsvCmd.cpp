#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <vector>
#include <set>
#include <algorithm>
#include <cstdlib>

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintMoCut(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocut", Lsv_CommandPrintMoCut, 0);
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
    ////printf("Object Id = %d, name = %s\n", Abc_ObjId(pObj), Abc_ObjName(pObj));
    Abc_Obj_t* pFanin;
    int j;
    Abc_ObjForEachFanin(pObj, pFanin, j) {
      //printf("  Fanin-%d: Id = %d, name = %s\n", j, Abc_ObjId(pFanin),Abc_ObjName(pFanin));
    }
    if (Abc_NtkHasSop(pNtk)) {
      //printf("The SOP of this node:\n%s", (char*)pObj->pData);
    }
  }
}
static std::vector<std::set<int>> create_cut(
    int k,
    int fanin0,
    int fanin1,
    const std::vector<std::vector<std::set<int>>>& cuts) {
  std::set<std::set<int>> unique_cuts;
  const auto& cuts0 = cuts[fanin0];
  const auto& cuts1 = cuts[fanin1];
  //printf("merged %d and %d :\n",fanin0,fanin1);

  for (const auto& a : cuts0) {
    for (const auto& b : cuts1) {

      for(const auto& n :a){
        //printf("%d ",n);

      }
      //printf("\n");

      for(const auto& n :b){
        //printf("%d ",n);
      }
      //printf("\n");

      std::set<int> merged;
      std::set_union(a.begin(), a.end(), b.begin(), b.end(),
                     std::inserter(merged, merged.begin()));
      if ((int)merged.size() <= k) {
        unique_cuts.insert(std::move(merged));
      }
    }
  }
  // Convert to vector
  return std::vector<std::set<int>>(unique_cuts.begin(), unique_cuts.end());
}


void Lsv_NtkPrintCut(Abc_Ntk_t* pNtk, int k, int l) {
  Abc_Obj_t* pObj;
  int i;

  int id_max = 0;
  int level_max = 0;
  Abc_NtkForEachNode(pNtk, pObj, i) {
    id_max = std::max(id_max, (int)Abc_ObjId(pObj));
    level_max = std::max(level_max, Abc_ObjLevel(pObj));
  }
  std::vector<std::vector<int>> fanin(id_max+1);
  std::vector<std::vector<int>> level_vec(level_max+1);

  Abc_NtkForEachNode(pNtk, pObj, i) {
    int id = Abc_ObjId(pObj);
    int level = Abc_ObjLevel(pObj);
    //printf("Object Id = %d, name = %s ObjLevel = %d\n", id, Abc_ObjName(pObj), level);
    Abc_Obj_t* pFanin;
    level_vec[level].push_back(id);
    int j;
    Abc_ObjForEachFanin(pObj, pFanin, j) {
      int fid = (int)Abc_ObjId(pFanin);
      fanin[id].push_back(fid);
      if (fid > id_max) {
        id_max = fid;
      }
    }
  }
  std::vector<std::vector<std::set<int>>> cuts(id_max+1);
  for(int id =0;id<id_max+1;id++){
    cuts[id].push_back(std::set<int>{id});
  }
  // int limit_level = std::min(level_max, l);
  for (int cur_level = 0; cur_level <= level_max; ++cur_level) {
    for (int id : level_vec[cur_level]) {
      // Assume 2-input AIG. Handle leaves/trivial cases.
      

      // size >= 2
      // Always include the trivial cut containing the node itself (if allowed)
      if(cur_level ==1){

      }
      // Build from fanin cuts
      const int f0 = fanin[id][0];
      const int f1 = fanin[id][1];
      if(cur_level ==1){
        cuts[id].push_back(std::set<int>{f0,f1});
      }
      else{
        auto merged = create_cut(k, f0, f1, cuts);
        // Dedup with existing
        std::set<std::set<int>> uniq(cuts[id].begin(), cuts[id].end());
        for (auto& s : merged) uniq.insert(s);
        cuts[id].assign(uniq.begin(), uniq.end());
      }
    }
  }

  // Print cuts up to level l
  for (int cur_level = 0; cur_level <= level_max; ++cur_level) {
    for (int id : level_vec[cur_level]) {
      printf("Cuts for node %d (level %d):\n", id, cur_level);
      int idx = 0;
      for (const auto& s : cuts[id]) {
        printf("  Cut %d: ", idx++);
        bool first = true;
        for (int v : s) {
          if (!first) printf(", ");
          first = false;
          printf("%d", v);
        }
        printf("\n");
      }
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

int Lsv_CommandPrintMoCut(Abc_Frame_t* pAbc, int argc, char** argv) {

  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
      case 'h':
        Abc_Print(-2, "usage: lsv_printmocut <k> <l> [-h]\n");
        Abc_Print(-2, "\t        prints the k-l cut in the network\n");
        Abc_Print(-2, "\t-h    : print the command usage\n");
        return 1;
      default:
        Abc_Print(-2, "usage: lsv_printmocut <k> <l> [-h]\n");
        Abc_Print(-2, "\t        prints the k-l cut in the network\n");
        Abc_Print(-2, "\t-h    : print the command usage\n");
        return 1;
    }
  }
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  if (argc < 3) {
    Abc_Print(-2, "usage: lsv_printmocut <k> <l> [-h]\n");
    Abc_Print(-2, "\t        prints the k-l cut in the network\n");
    Abc_Print(-2, "\t-h    : print the command usage\n");
    return 1;
  }
  int k = atoi(argv[1]);
  int l = atoi(argv[2]);
  if (k <= 2 || l < 1) {
    Abc_Print(-2, "usage: lsv_printmocut <k> <l> [-h]\n");
    Abc_Print(-2, "\t        prints the k-l cut in the network\n");
    Abc_Print(-2, "\t-h    : print the command usage\n");
    return 1;
  }
  Lsv_NtkPrintCut(pNtk, k, l);
  return 0;
}
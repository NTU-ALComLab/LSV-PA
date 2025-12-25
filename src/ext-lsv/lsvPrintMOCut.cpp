#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

// STL related
#include <vector>
#include <set>
#include <map>

// ===================================================================
// Command lsv_print_nodes
// ===================================================================

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
  Abc_Print(-2, "Usage: lsv_print_nodes [-h]\n");
  Abc_Print(-2, "\t        prints the nodes in the network\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}


// ===================================================================
// Command lsv_printmocut
// ===================================================================

void Set_Union(const std::set<unsigned>& s1, const std::set<unsigned>& s2, std::set<unsigned>& s_union){
  s_union.clear();
  std::set_union(s1.begin(), s1.end(), s2.begin(), s2.end(), 
                 std::inserter(s_union, s_union.begin()));
}

void Lsv_Iterate_Cuts(
  Abc_Ntk_t* pNtk, 
  Abc_Obj_t* pObj, 
  const int size_upper_bound, 
  std::vector<std::vector<std::set<unsigned>>>& cut_list, 
  std::map<std::set<unsigned>, std::set<unsigned>>& cut_map){

  unsigned id = Abc_ObjId(pObj);
  cut_list[id].push_back(std::set<unsigned>{id});
  cut_map[std::set<unsigned>{id}] = std::set<unsigned>{id};

  // printf("Iterate cuts of node  %d with type %d\n", Abc_ObjId(pObj), Abc_ObjType(pObj));

  // Base case: (Const 1 node and PI nodes)
  if (!Abc_ObjIsNode(pObj)) {
    return;
  }

  // General case: 
  unsigned fanin0_id, fanin1_id;
  fanin0_id = Abc_ObjId(Abc_ObjFanin0(pObj));
  fanin1_id = Abc_ObjId(Abc_ObjFanin1(pObj));

  for (std::set<unsigned>& fanin0_cut : cut_list[fanin0_id]){
    for (std::set<unsigned>& fanin1_cut : cut_list[fanin1_id]){
      std::set<unsigned> new_cut;
      Set_Union(fanin0_cut, fanin1_cut, new_cut);

      if (new_cut.size() <= size_upper_bound){
        // Add the new cut to the cut list of this node
        cut_list[id].push_back(new_cut);

        // Add the new cut to the cut map
        if (cut_map.find(new_cut) == cut_map.end()){
          // This cut is not in the map yet
          cut_map[new_cut] = std::set<unsigned>{id};
        } else {
          // This cut is already in the map
          cut_map[new_cut].insert(id);
        }
      }

    //   // Debug: print new cut
    //   printf("New cut of node %d: ", id);
    //   for (unsigned e: new_cut){
    //     printf("%d ", e);
    //   }
    //   printf("\n");

    //   // Debug: print new map
    //   for (unsigned e: cut_map[new_cut]){
    //     printf("  Node with this cut: %d", e);
    //   }
    //   printf("\n");

    }
  }
}

void Lsv_NtkPrintMOCuts(Abc_Ntk_t* pNtk, const int k, const int l) {
  
  // Step 1: Declare the cut list and the cut map
  // ===========================================================
  // Build the cut list vector of size "vsize"
  // cut_list[i] means the cut list (of size <= k) of the i-th object.
  // cut_list[i][j] means the j-th cut of the i-th object.
  int vsize = Abc_NtkObjNumMax(pNtk);
  std::vector<std::vector<std::set<unsigned>>> cut_list(vsize);

  // cut_map[cut] = {list of nodes that have this cut}
  std::map<std::set<unsigned>, std::set<unsigned>> cut_map;
  
  // Step 2: Calculate the cut list and the cut map
  // ==========================================================
  Abc_Obj_t* pObj;
  int i;

  Abc_NtkForEachObj(pNtk, pObj, i) {
    // printf("Processing node %d with type %d\n", Abc_ObjId(pObj), Abc_ObjType(pObj));
    if (!Abc_ObjIsPo(pObj)) Lsv_Iterate_Cuts(pNtk, pObj, k, cut_list, cut_map);
  }

  // Step 3: Print the k-l multi-output cuts
  // ==========================================================
  for (auto& [cut, nodes] : cut_map){
    if ((cut.size() <= k) && (nodes.size() >= l)){
      for (unsigned fanin : cut){
        printf("%d ", fanin);
      }

      printf(":");

      for (unsigned node: nodes){
        printf(" %d", node);
      }

      printf("\n");
    }
  }
}

int Lsv_CommandPrintMOCuts(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c;
  Extra_UtilGetoptReset();

  int k = 0;
  int l = 0;

  // Reading -h option
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
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "The command can only be applied to the strashed network.\n");
    return 1;
  }

  // Reading <k> and <l> options
  if (argc == 3) {

    char *end1 = NULL, *end2 = NULL;

    // change argv[1] to long type, end1 points to the first non-numerical character, 10-based.
    long _k = strtol(argv[1], &end1, 10);
    long _l = strtol(argv[2], &end2, 10);

    // The number is changed to long type
    if ((*end1 == '\0') && (*end2 == '\0')){
      k = (int)_k;
      l = (int)_l;

      if (3 <= k && k <= 6 && 1 <= l && l <= 4){
        // legal k and l, execute the program
        Lsv_NtkPrintMOCuts(pNtk, k, l);
      } else {
        Abc_Print(-1, "Illegal <k> or <l>. Valid range: 3 <= k <= 6, 1 <= l <= 4.\n");
        goto usage;
      }
    } else {
      Abc_Print(-1, "Illegal <k> or <l>, not a number.\n");
      goto usage;
    }
  }
  else goto usage;

  return 0;

usage:
  Abc_Print(-2, "Usage: lsv_printmocut [-h] [k l]\n");
  Abc_Print(-2, "\t-h       : print the command usage\n");
  Abc_Print(-2, "\tk l      : integers with k in [3,6], l in [1,4], print k-l multi-output cut\n");
  return 1;
}
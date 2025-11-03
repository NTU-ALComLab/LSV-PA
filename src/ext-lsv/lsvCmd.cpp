#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "aig/aig/aig.h"
#include "opt/cut/cut.h"
#include "opt/cut/cutInt.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <algorithm>
#include <vector>
#include <set>
#include<unordered_map>
#include <map>
#include<iostream>
#include <sstream>

ABC_NAMESPACE_IMPL_START

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintMOCuts(Abc_Frame_t* pAbc, int argc, char** argv);
void Lsv_NtkPrintMOCuts(Abc_Ntk_t* pNtk, int k, int l);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocut", Lsv_CommandPrintMOCuts, 0);
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



std::set<unsigned int> Lsv_SetUnion(const std::set<unsigned int>& s1, const std::set<unsigned int>& s2) {
    std::set<unsigned int> result;
    std::set_union(s1.begin(), s1.end(), s2.begin(), s2.end(), 
                   std::inserter(result, result.begin()));
    return result;
}


bool Lsv_IsContained(const std::set<unsigned int>& cut_a, const std::set<unsigned int>& cut_b) {
    return std::includes(cut_b.begin(), cut_b.end(), cut_a.begin(), cut_a.end());
}



std::set<std::set<unsigned int>> Lsv_ComputeNodeCuts(
    Abc_Obj_t* pObj, 
    int k, 
    const std::map<unsigned int, std::set<std::set<unsigned int>>>& cuts_map) 
{
    std::set<std::set<unsigned int>> current_cuts;
    

    current_cuts.insert({Abc_ObjId(pObj)});

    if (Abc_ObjFaninNum(pObj) == 2) {
        Abc_Obj_t* pFanin0 = Abc_ObjFanin0(pObj);
        Abc_Obj_t* pFanin1 = Abc_ObjFanin1(pObj);

        if (cuts_map.count(Abc_ObjId(pFanin0)) && cuts_map.count(Abc_ObjId(pFanin1))) {
             const auto& cuts0 = cuts_map.at(Abc_ObjId(pFanin0));
             const auto& cuts1 = cuts_map.at(Abc_ObjId(pFanin1));

             for (const auto& cut0 : cuts0) {
                 for (const auto& cut1 : cuts1) {
                     std::set<unsigned int> combined_cut = Lsv_SetUnion(cut0, cut1);
                     if (combined_cut.size() <= k) {
                         current_cuts.insert(combined_cut);
                     }
                 }
             }
        }
    }
    
    std::set<std::set<unsigned int>> final_cuts;
    
    for (const auto& cut_candidate : current_cuts) {
        bool is_dominated = false;
        
        for (const auto& existing_cut : final_cuts) {
            if (Lsv_IsContained(existing_cut, cut_candidate) && existing_cut != cut_candidate) {
                is_dominated = true;
                break;
            }
        }
        
        if (!is_dominated) {
            std::set<std::set<unsigned int>> new_final_cuts;
            for (const auto& existing_cut : final_cuts) {
                if (Lsv_IsContained(cut_candidate, existing_cut) && cut_candidate != existing_cut) {
                } else {
                    new_final_cuts.insert(existing_cut);
                }
            }
            new_final_cuts.insert(cut_candidate);
            final_cuts = new_final_cuts;
        }
    }
    
    return final_cuts;
}

void Lsv_NtkPrintMOCuts(Abc_Ntk_t* pNtk, int k, int l) {
    Abc_Obj_t* pObj;
    int i;
    
    std::map<unsigned int, std::set<std::set<unsigned int>>> node_cuts_map;

    Abc_NtkForEachCi(pNtk, pObj, i) {
        if (Abc_ObjIsPi(pObj)) {
            node_cuts_map[Abc_ObjId(pObj)].insert({Abc_ObjId(pObj)});
        }
    }

    Abc_NtkForEachNode(pNtk, pObj, i) {
        std::set<std::set<unsigned int>> current_node_cuts = Lsv_ComputeNodeCuts(pObj, k, node_cuts_map);
        node_cuts_map[Abc_ObjId(pObj)] = current_node_cuts;
    }


    std::map<std::set<unsigned int>, std::set<unsigned int>> mo_cuts_aggregator;

    Abc_NtkForEachNode(pNtk, pObj, i) {
        unsigned int and_node_id = Abc_ObjId(pObj);
        
        if (node_cuts_map.count(and_node_id)) {
            const auto& node_cuts = node_cuts_map.at(and_node_id);
            

            for (const auto& cut : node_cuts) {
                mo_cuts_aggregator[cut].insert(and_node_id);
            }
        }
    }
    

    for (const auto& pair : mo_cuts_aggregator) {
        const std::set<unsigned int>& cut_set = pair.first;
        const std::set<unsigned int>& output_node_ids = pair.second;
        

        if (output_node_ids.size() >= (size_t)l) {
            
            bool first_node = true;
            for (unsigned int node_id : cut_set) {
                if (!first_node) printf(" ");
                printf("%u", node_id);
                first_node = false;
            }
            
            printf(" : ");
            
            bool first_out = true;
            for (unsigned int out_id : output_node_ids) {
                if (!first_out) printf(" ");
                printf("%u", out_id);
                first_out = false;
            }
            
            printf("\n");
        }
    }
}


int Lsv_CommandPrintMOCuts(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int k = 0;
  int l = 0;
  
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }

  if (Abc_NtkIsStrash(pNtk) == 0) {
    Abc_Print(-1, "Network is not in Strash AIG format. Run 'strash' first.\n");
    return 1;
  }

  if (argc < 3) {
      goto usage;
  }

  k = atoi(argv[1]); 
  l = atoi(argv[2]);
  
  if (k < 3 || k > 6 || l < 1 || l > 4) {
      Abc_Print(-1, "Error: Invalid k or l. Requires 3 <= k <= 6 and 1 <= l <= 4.\n");
      goto usage;
  }

  Lsv_NtkPrintMOCuts(pNtk, k, l);
  
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_printmocut <k> <l>\n");
  Abc_Print(-2, "\t        enumerates k-l multi-output cuts in an AIG (3<=k<=6, 1<=l<=4)\n");
  Abc_Print(-2, "\t<k>   : max size of the cut\n");
  Abc_Print(-2, "\t<l>   : min number of output nodes sharing the cut\n");
  return 1;
}

ABC_NAMESPACE_IMPL_END

#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

#include <iostream> 
#include <set>      
#include <string>   
#include <map>   
#include <vector>   
#include <algorithm>

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintmocuts(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocuts", Lsv_CommandPrintmocuts, 0);
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

void Lsv_NtkPrintmocuts (Abc_Ntk_t* pNtk,int k,int l);

int Lsv_CommandPrintmocuts(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c;
  int k, l;
  int argIndex = 1;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
      case 'h':
        goto usage;
      default:
        goto usage;
    }
  }
  if (argc - argIndex < 2) {
    Abc_Print(-1, "Error: missing parameters <k> and <l>.\n");
    goto usage;
  }

  k = atoi(argv[argIndex]);
  l = atoi(argv[argIndex + 1]);

  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  Lsv_NtkPrintmocuts(pNtk,k,l);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_printmocuts [-h] <k> <l>\n");
  Abc_Print(-2, "\t<k> <l>        prints k-l-feasible cuts\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}

void Lsv_NtkPrintmocuts (Abc_Ntk_t* pNtk,int k,int l){

  //nodes mapped with their k-feasible cuts 
  std::map<int,std::vector<std::set<int>>> nodes_cuts;
  //cuts mapped with their supported nodes
  std::map<std::set<int>,std::set<int>> cuts_supported_nodes;
  Abc_Obj_t* pObj;
  int i;
  std::set<int> new_cut;
  
  //iterate over all objects in topological order
  Abc_NtkForEachObj(pNtk,pObj,i){

    new_cut.clear();
    int node_id = Abc_ObjId(pObj);

    
    if(Abc_ObjIsPi(pObj)){
      
      //if it is a PI the only cut is himself
      new_cut.insert(node_id);
      nodes_cuts[node_id].push_back(new_cut);
      cuts_supported_nodes[new_cut].insert(node_id);

    }
    else if(Abc_ObjIsNode(pObj)){
      
      //if it is a AND node 
      //the cuts are the combination of the cuts of the fanins 
      std::vector<std::set<int>> cut_fanin0,cut_fanin1;
      int fanin0Id,fanin1Id;

      fanin0Id=Abc_ObjFaninId0(pObj);
      fanin1Id=Abc_ObjFaninId1(pObj);
      
      //get the cuts of the fanins
      cut_fanin0=nodes_cuts[fanin0Id];
      cut_fanin1=nodes_cuts[fanin1Id];
      
      //Combine every fanins cuts
      for (const auto& cut0 : cut_fanin0){
        for (const auto& cut1 : cut_fanin1){
          
          //filtering to have only cuts size < k
          if(cut0.size() + cut1.size() <= k){
            new_cut = cut0;
            new_cut.insert(cut1.begin(),cut1.end());

            //Irredundancy Check
            bool isSubset = false;
            // Iterate directly over the current node's existing cuts
            for(auto it = nodes_cuts[node_id].begin(); it != nodes_cuts[node_id].end();){
              //if a existing cut is a subset of the new_cut then we keep the existing cut and discard new_cut
              if(std::includes(new_cut.begin(), new_cut.end(), it->begin(), it->end())){
                isSubset = true;
                break;
              } 
              //if new_cut is a subset of a existing cut then we remove the existing cut and add new_cut
              else if(std::includes(it->begin(), it->end(), new_cut.begin(), new_cut.end())){
                it = nodes_cuts[node_id].erase(it); // erase returns the next iterator
                continue; // don't increment; already moved to next
                
              } 
              else{
                ++it;
              }
            }
            
            //If new_cut is not a superset of an existing cut, add it
            if (!isSubset) {
              nodes_cuts[node_id].push_back(new_cut);
              cuts_supported_nodes[new_cut].insert(node_id);
            }
          }
        }
      }

      //add the current node as cut
      new_cut.clear();
      new_cut.insert(node_id);
      nodes_cuts[node_id].push_back(new_cut);
      cuts_supported_nodes[new_cut].insert(node_id);
    }
  }

  //print the k-l-feasible nodes
  for (const auto& pair : cuts_supported_nodes) {
    if(pair.second.size()>=l){
      for(int i : pair.first){
        // printf("%d ",i);
        printf("%s ",Abc_ObjName(Abc_NtkObj(pNtk,i))); //print node names
      }
      printf(": ");
      for(int j : pair.second){
        // printf("%d ",j);
        printf("%s ",Abc_ObjName(Abc_NtkObj(pNtk,j))); //print node names
      }
      printf("\n");
    }
  }

}
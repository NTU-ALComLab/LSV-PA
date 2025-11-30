#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

#include "./lsvCut.h"
#include <stdint.h>
#include <vector> 
#include <map>
#ifndef ptrint
typedef intptr_t ptrint;
#endif
#include "bdd/cudd/cudd.h"
#include "bdd/cudd/cuddInt.h"

#include "sat/cnf/cnf.h"
extern "C"{
 Aig_Man_t* Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
}

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
// static int Lsv_CommandPrintMOCut(Abc_Frame_t* pAbc, int argc, char** argv);
static DdManager * build_bdds_for_network(Abc_Ntk_t * pNtk);
static int Lsv_CommandUnateBdd(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandUnate(Abc_Frame_t* pAbc, int argc, char** argv);


void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  // Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocut", Lsv_CommandPrintMOCut, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_unate_bdd", Lsv_CommandUnateBdd, 0);
  // Cmd_CommandAdd(pAbc, "LSV", "lsv_unate_bdd", Lsv_CommandUnate, 0);
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
  return;
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


/*
// return index of the node
int Lsv_find_cut(Abc_Obj_t* pObj, const int k_feasible, Cut_t*** k_cut, int& kcut_size, int* id_to_index, int* num_cut_per_obj) {
  int nodeID = Abc_ObjId(pObj);
  int index = find_index(id_to_index, kcut_size, nodeID);
  // printf("nodeID = %d, index = %d, kcut_size = %d\n", nodeID, index, kcut_size);
  if(index != -1){
    return index;
  }

  index = kcut_size;
  kcut_size++;
  id_to_index[index] = nodeID;
  // printf("nodeID = %d, index = %d, kcut_size = %d\n", nodeID, index, kcut_size);

  int fanin_num = Abc_ObjFaninNum(pObj);
  // printf("fanin_num = %d\n", fanin_num);
  if(fanin_num == 0){
    num_cut_per_obj[index] = 1;
    k_cut[index] = (Cut_t**)malloc(sizeof(Cut_t*) * 1);
    // printf("nodeID = %d, pcut = %p\n", nodeID, k_cut[index]);
    k_cut[index][0] = new_cut(&nodeID, 1);
    return index;
  }
  
  int cut_accumulate_size = 1;
  Cut_t** cut_accumulate = NULL;
  // cut_accumulate[0] = new_cut(&nodeID, 1);

  Abc_Obj_t* pFanin;
  int i;
  Abc_ObjForEachFanin(pObj, pFanin, i) {

    // int faninID = (int)Abc_ObjId(pFanin);

    int fanin_index = Lsv_find_cut(pFanin, k_feasible, k_cut, kcut_size, id_to_index, num_cut_per_obj);
    // printf("faninID = %d, fanin_index = %d\n", faninID, fanin_index);
    // printf("num_cut_per_obj[fanin_index] = %d\n", num_cut_per_obj[fanin_index]);
    
    Cut_t** fanin_cut = k_cut[fanin_index];
    // printf("fanin_cut[0] = %p\n", fanin_cut[0]);
    // printf("malloc size = %d\n", (cut_accumulate_size * num_cut_per_obj[fanin_index] + 1));
    // merge cut_accumulate and fanin_cut
    Cut_t** cut_temp = (Cut_t**)malloc(sizeof(Cut_t*) * (cut_accumulate_size * num_cut_per_obj[fanin_index] + 1));
    // if(cut_temp == NULL){
    //   printf("cut_temp == NULL\n");
    // }
    // printf("cut_temp = %p, %d\n", cut_temp, cut_temp);
    if(cut_accumulate != NULL){
      // printf("cut_accumulate != NULL\n");
      for(int j=0; j<cut_accumulate_size; j++){
        for(int k=0; k<num_cut_per_obj[fanin_index]; k++){
          // printf("j %d: ", cut_accumulate[j]->cut_size);
          // print_cut(cut_accumulate[j]);
          // printf("k %d: ", fanin_cut[k]->cut_size);
          // print_cut(fanin_cut[k]);
          cut_temp[j*num_cut_per_obj[fanin_index]+k] = new_cut(cut_accumulate[j], fanin_cut[k]);
        }
      }
      free_cuts(cut_accumulate, cut_accumulate_size);
    }
    else{
      for(int j=0; j<num_cut_per_obj[fanin_index]; j++){
        cut_temp[j] = copy_cut(fanin_cut[j]);
      }
    }
    cut_accumulate_size *= num_cut_per_obj[fanin_index];
    // printf("cut_accumulate_size = %d\n", cut_accumulate_size);
    cut_sort_and_eliminate(cut_temp, cut_accumulate_size, k_feasible);
    cut_accumulate = cut_temp;
  }

  if(cut_accumulate == NULL){
    num_cut_per_obj[index] = 1;
    k_cut[index] = (Cut_t**)malloc(sizeof(Cut_t*) * 1);
    // printf("nodeID = %d, pcut = %p\n", nodeID, k_cut[index]);
    k_cut[index][0] = new_cut(&nodeID, 1);
    return index;
  }

  cut_accumulate[cut_accumulate_size++] = new_cut(&nodeID, 1);
  num_cut_per_obj[index] = cut_accumulate_size;
  k_cut[index] = cut_accumulate;
  // printf("nodeID = %d, pcut = %p\n", nodeID, k_cut[index]);
  return index;
}

int Lsv_NtkPrintMOCut(Abc_Ntk_t* pNtk, int k_feasible) {
  
  int NtkObjNum = Abc_NtkObjNum(pNtk);
  int kcut_size = 0;
  int* id_to_index = (int*)malloc(sizeof(int) * NtkObjNum);
  int* num_cut_per_obj = (int*)malloc(sizeof(int) * NtkObjNum);
  Cut_t*** k_cut = (Cut_t***)malloc(sizeof(Cut_t**) * NtkObjNum);
  
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i) {
    int nodeID = Abc_ObjId(pObj);
    int index = Lsv_find_cut(pObj, k_feasible, k_cut, kcut_size, id_to_index, num_cut_per_obj);
    for(int j=0; j<num_cut_per_obj[index]; j++){
      printf("%d: ", nodeID);
      print_cut(k_cut[index][j]);
    }
  }

  for(int i=0; i<kcut_size; i++){
    // printf("Node %d\n", id_to_index[i]);
    free_cuts(k_cut[i], num_cut_per_obj[i]);
  }
  return 0;
}

// Parse the command line arguments and call the function to print the cuts
int Lsv_CommandPrintMOCut(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  
  if(argc != 2) {
    Abc_Print(-1, "Wrong number of arguments.\n");
    Abc_Print(-2, "usage: lsv_printmocut <k> [-h]\n");
    Abc_Print(-2, "\t        prints all k-feasible cuts for all nodes in the network\n");
    Abc_Print(-2, "\t-h    : print the command usage\n");
    return 1;
  }
  if(strlen(argv[1]) != 1 || argv[1][0] < '3' || argv[1][0] > '6') {
    Abc_Print(-1, "Invalid k value.\n");
    Abc_Print(-2, "usage: lsv_printmocut <k>\n");
    Abc_Print(-2, "\t        only accept 3<=k<=6\n");
    return 1;
  }

  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  
  int k_feasible = argv[1][0] - '0';
  Lsv_NtkPrintMOCut(pNtk, k_feasible);

  return 0;
}
*/

// Build simple BDDs for the whole network and attach them to pData.
DdManager * build_bdds_for_network(Abc_Ntk_t * pNtk)
{
  // create manager (tune params as needed)
  DdManager *dd = Cudd_Init(0,0,0,0,0);
  if (!dd) return NULL;

  // assign PI vars
  Abc_Obj_t * pObj;
  int idx = 0;
  Abc_NtkForEachPi(pNtk, pObj, idx) {
    DdNode *var = Cudd_bddIthVar(dd, idx);
    Cudd_Ref(var);                // keep a reference while attached
    pObj->pData = (void*)var;
    printf("DEBUG: PI id=%d name=%s var=%p pData=%p\n",
           Abc_ObjId(pObj), Abc_ObjName(pObj), (void*)var, pObj->pData);
  }

  // traverse internal nodes in topological order and build BDD
  Abc_NtkForEachNode(pNtk, pObj, idx) {
    // collect fanin BDDs and complement flags
    std::vector<DdNode*> fdds;
    std::vector<int> invs;
    Abc_Obj_t * pF;
    int j = 0;
    Abc_ObjForEachFanin(pObj, pF, j) {
      DdNode *fd = (DdNode*)pF->pData;
      if (fd == NULL) {
        printf("DEBUG: missing fanin BDD for fanin %d of node %d (%s)\n",
               j, Abc_ObjId(pObj), Abc_ObjName(pObj));
        return NULL;
      }
      /* use ABC API to detect complemented edges */
      int inv = Abc_ObjFaninC(pObj, j); /* returns 1 if fanin j is complemented */
      if (inv) fd = Cudd_Not(fd);
      fdds.push_back(fd);
      invs.push_back(inv);
      printf("DEBUG: Node id=%d name=%s Fanin-%d id=%d name=%s fd=%p inv=%d\n",
             Abc_ObjId(pObj), Abc_ObjName(pObj), j,
             Abc_ObjId(pF), Abc_ObjName(pF), (void*)fd, inv);
    }

    // compute node function depending on gate type
    DdNode *res = NULL;
    /* if node is truly an AND, combine fanins; otherwise you'll need to implement
        a proper translation for the node type (SOP/AIG/etc.). */
    if (fdds.size() == 1) {
      res = fdds[0];
      Cudd_Ref(res);
    } else if (fdds.size() == 2) {
      res = Cudd_bddAnd(dd, fdds[0], fdds[1]); Cudd_Ref(res);
    } else {
      res = Cudd_ReadOne(dd); Cudd_Ref(res);
      for (DdNode* a : fdds) {
        DdNode *t = Cudd_bddAnd(dd, res, a); Cudd_Ref(t);
        Cudd_RecursiveDeref(dd, res);
        res = t;
      }
    }
    

    // attach result to node (store pointer and keep ref)
    pObj->pData = (void*)res;
  }

  // build PO BDDs: PO pData = fanin BDD (respect complement)
  Abc_NtkForEachPo(pNtk, pObj, idx) {
    Abc_Obj_t * pFanin = Abc_ObjFanin0(pObj); // adapt this accessor
    DdNode *fd = (DdNode*)pFanin->pData;
    bool inv = Abc_ObjFaninC0(pObj); // true if PO fanin is complemented (first fanin)
    if (inv) fd = Cudd_Not(fd);
    Cudd_Ref(fd);
    pObj->pData = (void*)fd;
  }

  // store manager in network so other code can use it
  pNtk->pManFunc = (void*)dd;
  return dd;
}

int Lsv_CommandUnateBdd(Abc_Frame_t* pAbc, int argc, char** argv) {
  // check if everything is valid
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  assert(Abc_NtkIsBddLogic(pNtk));

  if(argc != 3) {
    Abc_Print(-1, "Wrong number of arguments.\n");
    Abc_Print(-2, "usage: lsv_unate_bdd <k> <i> [-h]\n");
    Abc_Print(-2, "\t        whether the function of yk is binate, positive unate, negative unate in xi, or independent of xi\n");
    Abc_Print(-2, "\t-h    : print the command usage\n");
    return 1;
  }
  int k = atoi(argv[1]);
  int i = atoi(argv[2]);
  // printf("DEBUG: k=%d, i=%d\n", k, i);
  // check if k < Abc_NtkPoNum(pNtk) && i < Abc_NtkPiNum(pNtk)
  int pi_num = Abc_NtkPiNum(pNtk);
  // printf("DEBUG: pi_num=%d\n", pi_num);
  if(k >= Abc_NtkPoNum(pNtk) || i >= pi_num || k < 0 || i < 0) {
    Abc_Print(-1, "Invalid k or i value.\n");
    Abc_Print(-2, "usage: lsv_unate_bdd <k> <i>\n");
    Abc_Print(-2, "\t        k should be less than number of POs (%d), i should be less than number of PIs (%d)\n", Abc_NtkPoNum(pNtk), Abc_NtkPiNum(pNtk));
    return 1;
  }

  DdManager * dd = (DdManager*)pNtk->pManFunc;
  if (dd == NULL) {
    Abc_Print(-1, "No BDD manager available in the network.\n");
    return 1;
  }
  // Abc_Print(-2, "DEBUG: dd=%p\n", (void*)dd);

  // get the BDD of the PO k
  Abc_Obj_t* pPO = Abc_NtkPo(pNtk, k);
  Abc_Obj_t *pRoot  = Abc_ObjFanin0( pPO );
  if (pPO == NULL || pRoot == NULL) {
    Abc_Print(-1, "Internal error: Abc_NtkPo returned NULL for k=%d\n", k);
    return 1;
  }
  // Abc_Print(-2, "DEBUG: PO id=%d name=%s pPO=%p pRoot= %p Data=%p\n", Abc_ObjId(pPO), Abc_ObjName(pPO), (void*)pPO, pRoot, pRoot->pData);
  
  DdNode * f = (DdNode *)pRoot->pData;
  // DdNode * f = (DdNode*)pPO->pData;
  if (f == NULL) {
    Abc_Print(-1, "Internal error: PO's pData is NULL (BDD not built for PO %d)\n", k);
    return 1;
  }
  // Abc_Print(-2, "DEBUG: BDD f=%p\n", (void*)f);
  Cudd_Ref(f);

  // get the variable of the PI i
  Abc_Obj_t* pPI = Abc_NtkPi(pNtk, i);
  if (pPI == NULL) {
      Abc_Print(-1, "Internal error: Abc_NtkPi returned NULL for i=%d\n", i);
      return 1;
  }
  // DdNode * x = Cudd_bddIthVar(dd, i);   // BUT the index may be different
  // DdNode * x = (DdNode *)pPI->pData; // BUT pData==NULL

  // std::map<int, int> id2idx;
  int idx = -1;
  for (int j = 0; j < Abc_ObjFaninNum(pRoot); j++)
  {
    // id2idx[Abc_ObjFaninId(pRoot, j) - 1] = j;
    if (Abc_ObjFaninId(pRoot, j) == i + 1) idx = j;
  }

  if(idx == -1)
  {
    printf("independent\n");
    Cudd_RecursiveDeref(dd, f);
    return 0;
  }
  DdNode *x = Cudd_bddIthVar(dd, idx);
    if (x == NULL) {
      Abc_Print(-1, "Internal error: PI's pData is NULL (BDD var not set for PI %d)\n", i);
      return 1;
  }
  // Abc_Print(-2, "DEBUG: PI i=%d id=%d pPI=%p\n", i, idx, (void*)x);
  Cudd_Ref(x);

  // cofactor f with respect to x
  DdNode * f_x1 = Cudd_Cofactor(dd, f, x); 
  Cudd_Ref(f_x1);
  DdNode * f_x0 = Cudd_Cofactor(dd, f, Cudd_Not(x)); 
  Cudd_Ref(f_x0);

  // check unate property
  int is_pos_unate = Cudd_bddLeq(dd, f_x0, f_x1); // f_x0 <= f_x1
  int is_neg_unate = Cudd_bddLeq(dd, f_x1, f_x0); // f_x1 <= f_x0

  // print result
  if(is_pos_unate && is_neg_unate) {
    Abc_Print(-2, "independent\n");
  } else if(is_pos_unate) {
    Abc_Print(-2, "positive unate\n");
  } else if(is_neg_unate) {
    Abc_Print(-2, "negative unate\n");
  } else {
    Abc_Print(-2, "binate\n");
    // find patterns
    int nVars  = Cudd_ReadSize(dd);
    char *raw = (char*)malloc(nVars + 1);
    if(raw == NULL) {
      Abc_Print(-1, "Error: memory allocation failed for cube1.\n");
    }
    raw[nVars] = '\0';

    DdNode *pattern1 = Cudd_bddAnd(dd, f_x1, Cudd_Not(f_x0)); 
    Cudd_Ref(pattern1);
    int ok1 = Cudd_bddPickOneCube(dd, pattern1, raw);
    if(!ok1) {
      Abc_Print(-1, "Error: failed to pick one cube from pattern1.\n");
    }
    // get only PI, the first pi_num variables
    char *cube1 = (char*)malloc(pi_num + 1);
    for (int j = 0; j < pi_num; ++j) {
        if      (raw[j] == '0') cube1[j] = '0';
        else if (raw[j] == '1') cube1[j] = '1';
        else                    cube1[j] = '2'; // '2' => don't care
    }
    cube1[pi_num] = '\0';
    cube1[i] = '-'; // set xi free
    Abc_Print(-2, "cube1: %s\n", cube1);

    DdNode *pattern2 = Cudd_bddAnd(dd, f_x0, Cudd_Not(f_x1)); 
    Cudd_Ref(pattern2);
    char *cube2 = (char*)malloc(pi_num + 1);
    cube2[pi_num] = '\0';
    int ok2 = Cudd_bddPickOneCube(dd, pattern2, raw);
    if(!ok2) {
      Abc_Print(-1, "Error: failed to pick one cube from pattern2.\n");
    }
    for (int j = 0; j < pi_num; ++j) {
        if      (raw[j] == '0') cube2[j] = '0';
        else if (raw[j] == '1') cube2[j] = '1';
        else                    cube2[j] = '2'; // '2' => don't care
    }
    cube2[i] = '-'; // set xi free
    Abc_Print(-2, "cube2: %s\n", cube1);
    Cudd_RecursiveDeref(dd, pattern1);
    Cudd_RecursiveDeref(dd, pattern2);
    free(cube1);
    free(cube2);
  }    

  // free
  Cudd_RecursiveDeref(dd, f);
  Cudd_RecursiveDeref(dd, f_x1);
  Cudd_RecursiveDeref(dd, f_x0);

  return 0;
}
/*
int Lsv_CommandUnate(Abc_Frame_t* pAbc, int argc, char** argv) {
  // 0. check if everything is valid
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  assert(Abc_NtkIsBddLogic(pNtk));

  if(argc != 3) {
    Abc_Print(-1, "Wrong number of arguments.\n");
    Abc_Print(-2, "usage: lsv_unate_bdd <k> <i> [-h]\n");
    Abc_Print(-2, "\t        whether the function of yk is binate, positive unate, negative unate in xi, or independent of xi\n");
    Abc_Print(-2, "\t-h    : print the command usage\n");
    return 1;
  }
  int k = atoi(argv[1]);
  int i = atoi(argv[2]);
  printf("DEBUG: k=%d, i=%d\n", k, i);
  // check if k < Abc_NtkPoNum(pNtk) && i < Abc_NtkPiNum(pNtk)
  int pi_num = Abc_NtkPiNum(pNtk);
  printf("DEBUG: pi_num=%d\n", pi_num);
  if(k >= Abc_NtkPoNum(pNtk) || i >= pi_num || k < 0 || i < 0) {
    Abc_Print(-1, "Invalid k or i value.\n");
    Abc_Print(-2, "usage: lsv_unate_bdd <k> <i>\n");
    Abc_Print(-2, "\t        k should be less than number of POs (%d), i should be less than number of PIs (%d)\n", Abc_NtkPoNum(pNtk), Abc_NtkPiNum(pNtk));
    return 1;
  }

  // 1. Ensure network is strashed (AIG)
  if ( !Abc_NtkIsStrash( pNtk ) ) {
      printf( "Converting current network to a strashed AIG...\n" );
      pNtk = Abc_NtkStrash( pNtk, 0, 1, 0 );
      if ( pNtk == NULL ) {
          printf( "Strashing failed.\n" );
          return 1;
      }
      Abc_FrameReplaceCurrentNetwork( pAbc, pNtk );
  }
  // 2. Build global BDDs if not already present
  if ( Abc_NtkGlobalBddMan( pNtk ) == NULL ) {
      int nBddSizeMax   = 10000000; // size limit
      int fDropInternal = 1;        // drop internal-node BDDs
      int fReorder      = 1;        // enable reordering
      int fVerbose      = 0;

      if ( Abc_NtkBuildGlobalBdds( pNtk,
                                    nBddSizeMax,
                                    fDropInternal,
                                    fReorder,
                                    fVerbose ) == NULL ) {
          printf( "BDD construction aborted (likely BDD blow-up).\n" );
          return 1;
      }
  }
  // 3. Grab manager and the BDDs you need
  DdManager *dd = Abc_NtkGlobalBddMan( pNtk );
  if ( dd == NULL ) {
      printf( "Internal error: no BDD manager.\n" );
      return 1;
  }


}
*/
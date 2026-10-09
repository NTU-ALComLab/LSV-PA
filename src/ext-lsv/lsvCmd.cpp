#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "bdd/cudd/cudd.h"
#include <bits/stdc++.h>
using namespace std;

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandLsv(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv", Lsv_CommandLsv, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

struct Cut{
    int ids[6];
    int size;
};

// Keep the nodes in a cut in ascending order when taking union
int unionCut(const Cut& a, const Cut& b, int k, Cut& out) {
  int i = 0, j = 0;
  out.size = 0;
  while (i < a.size || j < b.size) {
    int x;
    if (i == a.size) {
      x = b.ids[j++];
    }
    else if (j == b.size) {
      x = a.ids[i++];
    }
    else if (a.ids[i] < b.ids[j]) {
      x = a.ids[i++];
    }
    else if (a.ids[i] > b.ids[j]) {
      x = b.ids[j++];
    }
    else {
      x = a.ids[i]; i++; j++;
    }
    if (out.size >= k)
      return k + 1;
    out.ids[out.size++] = x;
  }
  return out.size;
}

// Notice that the answer in the example is ascending, this is for sort
bool cutLess(Cut& a, Cut& b) {
  if (a.size != b.size)
    return a.size < b.size;
  for (int i = 0; i < a.size; ++i) {
    if (a.ids[i] != b.ids[i])
      return a.ids[i] > b.ids[i];
  }
  return false;
}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct CutEnumerator{
    int k;
    vector<vector<Cut>> cache; //We memorized all cuts that have already been calculated
    vector<unsigned char> ready;
};

void cutInit(CutEnumerator* state, Abc_Ntk_t* ntk, int k) {
    int n = Abc_NtkObjNumMax(ntk);
    state->k = k;
    state->cache.resize(n);
    state->ready.assign(n, 0);
}

const vector<Cut>* cutGet(CutEnumerator* state, Abc_Obj_t* obj) {
  int id = Abc_ObjId(obj);
  if (state->ready[id] == 1)
    return &state->cache[id]; //If we already calculate this object, than return it directly
  state->ready[id] = 1;
  vector<Cut>* result = &state->cache[id];
  if (obj->Type == ABC_OBJ_CONST1) { //This is a always true node 
    Cut empty = {};
    result->push_back(empty);
  }else if (!Abc_AigNodeIsAnd(obj)) { //THis is a leaf node
    Cut c = {};
    c.ids[0] = id;
    c.size = 1;
    result->push_back(c);
  }else{
    Cut c = {};
    c.ids[0] = id;
    c.size = 1;
    result->push_back(c);
        
    const vector<Cut>* left = cutGet(state, Abc_ObjFanin0(obj)); //Left child
    const vector<Cut>* right = cutGet(state, Abc_ObjFanin1(obj)); //Right child
    int l = left->size(); int r = right->size();
    for (size_t i = 0; i < l; ++i) {
      for (size_t j = 0; j < r; ++j) {
        Cut combined = {};
        int union_size=unionCut((*left)[i], (*right)[j], state->k, combined);
        if(union_size<=state->k)
          result->push_back(combined);
      }
    }
  }
  sort(result->begin(), result->end(), cutLess);
  vector<Cut> kept; 
  for (size_t i = 0; i < result->size(); i++) {
    if (kept.empty() || cutLess(kept.back(), (*result)[i])) {
      kept.push_back((*result)[i]);
    }
  }
  result->swap(kept);
  return result;
}

int truthCalculate(Abc_Ntk_t* ntk, Abc_Obj_t* root, const Cut* cut, uint64_t* output) {
  int n = Abc_NtkObjNumMax(ntk);
  int count = 1 << cut->size; //count from 000000 to 111111
  int table[64] = {}; //There are at most 64 bits
  vector<int> leafPos(n, -1);
  vector<int> value(n, 0);
  vector<int> done(n, 0);
  for (int i = 0; i < cut->size; i++)
    leafPos[cut->ids[i]] = i;
  for (int j = 0; j < count; j++) {
    fill(done.begin(), done.end(), 0);
    vector<Abc_Obj_t*> st;
    st.push_back(root);
    while (!st.empty()) {
      Abc_Obj_t* obj = st.back();
      int id = Abc_ObjId(obj);
      if (done[id]) {
        st.pop_back();
        continue;
      }
      if (leafPos[id] != -1) {
        int p = leafPos[id];
        value[id] = (j >> (cut->size - 1 - p)) & 1;
        done[id] = 1;
        st.pop_back();
        continue;
      }
      if (obj->Type == ABC_OBJ_CONST1) {
        value[id] = 1;
        done[id] = 1;
        st.pop_back();
        continue;
      }
      //Non-leaf node error handling
      if (!Abc_AigNodeIsAnd(obj))
        return 0;
      Abc_Obj_t* left = Abc_ObjFanin0(obj);
      Abc_Obj_t* right = Abc_ObjFanin1(obj);
      int l = Abc_ObjId(left);
      int r = Abc_ObjId(right);
      if (!done[l]) {
        st.push_back(left);
        continue;
      }
      if (!done[r]) {
        st.push_back(right);
        continue;
      }
      int a = value[l];
      int b = value[r];
      if (Abc_ObjFaninC0(obj))
        a = !a;
      if (Abc_ObjFaninC1(obj))
        b = !b;
      value[id] = a & b;
      done[id] = 1;
      st.pop_back();
      }
      table[j] = value[Abc_ObjId(root)];
  }
  uint64_t ans = 0;
  for (int i=count-1; i>=0; i--) {
    ans*=2;
    ans+= table[i];
  }
  *output = ans;
  return 1;
}

//This one is easier since we have CUDD stuff 
DdNode* buildBdd(DdManager* manager, uint64_t truth, int offset, int length, int level){
  uint64_t bits = truth >> offset;
  uint64_t mask = (length == 64) ? UINT64_MAX : ((uint64_t(1) << length) - 1);
  if ((bits & mask) == 0) {
    DdNode* zero = Cudd_ReadLogicZero(manager);
    Cudd_Ref(zero);
    return zero;
  }
  if ((bits & mask) == mask) {
    DdNode* one = Cudd_ReadOne(manager);
    Cudd_Ref(one);
    return one;
  }
  int half = length / 2;
  DdNode* low = buildBdd(manager, truth, offset, half, level + 1);
  if (low == NULL)
    return NULL;
  DdNode* high = buildBdd(manager, truth, offset + half, half, level + 1);
  if (high == NULL) {
    Cudd_RecursiveDeref(manager, low);
    return NULL;
  }
  DdNode* node = Cudd_bddIte(manager, Cudd_bddIthVar(manager, level),high, low);
  if (node != NULL)
    Cudd_Ref(node);
  Cudd_RecursiveDeref(manager, low);
  Cudd_RecursiveDeref(manager, high);
  return node;
}

void printCut(int root, const Cut& cut){
  printf("%d: ", root);
  for (int j = 0; j < cut.size; j++) {
    if (j > 0)
      printf(" ");
    printf("%d", cut.ids[j]);
  }
  printf(": ");
}

int Lsv_CommandLsv(Abc_Frame_t* pAbc, int argc, char** argv) {
  if (argc != 4 || strcmp(argv[1], "cut") != 0 || (strcmp(argv[2], "tt") != 0 && strcmp(argv[2], "bddsize") != 0)) {
    Abc_Print(-2, "usage: lsv cut tt <k>\n       lsv cut bddsize <k>\n");
    return 1;
  }
  char* end;
  long k = strtol(argv[3], &end, 10);
  if (end == argv[3] || *end != '\0' || k < 2 || k > 6) {
    Abc_Print(-2, "k must be an integer in [2, 6].\n");
    return 1;
  }
  Abc_Ntk_t* ntk = Abc_FrameReadNtk(pAbc);
  if (ntk == NULL) {
    Abc_Print(-1, "Empty network. Read a BLIF first.\n");
    return 1;
  }
  if (!Abc_NtkIsStrash(ntk)) {
    Abc_Print(-1, "An AIG is required. Run 'strash' first.\n");
    return 1;
  }
  int bddMode = strcmp(argv[2], "bddsize") == 0;
  DdManager* manager = NULL;
  if (bddMode) {
    manager = Cudd_Init((int)k, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);
    if (manager == NULL) {
      Abc_Print(-1, "Unable to initialize CUDD.\n");
      return 1;
    }
    Cudd_AutodynDisable(manager);
  }
  CutEnumerator cuts;
  cutInit(&cuts, ntk, (int)k);
  int status = 0;
  Abc_Obj_t* node;
  int index;
  Abc_AigForEachAnd(ntk, node, index) {
    const vector<Cut>* nodeCuts = cutGet(&cuts, node);
    for (size_t i = 0; i < nodeCuts->size(); i++) {
      const Cut* cut = &(*nodeCuts)[i];
      uint64_t truth = 0;
      if (!truthCalculate(ntk, node, cut, &truth)) {
        Abc_Print(-1, "Invalid cut at AIG node %d.\n", Abc_ObjId(node));
        status = 1;
        break;
      }
      int size = 0;
      if (bddMode) {
        DdNode* bdd = buildBdd(manager, truth, 0, 1 << cut->size, 0);
        if (bdd == NULL) {
          Abc_Print(-1, "BDD creation failed at node %d.\n", Abc_ObjId(node));
          status = 1;
          break;
        }
        size = Cudd_DagSize(bdd);
        Cudd_RecursiveDeref(manager, bdd);
      }
      printCut(Abc_ObjId(node), *cut);
      if (bddMode)
        printf("%d\n", size);
      else
        printf("%llX\n", (unsigned long long)truth);
    }
    if (status)
      break;
  }
  if (manager != NULL)
    Cudd_Quit(manager);
  return status;
}

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
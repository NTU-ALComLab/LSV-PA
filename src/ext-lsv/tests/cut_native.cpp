#include "../lsvCmd.cpp"

int main(int argc, char** argv) {
  Abc_Start();
  Abc_Frame_t* frame = Abc_FrameGetGlobalFrame();
  Abc_FrameReplaceCurrentNetwork(frame, Abc_NtkAlloc(ABC_NTK_STRASH, ABC_FUNC_AIG, 1));
  for (int k = 2; k <= 6; ++k) {
    for (const char* command : {"lsv_cut_tt", "lsv_cut_bddsize"}) {
      char script[64];
      snprintf(script, sizeof(script), "%s %d", command, k);
      assert(Cmd_CommandExecute(frame, script) == 0);
    }
  }
  puts("EMPTY_NETWORK_PASSED");
  Abc_Ntk_t* network = Abc_NtkAlloc(ABC_NTK_STRASH, ABC_FUNC_AIG, 1);
  Abc_Aig_t* aig = static_cast<Abc_Aig_t*>(network->pManFunc);
  Abc_Obj_t* x = Abc_NtkCreatePi(network);
  Abc_Obj_t* y = Abc_NtkCreatePi(network);
  Abc_Obj_t* z = Abc_NtkCreatePi(network);
  Abc_Obj_t* old = Abc_AigAnd(aig, x, y);
  Abc_Obj_t* root = Abc_AigAnd(aig, old, z);
  Abc_ObjAddFanin(Abc_NtkCreatePo(network), root);
  Abc_Obj_t* replacement = Abc_AigAnd(aig, x, Abc_ObjNot(y));
  Abc_AigReplace(aig, old, replacement, 1);
  Abc_Obj_t* dangling = Abc_AigAnd(aig, y, z);
  assert(Abc_ObjId(root) < Abc_ObjId(replacement));
  assert(Abc_ObjFanoutNum(dangling) == 0);
  Abc_FrameReplaceCurrentNetwork(frame, network);
  const int objects = Abc_NtkObjNumMax(network);
  const int fanin0 = Abc_ObjFaninId0(root);
  const int fanin1 = Abc_ObjFaninId1(root);
  printf("IDS %d %d %d %d %d %d\n", Abc_ObjId(x), Abc_ObjId(y),
         Abc_ObjId(z), Abc_ObjId(root), Abc_ObjId(replacement), Abc_ObjId(dangling));
  for (int k = 2; k <= 6; ++k) {
    for (const char* command : {"lsv_cut_tt", "lsv_cut_bddsize"}) {
      printf("CASE %s %d\n", command, k);
      char script[64];
      snprintf(script, sizeof(script), "%s %d", command, k);
      assert(Cmd_CommandExecute(frame, script) == 0);
      assert(Abc_FrameReadNtk(frame) == network);
      assert(Abc_NtkObjNumMax(network) == objects);
      assert(Abc_ObjFaninId0(root) == fanin0 && Abc_ObjFaninId1(root) == fanin1);
    }
  }

  Cut constant;
  constant.truth = 1;
  Cut six;
  six.size = 6;
  for (int i = 0; i < 6; ++i)
    six.leaves[i] = i + 1;
  assert(RemapTruth(constant, six) == UINT64_MAX);
  assert(TruthMask(0) == 1 && TruthMask(6) == UINT64_MAX);

  DdManager* manager = Cudd_Init(6, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);
  assert(manager);
  Cudd_AutodynDisable(manager);
  uint64_t random = 983;
  for (int width = 0; width <= 6; ++width) {
    for (int sample = 0; sample < 128; ++sample) {
      random ^= random << 13;
      random ^= random >> 7;
      random ^= random << 17;
      const uint64_t truth = random & TruthMask(width);
      DdNode* bdd = BuildBdd(manager, truth, width, 0);
      assert(bdd);
      for (int assignment = 0; assignment < (1 << width); ++assignment) {
        int values[6] = {};
        for (int variable = 0; variable < width; ++variable)
          values[variable] = (assignment >> (width - 1 - variable)) & 1;
        DdNode* value = Cudd_Eval(manager, bdd, values);
        assert(value == Cudd_NotCond(Cudd_ReadOne(manager),
                                    ((truth >> assignment) & 1) == 0));
      }
      Cudd_RecursiveDeref(manager, bdd);
      assert(Cudd_CheckZeroRef(manager) == 0);
    }
  }
  Cudd_Quit(manager);
  Abc_Stop();
  puts("NATIVE_CHECKS_PASSED");
  return 0;
}

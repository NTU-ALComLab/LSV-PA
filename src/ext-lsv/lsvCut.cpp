#include "lsvCut.h"

#include "base/abc/abc.h"

#ifdef ABC_USE_CUDD
#include "bdd/cudd/cudd.h"
#endif

#include <algorithm>
#include <cerrno>
#include <cinttypes>
#include <cstdint>
#include <cstdlib>
#include <functional>
#include <limits>
#include <unordered_set>
#include <vector>

// This file implements cut storage, union, truth-table simulation, and Shannon expansion.
// ABC provides the command interface and AIG access; CUDD provides general BDD operations.
namespace {

constexpr unsigned kMaxCutInputs = 6;

enum class CutOutput {
  TruthTable,
  BddSize,
};

// Active leaves have strictly increasing IDs; unused slots are ignored in equality and hashing.
struct Cut {
  unsigned size = 0;
  int leaves[kMaxCutInputs] = {};

  bool operator==(const Cut& other) const {
    if (size != other.size) {
      return false;
    }
    return std::equal(leaves, leaves + size, other.leaves);
  }
};

struct CutHash {
  std::size_t operator()(const Cut& cut) const {
    std::size_t hash = cut.size;
    for (unsigned leaf_index = 0; leaf_index < cut.size; ++leaf_index) {
      const std::size_t leaf_hash = std::hash<int>()(cut.leaves[leaf_index]);
      hash ^= leaf_hash + 0x9e3779b9u + (hash << 6) + (hash >> 2);
    }
    return hash;
  }
};

Cut UnitCut(int node_id) {
  Cut cut;
  cut.size = 1;
  cut.leaves[0] = node_id;
  return cut;
}

// Merge sorted leaf sets with two cursors, inserting each ID once.
// Reset the output and reject unions larger than k; edge polarity does not affect leaves.
bool MergeCuts(const Cut& left, const Cut& right, unsigned cut_limit,
               Cut& merged) {
  merged = Cut();
  unsigned left_position = 0;
  unsigned right_position = 0;

  while (left_position < left.size || right_position < right.size) {
    int next_leaf;
    if (left_position == left.size) {
      next_leaf = right.leaves[right_position];
      ++right_position;
    } else if (right_position == right.size) {
      next_leaf = left.leaves[left_position];
      ++left_position;
    } else if (left.leaves[left_position] < right.leaves[right_position]) {
      next_leaf = left.leaves[left_position];
      ++left_position;
    } else if (right.leaves[right_position] < left.leaves[left_position]) {
      next_leaf = right.leaves[right_position];
      ++right_position;
    } else {
      next_leaf = left.leaves[left_position];
      ++left_position;
      ++right_position;
    }

    if (merged.size == cut_limit) {
      return false;
    }
    merged.leaves[merged.size] = next_leaf;
    ++merged.size;
  }
  return true;
}

// n inputs require 2^n output bits; handle six inputs separately to avoid shifting by 64.
std::uint64_t TruthMask(unsigned input_count) {
  const unsigned output_bits = 1u << input_count;
  if (output_bits == 64) {
    return std::numeric_limits<std::uint64_t>::max();
  }
  return (std::uint64_t(1) << output_bits) - 1;
}

bool IsTwoInputAndNode(Abc_Obj_t* node) {
  if (!Abc_ObjIsNode(node)) {
    return false;
  }
  return Abc_ObjFaninNum(node) == 2;
}

class CutEngine {
 public:
  CutEngine(Abc_Ntk_t* network, unsigned cut_limit)
      : network_(network),
        cut_limit_(cut_limit),
        cuts_by_node_(Abc_NtkObjNumMax(network)),
        cuts_complete_(cuts_by_node_.size(), false),
        simulation_values_(cuts_by_node_.size(), 0),
        simulation_generations_(cuts_by_node_.size(), 0) {
    InitializeInputTruthTables();
  }

  bool Enumerate() {
    InitializeBaseCuts();

    // Visit all internal nodes, including dangling nodes, without assuming topological ID order.
    Abc_Obj_t* node;
    int node_index;
    Abc_NtkForEachNode(network_, node, node_index) {
      const int node_id = Abc_ObjId(node);
      if (cuts_complete_[node_id]) {
        continue;
      }
      if (!CompleteCutCone(node)) {
        return false;
      }
    }
    return true;
  }

  const std::vector<Cut>& CutsForNode(int node_id) const {
    return cuts_by_node_[node_id];
  }

  bool ComputeTruthTable(Abc_Obj_t* root, const Cut& cut,
                         std::uint64_t& truth) {
    BeginSimulationGeneration();
    const std::uint64_t active_mask = TruthMask(cut.size);
    InitializeCutBoundary(cut, active_mask);

    // Mark every cut leaf first so all reconvergent paths stop at the same boundary.
    // Simulate the root cone again; existing fanin-cut tables cannot be combined directly.
    work_stack_.clear();
    work_stack_.push_back(root);
    while (!work_stack_.empty()) {
      Abc_Obj_t* node = work_stack_.back();
      const int node_id = Abc_ObjId(node);
      if (simulation_generations_[node_id] == current_generation_) {
        work_stack_.pop_back();
        continue;
      }
      if (!IsTwoInputAndNode(node)) {
        // Reaching a CI outside the leaf set means the cut misses an input path.
        return false;
      }

      Abc_Obj_t* left_fanin = Abc_ObjFanin0(node);
      Abc_Obj_t* right_fanin = Abc_ObjFanin1(node);
      const int left_id = Abc_ObjId(left_fanin);
      const int right_id = Abc_ObjId(right_fanin);
      if (simulation_generations_[left_id] != current_generation_) {
        work_stack_.push_back(left_fanin);
        continue;
      }
      if (simulation_generations_[right_id] != current_generation_) {
        work_stack_.push_back(right_fanin);
        continue;
      }

      // Invert only active bits on complemented edges, then evaluate the node with bitwise AND.
      std::uint64_t left_truth = simulation_values_[left_id];
      if (Abc_ObjFaninC0(node)) {
        left_truth ^= active_mask;
      }
      std::uint64_t right_truth = simulation_values_[right_id];
      if (Abc_ObjFaninC1(node)) {
        right_truth ^= active_mask;
      }
      simulation_values_[node_id] = left_truth & right_truth;
      simulation_generations_[node_id] = current_generation_;
      work_stack_.pop_back();
    }

    truth = simulation_values_[Abc_ObjId(root)];
    return true;
  }

 private:
  void InitializeInputTruthTables() {
    // The smallest leaf ID is the most significant input bit; assignment 0 maps to output bit 0.
    // For two inputs, the variable tables are C and A; their AND table is 8.
    for (unsigned input_count = 1; input_count <= kMaxCutInputs;
         ++input_count) {
      const unsigned assignment_count = 1u << input_count;
      for (unsigned input_index = 0; input_index < input_count; ++input_index) {
        const unsigned input_bit = input_count - 1 - input_index;
        for (unsigned assignment = 0; assignment < assignment_count;
             ++assignment) {
          const bool input_is_one = ((assignment >> input_bit) & 1u) != 0;
          if (input_is_one) {
            input_truth_tables_[input_count][input_index] |=
                std::uint64_t(1) << assignment;
          }
        }
      }
    }
  }

  void InitializeBaseCuts() {
    // Each CI (PI or register output) has a singleton cut; constant 1 has an empty cut.
    // These base cuts support enumeration and are not printed by the commands.
    Abc_Obj_t* input;
    int input_index;
    Abc_NtkForEachCi(network_, input, input_index) {
      const int input_id = Abc_ObjId(input);
      cuts_by_node_[input_id].push_back(UnitCut(input_id));
      cuts_complete_[input_id] = true;
    }

    const int constant_id = Abc_ObjId(Abc_AigConst1(network_));
    cuts_by_node_[constant_id].push_back(Cut());
    cuts_complete_[constant_id] = true;
  }

  bool CompleteCutCone(Abc_Obj_t* root) {
    // An explicit postorder stack completes both fanins without deep C++ recursion.
    work_stack_.clear();
    work_stack_.push_back(root);
    while (!work_stack_.empty()) {
      Abc_Obj_t* node = work_stack_.back();
      const int node_id = Abc_ObjId(node);
      if (cuts_complete_[node_id]) {
        work_stack_.pop_back();
        continue;
      }
      if (!IsTwoInputAndNode(node)) {
        return false;
      }

      Abc_Obj_t* left_fanin = Abc_ObjFanin0(node);
      Abc_Obj_t* right_fanin = Abc_ObjFanin1(node);
      if (!cuts_complete_[Abc_ObjId(left_fanin)]) {
        work_stack_.push_back(left_fanin);
        continue;
      }
      if (!cuts_complete_[Abc_ObjId(right_fanin)]) {
        work_stack_.push_back(right_fanin);
        continue;
      }

      EnumerateNodeCuts(node);
      work_stack_.pop_back();
    }
    return true;
  }

  void EnumerateNodeCuts(Abc_Obj_t* node) {
    const int node_id = Abc_ObjId(node);
    const int left_id = Abc_ObjId(Abc_ObjFanin0(node));
    const int right_id = Abc_ObjId(Abc_ObjFanin1(node));
    std::vector<Cut>& node_cuts = cuts_by_node_[node_id];
    std::unordered_set<Cut, CutHash> seen_cuts;

    // Emit the unit cut first, then consider every pair of fanin cuts.
    // Reject only oversized or duplicate leaf sets; do not prune dominated cuts or limit their count.
    const Cut unit = UnitCut(node_id);
    node_cuts.push_back(unit);
    seen_cuts.insert(unit);
    for (const Cut& left_cut : cuts_by_node_[left_id]) {
      for (const Cut& right_cut : cuts_by_node_[right_id]) {
        Cut merged;
        if (!MergeCuts(left_cut, right_cut, cut_limit_, merged)) {
          continue;
        }
        const bool is_new_cut = seen_cuts.insert(merged).second;
        if (!is_new_cut) {
          continue;
        }
        node_cuts.push_back(merged);
      }
    }

    // The vector preserves insertion order independently of hash-container iteration order.
    cuts_complete_[node_id] = true;
  }

  void BeginSimulationGeneration() {
    // Generation tags allow cached values only within the current cut, avoiding full resets.
    // Unsigned wraparound reaches 0; clear old tags and restart at 1.
    ++current_generation_;
    if (current_generation_ == 0) {
      std::fill(simulation_generations_.begin(), simulation_generations_.end(),
                0);
      current_generation_ = 1;
    }
  }

  void InitializeCutBoundary(const Cut& cut, std::uint64_t active_mask) {
    const int constant_id = Abc_ObjId(Abc_AigConst1(network_));
    simulation_values_[constant_id] = active_mask;
    simulation_generations_[constant_id] = current_generation_;

    // Use the actual leaf count, with k only as an upper bound; each leaf is an independent input.
    for (unsigned leaf_index = 0; leaf_index < cut.size; ++leaf_index) {
      const int leaf_id = cut.leaves[leaf_index];
      simulation_values_[leaf_id] = input_truth_tables_[cut.size][leaf_index];
      simulation_generations_[leaf_id] = current_generation_;
    }
  }

  // Private arrays use ABC object IDs as indices, including gaps between IDs.
  // AIG edges, pData, pCopy, traversal IDs, and ABC flags remain unchanged.
  Abc_Ntk_t* network_;
  unsigned cut_limit_;
  std::vector<std::vector<Cut>> cuts_by_node_;
  std::vector<bool> cuts_complete_;
  std::vector<std::uint64_t> simulation_values_;
  std::vector<unsigned> simulation_generations_;
  std::vector<Abc_Obj_t*> work_stack_;
  unsigned current_generation_ = 0;
  std::uint64_t input_truth_tables_[kMaxCutInputs + 1][kMaxCutInputs] = {};
};

#ifdef ABC_USE_CUDD
// Build the BDD with our own Shannon expansion: f = x ? f(x=1) : f(x=0).
// The returned root has a Cudd_Ref; the caller must release it with Cudd_RecursiveDeref.
DdNode* BuildBdd(DdManager* manager, std::uint64_t truth,
                 unsigned remaining_inputs, unsigned level) {
  if (truth == 0) {
    DdNode* zero = Cudd_ReadLogicZero(manager);
    Cudd_Ref(zero);
    return zero;
  }
  if (truth == TruthMask(remaining_inputs)) {
    DdNode* one = Cudd_ReadOne(manager);
    Cudd_Ref(one);
    return one;
  }

  // The smallest ID is the most significant input; the low/high table halves are x=0/x=1.
  // Constant cases have already returned, so at least one input remains here.
  const unsigned next_input_count = remaining_inputs - 1;
  const unsigned half_bits = 1u << next_input_count;
  const unsigned next_level = level + 1;
  const std::uint64_t low_truth = truth & TruthMask(next_input_count);
  const std::uint64_t high_truth = truth >> half_bits;

  DdNode* low = BuildBdd(manager, low_truth, next_input_count, next_level);
  if (!low) {
    return nullptr;
  }
  DdNode* high = BuildBdd(manager, high_truth, next_input_count, next_level);
  if (!high) {
    Cudd_RecursiveDeref(manager, low);
    return nullptr;
  }

  // ITE takes (condition, true branch, false branch), hence (x, high, low).
  // Reduction may return a child; reference the result before releasing either child root.
  DdNode* variable = Cudd_bddIthVar(manager, level);
  DdNode* result = Cudd_bddIte(manager, variable, high, low);
  if (result) {
    Cudd_Ref(result);
  }
  Cudd_RecursiveDeref(manager, low);
  Cudd_RecursiveDeref(manager, high);
  return result;
}

// Each BDD command owns a manager, released by RAII on every return path.
// Cuts share that manager; variable indices represent leaf ID ranks within each cut.
class BddManager {
 public:
  BddManager(unsigned variables, CutOutput output) : manager_(nullptr) {
    if (output == CutOutput::BddSize) {
      manager_ = Cudd_Init(variables, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);
    }
  }

  ~BddManager() {
    if (manager_) {
      Cudd_Quit(manager_);
    }
  }

  DdManager* Get() const {
    return manager_;
  }

 private:
  DdManager* manager_;
};
#endif

const char* CommandName(CutOutput output) {
  if (output == CutOutput::BddSize) {
    return "lsv_cut_bddsize";
  }
  return "lsv_cut_tt";
}

void PrintCutUsage(CutOutput output) {
  Abc_Print(-2, "usage: %s <k>\n", CommandName(output));
  Abc_Print(-2, "       enumerate all internal-node cuts, with 1 <= k <= 6\n");
}

bool ParseCutLimit(const char* argument, unsigned& cut_limit) {
  // Validate integer parsing, trailing characters, and overflow; accept k=1 in addition to k=2..6.
  errno = 0;
  char* end = nullptr;
  const long parsed_limit = std::strtol(argument, &end, 10);
  if (errno != 0) {
    return false;
  }
  if (end == argument) {
    return false;
  }
  if (*end != '\0') {
    return false;
  }
  if (parsed_limit < 1 || parsed_limit > kMaxCutInputs) {
    return false;
  }
  cut_limit = static_cast<unsigned>(parsed_limit);
  return true;
}

void PrintCutResult(int root_id, const Cut& cut, CutOutput output,
                    std::uint64_t truth, int bdd_size) {
  // Format: root: increasing leaf IDs: value; an empty cut has an empty leaf field.
  // Print truth tables as uppercase hexadecimal without 0x, and BDD sizes as decimal.
  Abc_Print(1, "%d:", root_id);
  for (unsigned leaf_index = 0; leaf_index < cut.size; ++leaf_index) {
    Abc_Print(1, " %d", cut.leaves[leaf_index]);
  }
  if (output == CutOutput::BddSize) {
    Abc_Print(1, ": %d\n", bdd_size);
  } else {
    Abc_Print(1, ": %" PRIX64 "\n", truth);
  }
}

int RunCutCommand(Abc_Frame_t* frame, int argc, char** argv, CutOutput output) {
  Extra_UtilGetoptReset();
  const int option = Extra_UtilGetopt(argc, argv, "h");
  if (option != EOF) {
    PrintCutUsage(output);
    return 1;
  }
  if (argc != globalUtilOptind + 1) {
    PrintCutUsage(output);
    return 1;
  }

  unsigned cut_limit;
  if (!ParseCutLimit(argv[globalUtilOptind], cut_limit)) {
    Abc_Print(-1, "k must be an integer between 1 and 6.\n");
    return 1;
  }

  // Require read and strash first; this command only reads the current AIG.
  Abc_Ntk_t* network = Abc_FrameReadNtk(frame);
  if (!network) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  if (!Abc_NtkIsStrash(network)) {
    Abc_Print(-1, "Requires a structurally hashed AIG; run \"strash\" first.\n");
    return 1;
  }

#ifndef ABC_USE_CUDD
  // Keep truth-table support without CUDD; report the missing dependency for BDD output.
  if (output == CutOutput::BddSize) {
    Abc_Print(-1, "lsv_cut_bddsize requires ABC to be compiled with CUDD.\n");
    return 1;
  }
#else
  // Cudd_Init leaves dynamic reordering disabled, and this implementation keeps it disabled.
  // Variable indices follow increasing leaf IDs, so the smallest ID is tested first.
  BddManager manager(cut_limit, output);
  if (output == CutOutput::BddSize) {
    if (!manager.Get()) {
      Abc_Print(-1, "Could not initialize the BDD manager.\n");
      return 1;
    }
  }
#endif

  CutEngine engine(network, cut_limit);
  if (!engine.Enumerate()) {
    Abc_Print(-1, "Cut enumeration requires two-input AIG nodes.\n");
    return 1;
  }

  // Print only internal AND nodes; every unit cut has truth table 2.
  Abc_Obj_t* node;
  int node_index;
  Abc_NtkForEachNode(network, node, node_index) {
    const int node_id = Abc_ObjId(node);
    for (const Cut& cut : engine.CutsForNode(node_id)) {
      std::uint64_t truth;
      if (!engine.ComputeTruthTable(node, cut, truth)) {
        Abc_Print(-1, "Invalid cut boundary at node %d.\n", node_id);
        return 1;
      }

      int bdd_size = 0;
#ifdef ABC_USE_CUDD
      if (output == CutOutput::BddSize) {
        DdNode* bdd = BuildBdd(manager.Get(), truth, cut.size, 0);
        if (!bdd) {
          Abc_Print(-1, "BDD construction failed at node %d.\n", node_id);
          return 1;
        }
        // DagSize includes one physical terminal node, giving a single-variable function size 2.
        // Release this cut's root after measuring it; keep the manager until the command ends.
        bdd_size = Cudd_DagSize(bdd);
        Cudd_RecursiveDeref(manager.Get(), bdd);
      }
#endif
      PrintCutResult(node_id, cut, output, truth, bdd_size);
    }
  }
  return 0;
}

}  // namespace

// Both commands share cut enumeration and truth-table computation, selecting different output modes.
int Lsv_CommandCutTt(Abc_Frame_t* frame, int argc, char** argv) {
  return RunCutCommand(frame, argc, argv, CutOutput::TruthTable);
}

int Lsv_CommandCutBddSize(Abc_Frame_t* frame, int argc, char** argv) {
  return RunCutCommand(frame, argc, argv, CutOutput::BddSize);
}

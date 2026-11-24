#include "lsvKlFlex.h"
#include "lsvCut.h"

#include "sat/bsat/satSolver.h"
#include "sat/cnf/cnf.h"

#include <algorithm>
#include <cstdint>
#include <limits>
#include <memory>

// ABC C function: converts a strashed network into the AIG manager used by the CNF writers,
// keeping the PI/PO order. Both flags are 0 here because the network is combinational.
extern "C" Aig_Man_t *Abc_NtkToDar(Abc_Ntk_t *pNtk, int fExors, int fRegisters);

// Returns the signal in the new network that drives input index of obj: the copy of the old
// driver, complemented if the old edge is complemented. Used when copying ANDs and POs.
static Abc_Obj_t *CopyMiterFanin(const std::vector<Abc_Obj_t *> &copy,
                                Abc_Obj_t *obj, int index)
{
  int id = Abc_ObjId(Abc_ObjFanin(obj, index));
  return Abc_ObjNotCond(copy[id], Abc_ObjFaninC(obj, index));
}

// Builds the miter of pNtk for the given cut: an AIG that compares the outputs of the original
// circuit with those of the circuit whose roots are forced. The caller frees the network.
// Without a pattern, every root of the forced copy is a new PI p (in root order) that the queries
// fix by assumptions: one miter serves every root pattern. With a pattern c, the roots are the
// constants of c instead (the smallest-ID root is the MSB of c).
// PI order: [original PIs][p, only without a pattern]; PO order: [original leaves][diff].
// The CNF lookups rely on this order.
//
// With constants, Abc_AigAnd propagates them while building, and every forced node that ends up
// equal to its original counterpart is hashed into the same node, so the XORs of unaffected POs
// vanish. A SAT solver given PIs p = c only learns the values, not that the two copies of a node
// are equal, and has to rediscover those equalities by search; on large arithmetic circuits that
// makes queries several times slower. The price is one miter per c instead of one per cut.
static Abc_Ntk_t *BuildKlMiter(Abc_Ntk_t *pNtk, const KlCut &cut, std::optional<std::size_t> pattern)
{
  Abc_Ntk_t *miter = Abc_NtkAlloc(ABC_NTK_STRASH, ABC_FUNC_AIG, 1);
  miter->pName = Extra_UtilStrsav("lsv_kl_flex_miter");
  // manager builds the AND/XOR nodes of the new AIG. original[id] and forced[id] are the
  // signals of old node id in the two copies.
  auto *manager = static_cast<Abc_Aig_t *>(miter->pManFunc);
  std::vector<Abc_Obj_t *> original(Abc_NtkObjNumMax(pNtk), nullptr);
  std::vector<Abc_Obj_t *> forced(original.size(), nullptr);

  int constant = Abc_ObjId(Abc_AigConst1(pNtk));
  original[constant] = forced[constant] = Abc_AigConst1(miter);

  // Each original PI is created once and shared by both copies, so both see the same input.
  Abc_Obj_t *node;
  int i;
  Abc_NtkForEachPi(pNtk, node, i)
    original[Abc_ObjId(node)] = forced[Abc_ObjId(node)] = Abc_NtkCreatePi(miter);
  const std::size_t m = cut.roots.size();
  for (std::size_t j = 0; j < m; ++j)
    forced[cut.roots[j]] = pattern ? Abc_ObjNotCond(Abc_AigConst1(miter), !((*pattern >> (m - 1 - j)) & 1))
                                   : Abc_NtkCreatePi(miter);

  // nodes lists the internal ANDs in topological order, so both fanins of each AND already
  // have their signals in the miter when it is copied.
  Vec_Ptr_t *nodes = Abc_NtkDfs(pNtk, 1);
  Vec_PtrForEachEntry(Abc_Obj_t *, nodes, node, i)
  {
    int id = Abc_ObjId(node);
    original[id] = Abc_AigAnd(manager, CopyMiterFanin(original, node, 0), CopyMiterFanin(original, node, 1));
    // A forced[id] that is already set belongs to a root (its PI p or its constant). It stays so
    // even when another root lies in this root's fanin cone.
    if (!forced[id])
      forced[id] = Abc_AigAnd(manager, CopyMiterFanin(forced, node, 0), CopyMiterFanin(forced, node, 1));
  }
  Vec_PtrFree(nodes);

  // pairs holds original PO0, forced PO0, original PO1, forced PO1, and so on. Abc_AigMiter
  // XORs each pair and ORs the results, so diff = 1 iff some PO differs.
  Vec_Ptr_t *pairs = Vec_PtrAlloc(2 * Abc_NtkPoNum(pNtk));
  Abc_NtkForEachPo(pNtk, node, i)
  {
    Vec_PtrPush(pairs, CopyMiterFanin(original, node, 0));
    Vec_PtrPush(pairs, CopyMiterFanin(forced, node, 0));
  }
  Abc_Obj_t *diff = Abc_AigMiter(manager, pairs, 0);
  Vec_PtrFree(pairs);

  // Expose the original leaf values as POs so that the queries can constrain U = u. A leaf that
  // depends on a forced root may differ between the copies, so the original one is used.
  // diff is the last PO, after the leaves.
  for (int leaf : cut.leaves)
    Abc_ObjAddFanin(Abc_NtkCreatePo(miter), original[leaf]);
  Abc_ObjAddFanin(Abc_NtkCreatePo(miter), diff);
  return miter;
}

// Appends one assumption literal per variable, fixing the variables to the bits of value.
// The variables are in node-ID order, so the first variable takes the most significant bit.
static void AppendAssumptions(std::vector<lit> &assumptions,
                              const std::vector<int> &variables, std::size_t value)
{
  // For example, value = 011 with three variables gives var0 = 0, var1 = 1, var2 = 1.
  // The second argument of Abc_Var2Lit negates the literal, so fixing a variable to 0 passes 1.
  for (std::size_t i = 0; i < variables.size(); ++i)
  {
    bool bit = (value >> (variables.size() - 1 - i)) & 1;
    assumptions.push_back(Abc_Var2Lit(variables[i], !bit));
  }
}

// Turns nibbles (least significant first, four mask bits each) into an uppercase hexadecimal
// string without leading zeros; an all-zero mask gives "0". A nibble array also covers masks
// wider than 64 bits.
static std::string HexMask(const std::vector<unsigned char> &nibbles)
{
  const char digits[] = "0123456789ABCDEF";
  std::string result;
  // Write from the most significant nibble down and skip zeros until the first non-zero one.
  for (auto it = nibbles.rbegin(); it != nibbles.rend(); ++it)
    if (*it || !result.empty())
      result += digits[*it];
  return result.empty() ? "0" : result;
}

// originalRoots[u] is the root pattern that the circuit itself computes when the leaves take
// value u, numbered like the root patterns c. By K2 the roots are functions of the leaves, so
// simulating from the leaves with the PA1 truth tables is enough. PA1 also puts the leaf with
// the smallest ID in the most significant position, matching the numbering of u.
// The truth tables have 64 bits; with more than 6 leaves an empty vector is returned and the
// caller does not use this shortcut.
static std::vector<std::size_t> OriginalRootValues(Abc_Ntk_t *pNtk, const KlCut &cut)
{
  std::vector<std::size_t> values;
  if (cut.leaves.size() > 6)
    return values;
  Cut leaves;
  leaves.leaves = cut.leaves;
  std::vector<uint64_t> tables;
  for (int root : cut.roots)
    tables.push_back(Lsv_CutTt(Abc_NtkObj(pNtk, root), leaves));
  values.assign(std::size_t{1} << cut.leaves.size(), 0);
  for (std::size_t u = 0; u < values.size(); ++u)
    for (uint64_t table : tables)
      values[u] = (values[u] << 1) | ((table >> u) & 1); // the smallest-ID root ends up as the MSB
  return values;
}

// Runs one query on a solver. assumptions hold the literals for this query only. conflictLimit
// bounds the conflicts of this call (0 means no limit). Returns l_True, l_False, or l_Undef when
// the limit was reached.
static int SolveKlSat(sat_solver *solver, std::vector<lit> &assumptions, int conflictLimit = 0)
{
  lit *begin = assumptions.data();
  return sat_solver_solve(solver, begin, begin + assumptions.size(), conflictLimit, 0, 0, 0);
}

// Conflicts a forcing query may spend on the shared miter before it moves to the miter with
// constant roots. Easy queries finish far below this; the rest are worth a miter of their own.
static const int kSharedConflictLimit = 1000;

// Result of the simulation filter. seen[u]: some simulated input gives U = u. changed[u][c]:
// some simulated input with U = u changes a PO when the roots are forced to c.
struct FlexSimulation
{
  std::vector<char> seen;
  std::vector<std::vector<char>> changed;
};

// Answers most queries by simulation before any SAT call. Simulation can only prove existence:
// seeing U = u proves that u occurs, and seeing an output change proves that c is not allowed.
// Everything it does not prove is still decided by SAT, so the result is exactly the same as
// with SAT alone; the choice of inputs only affects how many queries are saved. The inputs are
// pseudo-random with a fixed seed, so every run behaves the same.
// Each uint64_t simulates 64 inputs at once, 64 * kWords inputs in total.
static FlexSimulation SimulateFlex(Abc_Ntk_t *pNtk, const KlCut &cut)
{
  const int kWords = 32;
  const std::size_t leafPatterns = std::size_t{1} << cut.leaves.size();
  const std::size_t rootPatterns = std::size_t{1} << cut.roots.size();
  FlexSimulation result;
  result.seen.assign(leafPatterns, 0);
  result.changed.assign(leafPatterns, std::vector<char>(rootPatterns, 0));

  // value[id * kWords + w] holds the values of node id for the w-th group of 64 inputs.
  std::vector<uint64_t> value(static_cast<std::size_t>(Abc_NtkObjNumMax(pNtk)) * kWords, 0);
  auto at = [&](int id) { return value.data() + static_cast<std::size_t>(id) * kWords; };
  // AND IDs are topological after strashing (fanins have smaller IDs), so ascending ID order works.
  auto simulateAnd = [&](Abc_Obj_t *node)
  {
    const uint64_t *in0 = at(Abc_ObjId(Abc_ObjFanin0(node)));
    const uint64_t *in1 = at(Abc_ObjId(Abc_ObjFanin1(node)));
    const uint64_t flip0 = Abc_ObjFaninC0(node) ? ~uint64_t{0} : 0;
    const uint64_t flip1 = Abc_ObjFaninC1(node) ? ~uint64_t{0} : 0;
    uint64_t *out = at(Abc_ObjId(node));
    for (int w = 0; w < kWords; ++w)
      out[w] = (in0[w] ^ flip0) & (in1[w] ^ flip1);
  };

  uint64_t state = 0x9E3779B97F4A7C15ULL; // fixed seed of the xorshift64 generator
  auto next = [&state]()
  {
    state ^= state << 13;
    state ^= state >> 7;
    state ^= state << 17;
    return state;
  };
  std::fill_n(at(Abc_ObjId(Abc_AigConst1(pNtk))), kWords, ~uint64_t{0});
  Abc_Obj_t *node;
  int i;
  Abc_NtkForEachPi(pNtk, node, i)
    for (int w = 0; w < kWords; ++w)
      at(Abc_ObjId(node))[w] = next();
  Abc_AigForEachAnd(pNtk, node, i)
    simulateAnd(node);

  // Record the original PO values, and for each leaf value u the inputs that produce it.
  // The smallest-ID leaf is the most significant bit of u.
  std::vector<std::vector<uint64_t>> original;
  Abc_NtkForEachPo(pNtk, node, i)
  {
    const uint64_t *driver = at(Abc_ObjId(Abc_ObjFanin0(node)));
    original.emplace_back(driver, driver + kWords);
  }
  const std::size_t n = cut.leaves.size();
  std::vector<std::vector<uint64_t>> leafMask(leafPatterns, std::vector<uint64_t>(kWords, ~uint64_t{0}));
  for (std::size_t u = 0; u < leafPatterns; ++u)
  {
    for (std::size_t j = 0; j < n; ++j)
    {
      const uint64_t *leaf = at(cut.leaves[j]);
      const bool bit = (u >> (n - 1 - j)) & 1;
      for (int w = 0; w < kWords; ++w)
        leafMask[u][w] &= bit ? leaf[w] : ~leaf[w];
    }
    for (int w = 0; w < kWords; ++w)
      result.seen[u] |= leafMask[u][w] != 0;
  }

  // For each c, set the roots to constants and resimulate. Nodes with IDs up to the smallest
  // root are not downstream of any root and keep their values, so only later ANDs are
  // recomputed. Every round overwrites those nodes, so nothing has to be restored.
  const int firstRoot = cut.roots.front();
  const std::size_t m = cut.roots.size();
  for (std::size_t c = 0; c < rootPatterns; ++c)
  {
    for (std::size_t j = 0; j < m; ++j)
      std::fill_n(at(cut.roots[j]), kWords, ((c >> (m - 1 - j)) & 1) ? ~uint64_t{0} : 0);
    Abc_AigForEachAnd(pNtk, node, i)
    {
      int id = Abc_ObjId(node);
      if (id > firstRoot && !std::binary_search(cut.roots.begin(), cut.roots.end(), id))
        simulateAnd(node);
    }
    // diff marks the inputs on which some PO differs from the original (a PO's complement is
    // the same on both sides, so it cancels in the XOR).
    std::vector<uint64_t> diff(kWords, 0);
    Abc_NtkForEachPo(pNtk, node, i)
    {
      const uint64_t *driver = at(Abc_ObjId(Abc_ObjFanin0(node)));
      for (int w = 0; w < kWords; ++w)
        diff[w] |= driver[w] ^ original[i][w];
    }
    for (std::size_t u = 0; u < leafPatterns; ++u)
      for (int w = 0; w < kWords && !result.changed[u][c]; ++w)
        result.changed[u][c] = (diff[w] & leafMask[u][w]) != 0;
  }
  return result;
}

// Builds the transitive fanin of the leaves (keeping all PIs), with one PO per leaf in order.
// It only answers whether U = u occurs, which depends on nothing but the logic above the leaves,
// so the whole miter is not needed. The caller frees the network.
static Abc_Ntk_t *BuildLeafCone(Abc_Ntk_t *pNtk, const KlCut &cut)
{
  Abc_Ntk_t *cone = Abc_NtkAlloc(ABC_NTK_STRASH, ABC_FUNC_AIG, 1);
  cone->pName = Extra_UtilStrsav("lsv_kl_flex_leaf_cone");
  auto *manager = static_cast<Abc_Aig_t *>(cone->pManFunc);
  std::vector<Abc_Obj_t *> copy(Abc_NtkObjNumMax(pNtk), nullptr);
  copy[Abc_ObjId(Abc_AigConst1(pNtk))] = Abc_AigConst1(cone);

  Abc_Obj_t *node;
  int i;
  Abc_NtkForEachPi(pNtk, node, i)
    copy[Abc_ObjId(node)] = Abc_NtkCreatePi(cone);
  // Abc_NtkDfsNodes collects the ANDs above the leaves in topological order (PI leaves add none).
  std::vector<Abc_Obj_t *> leafObjs;
  for (int leaf : cut.leaves)
    leafObjs.push_back(Abc_NtkObj(pNtk, leaf));
  Vec_Ptr_t *nodes = Abc_NtkDfsNodes(pNtk, leafObjs.data(), static_cast<int>(leafObjs.size()));
  Vec_PtrForEachEntry(Abc_Obj_t *, nodes, node, i)
    copy[Abc_ObjId(node)] = Abc_AigAnd(manager, CopyMiterFanin(copy, node, 0), CopyMiterFanin(copy, node, 1));
  Vec_PtrFree(nodes);

  for (int leaf : cut.leaves)
    Abc_ObjAddFanin(Abc_NtkCreatePo(cone), copy[leaf]);
  return cone;
}

// One SAT setup: the network, its converted AIG, the CNF and the solver. The unique_ptrs use the
// ABC release functions, and members are released in reverse declaration order.
struct FlexSolver
{
  std::unique_ptr<Abc_Ntk_t, decltype(&Abc_NtkDelete)> ntk{nullptr, Abc_NtkDelete};
  std::unique_ptr<Aig_Man_t, decltype(&Aig_ManStop)> aig{nullptr, Aig_ManStop};
  std::unique_ptr<Cnf_Dat_t, decltype(&Cnf_DataFree)> cnf{nullptr, Cnf_DataFree};
  std::unique_ptr<sat_solver, decltype(&sat_solver_delete)> solver{nullptr, sat_solver_delete};

  // Takes ownership of network and builds the solver; returns false on failure. Every PO keeps a
  // CNF variable so that the queries can constrain it.
  // With compact = false, Cnf_DeriveSimple writes the clauses AND by AND, which is fast to build.
  // With compact = true, Cnf_Derive first maps the AIG into cuts: slower to build, but the
  // smaller CNF solves hard queries faster.
  bool Init(Abc_Ntk_t *network, bool compact)
  {
    ntk.reset(network);
    if (!ntk)
      return false;
    aig.reset(Abc_NtkToDar(ntk.get(), 0, 0));
    if (!aig)
      return false;
    const int outputs = Aig_ManCoNum(aig.get());
    cnf.reset(compact ? Cnf_Derive(aig.get(), outputs) : Cnf_DeriveSimple(aig.get(), outputs));
    if (!cnf)
      return false;
    solver.reset(static_cast<sat_solver *>(Cnf_DataWriteIntoSolver(cnf.get(), 1, 0)));
    return solver != nullptr;
  }
  bool Ready() const { return solver != nullptr; }
  // Find the converted CI/CO by its creation order, then look up its CNF variable by its new ID.
  int CoVar(int index) const { return cnf->pVarNums[Aig_ManCo(aig.get(), index)->Id]; }
  int CiVar(int index) const { return cnf->pVarNums[Aig_ManCi(aig.get(), index)->Id]; }
};

// Computes the flexibility of one maximum cut. masks[u] is the mask for leaf value u: bit c is 1
// iff forcing the roots to pattern c changes no PO for any input with U = u. Returns nullopt if
// building a network or a CNF fails or a SAT call gives no answer; the command reports it.
//
// Most queries need no SAT call: the original root pattern is always allowed
// (OriginalRootValues); a u seen in simulation occurs, and a c with a simulated output change is
// not allowed (SimulateFlex). The rest go to SAT, and every SAT setup is built only when first
// needed. "Does U = u occur?" uses the small cone above the leaves. "Does forcing c change an
// output?" is asked in two stages: first, with a conflict limit, on one miter per cut whose roots
// are PIs p fixed by assumptions, which settles the easy queries without building more; a query
// that hits the limit is then solved without limit on a miter with the roots fixed to the
// constants of c, built once per c (see BuildKlMiter). Both miters encode the same question, so
// the answer does not depend on the stage.
std::optional<std::vector<std::string>> Lsv_ComputeFlexMasks(Abc_Ntk_t *pNtk, const KlCut &cut)
{
  // Patterns u and c are indexed by integers and counted with 1 << (number of nodes); make sure
  // the shift fits into size_t.
  if (cut.leaves.size() >= std::numeric_limits<std::size_t>::digits ||
      cut.roots.size() >= std::numeric_limits<std::size_t>::digits)
  {
    Abc_Print(-1, "Too many cut nodes to index all assignments.\n");
    return std::nullopt;
  }

  // leafPatterns is the number of masks to print, rootPatterns the number of root patterns per
  // mask. Mask bits are stored four per nibble; allAllowed is the mask with every pattern allowed.
  const std::size_t n = cut.leaves.size();
  const std::size_t m = cut.roots.size();
  const std::size_t leafPatterns = std::size_t{1} << n;
  const std::size_t rootPatterns = std::size_t{1} << m;
  const std::size_t nibbleCount = (rootPatterns + 3) / 4;
  const std::string allAllowed = rootPatterns == 2 ? "3" : std::string(nibbleCount, 'F');
  const std::vector<std::size_t> originalRoots = OriginalRootValues(pNtk, cut);
  const FlexSimulation simulation = SimulateFlex(pNtk, cut);

  // reach: the cone above the leaves; PO i is the i-th leaf.
  FlexSolver reach;
  std::vector<int> reachLeafVars;
  // A forcing miter with the CNF variables of its leaves, its forcing PIs (shared miter only) and
  // diff; see BuildKlMiter. shared has PIs p for the roots, constants[c] has the roots fixed to c.
  struct ForcingMiter
  {
    FlexSolver solver;
    std::vector<int> leafVars, rootVars;
    int diffVar = 0;
  };
  auto initMiter = [&](ForcingMiter &miter, std::optional<std::size_t> pattern) {
    // Queries that get here were not settled by simulation and may be hard, so use the compact CNF.
    if (!miter.solver.Init(BuildKlMiter(pNtk, cut, pattern), true))
      return false;
    for (std::size_t i = 0; i < n; ++i)
      miter.leafVars.push_back(miter.solver.CoVar(static_cast<int>(i)));
    if (!pattern)
    {
      const int firstForcingPi = Abc_NtkPiNum(pNtk);
      for (std::size_t i = 0; i < m; ++i)
        miter.rootVars.push_back(miter.solver.CiVar(firstForcingPi + static_cast<int>(i)));
    }
    miter.diffVar = miter.solver.CoVar(static_cast<int>(n));
    return true;
  };
  ForcingMiter shared;
  std::vector<ForcingMiter> constants(rootPatterns);

  std::vector<std::string> masks;
  std::vector<lit> assumptions;
  assumptions.reserve(n + m + 1);
  for (std::size_t u = 0; u < leafPatterns; ++u)
  {
    // First decide whether any PI assignment produces U = u; simulation may already have seen it.
    if (!simulation.seen[u])
    {
      if (!reach.Ready())
      {
        // These queries almost always end in propagation, so a fast build matters most.
        if (!reach.Init(BuildLeafCone(pNtk, cut), false))
          return std::nullopt;
        for (std::size_t i = 0; i < n; ++i)
          reachLeafVars.push_back(reach.CoVar(static_cast<int>(i)));
      }
      assumptions.clear();
      AppendAssumptions(assumptions, reachLeafVars, u);
      int reachable = SolveKlSat(reach.solver.get(), assumptions);
      if (reachable == l_False)
      {
        // U = u never occurs, so the condition holds vacuously: every root pattern is allowed.
        masks.push_back(allAllowed);
        continue;
      }
      if (reachable != l_True)
        return std::nullopt;
    }

    std::vector<unsigned char> nibbles(nibbleCount, 0);
    for (std::size_t c = 0; c < rootPatterns; ++c)
    {
      // Forcing the roots to the values they already compute changes nothing, so this c is
      // always allowed. Its SAT query is always UNSAT but has to prove two copies of the circuit
      // equivalent, which can take minutes on large arithmetic circuits.
      if (!originalRoots.empty() && c == originalRoots[u])
      {
        nibbles[c / 4] |= 1U << (c % 4);
        continue;
      }
      // Simulation already found an input whose outputs change: c is not allowed, bit stays 0.
      if (simulation.changed[u][c])
        continue;

      // Stage 1: fix U = u and p = c on the shared miter and ask for diff = 1, a counterexample.
      if (!shared.solver.Ready() && !initMiter(shared, std::nullopt))
        return std::nullopt;
      assumptions.clear();
      AppendAssumptions(assumptions, shared.leafVars, u);
      AppendAssumptions(assumptions, shared.rootVars, c);
      assumptions.push_back(Abc_Var2Lit(shared.diffVar, 0));
      int counterexample = SolveKlSat(shared.solver.solver.get(), assumptions, kSharedConflictLimit);
      if (counterexample == l_Undef)
      {
        // Stage 2: the roots are already c in this miter, so only U = u and diff = 1 are fixed.
        ForcingMiter &miter = constants[c];
        if (!miter.solver.Ready() && !initMiter(miter, c))
          return std::nullopt;
        assumptions.clear();
        AppendAssumptions(assumptions, miter.leafVars, u);
        assumptions.push_back(Abc_Var2Lit(miter.diffVar, 0));
        counterexample = SolveKlSat(miter.solver.solver.get(), assumptions);
      }
      // SAT: some input changes the outputs, so bit c stays 0. UNSAT: no counterexample, so bit c
      // is set (nibble c / 4, bit c % 4). Any other answer is an error and writes no mask.
      if (counterexample == l_False)
        nibbles[c / 4] |= 1U << (c % 4);
      else if (counterexample != l_True)
        return std::nullopt;
    }
    masks.push_back(HexMask(nibbles));
  }
  return masks;
}

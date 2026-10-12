#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "bdd/cudd/cudd.h"

#include <cstdint>
#include <cstdlib>
#include <set>
#include <unordered_map>
#include <vector>

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandCutTT(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandCutBddSize(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
	Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
	Cmd_CommandAdd(pAbc, "LSV", "lsv_cut_tt", Lsv_CommandCutTT, 0);
	Cmd_CommandAdd(pAbc, "LSV", "lsv_cut_bddsize", Lsv_CommandCutBddSize, 0);
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

/*=== k-feasible cut enumeration ===========================================*/

typedef std::vector<int> Lsv_Cut_t;           // leaf IDs, sorted ascending
typedef std::vector<Lsv_Cut_t> Lsv_CutSet_t;  // all k-feasible cuts of a node

// Merge two sorted leaf lists; return false if the union has more than k leaves.
static bool Lsv_CutMerge(const Lsv_Cut_t& a, const Lsv_Cut_t& b, int k, Lsv_Cut_t& out) {
	out.clear();
	size_t i = 0, j = 0;
	while (i < a.size() || j < b.size()) {
		int v;
		if (j == b.size() || (i < a.size() && a[i] < b[j])) {
			v = a[i++];
		}
		else if (i == a.size() || b[j] < a[i]) {
			v = b[j++];
		}
		else {
			v = a[i];
			++i;
			++j;
		}
		if ((int)out.size() >= k) return false;
		out.push_back(v);
	}
	return true;
}

// 64-bit signature of a cut: a superset test that never rejects a feasible
// merge, since popcount(sigA | sigB) <= |A u B|.
static inline uint64_t Lsv_LeafSig(int id) {
  	return 1ull << ((uint64_t)(unsigned)id * 0x9E3779B97F4A7C15ull >> 58);
}

// Enumerate all k-feasible cuts of every object in the strashed network.
// cuts[id] holds the cut set of the object with that ID.
static void Lsv_NtkEnumCuts(Abc_Ntk_t* pNtk, int k, std::vector<Lsv_CutSet_t>& cuts) {
	int nObjs = Abc_NtkObjNumMax(pNtk);
	cuts.assign(nObjs, Lsv_CutSet_t());
	std::vector<std::vector<uint64_t> > sigs(nObjs);

	// Constant node: no leaves (its function is constant 1).
	Abc_Obj_t* pConst = Abc_AigConst1(pNtk);
	if (pConst) {
		cuts[Abc_ObjId(pConst)].push_back(Lsv_Cut_t());
		sigs[Abc_ObjId(pConst)].push_back(0);
	}

	Abc_Obj_t* pObj;
	int i;
	Abc_NtkForEachCi(pNtk, pObj, i) {
		int id = Abc_ObjId(pObj);
		cuts[id].push_back(Lsv_Cut_t(1, id));
		sigs[id].push_back(Lsv_LeafSig(id));
	}

	// Internal nodes in topological order (including dangling ones).
	Vec_Ptr_t* vNodes = Abc_NtkDfs(pNtk, 1);
	Lsv_Cut_t merged;
	Vec_PtrForEachEntry(Abc_Obj_t*, vNodes, pObj, i) {
		if (!Abc_AigNodeIsAnd(pObj)) continue;

		int id = Abc_ObjId(pObj);
		Lsv_CutSet_t& set = cuts[id];
		std::vector<uint64_t>& sig = sigs[id];
		std::set<Lsv_Cut_t> seen;  // for duplicate detection
		set.push_back(Lsv_Cut_t(1, id));  // trivial cut
		sig.push_back(Lsv_LeafSig(id));
		seen.insert(set.back());

		int id0 = Abc_ObjFaninId0(pObj), id1 = Abc_ObjFaninId1(pObj);
		const Lsv_CutSet_t& s0 = cuts[id0];
		const Lsv_CutSet_t& s1 = cuts[id1];
		const std::vector<uint64_t>& g0 = sigs[id0];
		const std::vector<uint64_t>& g1 = sigs[id1];

		for (size_t a = 0; a < s0.size(); ++a) {
			for (size_t b = 0; b < s1.size(); ++b) {
				if (__builtin_popcountll(g0[a] | g1[b]) > k) continue;
				if (!Lsv_CutMerge(s0[a], s1[b], k, merged)) continue;
				if (!seen.insert(merged).second) continue;
				set.push_back(merged);
				sig.push_back(g0[a] | g1[b]);
			}
		}
	}
	Vec_PtrFree(vNodes);
}

/*=== truth table of a cut ================================================*/

// Projection pattern of the variable at index bit position `bit`.
static uint64_t Lsv_VarPattern(int bit) {
  static const uint64_t pat[6] = {0xAAAAAAAAAAAAAAAAull, 0xCCCCCCCCCCCCCCCCull,
                                  0xF0F0F0F0F0F0F0F0ull, 0xFF00FF00FF00FF00ull,
                                  0xFFFF0000FFFF0000ull, 0xFFFFFFFF00000000ull};
  return pat[bit];
}

struct Lsv_TTCtx {
	std::vector<uint64_t> val;
	std::vector<int> stamp;
	int cur;
};

static uint64_t Lsv_CutTTRec(Abc_Obj_t* pObj, Lsv_TTCtx& ctx) {
	int id = Abc_ObjId(pObj);
	if (ctx.stamp[id] == ctx.cur) return ctx.val[id];
	uint64_t r;
	if (Abc_AigNodeIsConst(pObj)) {
		r = ~0ull;
	}
	else {
		// Must be an AND node (leaves and CIs are already stamped).
		uint64_t t0 = Lsv_CutTTRec(Abc_ObjFanin0(pObj), ctx);
		uint64_t t1 = Lsv_CutTTRec(Abc_ObjFanin1(pObj), ctx);
		if (Abc_ObjFaninC0(pObj)) t0 = ~t0;
		if (Abc_ObjFaninC1(pObj)) t1 = ~t1;
		r = t0 & t1;
	}
	ctx.stamp[id] = ctx.cur;
	ctx.val[id] = r;
	return r;
}

// Compute the truth table of pRoot w.r.t. the leaves of `cut`.
// Leaf order: cut[0] is the most significant bit of the input assignment.
static uint64_t Lsv_CutTruthTable(Abc_Ntk_t* pNtk, Abc_Obj_t* pRoot, const Lsv_Cut_t& cut, Lsv_TTCtx& ctx) {
	ctx.cur++;
	int m = (int)cut.size();
	for (int i = 0; i < m; ++i) {
		ctx.stamp[cut[i]] = ctx.cur;
		ctx.val[cut[i]] = Lsv_VarPattern(m - 1 - i);
	}
	uint64_t r = Lsv_CutTTRec(pRoot, ctx);
	if (m < 6) r &= (1ull << (1 << m)) - 1;
	return r;
}

/*=== BDD of a cut ========================================================*/

struct Lsv_BddCtx {
	DdManager* dd;
	std::vector<DdNode*> val;
	std::vector<int> stamp;
	int cur;
};

// Returns a referenced BDD node.
static DdNode* Lsv_CutBddRec(Abc_Obj_t* pObj, Lsv_BddCtx& ctx) {
	int id = Abc_ObjId(pObj);
	if (ctx.stamp[id] == ctx.cur) {
		Cudd_Ref(ctx.val[id]);
		return ctx.val[id];
	}

	DdNode* r;
	if (Abc_AigNodeIsConst(pObj)) {
		r = Cudd_ReadOne(ctx.dd);
		Cudd_Ref(r);
	}
	else {
		DdNode* f0 = Lsv_CutBddRec(Abc_ObjFanin0(pObj), ctx);
		DdNode* f1 = Lsv_CutBddRec(Abc_ObjFanin1(pObj), ctx);
		DdNode* g0 = Abc_ObjFaninC0(pObj) ? Cudd_Not(f0) : f0;
		DdNode* g1 = Abc_ObjFaninC1(pObj) ? Cudd_Not(f1) : f1;
		r = Cudd_bddAnd(ctx.dd, g0, g1);
		Cudd_Ref(r);
		Cudd_RecursiveDeref(ctx.dd, f0);
		Cudd_RecursiveDeref(ctx.dd, f1);
	}
	ctx.stamp[id] = ctx.cur;
	ctx.val[id] = r;  // holds one reference until the cut is finished
	Cudd_Ref(r);
	return r;
}

// Build the ROBDD of pRoot w.r.t. the leaves of `cut` (leaf i -> BDD var i)
// and return its size.
static int Lsv_CutBddSize(Abc_Ntk_t* pNtk, Abc_Obj_t* pRoot, const Lsv_Cut_t& cut, Lsv_BddCtx& ctx) {
	ctx.cur++;
	std::vector<int> touched;
	for (size_t i = 0; i < cut.size(); ++i) {
		DdNode* v = Cudd_bddIthVar(ctx.dd, (int)i);
		Cudd_Ref(v);
		ctx.stamp[cut[i]] = ctx.cur;
		ctx.val[cut[i]] = v;
	}
	DdNode* f = Lsv_CutBddRec(pRoot, ctx);
	int size = Cudd_DagSize(f);
	Cudd_RecursiveDeref(ctx.dd, f);
	// Release the per-node references held in ctx.val for this cut.
	for (int id = 0; id < (int)ctx.val.size(); ++id) {
		if (ctx.stamp[id] == ctx.cur) {
			Cudd_RecursiveDeref(ctx.dd, ctx.val[id]);
			ctx.stamp[id] = 0;
		}
	}
  	return size;
}

/*=== commands ============================================================*/

static void Lsv_PrintCut(const Lsv_Cut_t& cut) {
	for (size_t i = 0; i < cut.size(); ++i) {
		if (i) printf(" ");
		printf("%d", cut[i]);
	}
}

static int Lsv_ParseK(int argc, char** argv, int& k) {
	if (argc != 2) return 0;
	char* end;
	long v = strtol(argv[1], &end, 10);
	if (*argv[1] == '\0' || *end != '\0' || v < 1 || v > 6) return 0;
	k = (int)v;
	return 1;
}

int Lsv_CommandCutTT(Abc_Frame_t* pAbc, int argc, char** argv) {
	Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
	int k;
	Extra_UtilGetoptReset();
	if (!Lsv_ParseK(argc, argv, k)) goto usage;
	if (!pNtk) {
		Abc_Print(-1, "Empty network.\n");
		return 1;
	}
	if (!Abc_NtkIsStrash(pNtk)) {
		Abc_Print(-1, "The network is not an AIG. Run \"strash\" first.\n");
		return 1;
	}

	{
		std::vector<Lsv_CutSet_t> cuts;
		Lsv_NtkEnumCuts(pNtk, k, cuts);
		Lsv_TTCtx ctx;
		ctx.val.assign(Abc_NtkObjNumMax(pNtk), 0);
		ctx.stamp.assign(Abc_NtkObjNumMax(pNtk), 0);
		ctx.cur = 0;
		Abc_Obj_t* pObj;
		int i;
		Abc_NtkForEachNode(pNtk, pObj, i) {
			const Lsv_CutSet_t& set = cuts[Abc_ObjId(pObj)];
			for (size_t c = 0; c < set.size(); ++c) {
				uint64_t tt = Lsv_CutTruthTable(pNtk, pObj, set[c], ctx);
				printf("%d: ", Abc_ObjId(pObj));
				Lsv_PrintCut(set[c]);
				printf(": %llX\n", (unsigned long long)tt);
			}
		}
	}
	return 0;

usage:
	Abc_Print(-2, "usage: lsv_cut_tt <k>\n");
	Abc_Print(-2, "\t        enumerates k-feasible cuts of every AIG node and\n");
	Abc_Print(-2, "\t        prints the truth table of each cut in hexadecimal\n");
	Abc_Print(-2, "\t<k>   : maximum number of cut leaves (1 <= k <= 6)\n");
	return 1;
}

int Lsv_CommandCutBddSize(Abc_Frame_t* pAbc, int argc, char** argv) {
	Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
	int k;
	Extra_UtilGetoptReset();
	if (!Lsv_ParseK(argc, argv, k)) goto usage;
	if (!pNtk) {
		Abc_Print(-1, "Empty network.\n");
		return 1;
	}
	if (!Abc_NtkIsStrash(pNtk)) {
		Abc_Print(-1, "The network is not an AIG. Run \"strash\" first.\n");
		return 1;
	}

	{
		std::vector<Lsv_CutSet_t> cuts;
		Lsv_NtkEnumCuts(pNtk, k, cuts);
		Lsv_BddCtx ctx;
		ctx.dd = Cudd_Init(k, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);
		ctx.val.assign(Abc_NtkObjNumMax(pNtk), (DdNode*)NULL);
		ctx.stamp.assign(Abc_NtkObjNumMax(pNtk), 0);
		ctx.cur = 0;
		Lsv_TTCtx ttctx;
		ttctx.val.assign(Abc_NtkObjNumMax(pNtk), 0);
		ttctx.stamp.assign(Abc_NtkObjNumMax(pNtk), 0);
		ttctx.cur = 0;
		// Cuts with the same leaf count and truth table (variable order is the
		// leaf order in both cases) have the same ROBDD, so cache the size.
		std::unordered_map<uint64_t, int> cache[7];
		Abc_Obj_t* pObj;
		int i;
		Abc_NtkForEachNode(pNtk, pObj, i) {
			const Lsv_CutSet_t& set = cuts[Abc_ObjId(pObj)];
			for (size_t c = 0; c < set.size(); ++c) {
				uint64_t tt = Lsv_CutTruthTable(pNtk, pObj, set[c], ttctx);
				std::unordered_map<uint64_t, int>& m = cache[set[c].size()];
				std::unordered_map<uint64_t, int>::iterator it = m.find(tt);

				int size;
				if (it != m.end()) {
					size = it->second;
				}
				else {
					size = Lsv_CutBddSize(pNtk, pObj, set[c], ctx);
					m[tt] = size;
				}
				printf("%d: ", Abc_ObjId(pObj));
				Lsv_PrintCut(set[c]);
				printf(": %d\n", size);
			}
		}
		Cudd_Quit(ctx.dd);
	}
	return 0;

usage:
	Abc_Print(-2, "usage: lsv_cut_bddsize <k>\n");
	Abc_Print(-2, "\t        enumerates k-feasible cuts of every AIG node and\n");
	Abc_Print(-2, "\t        prints the ROBDD size of each cut\n");
	Abc_Print(-2, "\t<k>   : maximum number of cut leaves (1 <= k <= 6)\n");
	return 1;
}

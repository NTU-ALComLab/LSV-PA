// Original: Alan Mishchenko
// Modified: Yen-Wen Chen
// for LSV PA1 Exercise 4
// implementation of `lsv_printmocut`

#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

// for DP cut enumeration, hash, set, ...
#include <vector>
#include <unordered_map>
#include <unordered_set>
#include <algorithm>
#include <cstdio>


static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintMoCut(Abc_Frame_t* pAbc, int argc, char** argv);  // multiple-output cuts

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

// Idea:
// We can derive each node's k-feasible cuts from merging the cuts of its FIs,
// keep reusing previously computed results
// -> Implement Cut enumeration with dynamic programming (DP)

// To store and check cuts efficiently, we use a hash table keyed by input vectors.
// FNV-1a hash function for fast & low collision hashing
// ref: https://mojoauth.com/hashing/fnv-1a-in-c/
struct VecHash {
  static constexpr size_t FNV_offset_basis = 1469598103934665603ull;
  static constexpr size_t FNV_prime = 1099511628211ull;
  size_t operator()(const std::vector<int>& v) const {
    size_t h = FNV_offset_basis;
    for (int x : v) {  // for every element in vector v
      h ^= (size_t)x;  // XOR the element to the bottom of hash
      h *= FNV_prime;  // Multiply the hash by the FNV prime
    }
    return h;
  }
};
struct VecEq {
  bool operator()(const std::vector<int>& vec1, const std::vector<int>& vec2) const {
    if (vec1 == vec2) {
      return true;
    } 
    return false;
  }
};

// Merge 2 sorted vectors into one & removing repeated elements
// Used for merging cuts from 2 subtrees
// Idea: Merge procedure in merge sort
static std::vector<int> VecMerge(const std::vector<int>& vec1, const std::vector<int>& vec2) {
    std::vector<int> u;
    int n1 = (int)vec1.size();
    int n2 = (int)vec2.size();
    
    int i = 0, j = 0;
    while (i < n1 && j < n2) {
        if (vec1[i] < vec2[j]) {
            u.push_back(vec1[i++]);
        } else if (vec2[j] < vec1[i]) {
            u.push_back(vec2[j++]);
        } else { // equal
            u.push_back(vec1[i]); // push only 1 of them because we only want unique elements
            i++;
            j++;
        }
    }
    while (i < n1) u.push_back(vec1[i++]);
    while (j < n2) u.push_back(vec2[j++]);
    return u;
}

// Return all k-feasible cuts of a node (PI or AND node)
static std::vector<std::vector<int>> cuts_of(Abc_Obj_t* pObj, int k, std::unordered_map<int, std::vector<std::vector<int>>>& memo) {
  // For memoization in DP, we use:
  // memo: a hash table
  // key: int k -> node ID
  // value: 2D vectors std::vector<std::vector<int>> -> all cuts of a node
  // e.g: memo[5] = { {5}, {1,2}, {1,3}, {2,3} }; -> node 5 has 4 cuts: {5}, {1,2}, {1,3}, {2,3}

  int id = Abc_ObjId(pObj);
  
  // check if already computed
  if (memo.count(id)) {
    return memo[id];
  }

  // if not computed yet:
  // build a 2D vector so we can contain cuts of this node (reference)
  std::vector<std::vector<int>> out;

  // k <= 0, no feasible cuts
  if (k <= 0) { 
    memo[id] = out;
    return out; 
  }

  // if current node is PI -> only 1 cut which is itself
  if (Abc_ObjIsPi(pObj)) {
    std::vector<int> cut;
    cut.push_back(id);
    out.push_back(cut);
    memo[id] = out;
    return out;
  }

  // if current node is AND -> merge cuts from its 2 FIs using DP + itself cut
  if (Abc_AigNodeIsAnd(pObj)) {
    Abc_Obj_t* a = Abc_ObjFanin0(pObj);
    Abc_Obj_t* b = Abc_ObjFanin1(pObj);

    std::vector<std::vector<int>> Cuts_of_a = cuts_of(a, k, memo);
    std::vector<std::vector<int>> Cuts_of_b = cuts_of(b, k, memo);

    // cut of itself
    std::vector<int> selfCut;
    selfCut.push_back(id);
    out.push_back(selfCut);

    // merge cuts from 2 FIs
    for (size_t i = 0; i < Cuts_of_a.size(); i++) {
      for (size_t j = 0; j < Cuts_of_b.size(); j++) {
        std::vector<int> U = VecMerge(Cuts_of_a[i], Cuts_of_b[j]);

        if ((int)U.size() <= k) { // if the merged cut is k-feasible
          // check duplicates
          bool duplicate = false;
          for (size_t m = 0; m < out.size(); m++) {
            if (out[m] == U) {
              duplicate = true;
              break;
            }
          }
          // if no duplicates -> push back into out
          if (!duplicate) {
            out.push_back(U);
          }
        }
      }
    }

    // sort every cut in case so that {2, 1} and {1, 2} is considered different cuts
    for (size_t i = 0; i < out.size(); i++) {
      std::sort(out[i].begin(), out[i].end());
    }
    std::sort(out.begin(), out.end());

    // remove duplicates
    for (size_t i = 0; i < out.size(); i++) {
      for (size_t j = i + 1; j < out.size(); ) {
        if (out[i] == out[j]) {
          out.erase(out.begin() + j);
        } else {
          j++;
        }
      }
    }
    memo[id] = out;
    return out;
  }

  // if current node is neither PI or AND -> PO or invalid -> just return
  memo[id] = out;
  return out;
}

// `lsv_printmocut -k <k> -l <l>` implementation
static int Lsv_CommandPrintMoCut(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  if (!pNtk || !Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "Network is not a strashed AIG. Please run `strash` first.\n");
    return 1;
  }

  int k = 3, l = 2;  // default values for k and l

  // command parse 
  // Reference: Lsv_CommandPrintNodes
  Extra_UtilGetoptReset();
  int c;
  while ((c = Extra_UtilGetopt(argc, argv, "k:l:h")) != EOF) {
    switch (c) {
      case 'k': k = atoi(globalUtilOptarg); break;
      case 'l': l = atoi(globalUtilOptarg); break;
      case 'h':
      default:
        Abc_Print(-2, "usage: lsv_printmocut [-k <k>] [-l <l>] or lsv_printmocut <k> <l>\n");
        return 1;
    }
  }

  // allow positional arguments (no need to specify -k or -l)
  int idx = globalUtilOptind;
  if (idx < argc) { k = atoi(argv[idx++]); }
  if (idx < argc) { l = atoi(argv[idx++]); }

  if (k <= 0 && l <= 0) {
    Abc_Print(-1, "k and l must be greater than 0.\n");
    return 1;
  } else if (k <= 0) {
    Abc_Print(-1, "k must be greater than 0.\n");
    return 1;
  }else if (l <= 0) {
    Abc_Print(-1, "l must be greater than 0.\n");
    return 1;
  }

  std::unordered_map<int, std::vector<std::vector<int>>> memo;
  std::unordered_map<std::vector<int>, std::vector<int>, VecHash, VecEq> cut_outs;

  // only take AND nodes into account
  // (we ignore PO nodes because they do not generate new cuts)
  {
    Abc_Obj_t* pNode;
    int i;
    Abc_NtkForEachNode(pNtk, pNode, i) { // traverse every node in the network
      if (!Abc_AigNodeIsAnd(pNode)) continue;  // skip non-AND nodes (PI and PO)

      // return all k-feasible cuts of pNode
      std::vector<std::vector<int>> cs = cuts_of(pNode, k, memo);

      // for every cut in cs, map it to the output node pNode, and store in cut_outs
      for (size_t idx = 0; idx < cs.size(); idx++) {
        const std::vector<int>& cut = cs[idx];
        cut_outs[cut].push_back(Abc_ObjId(pNode));
      }
    }
  }

  for (auto& it : cut_outs) {
    const std::vector<int>& cut = it.first;
    std::vector<int>& outs = it.second;

    std::sort(outs.begin(), outs.end());

    // remove duplicates in outs
    outs.erase(std::unique(outs.begin(), outs.end()), outs.end());

    if ((int)cut.size() <= k && (int)outs.size() >= l) {
      // print cut <in>
      for (size_t i = 0; i < cut.size(); ++i) {
        if (i) {
          printf(" ");
        }
        printf("%d", cut[i]);
      }

      printf(" : ");

      // print output nodes <out>
      for (size_t i = 0; i < outs.size(); ++i) {
        if (i) {
          printf(" ");
        }
        printf("%d", outs[i]);
      }
      printf("\n");
    }
  }
  return 0;
}

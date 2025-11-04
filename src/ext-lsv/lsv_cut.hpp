#pragma once
#include <vector>
#include <unordered_map>
#include <algorithm>
#include <cstdio>

// === Cut data structures switched from set/map to sorted vectors ===
// Old:
//   typedef std::set<unsigned int> Cut_t;
//   typedef std::vector<Cut_t>     CutList_t;
//   typedef std::map<unsigned int, CutList_t> NodeCuts_t;
//
// New (drop-in names preserved for minimal churn):
using Cut_t      = std::vector<unsigned>;
using CutList_t  = std::vector<Cut_t>;
using NodeCuts_t = std::unordered_map<unsigned, CutList_t>;

// --- Utilities ---

// Keep a cut sorted and unique.
inline void CutNormalize(Cut_t& cut) {
    if (cut.size() <= 1) return;
    std::sort(cut.begin(), cut.end());
    cut.erase(std::unique(cut.begin(), cut.end()), cut.end());
}

// Insert an element while keeping order/uniqueness; returns false if size would exceed k.
inline bool CutInsertBounded(Cut_t& cut, unsigned v, int k) {
    auto it = std::lower_bound(cut.begin(), cut.end(), v);
    if (it == cut.end() || *it != v) {
        cut.insert(it, v);
        if (k > 0 && (int)cut.size() > k) return false;
    }
    return true;
}

// Merge two sorted-unique cuts with early exit when size > k (return empty as sentinel).
inline Cut_t MergeCuts(const Cut_t& a, const Cut_t& b, int k) {
    Cut_t out;
    out.reserve(a.size() + b.size());
    auto ia = a.begin(), ib = b.begin();
    while (ia != a.end() && ib != b.end()) {
        if (*ia < *ib) {
            out.push_back(*ia++);
        } else if (*ib < *ia) {
            out.push_back(*ib++);
        } else { // equal
            out.push_back(*ia); ++ia; ++ib;
        }
        if (k > 0 && (int)out.size() > k) return {}; // exceed -> return empty
    }
    // Append tail
    while (ia != a.end()) {
        out.push_back(*ia++);
        if (k > 0 && (int)out.size() > k) return {};
    }
    while (ib != b.end()) {
        out.push_back(*ib++);
        if (k > 0 && (int)out.size() > k) return {};
    }
    // Already unique by construction
    return out;
}

// Test if 'small' is subset of 'big' (both sorted-unique)
inline bool CutIsSubsetOf(const Cut_t& small, const Cut_t& big) {
    if (small.size() > big.size()) return false;
    auto i = small.begin(), j = big.begin();
    while (i != small.end()) {
        while (j != big.end() && *j < *i) ++j;
        if (j == big.end() || *j != *i) return false;
        ++i; ++j;
    }
    return true;
}

// Lexicographical compare for deterministic ordering (if you keep sets/lists of cuts)
struct CutLexLess {
    bool operator()(const Cut_t& x, const Cut_t& y) const {
        return std::lexicographical_compare(x.begin(), x.end(), y.begin(), y.end());
    }
};

// Convenience printing (optional)
inline void CutPrint(const Cut_t& c) {
    std::printf("{");
    for (size_t i = 0; i < c.size(); ++i) {
        if (i) std::printf(" ");
        std::printf("%u", c[i]);
    }
    std::printf("}");
}

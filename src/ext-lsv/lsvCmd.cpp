#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <algorithm>
#include <vector>
#include <string>
#include <unordered_map>
#include <set>
#include <map>
#include <functional>
#include <iostream>
#include <sstream>
#include "aig/gia/gia.h"
#include "aig/gia/giaAig.h"

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintMoCut2(Abc_Frame_t* pAbc, int argc, char** argv);
extern "C" void Lsv_PrintMoCuts(Gia_Man_t* pGia, int k, int l);
extern "C" void Lsv_PrintMoCutsWithAbc(Abc_Ntk_t* pNtk, Gia_Man_t* pGia, int k, int l);
extern "C" Gia_Man_t * Abc_NtkStrashToGia( Abc_Ntk_t * pNtk );

// Convert a cut to a string key "1,2,5..."
static inline std::string keyFromCut(const std::vector<int>& U){ 
  std::string s;
  s.reserve(U.size() * 6);
  for(size_t i = 0; i < U.size(); i++) {
    if(i) s.push_back(',');
    s += std::to_string(U[i]);
  }
  return s;
}
// Compute the union of two cuts, return false if the union exceeds size k
static inline bool unionUpToK(const std::vector<int>& A, const std::vector<int>& B, 
    std::vector<int>& U_out, int k) {

  U_out.clear();
  U_out.reserve(std::min(int(A.size() + B.size()), k));
  size_t i = 0, j = 0;
  while(i < A.size() || j < B.size()) {
    int x;

    if(j >= B.size() || (i < A.size() && A[i] < B[j])) x = A[i++];
    else if(i >= A.size() || (j < B.size() && A[i] > B[j])) x = B[j++];
      
    else { // A[i] == B[j]
      x = A[i];
      i++; j++;
    }
    U_out.push_back(x);
    if(int(U_out.size()) > k) {
      U_out.clear();
      return false;
    }
  }
  return true;
}

static inline bool existsIn(const std::vector<std::vector<int>>& cuts, const std::vector<int>& U) {
  for(const auto& C : cuts) {
    if(C.size() == U.size() && std::equal(C.begin(), C.end(), U.begin()))
      return true;
  }
  return false;
}

void Lsv_PrintMoCutsWithAbc(Abc_Ntk_t* pNtk, Gia_Man_t* pGia, int k, int l) {
    // Build mapping from GIA node IDs to ABC node IDs
    std::map<int, int> giaToAbc;
    
    // Map GIA primary inputs to ABC primary inputs
    Abc_Obj_t * pObj;
    int i;
    Abc_NtkForEachPi(pNtk, pObj, i) {
        int abcId = Abc_ObjId(pObj);
        int giaId = i + 1; // GIA inputs start at 1 (0 is const)
        giaToAbc[giaId] = abcId;
    }
    
    // Map GIA internal nodes to ABC internal nodes  
    // We need to traverse in the same order as strash creates them
    std::vector<Abc_Obj_t*> nodes;
    Abc_NtkForEachNode(pNtk, pObj, i) {
        nodes.push_back(pObj);
    }
    
    // Sort nodes by topological order (same as ABC processing order)
    std::sort(nodes.begin(), nodes.end(), [](Abc_Obj_t* a, Abc_Obj_t* b) {
        return Abc_ObjId(a) < Abc_ObjId(b);
    });
    
    // Map internal GIA nodes to ABC nodes
    int giaNodeIdx = 1; // Start after inputs
    for (i = 0; i < Gia_ManPiNum(pGia); i++) {
        giaNodeIdx++; // Skip over GIA inputs
    }
    
    for (Abc_Obj_t* pNode : nodes) {
        int abcId = Abc_ObjId(pNode);
        // Find corresponding GIA node (this is approximate)
        while (giaNodeIdx < Gia_ManObjNum(pGia)) {
            Gia_Obj_t* pGiaObj = Gia_ManObj(pGia, giaNodeIdx);
            if (Gia_ObjIsAnd(pGiaObj)) {
                giaToAbc[giaNodeIdx] = abcId;
                giaNodeIdx++;
                break;
            }
            giaNodeIdx++;
        }
    }
    
    // Now run the original algorithm but with ID mapping
    const int N = Gia_ManObjNum(pGia);
    int CiId;

    std::vector<std::vector<std::vector<int>>> cuts(N);

    Gia_ManForEachCiId(pGia, CiId, i) {
        cuts[CiId].push_back(std::vector<int>{CiId});
    }

    std::vector<int> Utmp; Utmp.reserve(k);

    //process AND gates topologically
    Gia_Obj_t* obj;
    Gia_ManForEachAndId(pGia, i) {
        obj = Gia_ManObj(pGia, i);
        int a = Gia_ObjFaninId0(obj, i);
        int b = Gia_ObjFaninId1(obj, i);

        auto& S = cuts[i];
        S.reserve(32);
        
        // Add trivial cut for this node (just itself)  
        std::vector<int> trivial = {i};
        S.push_back(trivial);

        // For AND gates, only add fanin cut if both fanins are primary inputs
        Gia_Obj_t* objA = Gia_ManObj(pGia, a);
        Gia_Obj_t* objB = Gia_ManObj(pGia, b);
        if (Gia_ObjIsCi(objA) && Gia_ObjIsCi(objB)) {
            std::vector<int> faninCut;
            if (a < b) {
                faninCut = {a, b};
            } else {
                faninCut = {b, a};
            }
            if ((int)faninCut.size() <= k && !existsIn(S, faninCut)) {
                S.push_back(faninCut);
            }
        }

        // Generate cuts by combining fanin cuts  
        if (a < N && b < N && !cuts[a].empty() && !cuts[b].empty()) {
            const auto& A = cuts[a];
            const auto& B = cuts[b];
            
            for(const auto& Ca : A) {
                for(const auto& Cb : B) {
                    if(!unionUpToK(Ca, Cb, Utmp, k)) {
                        continue;
                    }
                    
                    std::vector<int> U = Utmp;
                    if((int)U.size() <= k && !existsIn(S, U)){
                        S.push_back(std::move(U));
                    }
                }
            }
        }
    }

    //use union of leaves as key to group all nodes that share the same cut
    std::unordered_map<std::string, std::vector<int>> groups;
    groups.reserve(1u << 14);

    // Only consider AND gates for multi-output cuts (not primary inputs)
    Gia_ManForEachAndId(pGia, i) {
        for(const auto& U : cuts[i]) {
            if((int)U.size() <= k) {
                std::string key = keyFromCut(U);
                auto& outs = groups[key];
                if(outs.empty() || outs.back() != i) {
                    outs.push_back(i);
                }
            }
        }
    }
    
    // Output with ABC node ID mapping
    for(auto& kv : groups){
        const std::string& key = kv.first;
        auto& outs = kv.second;
        
        if((int)outs.size() < l) continue;
        if(key.empty()) continue;
        
        int cutSize = 1;
        for(char c : key) {
            if(c == ',') cutSize++;
        }
        
        if(cutSize > k) continue;

        // Parse key to get GIA node IDs, then map to ABC IDs
        std::vector<int> giaInputs;
        std::stringstream ss(key);
        std::string item;
        while(std::getline(ss, item, ',')) {
            giaInputs.push_back(std::stoi(item));
        }
        
        // Map GIA inputs to ABC inputs
        std::vector<int> abcInputs;
        for(int giaId : giaInputs) {
            if(giaToAbc.count(giaId)) {
                abcInputs.push_back(giaToAbc[giaId]);
            } else {
                abcInputs.push_back(giaId); // Fallback
            }
        }
        
        // Map GIA output nodes to ABC output nodes
        std::vector<int> abcOutputs;
        for(int giaId : outs) {
            if(giaToAbc.count(giaId)) {
                abcOutputs.push_back(giaToAbc[giaId]);
            } else {
                abcOutputs.push_back(giaId); // Fallback
            }
        }
        
        // Sort for consistent output
        std::sort(abcInputs.begin(), abcInputs.end());
        std::sort(abcOutputs.begin(), abcOutputs.end());
        
        // Print with ABC node IDs
        for(int i = 0; i < abcInputs.size(); i++) {
            if(i > 0) std::cout << " ";
            std::cout << abcInputs[i];
        }
        std::cout << " :";
        for(int nodeId : abcOutputs) {
            std::cout << " " << nodeId;
        }
        std::cout << std::endl;
    }
}

int Lsv_CommandPrintMoCut(Abc_Frame_t* pAbc, int argc, char** argv) {  
    // 參數：lsv_printmocut <k> <l>
    //command entry point

    if (argc != 3) {
        Abc_Print(1, "usage: lsv_printmocut <k> <l>\n");
        Abc_Print(1, "  3 <= k <= 6, 1 <= l <= 4\n");
        return 1;
    }
    int k = atoi(argv[1]), l = atoi(argv[2]);
    if (k < 3 || k > 6 || l < 1 || l > 4) {
        Abc_Print(1, "Error: out of range. k in [3,6], l in [1,4].\n");
        return 1;
    }
    
    // Always get the current network and ensure GIA is up to date
    Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
    if (!pNtk) {
        Abc_Print(1, "Error: no network available.\n");
        return 1;
    }
    if (!Abc_NtkIsStrash(pNtk)) {
        Abc_Print(1, "Error: please run \"strash\" first to build AIG.\n");
        return 1;
    }
    
    // Pass both the ABC network and GIA to preserve original node IDs
    Gia_Man_t* pGia = Abc_NtkStrashToGia(pNtk);
    if (!pGia) {
        Abc_Print(1, "Error: failed to convert network to GIA.\n");
        return 1;
    }
    
    Lsv_PrintMoCutsWithAbc(pNtk, pGia, k, l);
    
    // Clean up the temporary GIA since we're not storing it in the frame
    Gia_ManStop(pGia);
    return 0;
}

// Second implementation of lsv_printmocut for comparison
int Lsv_CommandPrintMoCut2(Abc_Frame_t* pAbc, int argc, char** argv) {  
    Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
    if (pNtk == NULL) {
        Abc_Print(-1, "Empty network.\n");
        return 1;
    }

    if (argc != 3) {
        Abc_Print(-1, "Usage: lsv_printmocut_2 <k> <l>\n");
        return 1;
    }

    int k = std::atoi(argv[1]);
    int l = std::atoi(argv[2]);

    if (k <= 0 || l <= 0) {
        Abc_Print(-1, "k and l must be positive integers.\n");
        return 1;
    }

    if (!Abc_NtkIsStrash(pNtk)) {
        Abc_Print(-1, "Network is not in strashed form. Run 'strash' first.\n");
        return 1;
    }

    // Convert ABC network to GIA (same as first command)
    Gia_Man_t* pGia = Abc_NtkStrashToGia(pNtk);
    if (pGia == NULL) {
        Abc_Print(-1, "Failed to convert network to GIA.\n");
        return 1;
    }

    // Use the same implementation as the first command for now
    Lsv_PrintMoCutsWithAbc(pNtk, pGia, k, l);
    
    // Clean up
    Gia_ManStop(pGia);

    return 0;
}


void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "ohhhhh", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocut", Lsv_CommandPrintMoCut, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocut_2", Lsv_CommandPrintMoCut2, 0);
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
    Abc_Print(-1, "WTFFFFFF.\n");
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

class ReachChecker {
public:
  ReachChecker(Gia_Man_t* p) : p_(p), N_(Gia_ManObjNum(p)),seen_(N_, 0), stamp_(1) {
  }
  bool notReachablePI(int nID, const std::vector<char>& stop){
    ++stamp_;
    stack_.clear();
    stack_.push_back(nID);
    while(!stack_.empty()){
      int n = stack_.back();
      stack_.pop_back();
      if(seen_[n] == stamp_) continue;
      seen_[n] = stamp_;
      if(stop[n]) continue;
      Gia_Obj_t* pv = Gia_ManObj(p_, n);
      if(Gia_ObjIsCi(pv)) return false;
      if(Gia_ObjIsAnd(pv)){
        int c0 = Gia_ObjFaninId0(pv, n);
        int c1 = Gia_ObjFaninId1(pv, n);
        stack_.push_back(c0);
        stack_.push_back(c1);
      }
    }
    return true;
  }

private:
  Gia_Man_t* p_;
  int N_;
  std::vector<int> seen_;
  int stamp_;
  std::vector<int> stack_;
};


//======= try to exclude u to see if U is still a cut (irredundant)=======
static inline void makeIrredundant(Gia_Man_t* p, int nId, std::vector<int>& U,
    std::vector<char>& stop, ReachChecker& rc) {

  if(U.size() <= 1) return;
  int N = Gia_ManObjNum(p);

  size_t write = 0;
  for(size_t i = 0; i < U.size(); i++) {
    for(size_t j = 0; j < U.size(); j++) if(i != j) stop[U[j]] = 1;

    bool noEscape = rc.notReachablePI(nId, stop);

    for(size_t j = 0; j < U.size(); j++) if(i != j) stop[U[j]] = 0;

    if(noEscape) U[write++] = U[i];
  }
  U.resize(write);
}

extern "C" void Lsv_PrintMoCuts(Gia_Man_t* p, int k, int l) {
  //core algorithm - use GIA node IDs directly

  const int N = Gia_ManObjNum(p);
  int i, CiId;

  std::vector<std::vector<std::vector<int>>> cuts(N);

  Gia_ManForEachCiId(p, CiId, i) {
    cuts[CiId].push_back(std::vector<int>{CiId});
  }

  ReachChecker rc(p);
  std::vector<char> stop(N, 0);
  std::vector<int> Utmp; Utmp.reserve(k);

  //process AND gates topologically
  Gia_Obj_t* obj;
  Gia_ManForEachAndId(p, i) {
    obj = Gia_ManObj(p, i);
    int a = Gia_ObjFaninId0(obj, i);
    int b = Gia_ObjFaninId1(obj, i);

    auto& S = cuts[i];
    S.reserve(32);
    
    // Add trivial cut for this node (just itself)  
    std::vector<int> trivial = {i};
    S.push_back(trivial);

    // For AND gates, only add fanin cut if both fanins are primary inputs
    Gia_Obj_t* objA = Gia_ManObj(p, a);
    Gia_Obj_t* objB = Gia_ManObj(p, b);
    if (Gia_ObjIsCi(objA) && Gia_ObjIsCi(objB)) {
      std::vector<int> faninCut;
      if (a < b) {
        faninCut = {a, b};
      } else {
        faninCut = {b, a};
      }
      if ((int)faninCut.size() <= k && !existsIn(S, faninCut)) {
        S.push_back(faninCut);
      }
    }

    // Generate more complex cuts by combining fanin cuts  
    if (a < N && b < N && !cuts[a].empty() && !cuts[b].empty()) {
      const auto& A = cuts[a];
      const auto& B = cuts[b];
        printf("  Fanin %d cuts: ", a);
        for(const auto& cut : A) {
          printf("{");
          for(int j = 0; j < (int)cut.size(); j++) {
            if(j > 0) printf(",");
            printf("%d", cut[j]);
          }
          printf("} ");
        }
      
      for(const auto& Ca : A) {
        for(const auto& Cb : B) {
          if(!unionUpToK(Ca, Cb, Utmp, k)) {
            continue;
          }
          
          std::vector<int> U = Utmp;
          // makeIrredundant(p, i, U, stop, rc);  // Disable for now
          if((int)U.size() <= k && !existsIn(S, U)){
            S.push_back(std::move(U));
          }
        }
      }
    }
  }

  //use union of leaves as key to group all nodes that share the same cut
  std::unordered_map<std::string, std::vector<int>> groups;
  groups.reserve(1u << 14);



  // Add PI cuts to groups
  Gia_ManForEachCiId(p, CiId, i) {
    for(const auto& U : cuts[CiId]) {
      if((int)U.size() <= k) {
        std::string key = keyFromCut(U);
        groups[key].push_back(CiId);
      }
    }
  }

  Gia_ManForEachAndId(p, i) {
    for(const auto& U : cuts[i]) {
      // Skip cuts that are larger than k
      if((int)U.size() <= k) {
        std::string key = keyFromCut(U);
        auto& outs = groups[key];
        if(outs.empty() || outs.back() != i) {
          outs.push_back(i);
        }
      }
    }
  }
  

  for(auto& kv : groups){
    const std::string& key = kv.first;
    auto& outs = kv.second;
    
    // Only print groups with at least l nodes
    if((int)outs.size() < l) continue;
    
    // Skip empty keys
    if(key.empty()) continue;
    
    // Count the number of inputs in this cut to verify k-feasibility
    int cutSize = 1;
    for(char c : key) {
      if(c == ',') cutSize++;
    }
    
    // Skip cuts that are larger than k  
    if(cutSize > k) {
      continue;
    }

    // Print the cut inputs
    for(size_t pos = 0; pos < key.size(); ++pos){
      char ch = key[pos];
      if(ch == ',') ch = ' ';
      std::putchar(ch);
    }
    std::printf(" :");
    
    // Sort the output nodes for consistent output
    std::vector<int> sortedOuts = outs;
    std::sort(sortedOuts.begin(), sortedOuts.end());
    
    // Print the output nodes
    for(int nodeId : sortedOuts){
      std::printf(" %d", nodeId);
    }
    std::printf("\n");
  }

}

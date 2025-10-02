#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "misc/st/st.h"

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintMOCut(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocut", Lsv_CommandPrintMOCut, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

//----------------------------------------LSV Example----------------------------------------------//
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
//----------------------------------------LSV Example----------------------------------------------//

//----------------------------------------PA1 Multi_output_cut----------------------------------------------//

// Debug mode flag: set to 1 to enable debug output, 0 to disable
#define DEBUG_MODE 0

// Data structure for a single cut
typedef struct Lsv_Cut_t_ {
    int nInputs;              // Number of input nodes in this cut
    Vec_Int_t* vInputs;       // Array of input node IDs (sorted)
    Vec_Int_t* vOutputs;      // Array of output nodes sharing this cut (sorted)
} Lsv_Cut_t;

// Allocate a new cut
Lsv_Cut_t* Lsv_CutAlloc(int nInputs) {
    Lsv_Cut_t* pCut = ABC_ALLOC(Lsv_Cut_t, 1);
    pCut->nInputs = nInputs;
    pCut->vInputs = Vec_IntAlloc(nInputs);
    pCut->vOutputs = Vec_IntAlloc(4);  // Initial capacity for outputs
    return pCut;
}

// Free a cut
void Lsv_CutFree(Lsv_Cut_t* pCut) {
    if (pCut == NULL) return;
    Vec_IntFree(pCut->vInputs);
    Vec_IntFree(pCut->vOutputs);
    ABC_FREE(pCut);
}

// Print a single cut for debugging
void Lsv_CutPrint(Lsv_Cut_t* pCut) {
    int i, id;
    
    printf("Cut: Inputs = { ");
    Vec_IntForEachEntry(pCut->vInputs, id, i) {
        printf("%d ", id);
    }
    printf("}, Outputs = { ");
    Vec_IntForEachEntry(pCut->vOutputs, id, i) {
        printf("%d ", id);
    }
    printf("}\n");
}

// Check if two cuts have the same inputs (for duplicate detection)
int Lsv_CutIsEqual(Lsv_Cut_t* pCut0, Lsv_Cut_t* pCut1) {
    int i;
    
    // Different sizes -> not equal
    if (Vec_IntSize(pCut0->vInputs) != Vec_IntSize(pCut1->vInputs))
        return 0;
    
    // Compare each input (assuming both are sorted)
    for (i = 0; i < Vec_IntSize(pCut0->vInputs); i++) {
        if (Vec_IntEntry(pCut0->vInputs, i) != Vec_IntEntry(pCut1->vInputs, i))
            return 0;
    }
    
    return 1;  // Equal
}

// Merge two cuts using sorted merge algorithm
// Returns NULL if the merged cut would exceed k inputs
Lsv_Cut_t* Lsv_CutMerge(Lsv_Cut_t* pCut0, Lsv_Cut_t* pCut1, int k) {
    Vec_Int_t* vInputs = Vec_IntAlloc(k + 1);
    int i = 0, j = 0;
    int id0, id1;
    
    // Sorted merge: combine two sorted arrays
    while (i < Vec_IntSize(pCut0->vInputs) && j < Vec_IntSize(pCut1->vInputs)) {
        id0 = Vec_IntEntry(pCut0->vInputs, i);
        id1 = Vec_IntEntry(pCut1->vInputs, j);
        
        if (id0 < id1) {
            Vec_IntPush(vInputs, id0);
            i++;
        } else if (id0 > id1) {
            Vec_IntPush(vInputs, id1);
            j++;
        } else {  // Same element, add only once
            Vec_IntPush(vInputs, id0);
            i++;
            j++;
        }
        
        // Check if exceeds k
        if (Vec_IntSize(vInputs) > k) {
            Vec_IntFree(vInputs);
            return NULL;
        }
    }
    
    // Copy remaining elements from pCut0
    while (i < Vec_IntSize(pCut0->vInputs)) {
        Vec_IntPush(vInputs, Vec_IntEntry(pCut0->vInputs, i++));
        if (Vec_IntSize(vInputs) > k) {
            Vec_IntFree(vInputs);
            return NULL;
        }
    }
    
    // Copy remaining elements from pCut1
    while (j < Vec_IntSize(pCut1->vInputs)) {
        Vec_IntPush(vInputs, Vec_IntEntry(pCut1->vInputs, j++));
        if (Vec_IntSize(vInputs) > k) {
            Vec_IntFree(vInputs);
            return NULL;
        }
    }
    
    // Create new cut with merged inputs
    Lsv_Cut_t* pNewCut = Lsv_CutAlloc(Vec_IntSize(vInputs));
    Vec_IntFree(pNewCut->vInputs);
    pNewCut->vInputs = vInputs;
    pNewCut->nInputs = Vec_IntSize(vInputs);
    
    return pNewCut;
}

// Check if a cut already exists in the list
int Lsv_CutListContains(Vec_Ptr_t* vCuts, Lsv_Cut_t* pCut) {
    int i;
    Lsv_Cut_t* pCutTemp;
    
    Vec_PtrForEachEntry(Lsv_Cut_t*, vCuts, pCutTemp, i) {
        if (Lsv_CutIsEqual(pCutTemp, pCut))
            return 1;  // Found duplicate
    }
    
    return 0;  // Not found
}

// Check if pCut1's inputs are a proper subset of pCut2's inputs
// Returns 1 if pCut1 is a proper subset (all elements in pCut1 are in pCut2, but pCut1 has fewer elements)
int Lsv_CutIsSubset(Lsv_Cut_t* pCut1, Lsv_Cut_t* pCut2) {
    int i, j;
    int size1 = Vec_IntSize(pCut1->vInputs);
    int size2 = Vec_IntSize(pCut2->vInputs);
    
    // If pCut1 has more or equal elements, it cannot be a proper subset
    if (size1 >= size2)
        return 0;
    
    // Check if every element in pCut1 exists in pCut2
    // Both arrays are sorted
    j = 0;
    for (i = 0; i < size1; i++) {
        int val1 = Vec_IntEntry(pCut1->vInputs, i);
        
        // Find val1 in pCut2
        while (j < size2 && Vec_IntEntry(pCut2->vInputs, j) < val1)
            j++;
        
        // Not found or passed
        if (j >= size2 || Vec_IntEntry(pCut2->vInputs, j) != val1)
            return 0;
        
        j++;
    }
    
    return 1;  // All elements found, and pCut1 is smaller
}

// Check if pCut1 dominates pCut2
// pCut1 dominates pCut2 if pCut1's inputs are a proper subset of pCut2's inputs
// and both cuts have the same output node
int Lsv_CutDominates(Lsv_Cut_t* pCut1, Lsv_Cut_t* pCut2, int outputNode) {
    // Both cuts must contain the output node
    if (Vec_IntFind(pCut1->vOutputs, outputNode) == -1)
        return 0;
    if (Vec_IntFind(pCut2->vOutputs, outputNode) == -1)
        return 0;
    
    // Check if pCut1's inputs are a proper subset of pCut2's inputs
    return Lsv_CutIsSubset(pCut1, pCut2);
}

// Filter out dominated cuts from the list
// Remove cuts that are dominated by pNewCut
// Returns 1 if pNewCut is dominated by any existing cut, 0 otherwise
int Lsv_CutFilterDominated(Vec_Ptr_t* vCuts, Lsv_Cut_t* pNewCut, int outputNode, Vec_Ptr_t* vAllCuts) {
    int i, j;
    Lsv_Cut_t* pCutTemp;
    
    // First pass: check if pNewCut is dominated by any existing cut
    Vec_PtrForEachEntry(Lsv_Cut_t*, vCuts, pCutTemp, i) {
        if (Lsv_CutDominates(pCutTemp, pNewCut, outputNode)) {
            // pNewCut is dominated by existing cut, reject pNewCut
            if (DEBUG_MODE) printf("    [DOMINATE] New cut is dominated by existing cut %d\n", i);
            return 1;
        }
    }
    
    // Second pass: remove cuts dominated by pNewCut
    // We need to be careful when removing elements during iteration
    i = 0;
    while (i < Vec_PtrSize(vCuts)) {
        pCutTemp = (Lsv_Cut_t*)Vec_PtrEntry(vCuts, i);
        
        if (Lsv_CutDominates(pNewCut, pCutTemp, outputNode)) {
            // pNewCut dominates this existing cut, remove it
            if (DEBUG_MODE) printf("    [DOMINATE] New cut dominates existing cut %d\n", i);
            
            // Remove from vAllCuts as well
            for (j = 0; j < Vec_PtrSize(vAllCuts); j++) {
                if (Vec_PtrEntry(vAllCuts, j) == pCutTemp) {
                    Vec_PtrRemove(vAllCuts, pCutTemp);
                    break;
                }
            }
            
            // Remove from vCuts and free
            Vec_PtrRemove(vCuts, pCutTemp);
            Lsv_CutFree(pCutTemp);
            // Don't increment i because we just removed an element
        } else {
            i++;
        }
    }
    
    return 0;  // pNewCut is not dominated
}

// Compute cuts for a single node
void Lsv_NodeComputeCuts(Abc_Obj_t* pNode, Vec_Ptr_t** ppNodeCuts, 
                         Vec_Ptr_t* vAllCuts, int k) {
    int nodeId = Abc_ObjId(pNode);
    Lsv_Cut_t* pCut;
    int i, j;
    
    // Case 1: Primary Input - create unit cut
    if (Abc_ObjIsPi(pNode)) {
        pCut = Lsv_CutAlloc(1);
        Vec_IntPush(pCut->vInputs, nodeId);
        Vec_IntPush(pCut->vOutputs, nodeId);
        Vec_PtrPush(ppNodeCuts[nodeId], pCut);
        Vec_PtrPush(vAllCuts, pCut);
        
        if (DEBUG_MODE) printf("[DEBUG] PI node %d: created unit cut {%d}\n", nodeId, nodeId);
        return;
    }
    
    // Case 2: Internal node (AND gate)
    if (!Abc_ObjIsNode(pNode)) return;
    
    // Create trivial cut (only this node)
    pCut = Lsv_CutAlloc(1);
    Vec_IntPush(pCut->vInputs, nodeId);
    Vec_IntPush(pCut->vOutputs, nodeId);
    Vec_PtrPush(ppNodeCuts[nodeId], pCut);
    Vec_PtrPush(vAllCuts, pCut);
    
    if (DEBUG_MODE) printf("[DEBUG] Node %d: created trivial cut {%d}\n", nodeId, nodeId);
    
    // Get fanins
    Abc_Obj_t* pFanin0 = Abc_ObjFanin0(pNode);
    Abc_Obj_t* pFanin1 = Abc_ObjFanin1(pNode);
    int fanin0Id = Abc_ObjId(pFanin0);
    int fanin1Id = Abc_ObjId(pFanin1);
    
    Vec_Ptr_t* vCuts0 = ppNodeCuts[fanin0Id];
    Vec_Ptr_t* vCuts1 = ppNodeCuts[fanin1Id];
    
    if (DEBUG_MODE) printf("[DEBUG] Node %d: merging cuts from fanin0=%d (%d cuts) and fanin1=%d (%d cuts)\n",
           nodeId, fanin0Id, Vec_PtrSize(vCuts0), fanin1Id, Vec_PtrSize(vCuts1));
    
    // Merge all pairs of cuts from two fanins
    Lsv_Cut_t *pCut0, *pCut1, *pNewCut;
    Vec_PtrForEachEntry(Lsv_Cut_t*, vCuts0, pCut0, i) {
        Vec_PtrForEachEntry(Lsv_Cut_t*, vCuts1, pCut1, j) {
            pNewCut = Lsv_CutMerge(pCut0, pCut1, k);
            
            if (pNewCut == NULL) {
                // Merge failed (exceeds k)
                continue;
            }
            
            // Check if this cut already exists
            if (Lsv_CutListContains(ppNodeCuts[nodeId], pNewCut)) {
                if (DEBUG_MODE) printf("    [DUPLICATE] Cut already exists, skipping\n");
                Lsv_CutFree(pNewCut);
                continue;
            }
            
            // Add output node to this cut
            Vec_IntPush(pNewCut->vOutputs, nodeId);
            
            // Check dominance: filter out dominated cuts or reject if dominated
            if (Lsv_CutFilterDominated(ppNodeCuts[nodeId], pNewCut, nodeId, vAllCuts)) {
                // pNewCut is dominated by existing cut, reject it
                Lsv_CutFree(pNewCut);
                continue;
            }
            
            // Add the new irredundant cut
            Vec_PtrPush(ppNodeCuts[nodeId], pNewCut);
            Vec_PtrPush(vAllCuts, pNewCut);
            
            if (DEBUG_MODE) printf("[DEBUG] Node %d: created new cut with %d inputs\n", 
                   nodeId, pNewCut->nInputs);
        }
    }
    
    if (DEBUG_MODE) {
        printf("[DEBUG] Node %d: total %d cuts\n", nodeId, Vec_PtrSize(ppNodeCuts[nodeId]));
        
        // Print all cuts for this node
        Lsv_Cut_t* pCutTemp;
        int cutIdx;
        Vec_PtrForEachEntry(Lsv_Cut_t*, ppNodeCuts[nodeId], pCutTemp, cutIdx) {
            printf("  Cut %d: inputs={", cutIdx);
            for (int m = 0; m < Vec_IntSize(pCutTemp->vInputs); m++) {
                if (m > 0) printf(", ");
                printf("%d", Vec_IntEntry(pCutTemp->vInputs, m));
            }
            printf("}, outputs={");
            for (int m = 0; m < Vec_IntSize(pCutTemp->vOutputs); m++) {
                if (m > 0) printf(", ");
                printf("%d", Vec_IntEntry(pCutTemp->vOutputs, m));
            }
            printf("}\n");
        }
    }
}

void Lsv_NtkPrintMOCut(Abc_Ntk_t* pNtk, int k, int l) {
    Abc_Obj_t* pObj;
    int i;
    int nObjMax = Abc_NtkObjNumMax(pNtk);
    
    if (DEBUG_MODE) {
        printf("Computing %d-%d multi-output cuts...\n", k, l);
        printf("Network has %d PIs, %d POs, %d nodes\n", 
               Abc_NtkPiNum(pNtk), Abc_NtkPoNum(pNtk), Abc_NtkNodeNum(pNtk));
        printf("Max object ID: %d\n\n", nObjMax);
    }
    
    // Allocate cut storage for each node
    Vec_Ptr_t** ppNodeCuts = ABC_CALLOC(Vec_Ptr_t*, nObjMax);
    for (i = 0; i < nObjMax; i++) {
        ppNodeCuts[i] = Vec_PtrAlloc(16);  // Initial capacity
    }
    
    // Global list of all cuts
    Vec_Ptr_t* vAllCuts = Vec_PtrAlloc(1000);
    
    // Step 1: Process all Primary Inputs
    if (DEBUG_MODE) printf("=== Processing Primary Inputs ===\n");
    Abc_NtkForEachPi(pNtk, pObj, i) {
        Lsv_NodeComputeCuts(pObj, ppNodeCuts, vAllCuts, k);
    }
    
    // Step 2: Process all internal nodes in topological order
    if (DEBUG_MODE) printf("\n=== Processing Internal Nodes ===\n");
    Abc_NtkForEachNode(pNtk, pObj, i) {
        Lsv_NodeComputeCuts(pObj, ppNodeCuts, vAllCuts, k);
    }
    
    // Step 3: Print statistics
    if (DEBUG_MODE) {
        printf("\n=== Cut Enumeration Complete ===\n");
        printf("Total cuts generated: %d\n", Vec_PtrSize(vAllCuts));
    }
    
    // Step 4: Find multi-output cuts using hash table optimization
    if (DEBUG_MODE) printf("\n=== Finding Multi-Output Cuts (l >= %d) ===\n", l);
    
    // Create hash table: Key = input signature (string), Value = merged cut
    // This reduces complexity from O(n^2) to O(n)
    st__table* tInputToCut = st__init_table(strcmp, st__strhash);
    Vec_Ptr_t* vMultiOutputCuts = Vec_PtrAlloc(100);
    
    if (DEBUG_MODE) printf("[DEBUG] Building hash table to group cuts by inputs...\n");
    
    Lsv_Cut_t* pCut;
    int ii, m;
    
    // Process each cut and group by input signature
    Vec_PtrForEachEntry(Lsv_Cut_t*, vAllCuts, pCut, ii) {
        // Skip trivial cuts (single node as both input and output)
        if (Vec_IntSize(pCut->vInputs) == 1 && 
            Vec_IntSize(pCut->vOutputs) == 1 &&
            Vec_IntEntry(pCut->vInputs, 0) == Vec_IntEntry(pCut->vOutputs, 0)) {
            continue;
        }
        
        // Generate hash key from sorted inputs: "2_3_5_7"
        // Maximum key length: k inputs * (10 digits + 1 underscore) + null terminator
        char key[256];
        key[0] = '\0';
        char temp[32];
        for (m = 0; m < Vec_IntSize(pCut->vInputs); m++) {
            if (m > 0) strcat(key, "_");
            sprintf(temp, "%d", Vec_IntEntry(pCut->vInputs, m));
            strcat(key, temp);
        }
        
        // Look up if we've seen this input signature before
        Lsv_Cut_t* pExistingCut;
        if (st__lookup(tInputToCut, key, (char**)&pExistingCut)) {
            // Found existing cut with same inputs - merge outputs
            if (DEBUG_MODE) {
                printf("[DEBUG] Merging outputs for key '%s'\n", key);
            }
            
            // Add all outputs from current cut to existing cut
            for (m = 0; m < Vec_IntSize(pCut->vOutputs); m++) {
                int outputId = Vec_IntEntry(pCut->vOutputs, m);
                // Check if output already exists (avoid duplicates)
                if (Vec_IntFind(pExistingCut->vOutputs, outputId) == -1) {
                    Vec_IntPush(pExistingCut->vOutputs, outputId);
                }
            }
        } else {
            // First time seeing this input signature - create new merged cut
            Lsv_Cut_t* pNewCut = Lsv_CutAlloc(Vec_IntSize(pCut->vInputs));
            
            // Copy inputs
            for (m = 0; m < Vec_IntSize(pCut->vInputs); m++) {
                Vec_IntPush(pNewCut->vInputs, Vec_IntEntry(pCut->vInputs, m));
            }
            pNewCut->nInputs = Vec_IntSize(pCut->vInputs);
            
            // Copy outputs
            for (m = 0; m < Vec_IntSize(pCut->vOutputs); m++) {
                Vec_IntPush(pNewCut->vOutputs, Vec_IntEntry(pCut->vOutputs, m));
            }
            
            // Store in hash table (need to duplicate key string)
            char* keyCopy = Abc_UtilStrsav(key);
            st__insert(tInputToCut, keyCopy, (char*)pNewCut);
            
            if (DEBUG_MODE) {
                printf("[DEBUG] New cut with key '%s', inputs=%d, outputs=%d\n", 
                       key, Vec_IntSize(pNewCut->vInputs), Vec_IntSize(pNewCut->vOutputs));
            }
        }
    }
    
    if (DEBUG_MODE) {
        printf("[DEBUG] Hash table built with %d unique input signatures\n", st__count(tInputToCut));
    }
    
    // Extract cuts from hash table and filter by output count
    st__generator* gen;
    const char* key;
    Lsv_Cut_t* pMergedCut;
    st__foreach_item(tInputToCut, gen, &key, (char**)&pMergedCut) {
        // Sort outputs for consistent ordering
        Vec_IntSort(pMergedCut->vOutputs, 0);
        
        int nOutputs = Vec_IntSize(pMergedCut->vOutputs);
        
        if (DEBUG_MODE) {
            printf("[DEBUG] Cut with inputs={");
            for (m = 0; m < Vec_IntSize(pMergedCut->vInputs); m++) {
                if (m > 0) printf(", ");
                printf("%d", Vec_IntEntry(pMergedCut->vInputs, m));
            }
            printf("} has %d outputs: {", nOutputs);
            for (m = 0; m < nOutputs; m++) {
                if (m > 0) printf(", ");
                printf("%d", Vec_IntEntry(pMergedCut->vOutputs, m));
            }
            printf("}\n");
        }
        
        if (nOutputs >= l) {
            if (DEBUG_MODE) printf("  -> This is a multi-output cut!\n");
            Vec_PtrPush(vMultiOutputCuts, pMergedCut);
        } else {
            // Free cut if it doesn't meet output threshold
            Lsv_CutFree(pMergedCut);
        }
        
        // Free the key string we allocated
        ABC_FREE(key);
    }
    
    // Free hash table structure (cuts are either in vMultiOutputCuts or freed)
    st__free_table(tInputToCut);
    
    if (DEBUG_MODE) {
        printf("\n=== Multi-Output Cut Summary ===\n");
        printf("Found %d multi-output cuts with l >= %d\n", Vec_PtrSize(vMultiOutputCuts), l);
    }
    
    // Step 5: Format and print output
    // printf("\n");
    Lsv_Cut_t* pMOCut;
    Vec_PtrForEachEntry(Lsv_Cut_t*, vMultiOutputCuts, pMOCut, i) {
        // Print inputs
        int m;
        for (m = 0; m < Vec_IntSize(pMOCut->vInputs); m++) {
            if (m > 0) printf(" ");
            printf("%d", Vec_IntEntry(pMOCut->vInputs, m));
        }
        
        printf(" : ");
        
        // Print outputs
        for (m = 0; m < Vec_IntSize(pMOCut->vOutputs); m++) {
            if (m > 0) printf(" ");
            printf("%d", Vec_IntEntry(pMOCut->vOutputs, m));
        }
        
        printf("\n");
    }
    
    // Cleanup
    for (i = 0; i < nObjMax; i++) {
        Vec_PtrFree(ppNodeCuts[i]);
    }
    ABC_FREE(ppNodeCuts);
    
    // Free all cuts (reuse pCut variable from above)
    Vec_PtrForEachEntry(Lsv_Cut_t*, vAllCuts, pCut, i) {
        Lsv_CutFree(pCut);
    }
    Vec_PtrFree(vAllCuts);
    
    // Free multi-output cuts
    Vec_PtrForEachEntry(Lsv_Cut_t*, vMultiOutputCuts, pCut, i) {
        Lsv_CutFree(pCut);
    }
    Vec_PtrFree(vMultiOutputCuts);
}

int Lsv_CommandPrintMOCut(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int k, l;
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
  
  // Check if network exists
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  
  // Check if network is AIG (strashed)
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "Network must be an AIG. Run 'strash' first.\n");
    return 1;
  }
  
  // Parse k and l parameters
  if (argc != 3) {
    Abc_Print(-1, "Error: Wrong number of arguments.\n");
    goto usage;
  }
  
  k = atoi(argv[1]);
  l = atoi(argv[2]);
  
  // Validate parameters
  if (k < 3 || k > 6) {
    Abc_Print(-1, "Error: k must be in range [3, 6].\n");
    return 1;
  }
  
  if (l < 1 || l > 4) {
    Abc_Print(-1, "Error: l must be in range [1, 4].\n");
    return 1;
  }
  
  // Execute the main function
  Lsv_NtkPrintMOCut(pNtk, k, l);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_printmocut <k> <l>\n");
  Abc_Print(-2, "\t        enumerate k-l multi-output cuts in an AIG\n");
  Abc_Print(-2, "\t<k>   : cut size (3 <= k <= 6)\n");
  Abc_Print(-2, "\t<l>   : minimum number of outputs (1 <= l <= 4)\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}
//----------------------------------------PA1 Multi_output_cut----------------------------------------------//

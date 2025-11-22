/**
 * Logic Synthesis & Verification, Fall 2025
 * Programming Assignment 2 (Integrated with PA1/MoCut)
 */

 #include "base/abc/abc.h"
 #include "base/main/main.h"
 #include "base/main/mainInt.h"
 
 // PA2 Required Headers
 #include "sat/cnf/cnf.h"
 #include "bdd/cudd/cudd.h"
 #include "bdd/cudd/cuddInt.h"
 
 // PA1/Demo Required Headers
 #include <vector>
 #include <algorithm>
 #include <unordered_map>
 #include <string>
 #include <set>
 
 // PA2 Extern Declaration
 extern "C" {
     Aig_Man_t* Abc_NtkToDar(Abc_Ntk_t * pNtk, int fExors, int fRegisters);
     void Aig_ManStop(Aig_Man_t * p); 
 }
 
 // Forward Declarations
 static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
 static int Lsv_CommandPrintMoCut(Abc_Frame_t* pAbc, int argc, char** argv);
 // PA2 Commands
 static int Lsv_CommandUnateBdd(Abc_Frame_t* pAbc, int argc, char** argv);
 static int Lsv_CommandUnateSat(Abc_Frame_t* pAbc, int argc, char** argv);
 
 // ===========================================================================
 // Initialization & Registration
 // ===========================================================================
 
 void init(Abc_Frame_t* pAbc) {
     // Original Commands
     Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
     Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocut", Lsv_CommandPrintMoCut, 0);
     
     // PA2 Commands
     Cmd_CommandAdd(pAbc, "LSV", "lsv_unate_bdd", Lsv_CommandUnateBdd, 0);
     Cmd_CommandAdd(pAbc, "LSV", "lsv_unate_sat", Lsv_CommandUnateSat, 0);
 }
 
 void destroy(Abc_Frame_t* pAbc) {}
 
 Abc_FrameInitializer_t frame_initializer = {init, destroy};
 
 struct PackageRegistrationManager {
     PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
 } lsvPackageRegistrationManager;
 
 
 // ===========================================================================
 // Original Implementation (lsv_print_nodes & lsv_printmocut)
 // ===========================================================================
 
 void Lsv_NtkPrintNodes(Abc_Ntk_t* pNtk) {
     printf("Printing nodes...\n");
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
 
 // Utilities for k-l multi-output cuts
 static std::string Lsv_KeyFromCut(const std::vector<int>& cut) {
     std::string key;
     for (size_t i = 0; i < cut.size(); ++i) {
         if (i) key.push_back(' ');
         char buf[32];
         int n = snprintf(buf, sizeof(buf), "%d", cut[i]);
         key.append(buf, (size_t)n);
     }
     return key;
 }
 
 static std::vector<int> Lsv_MergeCutsLimited(const std::vector<int>& a,
                                              const std::vector<int>& b,
                                              int k,
                                              bool* ok) {
     std::vector<int> out;
     out.reserve(a.size() + b.size());
     size_t i = 0, j = 0;
     while (i < a.size() || j < b.size()) {
         int va = (i < a.size()) ? a[i] : 0x7fffffff;
         int vb = (j < b.size()) ? b[j] : 0x7fffffff;
         int v = va < vb ? va : vb;
         out.push_back(v);
         if (va == v) ++i;
         if (vb == v) ++j;
         if ((int)out.size() > k) { *ok = false; return {}; }
     }
     *ok = true;
     return out;
 }
 
 static bool Lsv_IsSuperset(const std::vector<int>& a, const std::vector<int>& b) {
     // return true if a is a strict superset of b (all b in a, and sizes differ)
     if (a.size() <= b.size()) return false;
     size_t i = 0, j = 0;
     while (i < a.size() && j < b.size()) {
         if (a[i] == b[j]) { ++i; ++j; }
         else if (a[i] < b[j]) { ++i; }
         else { return false; }
     }
     return j == b.size();
 }
 
 static int Lsv_CommandPrintMoCut(Abc_Frame_t* pAbc, int argc, char** argv) {
     Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
     if (!pNtk) { Abc_Print(-1, "Empty network.\n"); return 1; }
     if (!Abc_NtkIsStrash(pNtk)) {
         Abc_Print(-1, "Please run 'strash' before lsv_printmocut.\n");
         return 1;
     }
 
     if (argc != 3) {
         Abc_Print(-2, "usage: lsv_printmocut <k> <l>\n");
         Abc_Print(-2, "\t  3 <= k <= 6, 1 <= l <= 4\n");
         return 1;
     }
     int k = atoi(argv[1]);
     int l = atoi(argv[2]);
     if (k < 3 || k > 6 || l < 1 || l > 4) {
         Abc_Print(-1, "Argument out of range.\n");
         return 1;
     }
 
     // Topological order of internal nodes
     Vec_Ptr_t* vDfs = Abc_AigDfs(pNtk, 0, 0);
     int nDfs = vDfs ? Vec_PtrSize(vDfs) : 0;
 
     // Map from object id to list of cuts (each cut is sorted vector<int>)
     std::vector< std::vector< std::vector<int> > > idToCuts(Abc_NtkObjNumMax(pNtk) + 1);
 
     // Initialize PI cuts and treat them as outputs
     Abc_Obj_t* pObj;
     int i;
     Abc_NtkForEachPi(pNtk, pObj, i) {
         int id = Abc_ObjId(pObj);
         idToCuts[id].push_back(std::vector<int>(1, id));
     }
 
     // For AND nodes in DFS order, build cuts from fanin cuts and the trivial {node}
     for (i = 0; i < nDfs; ++i) {
         Abc_Obj_t* pNode = (Abc_Obj_t*)Vec_PtrEntry(vDfs, i);
         int id = Abc_ObjId(pNode);
         if (!Abc_ObjIsNode(pNode)) continue;
 
         // trivial cut {node}
         idToCuts[id].push_back(std::vector<int>(1, id));
 
         Abc_Obj_t* pF0 = Abc_ObjFanin0(pNode);
         Abc_Obj_t* pF1 = Abc_ObjFanin1(pNode);
         int id0 = Abc_ObjId(pF0);
         int id1 = Abc_ObjId(pF1);
         const auto& cuts0 = idToCuts[id0];
         const auto& cuts1 = idToCuts[id1];
 
         std::set<std::string> seen;
         // keep already inserted trivial {node}
         seen.insert(Lsv_KeyFromCut(idToCuts[id][0]));
 
         for (size_t a = 0; a < cuts0.size(); ++a) {
             for (size_t b = 0; b < cuts1.size(); ++b) {
                 bool ok = false;
                 std::vector<int> merged = Lsv_MergeCutsLimited(cuts0[a], cuts1[b], k, &ok);
                 if (!ok) continue;
                 std::string key = Lsv_KeyFromCut(merged);
                 if (seen.insert(key).second) {
                     idToCuts[id].push_back(std::move(merged));
                 }
             }
         }
 
         // Filter non-irrelevant: remove any cut that is a strict superset of another
         auto& cutsN = idToCuts[id];
         std::vector<char> drop(cutsN.size(), 0);
         for (size_t a = 0; a < cutsN.size(); ++a) {
             if (drop[a]) continue;
             for (size_t b = 0; b < cutsN.size(); ++b) {
                 if (a == b || drop[b]) continue;
                 if (Lsv_IsSuperset(cutsN[a], cutsN[b])) { drop[a] = 1; break; }
             }
         }
         std::vector< std::vector<int> > filtered;
         filtered.reserve(cutsN.size());
         for (size_t a = 0; a < cutsN.size(); ++a) if (!drop[a]) filtered.push_back(std::move(cutsN[a]));
         idToCuts[id].swap(filtered);
     }
 
     if (vDfs) Vec_PtrFree(vDfs);
 
     // Group multi-output cuts across all outputs (PIs and AND nodes)
     std::unordered_map<std::string, std::vector<int> > cutToOutputs;
     std::unordered_map<std::string, std::vector<int> > keyToInputs;
 
     // Add PIs
     Abc_NtkForEachPi(pNtk, pObj, i) {
         int id = Abc_ObjId(pObj);
         for (const auto& cut : idToCuts[id]) {
             std::string key = Lsv_KeyFromCut(cut);
             cutToOutputs[key].push_back(id);
             if (!keyToInputs.count(key)) keyToInputs[key] = cut;
         }
     }
     // Add AND nodes
     Abc_NtkForEachNode(pNtk, pObj, i) {
         int id = Abc_ObjId(pObj);
         for (const auto& cut : idToCuts[id]) {
             std::string key = Lsv_KeyFromCut(cut);
             cutToOutputs[key].push_back(id);
             if (!keyToInputs.count(key)) keyToInputs[key] = cut;
         }
     }
 
     // Collect and sort results before printing
     std::vector<std::pair<std::vector<int>, std::vector<int>>> results;
     for (const auto& kv : cutToOutputs) {
         const std::string& key = kv.first;
         const auto& outs = kv.second;
         if ((int)outs.size() < l) continue;
         const auto& ins = keyToInputs[key];
         
         // Sort inputs and outputs
         std::vector<int> sortedIns = ins;
         std::sort(sortedIns.begin(), sortedIns.end());
         std::vector<int> sortedOuts = outs;
         std::sort(sortedOuts.begin(), sortedOuts.end());
         
         results.push_back({sortedIns, sortedOuts});
     }
     
     // Sort results by input cuts (lexicographically)
     std::sort(results.begin(), results.end());
     
     // Print sorted results
     for (const auto& result : results) {
         const auto& sortedIns = result.first;
         const auto& sortedOuts = result.second;
         
         // print inputs
         for (size_t t = 0; t < sortedIns.size(); ++t) {
             if (t) printf(" ");
             printf("%d", sortedIns[t]);
         }
         printf(" : ");
         // print outputs
         for (size_t t = 0; t < sortedOuts.size(); ++t) {
             if (t) printf(" ");
             printf("%d", sortedOuts[t]);
         }
         printf("\n");
     }
 
     return 0;
 }
 
 // ===========================================================================
 // PA2 Implementation (lsv_unate_bdd & lsv_unate_sat)
 // ===========================================================================
 
 // Helper to print BDD patterns
 void Lsv_PrintBddPattern(DdManager * dd, DdNode * node, int nPis, int targetPiIndex) {
     int nVars = Cudd_ReadSize(dd);
     char * cube = new char[nVars]; 
     
     Cudd_bddPickOneCube(dd, node, cube);
     
     for (int i = 0; i < nPis; i++) {
         if (i == targetPiIndex) {
             printf("-");
         } else {
             printf("%d", (cube[i] == 1) ? 1 : 0); 
         }
     }
     printf("\n");
     delete[] cube;
 }
 
 int Lsv_CommandUnateBdd(Abc_Frame_t* pAbc, int argc, char** argv) {
     Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
     int outIndex, inIndex;
 
     if (argc != 3) {
         Abc_Print(-1, "Usage: lsv_unate_bdd <k> <i>\n");
         return 1;
     }
 
     if (!pNtk) {
         Abc_Print(-1, "Empty network.\n");
         return 1;
     }
     
     if (!Abc_NtkIsBddLogic(pNtk)) {
         Abc_Print(-1, "Network involves logic nodes but is not in BDD format. Run 'collapse' first.\n");
         return 1;
     }
 
     outIndex = atoi(argv[1]);
     inIndex = atoi(argv[2]);
 
     if (outIndex >= Abc_NtkPoNum(pNtk) || inIndex >= Abc_NtkPiNum(pNtk)) {
         Abc_Print(-1, "Index out of bounds.\n");
         return 1;
     }
 
     Abc_Obj_t* pPo = Abc_NtkPo(pNtk, outIndex);
     
     Abc_Obj_t* pDriver = Abc_ObjFanin0(pPo);
     DdManager * dd = (DdManager *)pNtk->pManFunc;
     
     DdNode * func = (DdNode *)pDriver->pData;
     if (Abc_ObjFaninC0(pPo)) {
         func = Cudd_Not(func);
     }
     
     DdNode * var = Cudd_bddIthVar(dd, inIndex);
     Cudd_Ref(var);
 
     // Compute Cofactors
     DdNode * cof1 = Cudd_Cofactor(dd, func, var);
     DdNode * cof0 = Cudd_Cofactor(dd, func, Cudd_Not(var));
 
     Cudd_Ref(cof1);
     Cudd_Ref(cof0);
 
     // Check Unateness
     int isPosUnate = Cudd_bddLeq(dd, cof0, cof1);
     int isNegUnate = Cudd_bddLeq(dd, cof1, cof0);
 
     if (isPosUnate && isNegUnate) {
         printf("independent\n");
     } else if (isPosUnate) {
         printf("positive unate\n");
     } else if (isNegUnate) {
         printf("negative unate\n");
     } else {
         printf("binate\n");
         
         // Pattern 1: Positive behavior (Counter-example for Negative Unate)
         DdNode * diff1 = Cudd_bddAnd(dd, cof1, Cudd_Not(cof0));
         Cudd_Ref(diff1);
         Lsv_PrintBddPattern(dd, diff1, Abc_NtkPiNum(pNtk), inIndex);
         Cudd_RecursiveDeref(dd, diff1);
 
         // Pattern 2: Negative behavior (Counter-example for Positive Unate)
         DdNode * diff2 = Cudd_bddAnd(dd, cof0, Cudd_Not(cof1));
         Cudd_Ref(diff2);
         Lsv_PrintBddPattern(dd, diff2, Abc_NtkPiNum(pNtk), inIndex);
         Cudd_RecursiveDeref(dd, diff2);
     }
 
     Cudd_RecursiveDeref(dd, cof1);
     Cudd_RecursiveDeref(dd, cof0);
     Cudd_RecursiveDeref(dd, var);
 
     return 0;
 }
 
 int Lsv_CommandUnateSat(Abc_Frame_t* pAbc, int argc, char** argv) {
     Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
     int outIndex, inIndex;
 
     if (argc != 3) {
         Abc_Print(-1, "Usage: lsv_unate_sat <k> <i>\n");
         return 1;
     }
     
     outIndex = atoi(argv[1]);
     inIndex = atoi(argv[2]);
 
     if (!pNtk) return 1;
 
     Abc_Obj_t* pPo = Abc_NtkPo(pNtk, outIndex);
     
     // 1. Extract Cone with fUseAllCis = 0
     // [IMPORTANT] This is the key fix. Only include PIs that physically drive the output logic.
     // Any PI NOT in this cone is structurally independent.
     Abc_Ntk_t* pCone = Abc_NtkCreateCone(pNtk, Abc_ObjFanin0(pPo), Abc_ObjName(pPo), 0);
     if (Abc_ObjFaninC0(pPo)) {
         Abc_ObjXorFaninC(Abc_NtkPo(pCone, 0), 0);
     }
 
     // 2. Convert to AIG
     Aig_Man_t* pAig = Abc_NtkToDar(pCone, 0, 0);
     
     // 3. Check if Target Input exists in the Cone
     // Using Name Mapping is the most reliable way.
     Abc_Obj_t* pTargetPi = Abc_NtkPi(pNtk, inIndex);
     char* pTargetName = Abc_ObjName(pTargetPi);
     Abc_Obj_t* pTargetConePi = Abc_NtkFindCi(pCone, pTargetName);
     
     // If input is not in Cone, it implies Independence.
     if (!pTargetConePi) {
         printf("independent\n");
         Aig_ManStop(pAig);
         Abc_NtkDelete(pCone);
         return 0;
     }
 
     // 4. Derive CNF
     Cnf_Dat_t* pCnf = Cnf_Derive(pAig, 1);
 
     // Identify Target Variable in CNF
     Aig_Obj_t* pTargetAigPi = (Aig_Obj_t*)pTargetConePi->pCopy;
     int targetCnfVar = pCnf->pVarNums[pTargetAigPi->Id];
     
     // Double check for valid CNF var (should be valid if present in AIG)
     if (targetCnfVar == -1) {
          printf("independent\n");
          Cnf_DataFree(pCnf);
          Aig_ManStop(pAig);
          Abc_NtkDelete(pCone);
          return 0;
     }
 
     // 5. Initialize SAT Solver (Instance A)
     sat_solver* pSat = sat_solver_new();
     Cnf_DataWriteIntoSolverInt(pSat, pCnf, 1, 0);
     
     // 6. Lift and Add Instance B
     int nVars = pCnf->nVars;
     Cnf_DataLift(pCnf, nVars); 
     
     sat_solver_setnvars(pSat, 2 * nVars + 16); // Manual Resize
     Cnf_DataWriteIntoSolverInt(pSat, pCnf, 1, 0);
     
     // 7. Equality Constraints
     // Iterate over ALL Original PIs. 
     // If a PI is in the Cone (and not target), constrain it.
     // If a PI is NOT in the Cone, ignore it (it doesn't affect output).
     int nPis = Abc_NtkPiNum(pNtk);
     for (int j = 0; j < nPis; j++) {
         if (j == inIndex) continue;
         
         Abc_Obj_t* pOriginalPi = Abc_NtkPi(pNtk, j);
         char* pName = Abc_ObjName(pOriginalPi);
         Abc_Obj_t* pConePi = Abc_NtkFindCi(pCone, pName);
         
         if (!pConePi) continue; // Not in Cone -> Independent -> No constraint needed
         
         Aig_Obj_t* pAigPi = (Aig_Obj_t*)pConePi->pCopy;
         if (!pAigPi) continue;
         
         int varA = pCnf->pVarNums[pAigPi->Id];
         if (varA == -1) continue;
         
         int varB = varA + nVars;
         if (varB >= sat_solver_nvars(pSat)) sat_solver_setnvars(pSat, varB + 16);
         
         // Add Equality Clause (A XNOR B)
         lit lits[2];
         lits[0] = toLitCond(varA, 1); lits[1] = toLitCond(varB, 0); 
         sat_solver_addclause(pSat, lits, lits + 2);
         lits[0] = toLitCond(varA, 0); lits[1] = toLitCond(varB, 1); 
         sat_solver_addclause(pSat, lits, lits + 2);
     }
 
     // Setup Target Variables
     int varInA = targetCnfVar;
     int varInB = varInA + nVars;
     
     int outId = Aig_ObjFanin0(Aig_ManCo(pAig, 0))->Id;
     int varOutA = pCnf->pVarNums[outId];
     int varOutB = varOutA + nVars;
     int outCompl = Aig_ObjFaninC0(Aig_ManCo(pAig, 0));
 
     // --- Check 1: Positive Behavior ---
     lit Lits[4];
     Lits[0] = toLitCond(varInA, 1); // xA=0
     Lits[1] = toLitCond(varInB, 0); // xB=1
     
     int valYA = 0, valYB = 1;
     int driverValA = outCompl ? !valYA : valYA;
     int driverValB = outCompl ? !valYB : valYB;
     
     Lits[2] = toLitCond(varOutA, !driverValA);
     Lits[3] = toLitCond(varOutB, !driverValB);
 
     int status1 = sat_solver_solve(pSat, Lits, Lits + 4, 0, 0, 0, 0);
     bool hasPosBehavior = (status1 == l_True); 
     
     std::vector<int> pattern1; 
     if (hasPosBehavior) {
         for (int j = 0; j < nPis; j++) {
             if (j == inIndex) pattern1.push_back(2); 
             else {
                 Abc_Obj_t* pOriginalPi = Abc_NtkPi(pNtk, j);
                 char* pName = Abc_ObjName(pOriginalPi);
                 Abc_Obj_t* pConePi = Abc_NtkFindCi(pCone, pName);
                 int val = 0;
                 if (pConePi) {
                     Aig_Obj_t* pAigPi = (Aig_Obj_t*)pConePi->pCopy;
                     if (pAigPi && pCnf->pVarNums[pAigPi->Id] != -1) {
                         val = sat_solver_var_value(pSat, pCnf->pVarNums[pAigPi->Id]);
                     }
                 }
                 pattern1.push_back(val);
             }
         }
     }
 
     // --- Check 2: Negative Behavior ---
     valYA = 1; valYB = 0;
     driverValA = outCompl ? !valYA : valYA;
     driverValB = outCompl ? !valYB : valYB;
     
     Lits[2] = toLitCond(varOutA, !driverValA);
     Lits[3] = toLitCond(varOutB, !driverValB);
     
     int status2 = sat_solver_solve(pSat, Lits, Lits + 4, 0, 0, 0, 0);
     bool hasNegBehavior = (status2 == l_True);
 
     std::vector<int> pattern2;
     if (hasNegBehavior) {
         for (int j = 0; j < nPis; j++) {
             if (j == inIndex) pattern2.push_back(2);
             else {
                 Abc_Obj_t* pOriginalPi = Abc_NtkPi(pNtk, j);
                 char* pName = Abc_ObjName(pOriginalPi);
                 Abc_Obj_t* pConePi = Abc_NtkFindCi(pCone, pName);
                 int val = 0;
                 if (pConePi) {
                     Aig_Obj_t* pAigPi = (Aig_Obj_t*)pConePi->pCopy;
                     if (pAigPi && pCnf->pVarNums[pAigPi->Id] != -1) {
                         val = sat_solver_var_value(pSat, pCnf->pVarNums[pAigPi->Id]);
                     }
                 }
                 pattern2.push_back(val);
             }
         }
     }
 
     // Output Results
     if (!hasPosBehavior && !hasNegBehavior) {
         printf("independent\n");
     } else if (hasPosBehavior && !hasNegBehavior) {
         printf("positive unate\n");
     } else if (!hasPosBehavior && hasNegBehavior) {
         printf("negative unate\n");
     } else {
         printf("binate\n");
         for(int val : pattern1) {
             if(val == 2) printf("-");
             else printf("%d", val);
         }
         printf("\n");
         for(int val : pattern2) {
             if(val == 2) printf("-");
             else printf("%d", val);
         }
         printf("\n");
     }
 
     // Cleanup
     sat_solver_delete(pSat);
     Cnf_DataFree(pCnf);
     Aig_ManStop(pAig); 
     Abc_NtkDelete(pCone);
     
     return 0;
 }
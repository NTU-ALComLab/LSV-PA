#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "sat/cnf/cnf.h"
#include "sat/bsat/satStore.h"
#include "lsvpa.h"

#include <vector>
#include <stdlib.h>
#include <algorithm>
#include <iostream>

ABC_NAMESPACE_IMPL_START

static int Lsv_CommandPrintPONodes(Abc_Frame_t* pAbc, int argc, char** argv);

void lsv_print_PONodeinit(Abc_Frame_t* pAbc) {
    Cmd_CommandAdd(pAbc, "LSV", "lsv_print_pounate", Lsv_CommandPrintPONodes, 0);
}

void lsv_print_POdestroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_printpo_initializer = {lsv_print_PONodeinit, lsv_print_POdestroy};

struct PackageRegistrationManager {
    PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_printpo_initializer); }
} lsvPoPackageRegistrationManager;

void print_Abc_Ntk(Abc_Ntk_t* pNtk) {
    int k;
    Abc_Obj_t* ptraversal;
    printf("abc_ntk print nodes\n");
    Abc_NtkForEachNode( pNtk, ptraversal, k) {
        printf("%d %d %d\n", ptraversal-> Id, ptraversal-> fCompl0, ptraversal-> fCompl1);
    }
    printf("pi\n");
    Abc_NtkForEachPi( pNtk, ptraversal, k) {
        printf("%d %d\n", ptraversal-> Id, Abc_ObjIsComplement(ptraversal));
    }
    printf("po\n");
    Abc_NtkForEachPo( pNtk, ptraversal, k) {
        printf("%d %d\n", ptraversal-> Id, Abc_ObjIsComplement(ptraversal));
    }
    printf("\n");
}
void print_Aig_Man(Aig_Man_t* pMan) {
    int k;
    Aig_Obj_t* paig;
    printf("aig_print_nodes\n");
    Aig_ManForEachNode( pMan, paig, k) {
        printf("%d %d\n", paig-> Id, paig-> Type);
    }
    Aig_ManForEachCi( pMan, paig, k) {
        printf("%d %d\n", paig-> Id, paig-> Type);
    }
    Aig_ManForEachCo( pMan, paig, k) {
        printf("%d %d\n", paig-> Id, paig-> Type);
    }
    printf("\n");
}
void print_cnf(Cnf_Dat_t* pCnf) {
    // std::cout << pCnf-> nVars << ' ' << pCnf-> nLiterals << ' ' << pCnf-> nClauses << std::endl;
    Cnf_DataPrint(pCnf, 1);
    int size_aig = pCnf-> pMan-> vObjs-> nSize;
    for(int i = 0 ; i < size_aig ; i++) {
        std::cout << i << ' ' << pCnf-> pVarNums[i] << std::endl;
    }
    printf("\n");
}

void* combine_Cnf_Data_toSolver( Cnf_Dat_t * p1, Cnf_Dat_t * p2 ) {
    sat_solver* pSat = sat_solver_new();
    sat_solver_setnvars( pSat, p1->nVars + p2->nVars );
    for ( int i = 0; i < p1->nClauses; i++ )
    {
        if ( !sat_solver_addclause( pSat, p1->pClauses[i], p1->pClauses[i+1] ) )
        {
            sat_solver_delete( pSat );
            return NULL;
        }
    }
    for ( int i = 0; i < p1->nClauses; i++ )
    {
        if ( !sat_solver_addclause( pSat, p2->pClauses[i], p2->pClauses[i+1] ) )
        {
            sat_solver_delete( pSat );
            return NULL;
        }
    }
    int status = sat_solver_simplify(pSat);
    if ( status == 0 )
    {
        sat_solver_delete( pSat );
        return NULL;
    }
    return pSat;
}

bool comp1(std::pair<unsigned, char*>& a, std::pair<unsigned, char*>& b) {
  return a.first < b.first;  
}
void print_result(
            std::vector<std::pair<unsigned, char*> >& positive_unate_var,
            std::vector<std::pair<unsigned, char*> >& negative_unate_var,
            std::vector<std::pair<unsigned, char*> >& binate_var
        ) 
    {
    sort(positive_unate_var.begin(), positive_unate_var.end(), comp1);
    sort(negative_unate_var.begin(), negative_unate_var.end(), comp1);
    sort(binate_var.begin(), binate_var.end(), comp1);

    for(int n = 0 ; n < positive_unate_var.size() ; n++) {
        if(n == 0) {
        printf("+unate inputs: ");
        printf("%s", positive_unate_var[n].second);
        }
        else printf(",%s", positive_unate_var[n].second);
    }
    if(!positive_unate_var.empty()) printf("\n");

    for(int n = 0 ; n < negative_unate_var.size() ; n++) {
        if(n == 0) {
        printf("-unate inputs: ");
        printf("%s", negative_unate_var[n].second);
        }
        else printf(",%s", negative_unate_var[n].second);
    }
    if(!negative_unate_var.empty()) printf("\n");

    for(int n = 0 ; n < binate_var.size() ; n++) {
        if(n == 0) {
        printf("binate inputs: ");
        printf("%s", binate_var[n].second);
        }
        else printf(",%s", binate_var[n].second);
    }
    if(!binate_var.empty()) printf("\n");
}

void Lsv_NtkPrintPONodes(Abc_Ntk_t* pNtk) {
    assert(pNtk-> ntkType == 3); // strash(aig)
    Abc_Obj_t* pPo;
    int i;
    
    std::vector<std::pair<unsigned, char*> > fanin_name;
    Abc_NtkForEachPi(pNtk, pPo, i) {
      std::pair<unsigned, char*> p(Abc_ObjId(pPo), Abc_ObjName(pPo));
      fanin_name.push_back(p);
    }
    
    Abc_NtkForEachPo(pNtk, pPo, i) {
        printf("node %s:\n", Abc_ObjName(pPo));
        int j;
        Abc_Obj_t* pFanin;
        // po has only one fanin
        Abc_ObjForEachFanin( pPo, pFanin, j ) {
            Abc_Ntk_t* pNtk_cone = Abc_NtkCreateCone(pNtk, pFanin, (char*)"ss", 1);
            if (Abc_ObjFaninC0(pPo) )
            {
                Abc_NtkPo(pNtk_cone, 0)->fCompl0  ^= 1;
            }
            // print_Abc_Ntk(pNtk_cone);
            Aig_Man_t* pMan = Abc_NtkToDar(pNtk_cone, 0, 0);
            // print_Aig_Man(pMan);
            
            Cnf_Dat_t* pCnf = Cnf_Derive(pMan, 1);
            // print_cnf(pCnf);

            Cnf_Dat_t* pCnf_copy = Cnf_DataDup(pCnf);
            Cnf_DataLift(pCnf_copy, pCnf-> nVars);
            // print_cnf(pCnf_copy);
            // printf("========\n");

            // sat solver
            sat_solver* pSat = (sat_solver*) combine_Cnf_Data_toSolver(pCnf, pCnf_copy);
            
            Aig_Obj_t* aig_obj = Aig_ManCo(pMan, 0);
            int aig_po1, aig_po2;
            aig_po1 = pCnf-> pVarNums[aig_obj-> Id];
            aig_po2 = pCnf_copy-> pVarNums[aig_obj-> Id];
            
            int k;
            Aig_ManForEachCi(pMan, aig_obj, k) {
                sat_solver_addvar(pSat);
                sat_solver_add_buffer_enable(
                    pSat, pCnf-> pVarNums[aig_obj-> Id], pCnf_copy-> pVarNums[aig_obj-> Id], pSat->size-1, 0
                );
            }

            int ci_size = pMan-> vCis-> nSize;
            int assumpt_size = ci_size + 4;
            lit* assumption = new lit[assumpt_size];
            
            // init
            for(int vi = pSat->size - ci_size, ai = 0 ; vi < pSat-> size ; vi++, ai++) {
                assumption[ai] = toLitCond(vi, 0);
            }

            std::vector<std::pair<unsigned, char*> > positive_unate_pi;
            std::vector<std::pair<unsigned, char*> > negative_unate_pi;
            std::vector<std::pair<unsigned, char*> > binate_pi;
            Aig_ManForEachCi(pMan, aig_obj, k) {
                assumption[k] += 1;
                assumption[ci_size + 0] = toLitCond(pCnf-> pVarNums[aig_obj-> Id], 0);  // x1 = 1
                assumption[ci_size + 1] = toLitCond(pCnf_copy-> pVarNums[aig_obj-> Id], 1);  // x2 = 0
                
                // pos
                assumption[ci_size + 2] = toLitCond(aig_po1, 1);  // y1 = 0
                assumption[ci_size + 3] = toLitCond(aig_po2, 0);  // y2 = 1
                lbool sat_pos = sat_solver_solve(pSat, assumption, assumption + assumpt_size, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
                if(sat_pos == l_False) {
                    positive_unate_pi.push_back(fanin_name[k]);
                }

                // neg
                assumption[ci_size + 2] = toLitCond(aig_po1, 0);  // y1 = 1
                assumption[ci_size + 3] = toLitCond(aig_po2, 1);  // y2 = 0
                lbool sat_neg = sat_solver_solve(pSat, assumption, assumption + assumpt_size, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
                if(sat_neg == l_False) {
                    negative_unate_pi.push_back(fanin_name[k]);
                }
                if(sat_neg == l_True && sat_pos == l_True) binate_pi.push_back(fanin_name[k]);
                assumption[k] -= 1;
            }
            print_result(positive_unate_pi, negative_unate_pi, binate_pi);
        }
    }
    
}

int Lsv_CommandPrintPONodes(Abc_Frame_t* pAbc, int argc, char** argv) {
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
    Lsv_NtkPrintPONodes(pNtk);
    return 0;

    usage:
    Abc_Print(-2, "usage: lsv_print_pounate [-h]\n");
    Abc_Print(-2, "\t        prints the nodes in the network\n");
    Abc_Print(-2, "\t-h    : print the command usage\n");
    return 1;
}

ABC_NAMESPACE_IMPL_END
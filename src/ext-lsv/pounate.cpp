#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "sat/cnf/cnf.h"
#include "sat/bsat/satSolver.h"
#include "sat/bsat/satStore.h"
#include "pounate.h"
#include <iostream>
#include <vector>
#include <string>


using namespace std;
namespace pounate{

class pi{
public:
    int ID;
    int var;
    int ass_var;
    bool p_unate;
    bool n_unate;
    bool binate;
    pi(int id, int v, int a, bool p, bool n, bool b): ID(id), var(v), ass_var(a), p_unate(p), n_unate(n), binate(b){}
};
class Ntk_pi{
public:
    string name;
    pi inf;
    Ntk_pi(string n, pi p): name(n), inf(p){}
};

void Duplicate_allClauses(sat_solver * p, Cnf_Dat_t * pCnf)
{
    int * pStop;
    int * pLit;
    int RetValue, nClauses, nVarsOld, nLitsOld, c;
    // get the number of variables
    nVarsOld = p->size;
    nLitsOld = 2 * p->size;
    // extend the solver to depend on two sets of variables
    sat_solver_setnvars( p, 2 * p->size );
    // duplicate clauses
    nClauses = pCnf->nClauses;
    for ( c = 0; c < nClauses; c++ )
    {
        for (pLit = pCnf->pClauses[c], pStop = pCnf->pClauses[c+1]; pLit < pStop; pLit++)
            (*pLit) += nLitsOld;
        RetValue = sat_solver_addclause( p, pCnf->pClauses[c], pStop);
        assert( RetValue );
        for (pLit = pCnf->pClauses[c], pStop = pCnf->pClauses[c+1]; pLit < pStop; pLit++)
            (*pLit) -= nLitsOld;
    }

}  

int Write_output_node_clause(sat_solver * pSat, Cnf_Dat_t * pCnf) {
    Aig_Obj_t * pObj;
    int i, * pLits, * pLits2;  //positve, negative
    assert(Aig_ManCoNum(pCnf->pMan) == 1);
    pLits = ABC_ALLOC( int, Aig_ManCoNum(pCnf->pMan) );
    pLits2 = ABC_ALLOC( int, Aig_ManCoNum(pCnf->pMan) );
    Aig_ManForEachCo( pCnf->pMan, pObj, i ) {
        pLits[i] = toLitCond( pCnf->pVarNums[pObj->Id], 0 );
        pLits2[i] = pLits[i] + (pSat->size)  + 1; //negate
        i = sat_solver_addclause( pSat, pLits, pLits + Aig_ManCoNum(pCnf->pMan));
        if(i == 0)
            return 1;
        i = sat_solver_addclause( pSat, pLits2, pLits2 + Aig_ManCoNum(pCnf->pMan));
        if(i == 0)
            return 1;
    }
    return 0;
}

void Sort_Id(vector<Ntk_pi> &v) {
    for(int i = 1; i < v.size(); ++i) {
        Ntk_pi target = v[i];
        int j = i - 1;
        while (target.inf.ID < v[j].inf.ID && j >= 0) {
            v[j+1] = v[j];
            j--;
        }
        v[j+1] = target;
    }
}

vector<pi> add_pi_assumption(sat_solver * pSat, Cnf_Dat_t * pCnf) {
    Aig_Obj_t * pObj;
    int nVarsOld = pSat->size;
    int nPi = Aig_ManCiNum(pCnf->pMan);
    sat_solver_setnvars(pSat, (pSat->size) + nPi);
    int var, i, ass_var;
    int * pLits, * pLits2;
    vector<pi> PI_list;
    Aig_ManForEachCi( pCnf->pMan, pObj, i ) {
        var = pCnf->pVarNums[pObj->Id];
        ass_var = nVarsOld + i + 1;
        pi temp(pObj->Id, var, ass_var, false, false, false);
        PI_list.push_back(temp);
    
        int j;
        int * pLits, * pLits2;
        pLits = ABC_ALLOC(int, 3);
        pLits2 = ABC_ALLOC(int, 3);
        pLits[0] = toLitCond(ass_var, 0 );
        pLits[1] = toLitCond(var, 0 );
        pLits[2] = toLitCond(var + nVarsOld / 2, 1 );
        pLits2[0] = toLitCond(ass_var, 0 );
        pLits2[1] = toLitCond(var, 1 );
        pLits2[2] = toLitCond(var + nVarsOld / 2, 0 );
        j = sat_solver_addclause( pSat, pLits, pLits + 3);
        assert( j != 0);
        j = sat_solver_addclause( pSat, pLits2, pLits2 + 3);
        assert( j != 0);
        
    }
    return PI_list;
}


int Lsv_CommandPrintPoUnate(Abc_Frame_t* pAbc, int argc, char** argv) {
    
    Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
    if(!pNtk) {
        Abc_Print(-1, "Empty Network.\n");
        return 1;
    }
    if(Abc_NtkIsStrash(pNtk) == 0){
        Abc_Print(-1, "The network type should be AIG.\n");
        return 1;
    }
    
    int i;
    Abc_Obj_t* pPo;
    Abc_NtkForEachPo( pNtk, pPo, i ){
        Abc_Ntk_t* pPo_ConeNtk;
        int j, k;
        Aig_Man_t * pMan;
        Cnf_Dat_t * pCnf;
        Abc_Obj_t * p;
        sat_solver * pSat;
        vector<pi> PI_list;
        int status, RetValue = 0;

        pPo_ConeNtk = Abc_NtkCreateCone( pNtk, Abc_ObjFanin0(pPo), Abc_ObjName(pPo), 0 );
        //Negate PO correctly
        Abc_NtkForEachPo( pPo_ConeNtk, p, j ) {
            assert( j == 0);
            if (Abc_ObjFaninC0(pPo) != Abc_ObjFaninC0(p))
                Abc_ObjXorFaninC(p, 0);
        }
        pMan = Abc_NtkToDar(pPo_ConeNtk, 0, 0 );
        pMan->pData = NULL;
        pCnf = Cnf_Derive(pMan, Aig_ManCoNum(pMan) );
        
        pSat = (sat_solver *)Cnf_DataWriteIntoSolver( pCnf, 1, 0 );
        Duplicate_allClauses(pSat, pCnf);
        RetValue = Write_output_node_clause(pSat, pCnf);
        //if(RetValue), all inputs are unate, jump to print output
        if(RetValue == 0){

            Aig_Obj_t * pObj;
            int nVarsOld = pSat->size;
            PI_list = add_pi_assumption(pSat, pCnf);
            assert( PI_list.size() == Aig_ManCiNum(pCnf->pMan));
        
            lit * assumptions = new lit[2 + Aig_ManCiNum(pCnf->pMan)];
            Aig_ManForEachCi( pCnf->pMan, pObj, j ){
                assumptions[j + 2] = (PI_list[j].ass_var) * 2 + 1; //set all eq assumptions is false
            }
        
            Aig_ManForEachCi( pCnf->pMan, pObj, j ){
                int id = pObj->Id;
                assert(PI_list[j].ID == id);
                if(j == 0)
                    assumptions[j + 2] ^= 1;
                else {
                    assumptions[j + 1] ^= 1;
                    assumptions[j + 2] ^= 1;
                }

                // 0 for positive unate, 1 for negative unate
                for(int k = 0; k < 2; ++k) {
                    if(k == 0) {
                        assumptions[0] = toLitCond(PI_list[j].var, 1);
                        assumptions[1] = toLitCond(PI_list[j].var + nVarsOld / 2, 0);
                    }
                    else {
                        assumptions[0] = toLitCond(PI_list[j].var, 0);
                        assumptions[1] = toLitCond(PI_list[j].var + nVarsOld / 2, 1);
                    }
                    status = sat_solver_simplify(pSat);
                    if ( status == 0 )
                    {
                        sat_solver_delete( pSat );
                        if(k == 0)
                            PI_list[j].p_unate = true;
                        else
                            PI_list[j].n_unate = true;
                        //cout << "UNSAT" << endl;
                        return 0;
                    }
                    //sat solving with assumptions
                    status = sat_solver_solve( pSat, assumptions, assumptions + 2 + Aig_ManCiNum(pCnf->pMan), 0, 0, 0, 0 );
               
                    if ( status == l_False )
                    {
                        if(k == 0)
                            PI_list[j].p_unate = true;
                        else
                            PI_list[j].n_unate = true;
                    
                    //cout << "UNSAT" << endl;
                    }
                }
                if(PI_list[j].p_unate == false && PI_list[j].n_unate == false)
                {
                    PI_list[j].binate = true;
                }
                
            }//end of sat solver
            delete assumptions;
        }

        //match pi of cnf and pi of cone ntk
        vector<Ntk_pi> NtkPI_list;
        Abc_NtkForEachPi( pPo_ConeNtk, p, j ) {
            for(int k = 0; k < PI_list.size(); ++k) {
                if(PI_list[k].ID == Abc_ObjId(p)) {
                    Ntk_pi temp(Abc_ObjName(p), PI_list[k]);
                    NtkPI_list.push_back(temp);
                    break;
                }
            }      
        }

        Abc_NtkForEachPi( pNtk, p, j ) {
            //every inputs is unate
            if(NtkPI_list.size() == 0) {
                pi tpi(Abc_ObjId(p), 0, 0, true, true, false);
                Ntk_pi temp(Abc_ObjName(p), tpi);
                NtkPI_list.push_back(temp);
            }
            for(int k = 0; k < NtkPI_list.size(); ++k) {
                if(NtkPI_list[k].name == Abc_ObjName(p)) {
                    NtkPI_list[k].inf.ID = Abc_ObjId(p);
                    break;
                }
                //no match, means independant
                if(k == NtkPI_list.size() - 1) {
                    pi tpi(Abc_ObjId(p), 0, 0, true, true, false);
                    Ntk_pi temp(Abc_ObjName(p), tpi);
                    NtkPI_list.push_back(temp);
                }
            }      
        }

        Sort_Id(NtkPI_list);

        //print
        cout << "node " << Abc_ObjName(Abc_NtkPo( pPo_ConeNtk, 0)) <<':' << endl;
        bool has_pos_unate = false;
        bool has_neg_unate = false;
        bool has_binate = false;

        for(int k = 0; k < NtkPI_list.size(); ++k){
            if(NtkPI_list[k].inf.p_unate == true) {
                if(has_pos_unate == false) {
                    cout << "+unate inputs: ";
                    has_pos_unate = true;
                }
                else
                    cout << ',';
                cout << NtkPI_list[k].name;
            }
        }
        if(has_pos_unate)
            cout << endl;

        for(int k = 0; k < NtkPI_list.size(); ++k){
            if(NtkPI_list[k].inf.n_unate == true) {
                if(has_neg_unate == false) {
                    cout << "-unate inputs: ";
                    has_neg_unate = true;
                }
                else
                    cout << ',';
                cout << NtkPI_list[k].name;
            }
        }
        if(has_neg_unate)
            cout << endl;

        for(int k = 0; k < NtkPI_list.size(); ++k){
            if(NtkPI_list[k].inf.binate == true) {
                if(has_binate == false) {
                    cout << "binate inputs: ";
                    has_binate = true;
                }
                else
                    cout << ',';
                cout << NtkPI_list[k].name;
            }
        }
        if(has_binate)
            cout << endl;
    }
    return 0;
}

void init(Abc_Frame_t* pAbc) {
    Cmd_CommandAdd(pAbc, "Print unate", "lsv_print_pounate", Lsv_CommandPrintPoUnate, 0);
}    

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct registration_lsv_pounate {
    registration_lsv_pounate() { Abc_FrameAddInitializer(&frame_initializer); }
} registration_lsv_pounate;


}//end of namespace

#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "sat/bsat/satSolver.h"
#include "sat/cnf/cnf.h"
#include "aig/aig/aig.h"
//#include "sat/bsat/satStore.h"
//#include "sat/bsat/satVec.h"
#include <iostream>
#include <vector>
#include <algorithm>
#include <unordered_map> 
using namespace std;

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_PrintSopunate_Command(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPOunate(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintPoUnate(Abc_Frame_t* pAbc, int argc, char** argv); //

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd( pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd( pAbc, "LSV", "lsv_print_sopunate", Lsv_PrintSopunate_Command, 0);
  Cmd_CommandAdd(pAbc, "Print unate", "lsv_print_pounate", Lsv_CommandPrintPoUnate, 0);
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
      printf("The SOP of this node:\n%s", (char*)pObj->pData); //Abc_ObjData( Abc_Obj_t * pObj )
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

//=======================
//Print_Sopunate_Command
//=======================
void print_pos_neg_unate(vector<Abc_Obj_t*> &pos_unate, vector<Abc_Obj_t*> &neg_unate, vector<Abc_Obj_t*> &binate);
bool object_id_compare (Abc_Obj_t* a, Abc_Obj_t* b) { return (Abc_ObjId(a) < Abc_ObjId(b)); }
int Lsv_PrintSopunate_Command(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  Abc_Obj_t* pObj;
  Abc_Obj_t* pFanin;
  char * pSop, * pCube;
  int nVars, Value;
  int i, j, k; //i: each node, j: cube for each var, k: each fanin
  int *A;

  vector<Abc_Obj_t*> pos_unate, neg_unate, binate;

  Abc_NtkForEachNode(pNtk, pObj, i) {
    if(Abc_ObjFaninNum(pObj) == 0) continue;

    printf("node %s:\n", Abc_ObjName(pObj));

    if(Abc_NtkHasSop(pNtk)) { 
      pSop = (char*)Abc_ObjData(pObj);
      //printf("The SOP of this node:\n%s", pSop);

      nVars = Abc_SopGetVarNum(pSop);
      //new array
      A = new int[nVars];
      for(int m = 0; m < nVars; m++) //initialization
        A[m] = -1;

      Abc_SopForEachCube( pSop, nVars, pCube ) {
        Abc_CubeForEachVar( pCube, Value, j ) {
          //printf("Value=%d, A[%d]=%d\n", Value, j, A[j]);
          if(A[j] == -1) {
            if(Value == '0' || Value == '1') {
              A[j] = Value - '0';
            }
          }
          else if((A[j]==1 && Value=='0') || (A[j]==0 && Value=='1'))
            A[j] = 3; //binate     
        }
      }

      //catagorize
      Abc_ObjForEachFanin(pObj, pFanin, k) {
        if(A[k] == 1)
          pos_unate.push_back(pFanin);
        else if(A[k] == 0)
          neg_unate.push_back(pFanin);
        else if(A[k] == 3) {
          binate.push_back(pFanin);
          
        }else if(A[k] == -1) {
          pos_unate.push_back(pFanin);
          neg_unate.push_back(pFanin);
        }
      }
      
      delete[] A;

      // sort by object id
      sort(pos_unate.begin(), pos_unate.end(), object_id_compare);
      sort(neg_unate.begin(), neg_unate.end(), object_id_compare);
      sort(binate.begin(), binate.end(), object_id_compare);

      //print
      if(Abc_SopGetPhase(pSop) == 1) 
        print_pos_neg_unate(pos_unate, neg_unate, binate);
      else 
        print_pos_neg_unate(neg_unate, pos_unate, binate); // Abc_SopGetPhase(pSop) == 0 --> negate
    

      pos_unate.clear();
      neg_unate.clear();
      binate.clear();

    }
    
  }
  return 0;
}

void print_pos_neg_unate(vector<Abc_Obj_t*> &pos_unate, vector<Abc_Obj_t*> &neg_unate, vector<Abc_Obj_t*> &binate) {
  if(pos_unate.size() != 0){
    printf("+unate inputs: ");
    for(int m = 0; m < pos_unate.size(); m++) {
      if(m == pos_unate.size() - 1)
        printf("%s\n", Abc_ObjName(pos_unate[m]));
      else  
        printf("%s,", Abc_ObjName(pos_unate[m]));
    }
  }
        
  if(neg_unate.size() != 0){
    printf("-unate inputs: ");
    for(int m = 0; m < neg_unate.size(); m++) {
      if(m == neg_unate.size() - 1)
        printf("%s\n", Abc_ObjName(neg_unate[m]));
      else  
        printf("%s,", Abc_ObjName(neg_unate[m]));
    }
  }

  if(binate.size() != 0){
    printf("binate inputs: ");
    for(int m = 0; m < binate.size(); m++) {
      if(m == binate.size() - 1)
        printf("%s\n", Abc_ObjName(binate[m]));
      else  
        printf("%s,", Abc_ObjName(binate[m]));
    }
  }
}

/**Function*************************************************************

  Synopsis    [Converts the network from the AIG manager into ABC.]

  Description [Assumes that registers are ordered after PIs/POs.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters )
{
    Vec_Ptr_t * vNodes;
    Aig_Man_t * pMan;
    Aig_Obj_t * pObjNew;
    Abc_Obj_t * pObj;
    int i, nNodes, nDontCares;
    // make sure the latches follow PIs/POs
    if ( fRegisters ) 
    { 
        assert( Abc_NtkBoxNum(pNtk) == Abc_NtkLatchNum(pNtk) );
        Abc_NtkForEachCi( pNtk, pObj, i )
            if ( i < Abc_NtkPiNum(pNtk) )
            {
                assert( Abc_ObjIsPi(pObj) );
                if ( !Abc_ObjIsPi(pObj) )
                    Abc_Print( 1, "Abc_NtkToDar(): Temporary bug: The PI ordering is wrong!\n" );
            }
            else
                assert( Abc_ObjIsBo(pObj) );
        Abc_NtkForEachCo( pNtk, pObj, i )
            if ( i < Abc_NtkPoNum(pNtk) )
            {
                assert( Abc_ObjIsPo(pObj) );
                if ( !Abc_ObjIsPo(pObj) )
                    Abc_Print( 1, "Abc_NtkToDar(): Temporary bug: The PO ordering is wrong!\n" );
            }
            else
                assert( Abc_ObjIsBi(pObj) );
        // print warning about initial values
        nDontCares = 0;
        Abc_NtkForEachLatch( pNtk, pObj, i )
            if ( Abc_LatchIsInitDc(pObj) )
            {
                Abc_LatchSetInit0(pObj);
                nDontCares++;
            }
        if ( nDontCares )
        {
            Abc_Print( 1, "Warning: %d registers in this network have don't-care init values.\n", nDontCares );
            Abc_Print( 1, "The don't-care are assumed to be 0. The result may not verify.\n" );
            Abc_Print( 1, "Use command \"print_latch\" to see the init values of registers.\n" );
            Abc_Print( 1, "Use command \"zero\" to convert or \"init\" to change the values.\n" );
        }
    }
    // create the manager
    pMan = Aig_ManStart( Abc_NtkNodeNum(pNtk) + 100 );
    pMan->fCatchExor = fExors;
    pMan->nConstrs = pNtk->nConstrs;
    pMan->nBarBufs = pNtk->nBarBufs;
    pMan->pName = Extra_UtilStrsav( pNtk->pName );
    pMan->pSpec = Extra_UtilStrsav( pNtk->pSpec );
    // transfer the pointers to the basic nodes
    Abc_AigConst1(pNtk)->pCopy = (Abc_Obj_t *)Aig_ManConst1(pMan);
    Abc_NtkForEachCi( pNtk, pObj, i )
    {
        pObj->pCopy = (Abc_Obj_t *)Aig_ObjCreateCi(pMan);
        // initialize logic level of the CIs
        ((Aig_Obj_t *)pObj->pCopy)->Level = pObj->Level;
    }

    // complement the 1-values registers
    if ( fRegisters ) {
        Abc_NtkForEachLatch( pNtk, pObj, i )
            if ( Abc_LatchIsInit1(pObj) )
                Abc_ObjFanout0(pObj)->pCopy = Abc_ObjNot(Abc_ObjFanout0(pObj)->pCopy);
    }
    // perform the conversion of the internal nodes (assumes DFS ordering)
//    pMan->fAddStrash = 1;
    vNodes = Abc_NtkDfs( pNtk, 0 );
    Vec_PtrForEachEntry( Abc_Obj_t *, vNodes, pObj, i )
//    Abc_NtkForEachNode( pNtk, pObj, i )
    {
        pObj->pCopy = (Abc_Obj_t *)Aig_And( pMan, (Aig_Obj_t *)Abc_ObjChild0Copy(pObj), (Aig_Obj_t *)Abc_ObjChild1Copy(pObj) );
//        Abc_Print( 1, "%d->%d ", pObj->Id, ((Aig_Obj_t *)pObj->pCopy)->Id );
    }
    Vec_PtrFree( vNodes );
    pMan->fAddStrash = 0;
    // create the POs
    Abc_NtkForEachCo( pNtk, pObj, i )
        Aig_ObjCreateCo( pMan, (Aig_Obj_t *)Abc_ObjChild0Copy(pObj) );
    // complement the 1-valued registers
    Aig_ManSetRegNum( pMan, Abc_NtkLatchNum(pNtk) );
    if ( fRegisters )
        Aig_ManForEachLiSeq( pMan, pObjNew, i )
            if ( Abc_LatchIsInit1(Abc_ObjFanout0(Abc_NtkCo(pNtk,i))) )
                pObjNew->pFanin0 = Aig_Not(pObjNew->pFanin0);
    // remove dangling nodes
    nNodes = (Abc_NtkGetChoiceNum(pNtk) == 0)? Aig_ManCleanup( pMan ) : 0;
    if ( !fExors && nNodes )
        Abc_Print( 1, "Abc_NtkToDar(): Unexpected %d dangling nodes when converting to AIG!\n", nNodes );
//Aig_ManDumpVerilog( pMan, "test.v" );
    // save the number of registers
    if ( fRegisters )
    {
        Aig_ManSetRegNum( pMan, Abc_NtkLatchNum(pNtk) );
        pMan->vFlopNums = Vec_IntStartNatural( pMan->nRegs );
//        pMan->vFlopNums = NULL;
//        pMan->vOnehots = Abc_NtkConverLatchNamesIntoNumbers( pNtk );
        if ( pNtk->vOnehots )
            pMan->vOnehots = (Vec_Ptr_t *)Vec_VecDupInt( (Vec_Vec_t *)pNtk->vOnehots );
    }
    if ( !Aig_ManCheck( pMan ) )
    {
        Abc_Print( 1, "Abc_NtkToDar: AIG check has failed.\n" );
        Aig_ManStop( pMan );
        return NULL;
    }
    return pMan;
}


class pi_node{
public:
    int id;
    int var;
    int var_dup;
    int enable_var;
    bool pos_unate;
    bool neg_unate;
    bool binate;
    pi_node(int _id, int _var, int _var_dup, int _enable_var, bool pos, bool neg, bool bi): id(_id), var(_var), var_dup(_var_dup), enable_var(_enable_var), pos_unate(pos), neg_unate(neg), binate(bi){}
};
class ntkPI{
public:
    string name;
    pi_node pi;
    ntkPI(string _name, pi_node _pi): name(_name), pi(_pi){}
};

int add_po_clause(sat_solver * pSat, Cnf_Dat_t * pCnf, Cnf_Dat_t * pCnf_dup) {
    Aig_Obj_t * pObj;
    int Lits[1], Lits_neg[1], retval;  //f, negate f
    assert(Aig_ManCoNum(pCnf->pMan) == 1);
  
    pObj = Aig_ManCo(pCnf->pMan, 0);

    Lits[0] = toLitCond( pCnf->pVarNums[pObj->Id], 0 );
    //pLits2[i] = pLits[i] + (pSat->size)  + 1; //negate
    Lits_neg[0] = toLitCond( pCnf_dup->pVarNums[pObj->Id], 1 );
    retval = sat_solver_addclause( pSat, Lits, Lits + 1);
    if(retval == 0) return 1;
        
    retval = sat_solver_addclause( pSat, Lits_neg, Lits_neg + 1);
    if(retval == 0) return 1;
            
    return 0;
}
bool compare (ntkPI a, ntkPI b) { return (a.pi.id < b.pi.id); }

vector<pi_node> add_pi_clause(sat_solver * pSat, Cnf_Dat_t * pCnf, Cnf_Dat_t * pCnf_dup) {
    Aig_Obj_t * pObj;
    int var, i, enable_var, var_dup, retval;
    int Lits[3];
    vector<pi_node> pi_list;
    Aig_ManForEachCi( pCnf->pMan, pObj, i ) {
        var = pCnf->pVarNums[Aig_ObjId(pObj)]; 
        var_dup = pCnf_dup->pVarNums[Aig_ObjId(pObj)];
        enable_var = sat_solver_addvar(pSat);
        pi_node tmp(pObj->Id, var, var_dup, enable_var, false, false, false);
        pi_list.push_back(tmp);
        
        Lits[0] = toLitCond(enable_var, 0 );
        Lits[1] = toLitCond(var, 0 );
        Lits[2] = toLitCond(var_dup, 1 );
        
        retval = sat_solver_addclause( pSat, Lits, Lits + 3);
        assert( retval == 1 );
        
        Lits[0] = toLitCond(enable_var, 0 );
        Lits[1] = toLitCond(var, 1 );
        Lits[2] = toLitCond(var_dup, 0 );
        
        retval = sat_solver_addclause( pSat, Lits, Lits + 3);
        assert( retval == 1 );
        
    }
    return pi_list;
}


int Lsv_CommandPrintPoUnate(Abc_Frame_t* pAbc, int argc, char** argv) {
    
    Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
    int i;
    Abc_Obj_t* pPo;
    Abc_NtkForEachPo( pNtk, pPo, i ){
        Abc_Ntk_t* pNtk_Coned;
        int j;
        Aig_Man_t * pMan;
        Cnf_Dat_t * pCnf, * pCnf_dup;
        Abc_Obj_t * pobj;
        sat_solver * pSat;
        vector<pi_node> pi_list;
        vector<string> pos_unate, neg_unate, binate;
        //bool not_pos_neg_unate = 1;
        
        int status, RetValue = 0;

        pNtk_Coned = Abc_NtkCreateCone( pNtk, Abc_ObjFanin0(pPo), Abc_ObjName(pPo), 0 );
       
        Abc_NtkForEachPo( pNtk_Coned, pobj, j ) { // negate PO
          if (Abc_ObjFaninC0(pPo) != Abc_ObjFaninC0(pobj))
              Abc_ObjXorFaninC(pobj, 0);
        }
        pMan = Abc_NtkToDar(pNtk_Coned, 0, 0 );
        pMan->pData = NULL;
        pCnf = Cnf_Derive(pMan, Aig_ManCoNum(pMan) );
        
        pSat = (sat_solver *)Cnf_DataWriteIntoSolver( pCnf, 1, 0 );
        
        // create copy
        pCnf_dup = Cnf_DataDup(pCnf);
        Cnf_DataLift( pCnf_dup, pCnf->nVars );
        sat_solver_setnvars(pSat, 2 * pSat ->size);
        for(int k = 0; k < pCnf_dup -> nClauses; k++) {
          sat_solver_addclause(pSat, pCnf_dup -> pClauses[k], pCnf_dup -> pClauses[k+1]);
        }
        
        RetValue = add_po_clause(pSat, pCnf, pCnf_dup);
        
        if(RetValue == 0){ 

          Aig_Obj_t * pObj;
          pi_list = add_pi_clause(pSat, pCnf, pCnf_dup);
          assert( pi_list.size() == Aig_ManCiNum(pCnf->pMan));
      
          lit * assumption_list = new lit[2 + Aig_ManCiNum(pCnf->pMan)];
          Aig_ManForEachCi( pCnf->pMan, pObj, j ){
            assumption_list[j + 2] = toLitCond(pi_list[j].enable_var, 1);
          }
      
          Aig_ManForEachCi( pCnf->pMan, pObj, j ){
            int id = pObj->Id;
            assert(pi_list[j].id == id);
            if(j == 0)
                assumption_list[j + 2] ^= 1;  
            else {
                assumption_list[j + 1] ^= 1;
                assumption_list[j + 2] ^= 1;
            }

            for(int t = 0; t < 2; ++t) {
              if(t == 0) { 
                assumption_list[0] = toLitCond(pi_list[j].var, 1);
                assumption_list[1] = toLitCond(pi_list[j].var_dup, 0);
              }
              else {
                assumption_list[0] = toLitCond(pi_list[j].var, 0);
                assumption_list[1] = toLitCond(pi_list[j].var_dup, 1);
              }
              sat_solver_simplify(pSat);

              //sat solving
              status = sat_solver_solve( pSat, assumption_list, assumption_list + 2 + Aig_ManCiNum(pCnf->pMan), 0, 0, 0, 0 );
          
              if ( status == l_False ){
                // unsat
                if(t == 0)
                    pi_list[j].pos_unate = true;
                else
                    pi_list[j].neg_unate = true;
              }
                
            }
            if(pi_list[j].pos_unate == false && pi_list[j].neg_unate == false)
              pi_list[j].binate = true;
      
          }
          delete assumption_list;
        }


        vector<ntkPI> ntkPI_list;
        Abc_NtkForEachPi( pNtk_Coned, pobj, j ) {
          for(int k = 0; k < pi_list.size(); ++k) {
            if(pi_list[k].id == Abc_ObjId(pobj)) {
                ntkPI tmp(Abc_ObjName(pobj), pi_list[k]);
                ntkPI_list.push_back(tmp);
                break;
            }
          }      
        }

        Abc_NtkForEachPi( pNtk, pobj, j ) {
          if(ntkPI_list.size() == 0) {
            pi_node tmppi(Abc_ObjId(pobj), 0, 0, 0, true, true, false);
            ntkPI tmp(Abc_ObjName(pobj), tmppi);
            ntkPI_list.push_back(tmp);
          }
          for(int k = 0; k < ntkPI_list.size(); ++k) {
            if(ntkPI_list[k].name == Abc_ObjName(pobj)) {
              ntkPI_list[k].pi.id = Abc_ObjId(pobj);
              break;
            }
            //independant
            if(k == ntkPI_list.size() - 1) {
              pi_node tmppi(Abc_ObjId(pobj), 0, 0, 0, true, true, false);
              ntkPI tmp(Abc_ObjName(pobj), tmppi);
              ntkPI_list.push_back(tmp);
            }
          }      
        }

        sort(ntkPI_list.begin(), ntkPI_list.end(), compare);

        //print
        printf("node %s:\n", Abc_ObjName(pPo));

        for(int k=0; k < ntkPI_list.size(); k++) {
          if(ntkPI_list[k].pi.pos_unate)
            pos_unate.push_back(ntkPI_list[k].name);
          
          if(ntkPI_list[k].pi.neg_unate)
            neg_unate.push_back(ntkPI_list[k].name);

          if(ntkPI_list[k].pi.binate)
            binate.push_back(ntkPI_list[k].name);
        }
        if(pos_unate.size() > 0) {
          cout << "+unate inputs: " << pos_unate[0];
          for(int m = 1; m < pos_unate.size(); m++)
            cout << "," << pos_unate[m];
          printf("\n");
        }

        if(neg_unate.size() > 0) {
          cout << "-unate inputs: " << neg_unate[0];
          for(int m = 1; m < neg_unate.size(); m++)
            cout << "," << neg_unate[m];
          printf("\n");
        }

        if(binate.size() > 0) {
          cout << "binate inputs: " << binate[0];
          for(int m = 1; m < binate.size(); m++)
            cout << "," << binate[m];
          printf("\n");
        }

        pos_unate.clear();
        neg_unate.clear();
        binate.clear();
    }
    return 0;
}

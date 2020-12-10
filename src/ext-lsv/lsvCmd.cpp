#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "sat/cnf/cnf.h"
#include <iostream>
#include <vector>
#include <algorithm>
#include <unordered_set>
#include <string>


static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintSOPUnate(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintPOUnate(Abc_Frame_t* pAbc, int argc, char** argv);

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


void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
}
void sopUnateCmdInit(Abc_Frame_t* pAbc){
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_sopunate", Lsv_CommandPrintSOPUnate, 0);
}

void poUnateCmdInit(Abc_Frame_t* pAbc){
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_pounate", Lsv_CommandPrintPOUnate, 0);
}

void destroy(Abc_Frame_t* pAbc) {}
void sopUnateCmdDestroy(Abc_Frame_t* pAbc) {}
void poUnateCmdDestroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};
Abc_FrameInitializer_t sopUnateCmdFrameInitializer = {sopUnateCmdInit, sopUnateCmdDestroy};
Abc_FrameInitializer_t poUnateCmdFrameInitializer = {poUnateCmdInit, poUnateCmdDestroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() { 
    Abc_FrameAddInitializer(&frame_initializer);
    Abc_FrameAddInitializer(&sopUnateCmdFrameInitializer);
    Abc_FrameAddInitializer(&poUnateCmdFrameInitializer);
  }
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

bool nodeIDComp(Abc_Obj_t* obj_1, Abc_Obj_t* obj_2){
  return (Abc_ObjId(obj_1) < Abc_ObjId(obj_2));
}

void Lsv_NtkPrintSOPUnate(Abc_Ntk_t* pNtk){
  Abc_Obj_t* pObj;
  int idx;
  Abc_NtkForEachNode(pNtk, pObj, idx) {
    if (Abc_NtkHasSop(pNtk)) {
      std::vector<Abc_Obj_t*> vPUnate;
      std::vector<Abc_Obj_t*> vNUnate;
      std::vector<Abc_Obj_t*> vBinate;
      std::vector<std::pair<bool,bool> > vCount(Abc_ObjFaninNum(pObj),std::make_pair(0,0));
    // printf("Number of Fanin: %d\n", Abc_ObjFaninNum(pObj));

      int i = 0;
      bool invert = ((char*)pObj->pData)[Abc_ObjFaninNum(pObj)+1] == '0';
      while(((char*)pObj->pData)[i] != '\0'){
      
        if(i % (Abc_ObjFaninNum(pObj)+3) >= Abc_ObjFaninNum(pObj)) {++i; continue;};
      // printf("%d %c ", i, ((char*)pObj->pData)[i]);
        if(((char*)pObj->pData)[i] == '1') {
          if(!invert) vCount[i % (Abc_ObjFaninNum(pObj)+3)].first = true;
          else vCount[i % (Abc_ObjFaninNum(pObj)+3)].second = true;
        }
        else if(((char*)pObj->pData)[i] == '0'){
          if(!invert) vCount[i % (Abc_ObjFaninNum(pObj)+3)].second = true;
          else vCount[i % (Abc_ObjFaninNum(pObj)+3)].first = true;
        }
        ++i;
      }

      Abc_Obj_t* pFanin;
      int j;

      Abc_ObjForEachFanin(pObj, pFanin, j) {
        if(vCount[j].first == true && vCount[j].second == true) vBinate.push_back(pFanin);
        else if(vCount[j].first == true) vPUnate.push_back(pFanin);
        else if(vCount[j].second == true) vNUnate.push_back(pFanin);
      }

      sort(vPUnate.begin(), vPUnate.end(), nodeIDComp);
      sort(vNUnate.begin(), vNUnate.end(), nodeIDComp);
      sort(vBinate.begin(), vBinate.end(), nodeIDComp);

      if(vPUnate.empty() && vNUnate.empty() && vBinate.empty()) continue;
      printf("node %s:\n", Abc_ObjName(pObj));

      if(!vPUnate.empty()){
        printf("+unate inputs:");
        for(int i = 0; i < vPUnate.size(); ++i){
          printf(" %s", Abc_ObjName(vPUnate[i]));
          if(i != vPUnate.size() - 1) printf(",");
        }
        printf("\n");
      }
      if(!vNUnate.empty()){
        printf("-unate inputs:");
        for(int i = 0; i < vNUnate.size(); ++i){
          printf(" %s", Abc_ObjName(vNUnate[i]));
          if(i != vNUnate.size() - 1) printf(",");
        }
        printf("\n");
      }
      if(!vBinate.empty()){
        printf("binate inputs:");
        for(int i = 0; i < vBinate.size(); ++i){
          printf(" %s", Abc_ObjName(vBinate[i]));
          if(i != vBinate.size() - 1) printf(",");
        }
        printf("\n");
      }
    }
  }
}



int Lsv_CommandPrintSOPUnate(Abc_Frame_t* pAbc, int argc, char** argv){
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
  Lsv_NtkPrintSOPUnate(pNtk);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_print_sopunate [-h]\n");
  Abc_Print(-2, "\t        prints the unate information of each node\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}

void Lsv_NtkPrintPOUnate(Abc_Ntk_t* pNtk) {

  Abc_Obj_t* pObj;
  std::vector<Abc_Obj_t*> binateInputs;
  std::vector<Abc_Obj_t*> pUnateInputs;
  std::vector<Abc_Obj_t*> nUnateInputs;

  int p;
  Abc_NtkForEachPo(pNtk, pObj,p){
    Abc_Ntk_t* poNtk = Abc_NtkCreateCone(pNtk, Abc_ObjFanin0(pObj), Abc_ObjName(pObj), 0);
    Aig_Man_t* pAig = Abc_NtkToDar(poNtk,0,0);
    Cnf_Dat_t* pCnf = Cnf_Derive( pAig, Aig_ManCoNum(pAig) );
    Cnf_Dat_t* negpCnf = Cnf_DataDup(pCnf);
    Cnf_DataLift(negpCnf, pCnf -> nVars);

    sat_solver* pSat = sat_solver_new();
    sat_solver_setnvars(pSat, pCnf->nVars * 2 + Aig_ManCiNum(pAig));

    for(int i = 0; i < pCnf -> nClauses; ++i){
      sat_solver_addclause(pSat, *((pCnf -> pClauses) + i), *((pCnf -> pClauses) + i + 1));
    }
    for(int i = 0; i < negpCnf -> nClauses; ++i){
      sat_solver_addclause(pSat, *((negpCnf -> pClauses) + i), *((negpCnf -> pClauses) + i + 1));
    }

    std::vector<int> assumptions;
    assumptions.resize(Aig_ManCiNum(pAig)+4);
    Aig_Obj_t* aObj;
    int v;
    Aig_ManForEachCi(pCnf->pMan, aObj, v){
        //if(pCnf->pVarNums[aObj->Id] >= 0){
        sat_solver_add_buffer_enable(pSat, pCnf->pVarNums[aObj->Id], pCnf->pVarNums[aObj->Id] + pCnf -> nVars, pCnf -> nVars * 2+ v, 0);
        assumptions[v] = (pCnf -> nVars * 2+ v)*2; // Set all enable variable = 1
    }

    // solve SAT
    Aig_Obj_t* poObj = Aig_ManCo(pAig, 0);
    std::unordered_set<std::string> posUnateSet;
    std::unordered_set<std::string> negUnateSet;
    std::unordered_set<std::string> binateSet;
    
    Aig_ManForEachCi(pCnf->pMan, aObj, v){
        //if(pCnf->pVarNums[aObj->Id] >= 0){
        // Check positive unateness (F_(~x) ^ ~F_x)
        assumptions[v] += 1; // Set the enable variable for the current input as 0
        assumptions[Aig_ManCiNum(pAig)] = (pCnf->pVarNums[aObj->Id] * 2); // Positive unate input
        assumptions[Aig_ManCiNum(pAig) + 1] = (pCnf->pVarNums[aObj->Id] + pCnf -> nVars) * 2 + 1; // Negative unate input
        assumptions[Aig_ManCiNum(pAig) + 2] = (pCnf->pVarNums[poObj->Id] * 2 + 1); // Negative output for the positive unate CNF
        assumptions[Aig_ManCiNum(pAig) + 3] = (pCnf->pVarNums[poObj->Id] + pCnf -> nVars) * 2; // Positive output for the negative unate CNF
        int posSAT = sat_solver_solve(pSat, &(*assumptions.begin()), &(*assumptions.end()), 0, 0, 0, 0);

        // Check negative unateness (F_x ^ ~F_(~x))
        assumptions[Aig_ManCiNum(pAig) + 2] = (pCnf->pVarNums[poObj->Id] * 2); // Positive output for the positive unate CNF
        assumptions[Aig_ManCiNum(pAig) + 3] = (pCnf->pVarNums[poObj->Id] + pCnf -> nVars) * 2 + 1; // Negative output for the negative unate CNF
        int negSAT = sat_solver_solve(pSat, &(*assumptions.begin()), &(*assumptions.end()), 0, 0, 0, 0);
        assumptions[v] -= 1;

        // Check result
        if(posSAT == l_False){
          //std::cout << "posUnate: " << Abc_ObjName(Abc_NtkPi(poNtk,v))<< std::endl;
          posUnateSet.insert(Abc_ObjName(Abc_NtkPi(poNtk,v)));
        }
        if(negSAT == l_False) {
          //std::cout << "negUnate: " << Abc_ObjName(Abc_NtkPi(poNtk,v))<< std::endl;
          negUnateSet.insert(Abc_ObjName(Abc_NtkPi(poNtk,v)));
        }
        if(posSAT == l_True && negSAT == l_True) {
          //std::cout << "addbinate: " << Abc_ObjName(Abc_NtkPi(poNtk,v))<< std::endl;
          binateSet.insert(Abc_ObjName(Abc_NtkPi(poNtk,v)));
        }
    }

    // Collect result
    Abc_Obj_t* piObj;
    //std::cout << posUnateSet.size() << " " << negUnateSet.size() << " " << binateSet.size() << std::endl;
    Abc_NtkForEachPi(pNtk, piObj, v){
      
      if(Abc_NtkPo(poNtk, 0) -> fCompl0 == pObj -> fCompl0){
        if(posUnateSet.find(Abc_ObjName(piObj)) != posUnateSet.end()) pUnateInputs.push_back(piObj);
        if(negUnateSet.find(Abc_ObjName(piObj)) != negUnateSet.end() ) nUnateInputs.push_back(piObj);
        if(binateSet.find(Abc_ObjName(piObj)) != binateSet.end() ) binateInputs.push_back(piObj);
        if(  posUnateSet.find(Abc_ObjName(piObj)) == posUnateSet.end()
          && negUnateSet.find(Abc_ObjName(piObj)) == negUnateSet.end()
          && binateSet.find(Abc_ObjName(piObj)) == binateSet.end()){ // PI not a support of PO
          pUnateInputs.push_back(piObj);
          nUnateInputs.push_back(piObj);
        }
      }
      else{
        if(posUnateSet.find(Abc_ObjName(piObj)) != posUnateSet.end()) nUnateInputs.push_back(piObj);
        if(negUnateSet.find(Abc_ObjName(piObj)) != negUnateSet.end() ) pUnateInputs.push_back(piObj);
        if(binateSet.find(Abc_ObjName(piObj)) != binateSet.end() ) binateInputs.push_back(piObj);
        if(  posUnateSet.find(Abc_ObjName(piObj)) == posUnateSet.end()
          && negUnateSet.find(Abc_ObjName(piObj)) == negUnateSet.end()
          && binateSet.find(Abc_ObjName(piObj)) == binateSet.end()){// PI not a support of PO
          pUnateInputs.push_back(piObj);
          nUnateInputs.push_back(piObj);
        }
      }
      
    }
    // Output result
    std::cout << "node " << Abc_ObjName(pObj) << ":" << std::endl;

    if(pUnateInputs.size() != 0) std::cout << "+unate inputs: ";
    for(int i = 0; i < pUnateInputs.size(); ++i){
      std::cout << Abc_ObjName(pUnateInputs[i]);
      if(i == pUnateInputs.size() - 1) std::cout << std::endl;
      else std::cout << ",";
    }

    if(nUnateInputs.size() != 0) std::cout << "-unate inputs: ";
    for(int i = 0; i < nUnateInputs.size(); ++i){
      std::cout << Abc_ObjName(nUnateInputs[i]);
      if(i == nUnateInputs.size() - 1) std::cout << std::endl;
      else std::cout << ",";
    }

    if(binateInputs.size() != 0) std::cout << "binate inputs: ";
    for(int i = 0; i < binateInputs.size(); ++i){
      std::cout << Abc_ObjName(binateInputs[i]);
      if(i == binateInputs.size() - 1) std::cout << std::endl;
      else std::cout << ",";
    }

    pUnateInputs.clear();
    nUnateInputs.clear();
    binateInputs.clear();
  }
}

int Lsv_CommandPrintPOUnate(Abc_Frame_t* pAbc, int argc, char** argv){
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
  Lsv_NtkPrintPOUnate(pNtk);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_print_sopunate [-h]\n");
  Abc_Print(-2, "\t        prints the unate information of each node\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}
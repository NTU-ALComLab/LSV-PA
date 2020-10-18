#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <queue>
#include <vector>
#include <algorithm>
#include <functional>

using namespace std;

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////


static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintSopunate(Abc_Frame_t* pAbc, int argc, char** argv);

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

typedef pair<int, Abc_Obj_t* > IdObj;
typedef priority_queue< IdObj, vector<IdObj>, greater<IdObj> > IdObjQueue;

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_sopunate", Lsv_CommandPrintSopunate, 0);
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

////////////////////////////////////////////////////////////////////////
///             Helper functions of Lsv_NtkPrintSopunate             ///
////////////////////////////////////////////////////////////////////////

void resetUnateVec(vector<int>& UnateVec, Abc_Obj_t *pObj){
    //reset the content of UnateVec to binary value:11
    fill(UnateVec.begin(), UnateVec.end(),3); 
    
    int nFanins =  Abc_ObjFaninNum( pObj );
    UnateVec.resize(nFanins,3);    
}

void setUnateVec( vector<int>& UnateVec, Abc_Obj_t *pObj){
    char *pSop = (char *)pObj->pData;      
    int nFanins =  Abc_ObjFaninNum( pObj );
    char *pCube;
    char Value;  
    int i;
    
    Abc_SopForEachCube( pSop, nFanins, pCube ){
        Abc_CubeForEachVar( pCube, Value, i ){
            if(Value!='-')
                UnateVec[i] &= ( 1 << ( Abc_SopIsComplement(pCube) == (Value-'0') ) );
                //  Value   IsComplent  Encode
                //  0       0           10 (neg)
                //  1       0           01 (pos)
                //  0       1           01 (pos)
                //  1       1           10 (neg)
        }
    }
}

void printQueue( IdObjQueue& pq ){
    int i=0;
    while(!pq.empty()){
        if(i==0) printf(" %s",Abc_ObjName(pq.top().second));
        else printf (",%s", Abc_ObjName(pq.top().second));
        pq.pop();
        ++i;
    }
    printf("\n");
}

void Lsv_NtkPrintSopunate(Abc_Ntk_t* pNtk) {
    
    if (!Abc_NtkHasSop(pNtk)){
        printf("Error! The circuit has no Sop\n");
        return;
    } 

    vector<int> UnateVec;
    // Encode:
    // 11: don't care
    // 00: binate
    // 01: positive unate
    // 10: negative unate

    //sort by pair( Id, Abc_Obj_t* )
    IdObjQueue PosQueue, NegQueue, BiQueue; 

    Abc_Obj_t* pObj; int i;
    Abc_NtkForEachNode(pNtk, pObj, i) {
        
        // traverse the cubes in sop to decide the unateness        
        resetUnateVec(UnateVec, pObj); 
        setUnateVec(UnateVec, pObj);        
       
        // sort by Id 
        Abc_Obj_t* pFanin; int j;
        Abc_ObjForEachFanin(pObj, pFanin, j) {
            IdObj p(Abc_ObjId(pFanin), pFanin);
            if( UnateVec[j] == 0 ) //00
                BiQueue.push(p);
            else if( UnateVec[j] == 1 ) //01
                PosQueue.push(p);
            else if( UnateVec[j] == 2 ) //10
                NegQueue.push(p);
        }
       
        // print the unateness message for each node 
        printf("node %s:\n", Abc_ObjName(pObj));
        if(!PosQueue.empty()){
            printf("+unate inputs:");
            printQueue(PosQueue);
        }
        if(!NegQueue.empty()){
            printf("-unate inputs:");
            printQueue(NegQueue);
        }
        if(!BiQueue.empty()) {
            printf("binate inputs:");
            printQueue(BiQueue);
        }
    }
}

int Lsv_CommandPrintSopunate(Abc_Frame_t* pAbc, int argc, char** argv) {
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
  Lsv_NtkPrintSopunate(pNtk);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_print_nodes [-h]\n");
  Abc_Print(-2, "\t        prints the nodes in the network\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}

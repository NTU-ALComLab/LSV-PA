/**CFile****************************************************************

  FileName    [lsvSopUnate.cpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [External command.]

  Synopsis    [External declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [NTU EE]

  Date        [Ver. 1.0. Started - June 27, 2020.]

***********************************************************************/

////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////
#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <algorithm>



namespace SOPUnate {

// Init command function
static int Lsv_CommandPrintSOPUnate(Abc_Frame_t* pAbc, int argc, char** argv);

////////////////////////////////////////////////////////////////////////
///                      Command Registeration                       ///
////////////////////////////////////////////////////////////////////////
void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_sopunate", Lsv_CommandPrintSOPUnate, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

////////////////////////////////////////////////////////////////////////
///                         Basic type                               ///
////////////////////////////////////////////////////////////////////////


typedef char LSV_literal_type;

class LSV_iFan_list {

  // Helper struct for sorting key
  struct LSV_iFan_cmp {
      inline bool operator() (Abc_Obj_t *a, Abc_Obj_t *b) {
          return (Abc_ObjId(a) < Abc_ObjId(b));
      }
  };

  private:
    Abc_Obj_t   **faninList;
    unsigned int  size,
                  capacity;

  public:

    LSV_iFan_list(unsigned int c): size(0), capacity(c) { faninList = new Abc_Obj_t*[c]; }
    ~LSV_iFan_list() { delete faninList; }
    bool push_back(Abc_Obj_t* fanin) {
      if ( size < capacity ) {
        faninList[size++] = fanin;
        return true; 
      } 
        return false;
    }

    void print(char* title) {
        this->sort();
        if (size) {
          printf(title);
          for (unsigned int iFanin=0; iFanin<size;++iFanin) {
            printf("%s", Abc_ObjName(faninList[iFanin]));
            if (iFanin != size-1) printf(",");
            else printf("\n");
          }
        }
    }

    void sort() {
      std::sort(faninList, faninList+size, LSV_iFan_cmp());
    }
};


////////////////////////////////////////////////////////////////////////
///                      Command Function                            ///
////////////////////////////////////////////////////////////////////////

void Lsv_NtkPrintSOPUnate(Abc_Ntk_t* pNtk) {
  const LSV_literal_type  POS_LITERAL = 1, NEG_LITERAL = 2,
                          BIN_LITERAL = POS_LITERAL|NEG_LITERAL;
  LSV_literal_type pos_literaL_value, neg_literal_value;

  Abc_Obj_t *pObj, *pFanin;
  char *pSop, *pCube, Value;
  int  iNode, iVar, iFanin, nFanins;
  bool isOnset;

  if (Abc_NtkHasSop(pNtk)) {
    Abc_NtkForEachNode(pNtk, pObj, iNode) {
      if ((nFanins = Abc_ObjFaninNum(pObj)) ) {
        LSV_iFan_list posUnate(nFanins), negUnate(nFanins), Binate(nFanins);
        LSV_literal_type *literal_list = new LSV_literal_type[nFanins];
        std::fill_n(literal_list, nFanins, 0);

        pSop = (char*)pObj->pData;
        Abc_SopForEachCube(pSop, nFanins, pCube) {
          isOnset = (*(pCube + (nFanins) + 1) == '1')?1:0;
          Abc_CubeForEachVar(pCube, Value, iVar) {
            pos_literaL_value = (isOnset)?POS_LITERAL:NEG_LITERAL;
            neg_literal_value = (isOnset)?NEG_LITERAL:POS_LITERAL;
            switch(Value) {
              case '0': literal_list[iVar] |= neg_literal_value; break;
              case '1': literal_list[iVar] |= pos_literaL_value; break;
              case '-': 
              default : literal_list[iVar] |= 0;
            }
          }
        }

        Abc_ObjForEachFanin(pObj, pFanin, iFanin) {
          switch(literal_list[iFanin]) {
            case POS_LITERAL: posUnate.push_back(pFanin); break;
            case NEG_LITERAL: negUnate.push_back(pFanin); break;
            case BIN_LITERAL: Binate.push_back(pFanin);   break;
            case 0:
            default:
              posUnate.push_back(pFanin);
              negUnate.push_back(pFanin);
          }
        }

        printf("node %s:\n", Abc_ObjName(pObj));
        posUnate.print("+unate inputs: ");
        negUnate.print("-unate inputs: ");
        Binate.print("binate inputs: ");
        
      }
    }
  }
}

int Lsv_CommandPrintSOPUnate(Abc_Frame_t* pAbc, int argc, char** argv) {
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
  return 1;
}
}
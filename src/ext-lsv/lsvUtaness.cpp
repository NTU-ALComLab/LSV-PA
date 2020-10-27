#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <algorithm>

namespace {

static int Lsv_CommandPrintSOPUnate(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_sopunate", Lsv_CommandPrintSOPUnate, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;


void Lsv_NtkPrintSOPUnate(Abc_Ntk_t* pNtk) {
  struct pFanin_pair {
    int idx; Abc_Obj_t* fanin;
  };

  struct pFanin_pair_key
  {
      inline bool operator() (const pFanin_pair& a, const pFanin_pair& b)
      {
          return (Abc_ObjId(a.fanin) < Abc_ObjId(b.fanin));
      }
  };


  pFanin_pair *pFanin_List;
  Abc_Obj_t *pObj, *pFanin,
          **posUnate, **negUnate, **Binate;
  char *pSop,
      *pCube, Value,
      *Unateness, posVal, negVal;
  int iNode, iVar, iFanin,
      nFanins,
      posUnateSize, negUnateSize, BinateSize;
  bool isOnset;

  Abc_NtkForEachNode(pNtk, pObj, iNode) {
    if ((nFanins = Abc_ObjFaninNum(pObj)) && Abc_NtkHasSop(pNtk)) {
      posUnate  = new Abc_Obj_t*[nFanins];
      negUnate  = new Abc_Obj_t*[nFanins];
      Binate    = new Abc_Obj_t*[nFanins];
      posUnateSize = negUnateSize = BinateSize = 0;
      pFanin_List = new pFanin_pair[nFanins];
      Unateness   = new char[nFanins];
      std::fill_n(Unateness, nFanins, 0);

      pSop = (char*)pObj->pData;
      Abc_SopForEachCube(pSop, nFanins, pCube) {
        isOnset = (*(pCube + (nFanins) + 1) == '1')?1:0;
        Abc_CubeForEachVar(pCube, Value, iVar) {
          posVal = (isOnset)?2:1;
          negVal = (isOnset)?1:2;
          switch(Value) {
            case '0': Unateness[iVar] |= negVal; break;
            case '1': Unateness[iVar] |= posVal; break;
            case '-': 
            default : Unateness[iVar] |= 0;
          }
        }
      }

      Abc_ObjForEachFanin(pObj, pFanin, iFanin) {
        pFanin_List[iFanin] = {iFanin, pFanin};
      }
      std::sort(pFanin_List, pFanin_List+nFanins, pFanin_pair_key());

      for (iFanin = 0; iFanin < nFanins; ++iFanin) {
        switch(Unateness[pFanin_List[iFanin].idx]) {
          case 1: negUnate[negUnateSize++] = pFanin_List[iFanin].fanin; break;
          case 2: posUnate[posUnateSize++] = pFanin_List[iFanin].fanin; break;
          case 3: Binate[BinateSize++]     = pFanin_List[iFanin].fanin; break;
          case 0:
          default:
            posUnate[posUnateSize++] = pFanin_List[iFanin].fanin;
            negUnate[negUnateSize++] = pFanin_List[iFanin].fanin;
        }
      }

      printf("node %s:\n", Abc_ObjName(pObj));
      if (posUnateSize) {
        printf("+unate inputs: ");
        for (iFanin = 0; iFanin < posUnateSize;++iFanin) {
          printf("%s", Abc_ObjName(posUnate[iFanin]));
          if (iFanin != posUnateSize-1) printf(",");
          else printf("\n");
        }
      }
      if (negUnateSize) {
        printf("-unate inputs: ");
        for (iFanin = 0; iFanin < negUnateSize;++iFanin) {
          printf("%s", Abc_ObjName(negUnate[iFanin]));
          if (iFanin != negUnateSize-1) printf(",");
          else printf("\n");
        }


      }
      if (BinateSize) {
        printf("binate inputs: ");
        for (iFanin = 0; iFanin < BinateSize;++iFanin) {
          printf("%s", Abc_ObjName(Binate[iFanin]));
          if (iFanin != BinateSize-1) printf(",");
          else printf("\n");
        }
      }

      delete [] posUnate;
      delete [] negUnate;
      delete [] Binate;
      delete [] pFanin_List;
      delete [] Unateness;
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
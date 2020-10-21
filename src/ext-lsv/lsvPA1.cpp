#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"


static int Lsv_CommandPrintSopunate(Abc_Frame_t* pAbc);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_sopunate", Lsv_CommandPrintSopunate, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

int Lsv_CommandPrintSopunate(Abc_Frame_t* pAbc)
{
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i) {
    printf("node %s:\n", Abc_ObjName(pObj));
    if (Abc_NtkHasSop(pNtk)) {
      vector<pair<int,char*>> faninV;
      Abc_Obj_t* pFanin;
      int j;
      Abc_ObjForEachFanin(pObj, pFanin, j) {
        printf("  Fanin-%d: Id = %d, name = %s\n", j, Abc_ObjId(pFanin),
             Abc_ObjName(pFanin));
        faninV.push_back(pair<int,char*>(-1,Abc_ObjName(pFanin)))
      }
      char* pSop = (char*)pObj->pData);
      int count = 0;
      for ( pCur = pSop; *pCur; pCur++ ){
        if(*pCur == '1'){
          switch(faninV[count]->first){
            case -1:
              faninV[count]->first = 1;
              break;
            case 0:
              faninV[count]->first = 2;
              break;
            case 1: case 2: default:
              break;
          }
          count++;
        }
        else if(*pCur == '0'){
          switch(faninV[count]->first){
            case -1:
              faninV[count]->first = 0;
              break;
            case 1:
              faninV[count]->first = 2;
              break;
            case 0: case 2: default:
              break;
          }
          count++;
        }
        else if(*pCur == '-1'){
          count++;
        }
        else if(*pCur == ' '){
          pCur++;
        }
        else if(*pCur == '\n'){
          count = 0;
        }
      }
      if(!Abc_SopIsComplement){
        count = 0;
        printf("+unate inputs: ");
        for(auto p : faninV){
          if(p->first == 1){
            if(count == 0)printf("%s",p->seconf);
            else printf(",%s",p->seconf);
            count++;
          }
        }
        count = 0;
        printf("\n");
        printf("-unate inputs: ");
        for(auto p : faninV){
          if(p->first == 0){
            if(count == 0)printf("%s",p->seconf);
            else printf(",%s",p->seconf);
            count++;
          }
        }
        count = 0;
        printf("\n");
        printf("binate inputs: ");
        for(auto p : faninV){
          if(p->first == 2){
            if(count == 0)printf("%s",p->seconf);
            else printf(",%s",p->seconf);
            count++;
          }
        }
      }
      else{
        count = 0;
        printf("+unate inputs: ");
        for(auto p : faninV){
          if(p->first == 0){
            if(count == 0)printf("%s",p->seconf);
            else printf(",%s",p->seconf);
            count++;
          }
        }
        count = 0;
        printf("\n");
        printf("-unate inputs: ");
        for(auto p : faninV){
          if(p->first == 1){
            if(count == 0)printf("%s",p->seconf);
            else printf(",%s",p->seconf);
            count++;
          }
        }
        count = 0;
        printf("\n");
        printf("binate inputs: ");
        for(auto p : faninV){
          if(p->first == 2){
            if(count == 0)printf("%s",p->seconf);
            else printf(",%s",p->seconf);
            count++;
          }
        }
      }
    }
  }
}

//int Abc_SopIsComplement
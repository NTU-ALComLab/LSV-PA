#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <vector>
#include <algorithm>

#include <iostream>
#include <fstream>

bool comp(const std::pair<int,int> &a,const std::pair<int,int> &b)
{
  return a.first<b.first;
}


static int Lsv_CommandPrintSopunate(Abc_Frame_t* pAbc, int argc, char** argv);

void init_pa1(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_sopunate", Lsv_CommandPrintSopunate, 0);
}

void destroy_pa1(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer_pa1 = {init_pa1, destroy_pa1};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer_pa1); }
} lsvPackageRegistrationManager_pa1;

int Lsv_CommandPrintSopunate(Abc_Frame_t* pAbc, int argc, char** argv)
{
  //std::fstream ofs;
	//ofs.open("output.txt",std::ios::out);
  
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i) {
    //printf("node %s:\n", Abc_ObjName(pObj));
    //ofs<<"node "<<Abc_ObjName(pObj)<<":\n";
    if (Abc_NtkHasSop(pNtk)) {
      std::vector<std::pair<int,int> > faninV_sort; //(id,fanin_order)
      std::vector<std::pair<int,char*> > faninV; //(count,name)
      Abc_Obj_t* pFanin;
      int j;
      if(Abc_ObjFaninNum(pObj)>0){
        printf("node %s:\n", Abc_ObjName(pObj));
        Abc_ObjForEachFanin(pObj, pFanin, j) {
          //printf("  Fanin-%d: Id = %d, name = %s\n", j, Abc_ObjId(pFanin),Abc_ObjName(pFanin));
          faninV.push_back(std::make_pair<int,char*>(-1,Abc_ObjName(pFanin)));
          faninV_sort.push_back(std::make_pair<int,int>((int)Abc_ObjId(pFanin),(int)j));
        }
        std::sort(faninV_sort.begin(),faninV_sort.end(),comp);
        char* pSop = (char*)pObj->pData;
        //printf("  DATA = \n%s",pSop);
        int count = 0;
        char * pCur;
        for ( pCur = pSop; *pCur; pCur++ ){
          if(*pCur == '1'){
            switch(faninV[count].first){
              case -1:
                faninV[count].first = 1;
                break;
              case 0:
                faninV[count].first = 2;
                break;
              case 1: case 2: default:
                break;
            }
            count++;
          }
          else if(*pCur == '0'){
            switch(faninV[count].first){
              case -1:
                faninV[count].first = 0;
                break;
              case 1:
                faninV[count].first = 2;
                break;
              case 0: case 2: default:
                break;
            }
            count++;
          }
          else if(*pCur == ' '){
            pCur++;
          }
          else if(*pCur == '\n'){
            count = 0;
          }
          else{ //*pCur == '-'
            count++;
          }
        }
        if(!Abc_SopIsComplement((char*)pObj->pData)){
          count = 0;
          //printf("+unate inputs: ");
          for(int i = 0; i < faninV_sort.size();i++){
            std::pair<int,char*> p = faninV[faninV_sort[i].second];
            if((p.first == 1) || (p.first == -1)){
              if(count == 0){
                printf("+unate inputs: ");
                printf("%s",p.second);

                //ofs<<"+unate inputs: "<<p.second;
              }
              else {
                printf(",%s",p.second);
                //ofs<<","<<p.second;
              }
              count++;
            }
          }
          if(count != 0){
            printf("\n");
            //ofs<<"\n";
            count = 0;
          }
          //printf("-unate inputs: ");
          for(int i = 0; i < faninV_sort.size();i++){
            std::pair<int,char*> p = faninV[faninV_sort[i].second];
            if((p.first == 0) || (p.first == -1)){
              if(count == 0){
                printf("-unate inputs: ");
                printf("%s",p.second);
                //ofs<<"-unate inputs: "<<p.second;
              }
              else {
                printf(",%s",p.second);
                //ofs<<","<<p.second;
              }
              count++;
            }
          }
          if(count != 0){
            printf("\n");
            //ofs<<"\n";
            count = 0;
          }
        }
        else{
          count = 0;
          //printf("+unate inputs: ");
          for(int i = 0; i < faninV_sort.size();i++){
            std::pair<int,char*> p = faninV[faninV_sort[i].second];
            if((p.first == 0) || (p.first == -1)){
              if(count == 0){
                printf("+unate inputs: ");
                printf("%s",p.second);
                //ofs<<"+unate inputs: "<<p.second;
              }
              else {
                printf(",%s",p.second);
                //ofs<<","<<p.second;
              }
              count++;
            }
          }
          if(count != 0){
            printf("\n");
            //ofs<<"\n";
            count = 0;
          }
          //printf("-unate inputs: ");
          for(int i = 0; i < faninV_sort.size();i++){
            std::pair<int,char*> p = faninV[faninV_sort[i].second];
            if((p.first == 1) || (p.first == -1)){
              if(count == 0){
                printf("-unate inputs: ");
                printf("%s",p.second);
                //ofs<<"-unate inputs: "<<p.second;
              }
              else {
                printf(",%s",p.second);
                //ofs<<","<<p.second;
              }
              count++;
            }
          }
          if(count != 0){
            printf("\n");
            //ofs<<"\n";
            count = 0;
          }
        }
        //printf("binate inputs: ");
        for(int i = 0; i < faninV_sort.size();i++){
          std::pair<int,char*> p = faninV[faninV_sort[i].second];
          if((p.first == 2)  ){
            if(count == 0){
              printf("binate inputs: ");
              printf("%s",p.second);
              //ofs<<"binate inputs: "<<p.second;
            }
            else {
              printf(",%s",p.second);
              //ofs<<","<<p.second;
            }
            count++;
          }
        }
        if(count != 0){
            printf("\n");
            //ofs<<"\n";
            count = 0;
        }
      }
    }
  }
  //ofs.close();
  return 0;
}

//int Abc_SopIsComplement
#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <iostream>
#include <string.h>
using namespace std;

static int Lsv_CommandPrintSOP(Abc_Frame_t* pAbc, int argc, char** argv);

void initSOP(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_sopunate", Lsv_CommandPrintSOP, 0);
}

void destroySOP(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializerSOP = {initSOP, destroySOP};

struct PackageRegistrationManagerSOP {
  PackageRegistrationManagerSOP() { Abc_FrameAddInitializer(&frame_initializerSOP); }
} lsvPackageRegistrationManagerSOP;

// initial ok

struct inputnode{
  unsigned ID;
  char* name;
  int type;
  // 0: init didn't use
  // 1: have pos
  // 2: have negitive
  // 3: binate
};

void Lsv_NtkPrintSOP(Abc_Ntk_t* pNtk) {
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i) {
    printf("node %s:\n", Abc_ObjName(pObj));
    Abc_Obj_t* pFanin;
    int j;
    //get input
    Abc_ObjForEachFanin(pObj, pFanin, j) {
      //printf("Fanin-%d: Id = %d, name = %s\n", j, Abc_ObjId(pFanin),Abc_ObjName(pFanin)); //return char*
    }
    inputnode node[j];
    Abc_ObjForEachFanin(pObj, pFanin, j) {
      node[j].ID = Abc_ObjId(pFanin);
      node[j].name = Abc_ObjName(pFanin);
      node[j].type = 0;
    }
    //get SOP
    char* SOP = NULL;
    bool positiveSOP = false;
    int SOPline = 0;
    if (Abc_NtkHasSop(pNtk)) {
      SOP = (char*)pObj->pData;
    }
    //printf("SOP:\n%s",SOP);
    if(SOP!=NULL){ //mean didn't have SOP
      //get information
      if(SOP[j+1]=='1')positiveSOP = true;
      SOPline = strlen(SOP)/(j+3);
      //operate 
      for(int word=0; word<j; ++word){
        for(int loop=0; loop<SOPline; ++loop){
          int index = word+loop*(j+3);
          if(node[word].type==0){
            if(SOP[index]=='1'){node[word].type=1;}
            else if(SOP[index]=='0'){node[word].type=2;}
            else if(SOP[index]=='-'){}
            else cerr<<"error SOP"<<endl;
          }
          else if(node[word].type==1){
            if(SOP[index]=='1'){node[word].type=1;}
            else if(SOP[index]=='0'){node[word].type=3;}
            else if(SOP[index]=='-'){}
            else cerr<<"error SOP"<<endl;
          }
          else if(node[word].type==2){
            if(SOP[index]=='1'){node[word].type=3;}
            else if(SOP[index]=='0'){node[word].type=2;}
            else if(SOP[index]=='-'){}
            else cerr<<"error SOP"<<endl;
          }
          else if(node[word].type==3){
            if(SOP[index]=='1'){node[word].type=3;}
            else if(SOP[index]=='0'){node[word].type=3;}
            else if(SOP[index]=='-'){node[word].type=3;}
            else cerr<<"error SOP"<<endl;
          }
          else{
            cerr<<"error node type"<<endl;
          }
        }
      }
      //check negative
      if(positiveSOP == false){
        for(int i=0; i<j; ++i){
          if(node[i].type==1)node[i].type=2;
          else if(node[i].type==2)node[i].type=1;
        }
      }
      //insertion sort
      for(int i=1;i<j;i++){
        for(int index = i; index>0; --index){
          if(node[index].ID < node[index-1].ID){//need change
            inputnode temp;
            temp.ID = node[index].ID;
            temp.name = node[index].name;
            temp.type = node[index].type;
            node[index].ID = node[index-1].ID;
            node[index].name = node[index-1].name;
            node[index].type = node[index-1].type;
            node[index-1].ID = temp.ID;
            node[index-1].name = temp.name;
            node[index-1].type = temp.type;
          }
          else break;
        }
      }
      //count each type number
      int pos_unate = 0;
      int neg_unate = 0;
      int bi_unate = 0;
      for(int i=0; i<j; ++i){
        if(node[i].type==0){++pos_unate; ++neg_unate;}
        else if(node[i].type==1)++pos_unate;
        else if(node[i].type==2)++neg_unate;
        else if(node[i].type==3)++bi_unate;
      }
      //output
      int checkcount=0;
      if(pos_unate>0){
        printf("+unate inputs: ");
        for(int i=0; i<j; ++i){
          if(node[i].type==0 || node[i].type==1){
            ++checkcount;
            cout<<node[i].name;//<<'('<<node[i].ID<<")";
            if(checkcount!=pos_unate)cout<<',';
          }
        }
        cout<<endl;
      }
      checkcount=0;
      if(neg_unate>0){
        printf("-unate inputs: ");
        for(int i=0; i<j; ++i){
          if(node[i].type==0 || node[i].type==2){
            ++checkcount;
            cout<<node[i].name;//<<'('<<node[i].ID<<")";
            if(checkcount!=neg_unate)cout<<',';
          }
        }
        cout<<endl;
      }
      checkcount=0;
      if(bi_unate>0){
        printf("binate inputs: ");
        for(int i=0; i<j; ++i){
          if(node[i].type==3){
            ++checkcount;
            cout<<node[i].name;//<<'('<<node[i].ID<<")";
            if(checkcount!=bi_unate)cout<<',';
          }
        }
        cout<<endl;
      }
    }
  }
}

int Lsv_CommandPrintSOP(Abc_Frame_t* pAbc, int argc, char** argv) {
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
  Lsv_NtkPrintSOP(pNtk);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_print_sopunate [-h]\n");
  Abc_Print(-2, "\t        prints the nodes in the network\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}
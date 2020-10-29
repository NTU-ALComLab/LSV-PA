#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <vector>
#include <string>
#include <iostream>

using namespace std;

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_sopunate", Lsv_CommandPrintNodes, 0);
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
    Abc_Obj_t* pFanin;
    int j;
    char *sop = (char*)pObj->pData;
    if (Abc_SopIsConst0(sop) || Abc_SopIsConst1(sop)) continue;
        printf("node %s:\n", Abc_ObjName(pObj));
    Abc_ObjForEachFanin(pObj, pFanin, j) {
      // printf("  Fanin-%d: Id = %d, name = %s\n", j, Abc_ObjId(pFanin),
      //        Abc_ObjName(pFanin));  
    }
    char onset = 0;
 

    if (Abc_NtkHasSop(pNtk)) {
      //printf("The SOP of this node:\n%s", (char*)pObj->pData);
      int len = strlen((char*)pObj->pData);
      // printf("total length %d/n",len);
      // printf("VAR NUM :%d/n",var_number);
      

      //char * array;
      char array[len];
      strcpy(array,(char*)pObj->pData);
      //printf("The SOP of this node:\n%s", (char*)array);
      onset = array[j+1];
      // printf("on/offset : %c\n",onset);

      int unate[j];
      for (size_t u = 0; u < j; u++){
                  unate[u] = 0;
        }
      unate[0] = 0;
      int temp = 0;
      while (array[temp] != '\0')
      {
        // printf("%c",array[temp]);
        
        if ((temp%(j+3)) < j)
        {
          if (array[temp] == '0'){
            if (unate[temp%(j+3)] == 2 || unate[temp%(j+3)] == 3){
              unate[temp%(j+3)] = 3;
            }
            else{
              unate[temp%(j+3)] = 1;
            }
          }
          else if(array[temp] == '1'){
            if (unate[temp%(j+3)] == 1 || unate[temp%(j+3)] == 3){
              unate[temp%(j+3)] = 3;
            }
            else{
              unate[temp%(j+3)] = 2;
            }
          }
          else if(array[temp] == '-'){
          }  
        }
        temp++;
      }
      string name [j];
      int name_id [j];
      Abc_ObjForEachFanin(pObj, pFanin, j) {
        name[j] = Abc_ObjName(pFanin);
        name_id [j] = Abc_ObjId(pFanin);
        //printf(" name = %s\n", name[j]); 
      }
      // for (size_t u = 0; u < j; u++){
      //             printf("%d",unate[u]);
      //       }
    //printf(" onset = %c\n", onset);
    int s_x = 0, s_y = 0;
    string s_tmp;
    int tmp_unate;
    int id_tmp;
    for (s_x = 0; s_x < j; s_x++) {   // loop n times - 1 per element
        for (s_y = 0; s_y < j - s_x - 1; s_y++) { // last i elements are sorted already
            if (name_id[s_y] > name_id[s_y + 1]) {  // swop if order is broken
                id_tmp = name_id[s_y];
                name_id[s_y] = name_id[s_y + 1];
                name_id[s_y + 1] = id_tmp;
                s_tmp = name[s_y];
                name[s_y] = name[s_y + 1];
                name[s_y + 1] = s_tmp;
                tmp_unate = unate[s_y];
                unate[s_y] = unate[s_y + 1];
                unate[s_y + 1] = tmp_unate;
                
            }
        }
    }



    bool flag = 0;
      if(onset == '1' ){
            for (size_t u = 0; u < j; u++){
              if(unate[u] == 2){
                if(flag == 0){
                  //printf("+unate inputs: ");
                  cout<<"+unate inputs: ";
                  flag = 1;
                  //printf("%s",name[u]);
                  cout<<name[u];
                }
                else{
                  //printf(",%s",name[u]);
                  cout<<","<<name[u];
                }
              }
            }
            
            if(flag == 1){
              //printf("\n");
              cout<<endl;
              flag = 0;
            }
            for (size_t u = 0; u < j; u++){
              if(unate[u] == 1){
                if(flag == 0){
                  //printf("-unate inputs: ");
                  cout<<"-unate inputs: ";
                  flag = 1;
                  //printf("%s",name[u]);
                  cout<<name[u];
                }
                else{
                  // printf(",%s",name[u]);
                  cout<<","<<name[u];
                }
              }
            }
            
            if(flag == 1){
              //printf("\n");
              cout<<endl;
              flag = 0;
            }

            for (size_t u = 0; u < j; u++){
              if(unate[u] == 3){
                if(flag == 0){
                  //printf("binate inputs: ");
                  cout<<"binate inputs: ";
                  flag = 1;
                  //printf("%s",name[u]);
                  cout<<name[u];
                  
                }
                else{
                  // printf(",%s",name[u]);
                  cout<<","<<name[u];
                }
              }
            }
            
            if(flag == 1){
              //printf("\n");
              cout<<endl;
              flag = 0;
            }
      }
      else
      {            
        for (size_t u = 0; u < j; u++){
              if(unate[u] == 1){
                if(flag == 0){
                  //printf("+unate inputs: ");
                  cout<<"+unate inputs: ";
                  flag = 1;
                  //printf("%s",name[u]);
                  cout<<name[u];
                }
                else{
                  //printf(",%s",name[u]);
                  cout<<","<<name[u];
                }
              }
            }
            
            if(flag == 1){
              //printf("\n");
              cout<<endl;
              flag = 0;
            }
        for (size_t u = 0; u < j; u++){
              if(unate[u] == 2){
                if(flag == 0){
                  //printf("-unate inputs: ");
                  cout<<"-unate inputs: ";
                  flag = 1;
                  //printf("%s",name[u]);
                  cout<<name[u];
                }
                else{
                  //printf(",%s",name[u]);
                  cout<<","<<name[u];
                }
              }
            }
            
            if(flag == 1){
              //printf("\n");
              cout<<endl;
              flag = 0;
            }

            for (size_t u = 0; u < j; u++){
              if(unate[u] == 3){
                if(flag == 0){
                  //printf("binate inputs: ");
                  cout<<"binate inputs: ";
                  flag = 1;
                  //printf("%s",name[u]);
                  cout<<name[u];
                }
                else{
                  //printf(",%s",name[u]);
                  cout<<","<<name[u];
                }
              }
            }
            
            if(flag == 1){
              //printf("\n");
              cout<<endl;
              flag = 0;
            }
      }
      
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
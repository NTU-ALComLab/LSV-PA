#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

#include <iostream>

static int Hello_Command(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc)
{
    Cmd_CommandAdd( pAbc, "LSV", "lsv_print_sopunate", Hello_Command, 0);
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

int Hello_Command( Abc_Frame_t* pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk;
    Abc_Obj_t * pFanin;
    int innum;
    Abc_Obj_t* pObj;
    int i;
    int s;
    int c0, c1;
    char* sop;
    
    int cc;
    
    pNtk = Abc_FrameReadNtk(pAbc);
    
    Abc_NtkForEachNode( pNtk, pObj, i ){
        std::cout<<"node "<< Abc_ObjName(pObj)<<":";
        sop = ((char*)pObj->pData);
        innum = Abc_ObjFaninNum(pObj);
        if (sop[innum+1] == '1'){
            
            cc = 0;
            Abc_ObjForEachFanin(pObj, pFanin, s){
                c1 = 0;
                c0 = 0;
                for (int m = 0; m < strlen(sop); m += (innum+3)){
                    if (sop[s+m] == '1'){
                        c1 = 1;
                    }
                    else if (sop[s+m] == '0'){
                        c0 = 1;
                    }
                }
                if (c1 == 1 && c0 != 1){
                    if (cc == 0){
                        std::cout<<"\n"<<"+unate inputs: ";
                        std::cout<<Abc_ObjName(pFanin);
                        cc = 1;
                    }
                    else {
                        std::cout<<","<<Abc_ObjName(pFanin);
                    }
                }
            }
            
            cc = 0;
            Abc_ObjForEachFanin(pObj, pFanin, s){
                c1 = 0;
                c0 = 0;
                for (int m = 0; m < strlen(sop); m += (innum+3)){
                    if (sop[s+m] == '1'){
                        c1 = 1;
                    }
                    else if (sop[s+m] == '0'){
                        c0 = 1;
                    }
                }
                if (c1 != 1 && c0 == 1){
                    if (cc == 0){
                        std::cout<<"\n"<<"-unate inputs: ";
                        std::cout<<Abc_ObjName(pFanin);
                        cc = 1;
                    }
                    else {
                        std::cout<<","<<Abc_ObjName(pFanin);
                    }
                }
            }
            
            cc = 0;
            Abc_ObjForEachFanin(pObj, pFanin, s){
                c1 = 0;
                c0 = 0;
                for (int m = 0; m < strlen(sop); m += (innum+3)){
                    if (sop[s+m] == '1'){
                        c1 = 1;
                    }
                    else if (sop[s+m] == '0'){
                        c0 = 1;
                    }
                }
                if (c1 == 1 && c0 == 1){
                    if (cc == 0){
                        std::cout<<"\n"<<"binate inputs: ";
                        std::cout<<Abc_ObjName(pFanin);
                        cc = 1;
                    }
                    else {
                        std::cout<<","<<Abc_ObjName(pFanin);
                    }
                }
            }
        }
        else{
            cc = 0;
            Abc_ObjForEachFanin(pObj, pFanin, s){
                c1 = 0;
                c0 = 0;
                for (int m = 0; m < strlen(sop); m += (innum+3)){
                    if (sop[s+m] == '1'){
                        c1 = 1;
                    }
                    else if (sop[s+m] == '0'){
                        c0 = 1;
                    }
                }
                if (c1 != 1 && c0 == 1){
                    if (cc == 0){
                        std::cout<<"\n"<<"+unate inputs: ";
                        std::cout<<Abc_ObjName(pFanin);
                        cc = 1;
                    }
                    else {
                        std::cout<<","<<Abc_ObjName(pFanin);
                    }
                }
            }
            
            cc = 0;
            Abc_ObjForEachFanin(pObj, pFanin, s){
                c1 = 0;
                c0 = 0;
                for (int m = 0; m < strlen(sop); m += (innum+3)){
                    if (sop[s+m] == '1'){
                        c1 = 1;
                    }
                    if (sop[s+m] == '0'){
                        c0 = 1;
                    }
                }
                if (c1 == 1 && c0 != 1){
                    if (cc == 0){
                        std::cout<<"\n"<<"-unate inputs: ";
                        std::cout<<Abc_ObjName(pFanin);
                        cc = 1;
                    }
                    else {
                        std::cout<<","<<Abc_ObjName(pFanin);
                    }
                }
            }
            
            cc = 0;
            Abc_ObjForEachFanin(pObj, pFanin, s){
                c1 = 0;
                c0 = 0;
                for (int m = 0; m < strlen(sop); m += (innum+3)){
                    if (sop[s+m] == '1'){
                        c1 = 1;
                    }
                    if (sop[s+m] == '0'){
                        c0 = 1;
                    }
                }
                if (c1 == 1 && c0 == 1){
                    if (cc == 0){
                        std::cout<<"\n"<<"binate inputs: ";
                        std::cout<<Abc_ObjName(pFanin);
                        cc = 1;
                    }
                    else {
                        std::cout<<","<<Abc_ObjName(pFanin);
                    }
                }
            }
        }
        std::cout<<"\n";
    }
    return 0;
}

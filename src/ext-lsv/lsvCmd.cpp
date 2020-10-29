#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <string>
#include <vector>
static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintSopunate(Abc_Frame_t* pAbc, int argc, char** argv);

struct fanins{
	char* name;
	int type; // 0=no,1=pos unate,2=neg unate,3=binate
};

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

void Lsv_NtkPrintSopunate(Abc_Ntk_t* pNtk) {
  Abc_Obj_t* pObj;
  int i;
  int bi=0,nu=0,pu=0;
  bool pos_neg = true;
  char* node_name;
  std::vector<fanins> vf,binate,pos_unate,neg_unate;
  fanins temp;
  
  Abc_NtkForEachNode(pNtk, pObj, i) {
    //printf("Object Id = %d, name = %s\n", Abc_ObjId(pObj), Abc_ObjName(pObj));
	node_name = Abc_ObjName(pObj);
    Abc_Obj_t* pFanin;
    int j;
    Abc_ObjForEachFanin(pObj, pFanin, j) {
      //printf("  Fanin-%d: Id = %d, name = %s\n", j, Abc_ObjId(pFanin),
      //       Abc_ObjName(pFanin));
	  temp.name = Abc_ObjName(pFanin);
	  temp.type = 0;
	  vf.push_back(temp);
    }
	bi=0;
	nu=0;
	pu=0;
	int n=-1;
    if (Abc_NtkHasSop(pNtk)) {
      //printf("The SOP of this node:\n%s", (char*)pObj->pData);
	  for(int m = 0; ((char*)pObj->pData)[m] != '\0' ; m++){
		  if(((char*)pObj->pData)[m] == '\n'){
			  if(((char*)pObj->pData)[m-1]=='0'){
				  pos_neg = false;
			  }
			  else if(((char*)pObj->pData)[m-1]=='1'){
				  pos_neg = true;
			  }
			  break;
		  }
	  }
	  for(int m = 0; ((char*)pObj->pData)[m] != '\0' ; m++){
		  if(((char*)pObj->pData)[m] == '\n'){
			  n=-1;
		  }
		  else{
			  n++;
		  }
		  if(n<vf.size() && pos_neg){
			  if(((char*)pObj->pData)[m] == '0'){
			  	  vf[n].type = vf[n].type|2;
			  }
			  else if(((char*)pObj->pData)[m] == '1' && (vf[n].type + 1)%2){
			  	  vf[n].type = vf[n].type|1;
			  }
		  }
		  else if(n<vf.size() && !pos_neg){
			  if(((char*)pObj->pData)[m] == '1'){
			  	  vf[n].type = vf[n].type|2;
			  }
			  else if(((char*)pObj->pData)[m] == '0' && (vf[n].type + 1)%2){
			  	  vf[n].type = vf[n].type|1;
			  }
		  }
	  }
	  for(int x=0;x<vf.size();x++){
		  if(vf[x].type == 3){
			  binate.push_back(vf[x]);
			  bi += 1;
		  }
		  else if(vf[x].type == 2){
			  neg_unate.push_back(vf[x]);
			  nu += 1;
		  }
		  else if(vf[x].type == 1){
			  pos_unate.push_back(vf[x]);
			  pu += 1;
		  }
	  }
	  vf.clear();
	  if(bi||nu||pu){
		  printf("node %s:\n",node_name);
		  if(pu){
			  printf("+unate inputs: %s",pos_unate[0].name);
			  for(int a=1;a<pu;a++){
				  printf(",%s",pos_unate[a].name);
			  }
			  printf("\n");
			  pos_unate.clear();
		  }
		  if(nu){
			  printf("-unate inputs: %s",neg_unate[0].name);
			  for(int a=1;a<nu;a++){
				  printf(",%s",neg_unate[a].name);
			  }
			  printf("\n");
			  neg_unate.clear();
		  }
		  if(bi){
			  printf("binate inputs: %s",binate[0].name);
			  for(int a=1;a<bi;a++){
				  printf(",%s",binate[a].name);
			  }
			  printf("\n");
			  binate.clear();
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
  Abc_Print(-2, "usage: lsv_print_sopunate [-h]\n");
  Abc_Print(-2, "\t        prints the sopunate in the network\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}
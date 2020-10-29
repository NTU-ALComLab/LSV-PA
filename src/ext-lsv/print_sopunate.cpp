#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <vector>
#include <string>
using namespace std;

int Lsv_CommandPrintUnates(Abc_Frame_t* pAbc, int argc, char** argv) {
	Abc_Obj_t* pObj;
	Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
	if (!pNtk) {
	    Abc_Print(-1, "Empty network.\n");
	    return 1;
	}
	int i;
	vector< pair<int,char*> > Objs;
	Abc_NtkForEachNode(pNtk, pObj, i) {
	   	//printf("Object Id = %d, name = %s\n", Abc_ObjId(pObj), Abc_ObjName(pObj));
		Objs.push_back(make_pair(Abc_ObjId(pObj),Abc_ObjName(pObj)));
	    	Abc_Obj_t* pFanin;
	    	int j;
		char* p_data;
  	   	vector< pair<int,char*> > fanin;
		vector< pair<int,int> > unate; //Define +unate = 1 -unate=0 binate=-1
	    	Abc_ObjForEachFanin(pObj, pFanin, j) {
			fanin.push_back(make_pair(Abc_ObjId(pFanin),Abc_ObjName(pFanin)));
	   	}
	   	int Fanin_Size = fanin.size();
		for(int i = 0;i<Fanin_Size;i++){
			//printf("Id = %d, name = %s\n",fanin[i].first,fanin[i].second);
			unate.push_back(make_pair(i+1,-2)); //Init this vector's second element as -2
		}
				
		
		p_data = (char*)pObj->pData;
		if (Abc_NtkHasSop(pNtk)) {
	     	 //printf("The SOP of this node:\n%s", p_data);
	   	}
		int p_counter = 0;
		for (; *p_data; p_data++){

			//printf("MOD:%d\n",p_counter%(Fanin_Size+3)+1);
			int vertex = p_counter%(Fanin_Size+3);
			if((p_counter%(Fanin_Size+3)<Fanin_Size)){
				//printf("Number:%d,%s",vertex,fanin[vertex].second);
				//The element "vertex" we want to check
				if((*p_data=='1')&(unate[vertex].second==-1|unate[vertex].second==0))
					unate[vertex].second = -1;
				else if ((*p_data=='1')&(unate[vertex].second==-2|unate[vertex].second==1))
					unate[vertex].second = 1;

				else if ((*p_data=='0')&(unate[vertex].second==-2|unate[vertex].second==0))
					unate[vertex].second = 0;
				else if ((*p_data=='0')&(unate[vertex].second==-1|unate[vertex].second==1))
					unate[vertex].second = -1;

				else if (*p_data=='-')
					//skip
					;
			}
			//printf("%c", *p_data);
			p_counter = p_counter +1; 
		}
		//printf("Fanin.size=%d\n",Fanin_Size);

		//for(int iter=0;iter<fanin.size();iter++){
		//	printf("Vertex %s,%d\n",fanin[iter].second,unate[iter].second);	
		//}
    int p = 0,n=0,b=0;
		for(int iter=0;iter<Fanin_Size;iter++){
			if(unate[iter].second==1)
        p = p +1;
		}
		for(int iter=0;iter<Fanin_Size;iter++){
			if(unate[iter].second==0)
        n = n +1;
		}
		for(int iter=0;iter<Fanin_Size;iter++){
			if(unate[iter].second==-1)
        b = b +1;
		}

    // printf("p=%d ,n=%d ,b=%d",p,n,b);

    int counter = 0;
		printf("node %s\n",Abc_ObjName(pObj));
		printf("+unate inputs: ");
		for(int iter=0;iter<Fanin_Size;iter++){
			if(unate[iter].second==1){
        counter = counter +1;
        if(counter==p){
          printf("%s",fanin[iter].second);
        }else{
          printf("%s,",fanin[iter].second);
        }
      }
		}
    counter = 0;
		printf("\n-unate inputs: ");
		for(int iter=0;iter<Fanin_Size;iter++){
			if(unate[iter].second==0){
        counter = counter +1;
        if(counter==n){
          printf("%s",fanin[iter].second);
        }else{
          printf("%s,",fanin[iter].second);
        }
      }
		}
    counter = 0;
		printf("\nbinate inputs: ");
		for(int iter=0;iter<Fanin_Size;iter++){
			if(unate[iter].second==-1){
        counter = counter +1;
        if(counter==b){
          printf("%s",fanin[iter].second);
        }else{
          printf("%s,",fanin[iter].second);
        }
        }
		}
		printf("\n");

	}
	//for(int i = 0;i<Objs.size();i++){
	//	printf("Node: %d Object Id = %d, name = %s\n",i+1,Objs[i].first,Objs[i].second);
	//
	//}
	return 0;

}

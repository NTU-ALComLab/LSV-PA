#include "base/main/main.h"
#include "base/main/mainInt.h"

#include <iostream>
#include <stdlib.h>
#include <vector>
#include <algorithm>
using namespace std;

namespace
{

void parseSOP(const string &str, vector<int> &record, bool &flip)
{
	//flag
    bool newline = true;
    int nodeID = 0;

	//parse
	for(string::const_iterator idx = str.begin(); idx != str.end(); ++idx){
		switch(*idx){
			case ' ':
				++idx;
				flip = (*idx == '1')? false: true;
				break;
			case '\n':
				newline = true;
				break;
			case '1':
				if(newline){
					newline = false;
					nodeID = 0;
				}
				if(record[nodeID] == 0) record[nodeID] = 1;
				else if(record[nodeID] == 2) record[nodeID] = 3;
				++nodeID;
				break;
			case '0':
				if(newline){
                    newline = false;
					nodeID = 0;
                }
				if(record[nodeID] == 0) record[nodeID] = 2;
                else if(record[nodeID] == 1) record[nodeID] = 3;
					++nodeID;
					break;
			case '-':
				if(newline){
			        newline = false;
					nodeID = 0;
				}
				//record[nodeID] = 3;
				++nodeID;
				break;
			default:
				break;
		}//end switch
	}//end for			
}

bool myCompare(Abc_Obj_t* n1, Abc_Obj_t* n2){
	return Abc_ObjId(n1) < Abc_ObjId(n2);
}


int Lsv_CommandPrintSOPUnate( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
    Abc_Obj_t* pObj;

	int i;
	Abc_NtkForEachNode(pNtk, pObj, i) {
		//cout << "node " << Abc_ObjName(pObj) << ":" << endl;

		if (Abc_NtkHasSop(pNtk)) {
			string str((char*)pObj->pData);
			/*
			cout << "-------------------------" << endl;
			cout << str; 
			cout << "-------------------------" << endl;
			*/
			//parse sop
			bool flip = false;
			int faninNum = Abc_ObjFaninNum(pObj);
			vector<int> record; // 0: init 1: +unite 2: -unite 3: binite 
			record.reserve(faninNum);
			record.resize(faninNum);
			parseSOP(str, record, flip);

			vector<Abc_Obj_t*> p_unate;
			p_unate.reserve(faninNum);
			vector<Abc_Obj_t*> n_unate;
			n_unate.reserve(faninNum);
			vector<Abc_Obj_t*> binate;
			binate.reserve(faninNum);

			Abc_Obj_t* pFanin;
            int j;
            Abc_ObjForEachFanin(pObj, pFanin, j){
                if( (record[j] == 1 && !flip) || (record[j] == 2 && flip) || (record[j] == 0) ){
                    p_unate.push_back(pFanin);
                }
				else if((record[j] == 2 && !flip) || (record[j] == 1 && flip) || (record[j] == 0) ){
					n_unate.push_back(pFanin);
				}
				else{
					binate.push_back(pFanin);
				}
            }

			//print ans
			if(!(p_unate.empty() && n_unate.empty() && binate.empty())){
				cout << "node " << Abc_ObjName(pObj) << ":" << endl;
			}
			if(!p_unate.empty()){
				sort(p_unate.begin(), p_unate.end(), myCompare);

				cout << "+unate inputs: ";
				for(vector<Abc_Obj_t*>::iterator idx = p_unate.begin(); idx != p_unate.end(); ++idx){
					if(idx == p_unate.begin()) cout << Abc_ObjName(*idx);
					else cout << "," << Abc_ObjName(*idx);
				}
				cout << endl;
			}
			if(!n_unate.empty()){
				sort(n_unate.begin(), n_unate.end(), myCompare);

                cout << "-unate inputs: ";
                for(vector<Abc_Obj_t*>::iterator idx = n_unate.begin(); idx != n_unate.end(); ++idx){
                    if(idx == n_unate.begin())  cout << Abc_ObjName(*idx);
                    else cout << "," << Abc_ObjName(*idx);
                }
                cout << endl;
            }
			if(!binate.empty()){
				sort(binate.begin(), binate.end(), myCompare);

                cout << "binate inputs: ";
                for(vector<Abc_Obj_t*>::iterator idx = binate.begin(); idx != binate.end(); ++idx){
                    if(idx == binate.begin()) cout << Abc_ObjName(*idx);
                    else cout << "," << Abc_ObjName(*idx);
                }
                cout << endl;
            }
			cout << endl;
		}//end if sop
	}//end for each node
	
    return 0;
}

// called during ABC startup
void init(Abc_Frame_t* pAbc)
{
    Cmd_CommandAdd( pAbc, "LSV", "lsv_print_sopunate", Lsv_CommandPrintSOPUnate, 0);
}

// called during ABC termination
void destroy(Abc_Frame_t* pAbc)
{
}

// this object should not be modified after the call to Abc_FrameAddInitializer
Abc_FrameInitializer_t frame_initializer = { init, destroy };

// register the initializer a constructor of a global object
// called before main (and ABC startup)
struct registrar
{
    registrar() 
    {
        Abc_FrameAddInitializer(&frame_initializer);
    }
} myAdd_registrar;

} // unnamed namespace

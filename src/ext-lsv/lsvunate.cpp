#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <iostream>
#include <vector>
#include <algorithm>


using namespace std;

namespace unate{

class fobj{
public:
    char Unate;
    int Id;
    string Name;
    fobj(char u, int i, string n): Unate(u), Id(i), Name(n){}
};

void Sort_Id(vector<fobj> &v_fobj) {
    for(int i = 1; i < v_fobj.size(); ++i) {
        fobj target = v_fobj[i];
        int j = i - 1;
        while (target.Id < v_fobj[j].Id && j >= 0) {
            v_fobj[j+1] = v_fobj[j];
            j--;
        }
        v_fobj[j+1] = target;
    }
}

int Lsv_CommandPrintUnate(Abc_Frame_t* pAbc, int argc, char** argv) {
    Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
    if(!pNtk) {
        Abc_Print(-1, "Empty Network.\n");
        return 1;
    }
    Abc_Obj_t* pObj;
    int i;
    Abc_NtkForEachNode(pNtk, pObj, i) {
        if (Abc_NtkHasSop(pNtk)) {
            int fanin_count = Abc_SopGetVarNum(((char*) pObj->pData));
            if(fanin_count > 0) {
                cout << "node " << Abc_ObjName(pObj) << ":" << endl;
            }
            char* pCube;
            int j;
            Abc_Obj_t* pFanin;
            //1:+, 0:-, '-':+-, b:binate
            vector<fobj> fanin_unate;
            Abc_ObjForEachFanin(pObj, pFanin, j) {
                fobj temp('-', Abc_ObjId(pFanin), Abc_ObjName(pFanin));
                fanin_unate.push_back(temp);
                //cout << fanin_unate[j].Unate << ' ' << fanin_unate[j].Id << ' ' << fanin_unate[j].Name << endl;
            }

            bool onset = (*(((char*) pObj->pData) + fanin_count + 1) == '1');

            char Value;
            Abc_SopForEachCube( ((char*) pObj->pData), fanin_count, pCube ) {
                Abc_CubeForEachVar( pCube, Value, j ){
                    if(fanin_unate[j].Unate == '-')
                        fanin_unate[j].Unate = Value;
                    else if(fanin_unate[j].Unate != Value && Value != '-')
                        fanin_unate[j].Unate = 'b';
                }
            }
            
            Sort_Id(fanin_unate);
            vector<string> positive_unates;
            vector<string> negative_unates;
            vector<string> binates;
            for(j = 0; j < fanin_unate.size(); ++j)
            {
                
                if(fanin_unate[j].Unate == '-') {
                    positive_unates.push_back(fanin_unate[j].Name);
                    negative_unates.push_back(fanin_unate[j].Name);
                }
                else if((fanin_unate[j].Unate == '1' && onset) || ((fanin_unate[j].Unate == '0' && !onset))){
                    positive_unates.push_back(fanin_unate[j].Name);
                }
                else if((fanin_unate[j].Unate == '0' && onset) || ((fanin_unate[j].Unate == '1' && !onset))){
                    negative_unates.push_back(fanin_unate[j].Name);
                }
                else {
                    binates.push_back(fanin_unate[j].Name);
                }
            }
            
            //print result
            if(positive_unates.size() > 0) {
                cout << "+unate inputs: ";
                for(j = 0; j < positive_unates.size() - 1; ++j) {
                    cout << positive_unates[j] << ',';
                }
                cout << positive_unates[j] << endl;
            }
            if(negative_unates.size() > 0) {
                cout << "-unate inputs: " ;
                for(j = 0; j < negative_unates.size() - 1; ++j) {
                    cout << negative_unates[j] << ','; 
                }
                cout << negative_unates[j] << endl;
            }
            if(binates.size() > 0) {
                cout << "binate inputs: ";
                for(j = 0; j < binates.size() - 1; ++j) {
                    cout << binates[j] << ',';
                }
                cout << binates[j] << endl;
            }

        }// if (Abc_NtkHasSop(pNtk))
    }// Abc_NtkForEachNode(pNtk, pObj, i)
    return 0;
}

void init(Abc_Frame_t* pAbc) {
    Cmd_CommandAdd(pAbc, "Print unate", "lsv_print_sopunate", Lsv_CommandPrintUnate, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct registration_lsv_unate {
    registration_lsv_unate() { Abc_FrameAddInitializer(&frame_initializer); }
} registration_lsv_unate;

}//end of namespace

#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "sat/cnf/cnf.h"
#include "sat/bsat/satSolver.h"
#include <vector>
#include <unordered_map>
#include <algorithm>
#include <string>
#include <iostream>

using namespace std;

extern "C" {
    Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
}

void addCnfClauses(sat_solver *pSat, Cnf_Dat_t *pCnf);

static int Lsv_CommandPrintPOUnate(Abc_Frame_t *pAbc, int argc, char **argv);

void init(Abc_Frame_t *pAbc)
{
    Cmd_CommandAdd(pAbc, "LSV", "lsv_print_pounate", Lsv_CommandPrintPOUnate, 0);
}

void destroy(Abc_Frame_t *pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager
{
    PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

void Lsv_NtkPrintPOUnate(Abc_Ntk_t *pNtk)
{
    Abc_Obj_t *pObjPi;
    int piIdx;
    
    // /*==print Obj PI Detail==*/
    // cout << "====Print Obj PI Detail====" << endl;
    // Abc_NtkForEachPi(pNtk,pObjPi,piIdx){//for each object pi of the NTK   
    //     cout << "The Obj name:" << Abc_ObjName(pObjPi) << ", ";
    //     cout << "The Id in Obj:" <<  Abc_ObjId(pObjPi);
    //     cout << endl;
    // }

    //Record the obj pi to NTK
    unordered_map<string,int> PiName2Idx;//first:key, second:value
    Abc_NtkForEachPi(pNtk,pObjPi,piIdx){//for each object pi of the NTK
        PiName2Idx[Abc_ObjName(pObjPi)]=piIdx;
    }

    // /*=print the list which piname to the obj id=*/
    // cout << "====Print the list which PiName to the Ntk Id====" << endl;
    // for (auto& it: PiName2Idx){
    //     cout << "PiName:" << it.first << ", "<< "NtkId:"<< it.second << endl;
    // }

    Abc_Obj_t * pObjPo;
    int poIdx;
    Abc_Ntk_t * pNtkPo;

    Abc_NtkForEachPo(pNtk,pObjPo,poIdx){//for each object po of the NTK

        pNtkPo = Abc_NtkCreateCone(pNtk,Abc_ObjFanin0(pObjPo),Abc_ObjName(pObjPo),0);//Change to the TFI Cone
    
        vector<int> vNtkPiIdx;
        vector<string> vPiName;
        vector<int> vPosUnate;
        vector<int> vNegUnate;
        vector<int> vBinate;
        vector<int> vNonSp;
        unordered_map<int,int> conePi2Id;
        unordered_map<int,int> conePi2NtkPi;
        
        //corresponding the cone pi to the original pi
        Abc_NtkForEachPi(pNtkPo,pObjPi,piIdx){
            conePi2Id[piIdx]=Abc_ObjId(pObjPi);
            vNtkPiIdx.push_back(PiName2Idx[Abc_ObjName(pObjPi)]);
            vPiName.push_back(Abc_ObjName(pObjPi));
            conePi2NtkPi[piIdx]=PiName2Idx[Abc_ObjName(pObjPi)];
        }

        // /*==Print Cone PI Detail==*/
        // cout << "====Print Cone PI Detail====" << endl;
        // cout << "POName: " << Abc_ObjName(pObjPo) << endl;
        // Abc_NtkForEachPi(pNtkPo,pObjPi,piIdx){//for each copi of the ObjPo   
        // cout << "The Cone of PI name:" << Abc_ObjName(pObjPi) << ", ";
        // cout << "The Id in Cone:" <<  Abc_ObjId(pObjPi) << ", ";
        // cout << "The Id in Ntk:" <<   conePi2NtkPi[piIdx] << endl;
        // }
       
        //======sat solver=======       
        Aig_Man_t *pMan;
        Cnf_Dat_t * pCnfPos, *pCnfNeg;
        sat_solver* pSat;

        //aig circuit
        pMan = Abc_NtkToDar(pNtkPo, 0, 0);
        
        //cnf
        pCnfPos = Cnf_Derive(pMan, Aig_ManCoNum(pMan));
        pCnfNeg = Cnf_DataDup(pCnfPos);
        Cnf_DataLift(pCnfNeg,pCnfPos->nVars);

        //a set solver    
        pSat = sat_solver_new();
        sat_solver_setnvars(pSat,pCnfPos->nVars + pCnfNeg->nVars);

        //add clauses for aig
        addCnfClauses(pSat, pCnfPos);
        addCnfClauses(pSat, pCnfNeg);

        //add alpha
        int i;
        Aig_Obj_t * pAigObjCi, *pAigObjPo;
        pAigObjPo = Aig_ManCo(pMan,0);
        vector<int> vAlphas;
        Aig_ManForEachCi(pMan, pAigObjCi, i){
            vAlphas.push_back(sat_solver_addvar(pSat));
            sat_solver_add_buffer_enable(pSat,pCnfPos->pVarNums[Aig_ObjId(pAigObjCi)],pCnfNeg->pVarNums[Aig_ObjId(pAigObjCi)],vAlphas.back(),0);
        }
        int ciNum = Aig_ManCiNum(pMan);
        int lits[ciNum + 4];
        bool UnateCheck[2] = {0};
    
        Aig_ManForEachCi(pMan,pAigObjCi,i){
            //if we want to check the i of Pi, we let alpha i = 0, and other set to 1
            //The above operation is same as to when i = j :toLitCond(alpha(i), 1)
            //else: toLitCond(alpha(i), 0)    
            for(int j = 0; j < ciNum ; j++){
                if(j != i) lits[j]=toLitCond(vAlphas[j],0);
                else lits[j]=toLitCond(vAlphas[j],1);
            }
            lits[ciNum] =toLitCond(pCnfPos->pVarNums[Aig_ObjId(pAigObjCi)],0);
            lits[ciNum + 1]=toLitCond(pCnfNeg->pVarNums[Aig_ObjId(pAigObjCi)],1);
            lits[ciNum + 2]=toLitCond(pCnfPos->pVarNums[Aig_ObjId(pAigObjPo)],0);//neg unate
            lits[ciNum + 3]=toLitCond(pCnfNeg->pVarNums[Aig_ObjId(pAigObjPo)],1);//neg unate
            UnateCheck[0] = sat_solver_solve(pSat,lits,lits+ciNum + 4,0,0,0,0) == l_False;

            lits[ciNum + 2]=toLitCond(pCnfPos->pVarNums[Aig_ObjId(pAigObjPo)],1);//pos unate
            lits[ciNum + 3]=toLitCond(pCnfNeg->pVarNums[Aig_ObjId(pAigObjPo)],0);//pos unate
            UnateCheck[1] = sat_solver_solve(pSat,lits,lits+ciNum + 4,0,0,0,0) == l_False;

            if(UnateCheck[0]){
                if(!(pObjPo->fCompl0)) vNegUnate.push_back(conePi2NtkPi[i]);
                else vPosUnate.push_back(conePi2NtkPi[i]);
            }
            if(UnateCheck[1]){
                if(!(pObjPo->fCompl0)) vPosUnate.push_back(conePi2NtkPi[i]);
                else vNegUnate.push_back(conePi2NtkPi[i]);
            }
        }

        
        Abc_NtkForEachPi(pNtk,pObjPi,piIdx){
            if(find(vPiName.begin(),vPiName.end(),Abc_ObjName(pObjPi))==vPiName.end()) vNonSp.push_back(piIdx);
        }

        for(int i=0; i<vNonSp.size(); i++)
        {
            vPosUnate.push_back(vNonSp[i]);
            vNegUnate.push_back(vNonSp[i]);
        }
        sort(vPosUnate.begin(), vPosUnate.end());
        sort(vNegUnate.begin(), vNegUnate.end());


        int sizeOfPosUnate = vPosUnate.size();
        int sizeOfNegUnate = vNegUnate.size();
        
        printf("node %s:\n",(char *)Abc_ObjName(pObjPo));
        if(sizeOfPosUnate>0){
            printf("+unate inputs: ");
            for (int i=0;i<sizeOfPosUnate;i++){ 
                if(i == sizeOfPosUnate-1) printf("%s\n",(char *)Abc_ObjName(Abc_NtkPi(pNtk,vPosUnate[i])));
                else printf("%s,",(char *)Abc_ObjName(Abc_NtkPi(pNtk,vPosUnate[i])));
            }
        }
        
        if(sizeOfNegUnate>0){
            printf("-unate inputs: ");
            for (int i=0;i<sizeOfNegUnate;i++){ 
                if(i == sizeOfNegUnate-1) printf("%s\n",(char *)Abc_ObjName(Abc_NtkPi(pNtk,vNegUnate[i])));
                else printf("%s,",(char *)Abc_ObjName(Abc_NtkPi(pNtk,vNegUnate[i])));
            }
        }

        for(int i=0;i<vNtkPiIdx.size();i++){
            if(find(vPosUnate.begin(),vPosUnate.end(),vNtkPiIdx[i])==vPosUnate.end() && find(vNegUnate.begin(),vNegUnate.end(),vNtkPiIdx[i])==vNegUnate.end()){
                vBinate.push_back(vNtkPiIdx[i]);
            }
        }
        sort(vBinate.begin(),vBinate.end());
        int sizeOfBinate = vBinate.size();

        if(sizeOfBinate>0){
            printf("binate inputs: ");
            for (int i=0;i<sizeOfBinate;i++){ 
                if(i == sizeOfBinate-1) printf("%s\n",(char *)Abc_ObjName(Abc_NtkPi(pNtk,vBinate[i])));
                else printf("%s,",(char *)Abc_ObjName(Abc_NtkPi(pNtk,vBinate[i])));
            }
        }        


        // if(vBinate.size()>0){
        //     printf("binate inputs: ");
        //     for(int i=0;i<vBinate.size();i++)
        //     {
        //         printf("%s",(char *)Abc_ObjName(Abc_NtkPi(pNtk,vBinate[i])));
        //         if(i<vBinate.size()-1)
        //             printf(",");
        //     }
        //     printf("\n");
        // }
        Abc_NtkDelete(pNtkPo);
        Cnf_DataFree(pCnfPos);
        Cnf_DataFree(pCnfNeg);
        Aig_ManStop(pMan);
        sat_solver_delete(pSat);
        
    }
}


void addCnfClauses(sat_solver *pSat, Cnf_Dat_t *pCnf)
{
    for (int i = 0; i < pCnf->nClauses; i++)
    {
        sat_solver_addclause(pSat, pCnf->pClauses[i], pCnf->pClauses[i + 1]);
    }
}

int Lsv_CommandPrintPOUnate(Abc_Frame_t *pAbc, int argc, char **argv)
{
    Abc_Ntk_t *pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    Extra_UtilGetoptReset();
    while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF)
    {
        switch (c)
        {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if (!pNtk)
    {
        Abc_Print(-1, "Empty network.\n");
        return 1;
    }
    Lsv_NtkPrintPOUnate(pNtk);
    return 0;

usage:
    Abc_Print(-2, "usage: lsv_print_pounate [-h]\n");
    Abc_Print(-2, "\t        prints the unate information of POs\n");
    Abc_Print(-2, "\t-h    : print the command usage\n");
    return 1;
}
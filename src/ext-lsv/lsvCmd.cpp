#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "sat/cnf/cnf.h"
#include "sat/bsat/satSolver.h"
#include <utility>
#include <vector>
#include <unordered_map>
#include <algorithm>
#include <string>
#include <iostream>

using namespace std;

extern "C" {
    Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
}

static int Lsv_CommandPrintNodeSopUnate(Abc_Frame_t *pAbc, int argc, char **argv);
static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintPOUnate(Abc_Frame_t *pAbc, int argc, char **argv);

void init(Abc_Frame_t *pAbc)
{
    Cmd_CommandAdd(pAbc, "LSV", "lsv_print_sopunate", Lsv_CommandPrintNodeSopUnate, 0);
    Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
    Cmd_CommandAdd(pAbc, "LSV", "lsv_print_pounate", Lsv_CommandPrintPOUnate, 0);
}

void destroy(Abc_Frame_t *pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager
{
    PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

void Lsv_NtkPrintNodeSOPUnate(Abc_Ntk_t *pNtk)
{
    Abc_Obj_t *pObj;
    char *pCube;
    std::vector<std::pair<int, int>> faninIds;
    std::pair<int, int> p;
    char **faninNames;
    int *unate; //-1: undecided, 0: pos unate, 1: neg unate, 2: binate

    int i;
    Abc_NtkForEachNode(pNtk, pObj, i)
    {
        if(Abc_SopIsConst1((char *)pObj->pData)||Abc_SopIsConst0((char *)pObj->pData))
            continue;
        printf("node %s:\n", Abc_ObjName(pObj));
        int numFanins = Abc_ObjFaninNum(pObj);
        faninNames = new char *[numFanins];
        unate = new int[numFanins];
        faninIds.clear();
        Abc_Obj_t *pFanin;
        int j;
        Abc_ObjForEachFanin(pObj, pFanin, j)
        {
            //printf("  Fanin-%d: Id = %d, name = %s\n", j, Abc_ObjId(pFanin), Abc_ObjName(pFanin));
            p.second = j;
            p.first = Abc_ObjId(pFanin); //to sort by id
            faninIds.push_back(p);
            faninNames[j] = Abc_ObjName(pFanin);
            unate[j] = -1;
        }

        if (Abc_NtkHasSop(pNtk))
        {
            //printf("The SOP of this node:\n%s", (char *)pObj->pData);
            //printf("Num fanin: %d\n", Abc_ObjFaninNum(pObj));

            Abc_SopForEachCube((char *)pObj->pData, Abc_ObjFaninNum(pObj), pCube)
            {
                //printf("cube: %s\n",(char*)pCube);
                //printf("cube:\n");
                int k;
                char value;
                bool outputPos = pCube[strlen(pCube) - 2] == '1' ? true : false;
                //printf("%c,  %d\n",pCube[strlen(pCube)-2],outputPos);
                Abc_CubeForEachVar(pCube, value, k)
                {
                    //printf("k: %d, value: %c", k, value);

                    if (unate[k] != 2)
                    {
                        if ((value == '1' && outputPos) || (value == '0' && !outputPos))
                        {
                            unate[k] = unate[k] == 1 ? 2 : 0;
                        }
                        else if ((value == '0' && outputPos) || (value == '1' && !outputPos))
                        {
                            unate[k] = unate[k] == 0 ? 2 : 1;
                        }
                    }

                    //printf("\n unate[k]: %d\n",unate[k]);
                }
            }
        }
        sort(faninIds.begin(), faninIds.end());
        std::vector<std::string> posUnateNames, negUnateNames, binateNames;
        int id, ind;
        for (int k = 0; k < faninIds.size(); k++)
        {
            id = faninIds[k].first;
            ind = faninIds[k].second;
            //printf("id:%d, name %s, unate: %d\n",id, faninNames[ind], unate[ind]);
            if (unate[ind] == 0)
            {
                posUnateNames.push_back(faninNames[ind]);
            }
            else if (unate[ind] == 1)
            {
                negUnateNames.push_back(faninNames[ind]);
            }
            else if (unate[ind] == 2)
            {
                binateNames.push_back(faninNames[ind]);
            }
            else
            {
                //printf("Wrong unate information!");
                binateNames.push_back(faninNames[ind]);
            }
        }
        if (posUnateNames.size() > 0)
        {
            printf("+unate inputs: ");
            for (int n = 0; n < posUnateNames.size(); n++)
            {
                std::cout << (posUnateNames[n]);
                if (n < posUnateNames.size() - 1)
                    printf(",");
            }
            printf("\n");
        }
        if (negUnateNames.size() > 0)
        {
            printf("-unate inputs: ");
            for (int n = 0; n < negUnateNames.size(); n++)
            {
                std::cout << (negUnateNames[n]);
                if (n < negUnateNames.size() - 1)
                    printf(",");
            }
            printf("\n");
        }
        if (binateNames.size() > 0)
        {
            printf("binate inputs: ");
            for (int n = 0; n < binateNames.size(); n++)
            {
                std::cout << (binateNames[n]);
                if (n < binateNames.size() - 1)
                    printf(",");
            }
            printf("\n");
        }

        printf("\n");
        delete[] unate;
        delete[] faninNames;
    }
}

int Lsv_CommandPrintNodeSopUnate(Abc_Frame_t *pAbc, int argc, char **argv)
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
    Lsv_NtkPrintNodeSOPUnate(pNtk);
    return 0;

usage:
    Abc_Print(-2, "usage: lsv_print_sopunate [-h]\n");
    Abc_Print(-2, "\t        prints the nodes in the network as well as the unate information\n");
    Abc_Print(-2, "\t-h    : print the command usage\n");
    return 1;
}

void Lsv_NtkPrintNodes(Abc_Ntk_t *pNtk)
{
    Abc_Obj_t *pObj;
    int i;
    Abc_NtkForEachNode(pNtk, pObj, i)
    {
        printf("Object Id = %d, name = %s\n", Abc_ObjId(pObj), Abc_ObjName(pObj));
        Abc_Obj_t *pFanin;
        int j;
        Abc_ObjForEachFanin(pObj, pFanin, j)
        {
            printf("  Fanin-%d: Id = %d, name = %s\n", j, Abc_ObjId(pFanin),
                   Abc_ObjName(pFanin));
        }
        if (Abc_NtkHasSop(pNtk))
        {
            printf("The SOP of this node:\n%s", (char *)pObj->pData);
        }
    }
}

int Lsv_CommandPrintNodes(Abc_Frame_t *pAbc, int argc, char **argv)
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
    Lsv_NtkPrintNodes(pNtk);
    return 0;

usage:
    Abc_Print(-2, "usage: lsv_print_nodes [-h]\n");
    Abc_Print(-2, "\t        prints the nodes in the network\n");
    Abc_Print(-2, "\t-h    : print the command usage\n");
    return 1;
}


//For PA2
void Lsv_NtkPrintPOUnate(Abc_Ntk_t *pNtk)
{
    Aig_Man_t *pMan;
    Abc_Obj_t * pObjPo, *pObjPi;
    int poInd,piInd;
    Abc_Ntk_t * pPoNtk;
    sat_solver* solver;
    int edgeComplimented;

    //std::cout << "numPo: " << Abc_NtkPoNum(pNtk) << std::endl;
    //std::unordered_map<char*,int> ntkPiName2Ind;
    std::unordered_map<string,int> ntkPiName2Ind;
    
    //std::cout << "PI ID,name:";
    Abc_NtkForEachPi(pNtk,pObjPi,piInd)
    {
        //std::cout << '(' << Abc_ObjId(pObjPi) << ',' << Abc_ObjName(pObjPi) << ')';
        ntkPiName2Ind[Abc_ObjName(pObjPi)]=piInd;
    }
    //cout << endl;
    //cout << "ntkPiName2Ind: " << endl;
    // for (auto& x: ntkPiName2Ind)
    // {
    //     std::cout << x.first << ": " << x.second << std::endl;
    // }

    //std::cout << std::endl;
    Abc_NtkForEachPo( pNtk,pObjPo,poInd)
    {
        //std::cout << "PO: " << Abc_ObjName(pObjPo) << std::endl;
        pPoNtk = Abc_NtkCreateCone(pNtk,Abc_ObjFanin0(pObjPo),Abc_ObjName(pObjPo),0);
        //std::cout << "cone PI IDs:\n";
        vector<int> conePiNtkInds;
        vector<string> conePiNames;
        std::unordered_map<int,int> conePiInd2Id;
        std::unordered_map<int,int> conePiInd2NtkPiInd;
        //cout << "cone Pi ID,name:";
        Abc_NtkForEachPi(pPoNtk,pObjPi,piInd)
        {
            //std::cout << '(' << Abc_ObjId(pObjPi) << ',' << Abc_ObjName(pObjPi) << ')';
            conePiInd2Id[piInd]=Abc_ObjId(pObjPi);
            conePiNtkInds.push_back(ntkPiName2Ind[Abc_ObjName(pObjPi)]);
            conePiNames.push_back(Abc_ObjName(pObjPi));
            //cout << "corresponding ntkInd:" << ntkPiName2Ind[Abc_ObjName(pObjPi)];
            conePiInd2NtkPiInd[piInd]=ntkPiName2Ind[Abc_ObjName(pObjPi)];
        }
        //std::cout << std::endl;
        
        // cout << "conePiInd2NtkPiInd: " << endl;
        // for (auto& x: conePiInd2NtkPiInd)
        // {
        //     std::cout << x.first << ": " << x.second << std::endl;
        // }

        vector<int> nonSupportNtkPiInds;
        //cout << "Non-support PIs:";
        Abc_NtkForEachPi(pNtk,pObjPi,piInd)
        {
            if(find(conePiNames.begin(),conePiNames.end(),Abc_ObjName(pObjPi))==conePiNames.end())
            {
                nonSupportNtkPiInds.push_back(piInd);
                //cout << (char *)Abc_ObjName(Abc_NtkPi(pNtk,ntkPiId2Ind[Abc_ObjId(pObjPi)]));
            }
        }
        //cout << endl;
        edgeComplimented = pObjPo->fCompl0;
        pMan = Abc_NtkToDar( pPoNtk, 0, 0 );
        Cnf_Dat_t * pCnfPos, *pCnfNeg;
        pCnfPos = Cnf_Derive(pMan, Aig_ManCoNum(pMan));
        pCnfNeg = Cnf_DataDup(pCnfPos);
        Cnf_DataLift(pCnfNeg,pCnfPos->nVars);
        solver = sat_solver_new();
        sat_solver_setnvars(solver,2*(pCnfPos->nVars));
        int * beg, *end;
        int i;
        //add clauses for AIG
        Cnf_CnfForClause(pCnfPos,beg,end,i)
        {
            sat_solver_addclause(solver,beg,end);
        }
        Cnf_CnfForClause(pCnfNeg,beg,end,i)
        {
            sat_solver_addclause(solver,beg,end);
        }
        //add clause for incremental solving
        int ciInd;
        Aig_Obj_t * pAigObjCi, *pAigObjPo;
        pAigObjPo = Aig_ManCo(pMan,0);
        std::vector<int> alphas;
        Aig_ManForEachCi(pMan, pAigObjCi, ciInd)
        {
            alphas.push_back(sat_solver_addvar(solver));
            sat_solver_add_buffer_enable(solver,pCnfPos->pVarNums[Aig_ObjId(pAigObjCi)],pCnfNeg->pVarNums[Aig_ObjId(pAigObjCi)],alphas.back(),0);
        }
        int assumption[alphas.size()+4];
        
        int solveRes;
        
        std::vector<int> posUnatePiNtkInd;
        std::vector<int> negUnatePiNtkInd;

        //std::cout << "starts to go through fainins" << std::endl;
        Aig_ManForEachCi(pMan,pAigObjCi,ciInd)
        {
            //std::cout << "PI: " << Abc_ObjName(Abc_NtkPi(pPoNtk,ciInd)) << std::endl;
            for(int j=0;j<alphas.size();j++)
            {
                if(j==ciInd)
                {
                    assumption[j]=toLitCond(alphas[j],1);//not enable, input set to (1,0) for (pos,neg) respectively later
                }
                else
                {
                    assumption[j]=toLitCond(alphas[j],0);//enable clauses, make input identical for pos and neg 
                }
            }
            //std::cout << "alpha assumptions done\n";
            assumption[alphas.size()]=toLitCond(pCnfPos->pVarNums[Aig_ObjId(pAigObjCi)],0);
            assumption[alphas.size()+1]=toLitCond(pCnfNeg->pVarNums[Aig_ObjId(pAigObjCi)],1);
            assumption[alphas.size()+2]=toLitCond(pCnfPos->pVarNums[Aig_ObjId(pAigObjPo)],0);//neg unate
            assumption[alphas.size()+3]=toLitCond(pCnfNeg->pVarNums[Aig_ObjId(pAigObjPo)],1);//neg unate
            //std::cout << "input output assumptions done\n";
            solveRes = sat_solver_solve(solver,assumption,assumption+alphas.size()+4,0,0,0,0);
            //std::cout << "solver solved\n";
            if(solveRes==l_False)
            {
                //std::cout << "unsat\n";
                if(!edgeComplimented)
                {
                    negUnatePiNtkInd.push_back(conePiInd2NtkPiInd[ciInd]);
                }
                else
                {
                    posUnatePiNtkInd.push_back(conePiInd2NtkPiInd[ciInd]);
                }
                
            }
            assumption[alphas.size()+2]=toLitCond(pCnfPos->pVarNums[Aig_ObjId(pAigObjPo)],1);//pos unate
            assumption[alphas.size()+3]=toLitCond(pCnfNeg->pVarNums[Aig_ObjId(pAigObjPo)],0);//pos unate
            solveRes = sat_solver_solve(solver,assumption,assumption+alphas.size()+4,0,0,0,0);
            if(solveRes==l_False)
            {
                //std::cout << "unsat\n";
                if(!edgeComplimented)
                {
                    posUnatePiNtkInd.push_back(conePiInd2NtkPiInd[ciInd]);
                }
                else
                {
                    negUnatePiNtkInd.push_back(conePiInd2NtkPiInd[ciInd]);
                }
            }
        }
        for(int i=0; i<nonSupportNtkPiInds.size(); i++)
        {
            posUnatePiNtkInd.push_back(nonSupportNtkPiInds[i]);
            negUnatePiNtkInd.push_back(nonSupportNtkPiInds[i]);
        }
        sort(posUnatePiNtkInd.begin(), posUnatePiNtkInd.end());
        sort(negUnatePiNtkInd.begin(), negUnatePiNtkInd.end());
        //std::cout << "went through PIs\n";
        //std::cout << "len posUnatePi:" << posUnatePi.size() << "len negUnatePi:" << negUnatePi.size() << std::endl;
        printf("node %s:\n",(char *)Abc_ObjName(pObjPo));
        if(posUnatePiNtkInd.size()>0)
        {
            printf("+unate inputs: ");
            for (int i=0;i<posUnatePiNtkInd.size();i++)
            {
                printf("%s",(char *)Abc_ObjName(Abc_NtkPi(pNtk,posUnatePiNtkInd[i])));
                if(i<posUnatePiNtkInd.size()-1)
                    printf(",");
            }
            printf("\n");
        }
        if(negUnatePiNtkInd.size()>0)
        {
            printf("-unate inputs: ");
            for (int i=0;i<negUnatePiNtkInd.size();i++)
            {
                printf("%s",(char *)Abc_ObjName(Abc_NtkPi(pNtk,negUnatePiNtkInd[i])));
                if(i<negUnatePiNtkInd.size()-1)
                    printf(",");
            }
            printf("\n");
        }

        std::vector<int> binateNtkInds;
        for(int i=0;i<conePiNtkInds.size();i++)
        {
            if(find(posUnatePiNtkInd.begin(),posUnatePiNtkInd.end(),conePiNtkInds[i])==posUnatePiNtkInd.end() && find(negUnatePiNtkInd.begin(),negUnatePiNtkInd.end(),conePiNtkInds[i])==negUnatePiNtkInd.end())
            {
                binateNtkInds.push_back(conePiNtkInds[i]);
            }
        }
        sort(binateNtkInds.begin(),binateNtkInds.end());
        if(binateNtkInds.size()>0)
        {
            printf("binate inputs: ");
            for(int i=0;i<binateNtkInds.size();i++)
            {
                printf("%s",(char *)Abc_ObjName(Abc_NtkPi(pNtk,binateNtkInds[i])));
                if(i<binateNtkInds.size()-1)
                    printf(",");
            }
            printf("\n");
        }

        // std::vector<int> binateNtkInds;
        // for(int i=0;i<PiIDs.size();i++)
        // {
        //     if(find(posUnatePiId.begin(),posUnatePiId.end(),PiIDs[i])==posUnatePiId.end() && find(negUnatePiId.begin(),negUnatePiId.end(),PiIDs[i])==negUnatePiId.end())
        //     {
        //         binateNtkInds.push_back(ntkPiId2Ind[PiIDs[i]]);
        //     }
        // }
        // if(binateNtkInds.size()>0)
        // {
        //     printf("binate inputs: ");
        //     for (int i=0;i<binateNtkInds.size();i++)
        //     {
        //         printf("%s",(char *)Abc_ObjName(Abc_NtkPi(pNtk,binateNtkInds[i])));
        //         //printf("(id:%d)",Abc_ObjId(Abc_NtkPi(pNtk,binateNtkInds[i])));
        //         if(i<binateNtkInds.size()-1)
        //             printf(",");
        //     }
        //     printf("\n");
        // }
            

        
    }
    sat_solver_delete(solver);
    // Abc_Obj_t *pObj;
    // int i;
    // Abc_NtkForEachPo(pNtk, pObj, i)
    // {
    //     printf("node %s:\n",(char *)Abc_ObjName(pObj));
    // }
    
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
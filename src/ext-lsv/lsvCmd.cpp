#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "sat/cnf/cnf.h"
#include <vector>
#include <algorithm>

/*== base/abci/abcDar.c ==*/
extern "C" { Aig_Man_t *Abc_NtkToDar(Abc_Ntk_t *pNtk, int fExors, int fRegisters); }

ABC_NAMESPACE_IMPL_START

using namespace std;

static Abc_Ntk_t * DummyFunction( Abc_Ntk_t * pNtk )
{
    Abc_Print( -1, "Please rewrite DummyFunction() in file \"icompactCommand.cc\".\n" );
    return NULL;
}

void printUnateInfo(Abc_Ntk_t *pNtk, Abc_Obj_t *pObj, vector<int>& vecPos, vector<int>& vecNeg, vector<int>& vecBi)
{
    printf("node %s:\n", Abc_ObjName(pObj));
    if(vecPos.size())
    {
        sort(vecPos.begin(), vecPos.end());
        printf("+unate inputs: ");
        for(int k=0; k<vecPos.size(); k++)
        {
            if(k!=0)
                printf(",");
            printf("%s", Abc_ObjName(Abc_NtkObj(pNtk, vecPos[k])));
        }
        printf("\n");
    }
    if(vecNeg.size())
    {
        sort(vecNeg.begin(), vecNeg.end());
        printf("-unate inputs: ");
        for(int k=0; k<vecNeg.size(); k++)
        {
            if(k!=0)
                printf(",");
            printf("%s", Abc_ObjName(Abc_NtkObj(pNtk, vecNeg[k])));
        }
        printf("\n");
    }
    if(vecBi.size())
    {
        sort(vecBi.begin(), vecBi.end());
        printf("binate inputs: ");
        for(int k=0; k<vecBi.size(); k++)
        {
            if(k!=0)
                printf(",");
            printf("%s", Abc_ObjName(Abc_NtkObj(pNtk, vecBi[k])));
        }
        printf("\n");
    }
}

static int sopunate_Command( Abc_Frame_t_ * pAbc, int argc, char ** argv )
{
    int result       = 0;
    int c            = 0;
    int fVerbose     = 0;
    
    Abc_Ntk_t *pNtk;
    Abc_Obj_t *pObj, *pFanin;
    int i, j;
    char *buff, *t;

    vector<int> vecInput, vecPcount, vecNcount, vecPos, vecNeg, vecBi;
    bool fOutput;
 
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "vh" ) ) != EOF )
    {
        switch ( c )
        {            
            case 'v':
                fVerbose ^= 1;
                break;
            case 'h':
                goto usage;
            default:
                goto usage;
        }
    }

    pNtk = Abc_FrameReadNtk(pAbc);
    if(!Abc_NtkIsSopLogic(pNtk))
    {
        printf("Error: input network is not in sop format.\n");
        return 1;
    }

    Abc_NtkForEachNode(pNtk, pObj, i)
    {
        vecInput.clear();
        vecPcount.clear();
        vecNcount.clear();
        vecPos.clear();
        vecNeg.clear();
        vecBi.clear();

        Abc_ObjForEachFanin(pObj, pFanin, j)
        {
            vecInput.push_back(Abc_ObjId(pFanin));
            vecPcount.push_back(0);
            vecNcount.push_back(0);
        }

        if(vecInput.size() == 0)
            continue;

        buff = (char*)pObj->pData;
        t = strtok(buff, "\n");
        fOutput = (t[vecInput.size()+1] == '1');
        while(true)
        {
            for(int k=0; k<vecInput.size(); k++)
            {
                if(t[k] == '1')
                    vecPcount[k]++;
                if(t[k] == '0')
                    vecNcount[k]++;
            }
            t = strtok(NULL, "\n");
            if(t == NULL)
                break;
        }

        for(int k=0; k<vecInput.size(); k++)
        {
            if(fOutput && (vecNcount[k] == 0))
                vecPos.push_back(vecInput[k]);
            if(!fOutput && (vecPcount[k] == 0))
                vecPos.push_back(vecInput[k]);
            if(fOutput && (vecPcount[k] == 0))
                vecNeg.push_back(vecInput[k]);
            if(!fOutput && (vecNcount[k] == 0))
                vecNeg.push_back(vecInput[k]);
            if((vecNcount[k]!=0) && (vecPcount[k]!=0))
                vecBi.push_back(vecInput[k]);            
        }

        printUnateInfo(pNtk, pObj, vecPos, vecNeg, vecBi);
    }
    return result;
    
usage:
    Abc_Print( -2, "usage: lsv_print_sopunate [options]\n" );
    Abc_Print( -2, "\t              prints the unate information for each node\n" );
    Abc_Print( -2, "\t-v            : verbosity [default = %d]\n", fVerbose );
    Abc_Print( -2, "\t-h            : print the command usage\n" );
    return 1;   
}

int sat_solver_addclause_from( sat_solver* pSat, Cnf_Dat_t * pCnf )
{
	for (int i = 0; i < pCnf->nClauses; i++ )
	{
		if (!sat_solver_addclause( pSat, pCnf->pClauses[i], pCnf->pClauses[i+1] ))
            return false;
	}
    return true;
}

static int pounate_Command( Abc_Frame_t_ * pAbc, int argc, char ** argv )
{
    int result       = 0;
    int c            = 0;
    int fVerbose     = 0;

    Abc_Ntk_t *pNtk;
    Abc_Obj_t *pPo;
    int l;
 
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "vh" ) ) != EOF )
    {
        switch ( c )
        {            
            case 'v':
                fVerbose ^= 1;
                break;
            case 'h':
                goto usage;
            default:
                goto usage;
        }
    }
   
    pNtk = Abc_FrameReadNtk(pAbc);

    Abc_NtkForEachPo(pNtk, pPo, l)
    {
        sat_solver *pSolver = sat_solver_new();
        int cid, vOriPo, vDupPo;
        vector<int> vecPos, vecNeg, vecBi; 

        Abc_Ntk_t *pNtkOri = Abc_NtkCreateCone(pNtk, Abc_ObjFanin0(pPo), Abc_ObjName(pPo), 0);
        bool comp = Abc_ObjFaninC0(pPo);
        Abc_Ntk_t *pNtkDup = Abc_NtkDup(pNtkOri);
        int nPi = Abc_NtkPiNum(pNtkOri);

        Vec_Int_t *pOriPi = Vec_IntAlloc(nPi);
        {
            Aig_Man_t *pAigOri = Abc_NtkToDar(pNtkOri, 0, 0);
            Cnf_Dat_t *pCnfOri = Cnf_Derive(pAigOri, Abc_NtkCoNum(pNtkOri));
            Cnf_DataLift(pCnfOri, sat_solver_nvars(pSolver));
            sat_solver_addclause_from(pSolver, pCnfOri);
            Aig_Obj_t * pAigObj = Aig_ManCo(pCnfOri->pMan, 0);
            vOriPo = pCnfOri->pVarNums[Aig_ObjId(pAigObj)];
            assert(vOriPo > 0);
            // sat_solver_print(pSolver, 1);
            // store var of pi
            for (int i = 0; i < nPi; i++)
            {
                Aig_Obj_t *pAigObjOri = Aig_ManCi(pCnfOri->pMan, i);
                int var = pCnfOri->pVarNums[Aig_ObjId(pAigObjOri)];
                // Abc_Print(1, "var of pi %d: %d\n", i, var);
                Vec_IntPush(pOriPi, var);
            }
            // memory free
            Cnf_DataFree(pCnfOri);
            Aig_ManStop(pAigOri);
        }

        Vec_Int_t *pDupPi = Vec_IntAlloc(nPi);
        {
            Aig_Man_t *pAigDup = Abc_NtkToDar(pNtkDup, 0, 0);
            Cnf_Dat_t *pCnfDup = Cnf_Derive(pAigDup, Abc_NtkCoNum(pNtkDup));
            Cnf_DataLift(pCnfDup, sat_solver_nvars(pSolver));
            sat_solver_addclause_from(pSolver, pCnfDup);
            Aig_Obj_t * pAigObj = Aig_ManCo(pCnfDup->pMan, 0);
            vDupPo = pCnfDup->pVarNums[Aig_ObjId(pAigObj)];
            assert(vDupPo > 0);
            // sat_solver_print(pSolver, 1);
            // store var of pi
            for (int i = 0; i < nPi; i++)
            {
                Aig_Obj_t *pAigObjDup = Aig_ManCi(pCnfDup->pMan, i);
                int var = pCnfDup->pVarNums[Aig_ObjId(pAigObjDup)];
                // Abc_Print(1, "var of pi %d: %d\n", i, var);
                Vec_IntPush(pDupPi, var);
            }
            // memory free
            Cnf_DataFree(pCnfDup);
            Aig_ManStop(pAigDup);
        }

        Vec_Int_t *pAlphaControls = Vec_IntAlloc(nPi);
        for (int i = 0; i < nPi; i++)
        {
            int varOri = Vec_IntEntry(pOriPi, i);
            int varDup = Vec_IntEntry(pDupPi, i);
            int varAlphaControl = sat_solver_addvar(pSolver);
            Vec_IntPush(pAlphaControls, varAlphaControl);
            cid = sat_solver_add_buffer_enable(pSolver, varOri, varDup, varAlphaControl, 0);
            assert(cid);
        }

        /////////////////////////
        // Start incremental solving
        bool posunate[nPi];
        for (int n = 0; n < nPi; n++)
        {
            int pLits[nPi+2+2]; // alpha + 2PI + 2PO
            for (int i = 0; i < nPi; i++)
            {
                if(i == n)
                    pLits[i] = Abc_Var2Lit(Vec_IntEntry(pAlphaControls, i),1);
                else
                    pLits[i] = Abc_Var2Lit(Vec_IntEntry(pAlphaControls, i),0);   
            }
            pLits[nPi] = Abc_Var2Lit(vOriPo, 1);
            pLits[nPi+1] = Abc_Var2Lit(vDupPo, 0);
            pLits[nPi+2] = Abc_Var2Lit(Vec_IntEntry(pOriPi, n),0^comp);
            pLits[nPi+3] = Abc_Var2Lit(Vec_IntEntry(pDupPi, n),1^comp);
            int status = sat_solver_solve(pSolver, pLits, pLits+nPi+4, 0, 0, 0, 0);
            posunate[n] = (status == l_False);
        }

        bool negunate[nPi];
        for (int n = 0; n < nPi; n++)
        {
            int pLits[nPi+2+2]; // alpha + 2PI + 2PO
            for (int i = 0; i < nPi; i++)
            {
                if(i == n)
                    pLits[i] = Abc_Var2Lit(Vec_IntEntry(pAlphaControls, i),1);
                else
                    pLits[i] = Abc_Var2Lit(Vec_IntEntry(pAlphaControls, i),0);   
            }
            pLits[nPi] = Abc_Var2Lit(vOriPo, 1);
            pLits[nPi+1] = Abc_Var2Lit(vDupPo, 0);
            pLits[nPi+2] = Abc_Var2Lit(Vec_IntEntry(pOriPi, n),1^comp);
            pLits[nPi+3] = Abc_Var2Lit(Vec_IntEntry(pDupPi, n),0^comp);
            int status = sat_solver_solve(pSolver, pLits, pLits+nPi+4, 0, 0, 0, 0);
            negunate[n] = (status == l_False);
        }
        
        ////////////////////////////////
        // Print 
        
        Abc_Obj_t *pPi;
        int m;
        Abc_NtkForEachPi(pNtk, pPi, m)
        {
            bool isTransFanin = 0;
            for(int i=0; i<nPi; i++)
            {
                if(strcmp(Abc_ObjName(pPi), Abc_ObjName(Abc_NtkPi(pNtkOri, i))) == 0)
                {
                    isTransFanin = 1;
                    break;
                }
            }
            if(!isTransFanin)
            {
                vecPos.push_back(Abc_ObjId(pPi));
                vecNeg.push_back(Abc_ObjId(pPi));
            }
        }
        
        for(int i=0; i<nPi; i++)
        {
            if(posunate[i])
            {
                Abc_Obj_t * pTmp = Abc_NtkFindCi(pNtk, Abc_ObjName(Abc_NtkPi(pNtkOri, i)));
                assert(pTmp != NULL);
                vecPos.push_back(Abc_ObjId(pTmp));
            } 
            if(negunate[i])
            {
                Abc_Obj_t * pTmp = Abc_NtkFindCi(pNtk, Abc_ObjName(Abc_NtkPi(pNtkOri, i)));
                assert(pTmp != NULL);
                vecNeg.push_back(Abc_ObjId(pTmp));
            }
            if(!posunate[i] && !negunate[i])
            {
                Abc_Obj_t * pTmp = Abc_NtkFindCi(pNtk, Abc_ObjName(Abc_NtkPi(pNtkOri, i)));
                assert(pTmp != NULL);
                vecBi.push_back(Abc_ObjId(pTmp));
            }
        }

        printUnateInfo(pNtk, pPo, vecPos, vecNeg, vecBi);        

        // cleanup
        sat_solver_delete(pSolver);
        Abc_NtkDelete(pNtkOri);
        Abc_NtkDelete(pNtkDup);
        Vec_IntFree(pOriPi);
        Vec_IntFree(pDupPi);
        Vec_IntFree(pAlphaControls);
    }

    return result;
    
usage:
    Abc_Print( -2, "usage: lsv_print_pounate [options]\n" );
    Abc_Print( -2, "\t              prints the unate information for each node\n" );
    Abc_Print( -2, "\t-v            : verbosity [default = %d]\n", fVerbose );
    Abc_Print( -2, "\t-h            : print the command usage\n" );
    return 1;   
}

// called during ABC startup
static void init(Abc_Frame_t* pAbc)
{ 
    Cmd_CommandAdd( pAbc, "AlCom", "lsv_print_sopunate", sopunate_Command, 1);
    Cmd_CommandAdd( pAbc, "AlCom", "lsv_print_pounate",  pounate_Command,  1);
}

// called during ABC termination
static void destroy(Abc_Frame_t* pAbc)
{
}

// this object should not be modified after the call to Abc_FrameAddInitializer
static Abc_FrameInitializer_t sopunate_frame_initializer = { init, destroy };

// register the initializer a constructor of a global object
// called before main (and ABC startup)
struct sopunate_registrar
{
    sopunate_registrar() 
    {
        Abc_FrameAddInitializer(&sopunate_frame_initializer);
    }
} sopunate_registrar_;

ABC_NAMESPACE_IMPL_END
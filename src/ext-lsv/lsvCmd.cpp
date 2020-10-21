#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <utility>
#include <vector>
#include <algorithm>
#include <string>
#include <iostream>

static int Lsv_CommandPrintNodeSopUnate(Abc_Frame_t *pAbc, int argc, char **argv);
static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t *pAbc)
{
    Cmd_CommandAdd(pAbc, "LSV", "lsv_print_sopunate", Lsv_CommandPrintNodeSopUnate, 0);
    Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
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
        // if(Abc_SopIsConst1((char *)pObj->pData)||Abc_SopIsConst0((char *)pObj->pData))
        //     continue;
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
                printf("Wrong unate information!");
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
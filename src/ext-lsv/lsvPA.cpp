#include <vector>
#include <string>
#include <algorithm>

#include "lsvPA.h"

// ABC_NAMESPACE_IMPL_START
using namespace std;

int Lsv_NtkPrintSopUnate(Abc_Ntk_t *pNtk)
{
    int i, j;
    int nFanins;
    Abc_Obj_t *pObj;
    char *pSop, *pCube;
    int type;
    char val;
    int numBinate;
    string name;

    Abc_NtkForEachNode(pNtk, pObj, i)
    {
        printf("node %s:\n", Abc_ObjName(pObj));
        nFanins = Abc_ObjFaninNum(pObj);

        vector<int> vType(nFanins, 0);

        pSop = (char *)pObj->pData;
        // check unateness
        Abc_SopForEachCube(pSop, nFanins, pCube)
        {
            numBinate = 0;
            Abc_CubeForEachVar(pCube, val, j)
            {
                type = vType[j];
                if (type == UNKNOWN)
                {
                    if (val == '0')
                        vType[j] = NEGUNATE;
                    else if (val == '1')
                        vType[j] = POSUNATE;
                }
                else if (type == POSUNATE)
                {
                    if (val == '0')
                        vType[j] = BINATE;
                }
                else if (type == NEGUNATE)
                {
                    if (val == '1')
                        vType[j] = BINATE;
                }
                else if (type == BINATE)
                {
                    numBinate++;
                }
                else
                {
                    printf("!!!Impossible state!!!\n");
                }
            }
            // early stop if all binate
            if (numBinate == nFanins)
                break;
        }

        // summarize types of fanins
        vector<string> punate, nunate, binate;
        for (j = 0; j < vType.size(); j++)
        {
            type = vType[j];
            name = Abc_ObjName(Abc_ObjFanin(pObj, j));
            if (type == POSUNATE)
                punate.push_back(name);
            else if (type == NEGUNATE)
                nunate.push_back(name);
            else if (type == BINATE)
                binate.push_back(name);
        }
        sort(punate.begin(), punate.end());
        sort(nunate.begin(), nunate.end());
        sort(binate.begin(), binate.end());

        // print results
        if (!punate.empty())
        {
            printf("+unate inputs:");
            for (j = 0; j < punate.size(); j++)
            {
                name = punate[j];
                printf(" %s", name.c_str());
            }
            printf("\n");
        }
        if (!nunate.empty())
        {
            printf("-unate inputs:");
            for (j = 0; j < nunate.size(); j++)
            {
                name = nunate[j];
                printf(" %s", name.c_str());
            }
            printf("\n");
        }
        if (!binate.empty())
        {
            printf("binate inputs:");
            for (j = 0; j < binate.size(); j++)
            {
                name = binate[j];
                printf(" %s", name.c_str());
            }
            printf("\n");
        }
    }

    return 0;
}

// ABC_NAMESPACE_IMPL_END

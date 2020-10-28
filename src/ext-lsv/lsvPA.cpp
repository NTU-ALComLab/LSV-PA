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
    int type, id;
    char val;
    int numBinate;
    Vec_Int_t *vType;
    Vec_Int_t *punate, *nunate, *binate;
    char *name;

    Abc_NtkForEachNode(pNtk, pObj, i)
    {
        nFanins = Abc_ObjFaninNum(pObj);
        if (nFanins == 0)
            continue;

        printf("node %s:\n", Abc_ObjName(pObj));

        vType = Vec_IntStart(nFanins);

        pSop = (char *)pObj->pData;
        // check unateness
        Abc_SopForEachCube(pSop, nFanins, pCube)
        {
            numBinate = 0;
            Abc_CubeForEachVar(pCube, val, j)
            {
                type = Vec_IntGetEntry(vType, j);
                if (type == UNKNOWN)
                {
                    if (val == '0')
                        Vec_IntWriteEntry(vType, j, NEGUNATE);
                    else if (val == '1')
                        Vec_IntWriteEntry(vType, j, POSUNATE);
                }
                else if (type == POSUNATE)
                {
                    if (val == '0')
                        Vec_IntWriteEntry(vType, j, BINATE);
                }
                else if (type == NEGUNATE)
                {
                    if (val == '1')
                        Vec_IntWriteEntry(vType, j, BINATE);
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

        // flip if the sop is offset
        if (Abc_SopIsComplement(pSop))
        {
            Vec_IntForEachEntry(vType, type, j)
            {
                if (type == POSUNATE)
                    Vec_IntWriteEntry(vType, j, NEGUNATE);
                else if (type == NEGUNATE)
                    Vec_IntWriteEntry(vType, j, POSUNATE);
            }
        }

        punate = Vec_IntAlloc(nFanins);
        nunate = Vec_IntAlloc(nFanins);
        binate = Vec_IntAlloc(nFanins);

        // summarize types of fanins
        Vec_IntForEachEntry(vType, type, j)
        {
            id = Abc_ObjId(Abc_ObjFanin(pObj, j));
            if (type == POSUNATE)
                Vec_IntPush(punate, id);
            else if (type == NEGUNATE)
                Vec_IntPush(nunate, id);
            else if (type == BINATE)
                Vec_IntPush(binate, id);
            else if (type == UNKNOWN)
            {
                Vec_IntPush(punate, id);
                Vec_IntPush(nunate, id);
            }
        }

        Vec_IntSort(punate, 0);
        Vec_IntSort(nunate, 0);
        Vec_IntSort(binate, 0);

        // print results
        if (Vec_IntSize(punate) != 0)
        {
            printf("+unate inputs:");
            Vec_IntForEachEntry(punate, id, j)
            {
                name = Abc_ObjName(Abc_NtkObj(pNtk, id));
                if (j == 0)
                    printf(" %s", name);
                else
                    printf(",%s", name);
            }
            printf("\n");
        }
        if (Vec_IntSize(nunate) != 0)
        {
            printf("-unate inputs:");
            Vec_IntForEachEntry(nunate, id, j)
            {
                name = Abc_ObjName(Abc_NtkObj(pNtk, id));
                if (j == 0)
                    printf(" %s", name);
                else
                    printf(",%s", name);
            }
            printf("\n");
        }
        if (Vec_IntSize(binate) != 0)
        {
            printf("binate inputs:");
            Vec_IntForEachEntry(binate, id, j)
            {
                name = Abc_ObjName(Abc_NtkObj(pNtk, id));
                if (j == 0)
                    printf(" %s", name);
                else
                    printf(",%s", name);
            }
            printf("\n");
        }

        Vec_IntFree(vType);
        Vec_IntFree(punate);
        Vec_IntFree(nunate);
        Vec_IntFree(binate);
    }

    return 0;
}

// ABC_NAMESPACE_IMPL_END

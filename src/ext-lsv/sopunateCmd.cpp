
#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <iostream>

using namespace std;
namespace
{

bool Vec_BitAll1(Vec_Bit_t * p)
{   
    int i;
    for (i = 0; i < Vec_BitSize(p); i++)
    {
        if (Vec_BitGetEntry(p, i) == 0)
            return 0;
    }
    return 1;
}

bool Vec_BitAll0(Vec_Bit_t * p)
{
    int i;
    for (i = 0; i < Vec_BitSize(p); i++)
    {
        if (Vec_BitGetEntry(p, i) == 1)
            return 0;
    }
    return 1;
}

void printUnate(Abc_Ntk_t* pNtk, Abc_Obj_t* pObj, Vec_Int_t * posUnate, Vec_Int_t * negUnate, Vec_Int_t * binate)
{
    int i;
    cout << "node " << Abc_ObjName(pObj) << ":\n";
    if (Vec_IntSize(posUnate))
    {
        cout << "+unate inputs: ";
        for (i = 0; i < Vec_IntSize(posUnate); i++)
            if (i == Vec_IntSize(posUnate) - 1)
                cout << Abc_ObjName(Abc_NtkObj(pNtk, Vec_IntGetEntry(posUnate, i)));
            else
                cout << Abc_ObjName(Abc_NtkObj(pNtk, Vec_IntGetEntry(posUnate, i))) << ",";
        cout << "\n";
    }
    if (Vec_IntSize(negUnate))
    {
        cout << "-unate inputs: ";
        for (i = 0; i < Vec_IntSize(negUnate); i++)
            if (i == Vec_IntSize(negUnate) - 1)
                cout << Abc_ObjName(Abc_NtkObj(pNtk, Vec_IntGetEntry(negUnate, i)));
            else
                cout << Abc_ObjName(Abc_NtkObj(pNtk, Vec_IntGetEntry(negUnate, i))) << ",";
        cout << "\n";
    }
    if (Vec_IntSize(binate))
    {
        cout << "binate inputs: ";
        for (i = 0; i < Vec_IntSize(binate); i++)
            if (i == Vec_IntSize(binate) - 1)
                cout << Abc_ObjName(Abc_NtkObj(pNtk, Vec_IntGetEntry(binate, i)));
            else
                cout << Abc_ObjName(Abc_NtkObj(pNtk, Vec_IntGetEntry(binate, i))) << ",";
        cout << "\n";
    }
}

void NodeUnate(Abc_Ntk_t* pNtk, Abc_Obj_t* pObj)
{
    int i;
    int FaninNum = Abc_ObjFaninNum(pObj);
    Vec_Int_t * posUnate = Vec_IntAlloc(0);
    Vec_Int_t * negUnate = Vec_IntAlloc(0);
    Vec_Int_t * binate = Vec_IntAlloc(0);
    Vec_Ptr_t * literalAppear = Vec_PtrAlloc(FaninNum);
    for (i = 0; i < FaninNum; i++)
    {
        Vec_Bit_t * tmp = Vec_BitAlloc(0);
        Vec_PtrPush(literalAppear, (void *)tmp);
    }

    // parse SOP string
    char *pCube, Value;
    char *pSop;
    pSop = (char *)Abc_ObjData(pObj);
    Abc_SopForEachCube(pSop, FaninNum, pCube) {
        Abc_CubeForEachVar(pCube, Value, i){
            if (Value == '1')
                Vec_BitPush((Vec_Bit_t *)Vec_PtrGetEntry(literalAppear, i), 1);
            else if (Value == '0')
                Vec_BitPush((Vec_Bit_t *)Vec_PtrGetEntry(literalAppear, i), 0);
        }
    }

    for (i = 0; i < FaninNum; i++)
    {
        Vec_Bit_t * p = (Vec_Bit_t *)Vec_PtrGetEntry(literalAppear, i);
        bool all1 = Vec_BitAll1(p), all0 = Vec_BitAll0(p);
        if (all1)
        {
            if (pSop[(FaninNum + 2) - 1] == '1') // onset
                Vec_IntPush(posUnate, Abc_ObjFaninId(pObj, i));
            else // offset
                Vec_IntPush(negUnate, Abc_ObjFaninId(pObj, i));
        }
        if (all0)
        {
            if (pSop[(FaninNum + 2) - 1] == '1')
                Vec_IntPush(negUnate, Abc_ObjFaninId(pObj, i));
            else
                Vec_IntPush(posUnate, Abc_ObjFaninId(pObj, i));
        }
        if (!(all1 || all0))
            Vec_IntPush(binate, Abc_ObjFaninId(pObj, i));
    }

    // sort in an increasing order w.r.t. ObjId
    Vec_IntSort(posUnate, 0);
    Vec_IntSort(negUnate, 0);
    Vec_IntSort(binate, 0);

    printUnate(pNtk, pObj, posUnate, negUnate, binate);

    /* free */
    for (i = 0; i < FaninNum; i++)
        Vec_BitFree((Vec_Bit_t *)Vec_PtrGetEntry(literalAppear, i));
    Vec_PtrFree(literalAppear);
    Vec_IntFree(posUnate);
    Vec_IntFree(negUnate);
    Vec_IntFree(binate);
}

int sopunate_Command(Abc_Frame_t *pAbc, int argc, char **argv)
{
    Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
    Abc_Obj_t* pObj;
    if (!Abc_NtkIsSopLogic(pNtk))
    {
        cout << "[error]The network should be a Boolean network whose function is expressed in SOP." << endl;
        return -1;
    }
    int i;
    Abc_NtkForEachNode(pNtk, pObj, i) {
        if (Abc_ObjFaninNum(pObj) != 0)
            NodeUnate(pNtk, pObj);
    }

    return 0;
} // namespace

// called during ABC startup
void init(Abc_Frame_t *pAbc)
{
    Cmd_CommandAdd(pAbc, "LSV", "lsv_print_sopunate", sopunate_Command, 0);
}

// called during ABC termination
void destroy(Abc_Frame_t *pAbc)
{
}

// this object should not be modified after the call to Abc_FrameAddInitializer
Abc_FrameInitializer_t frame_initializer = {init, destroy};

// register the initializer a constructor of a global object
// called before main (and ABC startup)
struct registrar
{
    registrar()
    {
        Abc_FrameAddInitializer(&frame_initializer);
    }
} sopunate_registrar;

} // unnamed namespace


#include "ext-lsv/lsv_cmd.h"

namespace lsv
{

static void print_po_unateness(Abc_Ntk_t* pNtk)
{
    int i;
    Abc_Obj_t* pPO;
    Abc_Obj_t* pPi;
    Abc_NtkForEachPo( pNtk, pPO, i )
    {
        std::cout << "node " << Abc_ObjName( pPO ) << ":" << std::endl;
    }
    Abc_NtkForEachPi( pNtk, pPi, i )
    {
        std::cout << "input " << Abc_ObjName( pPi ) << ":" << std::endl;
    }
}

static void HelpCommandPrintPOUnate()
{  
    Abc_Print(-2, "usage: lsv_print_pounate [-h]\n");
    Abc_Print(-2, "\t        report unateness for each PO\n");
    Abc_Print(-2, "\t-h    : print the command usage\n");
}

int CommandPrintPOUnate(Abc_Frame_t* pAbc, int argc, char** argv)
{
    Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    Extra_UtilGetoptReset();
    while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
        case 'h':
            HelpCommandPrintPOUnate();
            return 1;
        default:
            HelpCommandPrintPOUnate();
            return 1;
    }
    }
    if (!pNtk) {
        Abc_Print(-1, "Empty network.\n");
        return 1;
    }
    
    print_po_unateness(pNtk);
    return 0;
}

}   /// end of namespace lsv

#include "ext-lsv/lsv_cmd.h"

namespace lsv
{

static void dump_unateness( const std::vector<Unateness>& unate_vec, const std::vector<Abc_Obj_t*>& fanin_vec, Unateness unate_type )
{
    
    std::priority_queue< Abc_Obj_t*, std::vector< Abc_Obj_t* >, CompareAbcFaninPtr > sorted;
    for( int i=0; i<(int)unate_vec.size(); ++i )
    {
        if( unate_vec[i]==unate_type )
        {
            sorted.push( fanin_vec[i] );
        }
    }
    
    //
    if( !sorted.empty() )
    {
        switch( unate_type )
        {
            case POS_UNATE :
                std::cout << "+unate inputs: ";
                break;
            case NEG_UNATE :
                std::cout << "-unate inputs: ";
                break;
            case BINATE :
                std::cout << "binate inputs: ";
                break;
            default:
                std::cout << "non-unate inputs: ";
                break;
        }
        
        while( !sorted.empty() )
        {
            auto* pObj = sorted.top();
            sorted.pop();
            std::cout << Abc_ObjName( pObj );
            if( !sorted.empty() ) std::cout << ",";
        }
        std::cout << std::endl;
    }
    
}

static void compute_unateness( char* pData, int nFanins, std::vector<Unateness>* unate_vec )
{
    unate_vec->resize( nFanins );
    for( auto& u : *unate_vec ) u = NONE;
        
    bool isMaxterm = false;
    while( *pData )
    {
        int varIdx = 0;
        /// read a cube
        while( *pData!='\0' && *pData!='\n' )
        {
            if( varIdx < nFanins )
            {
                if( *pData == '0' ) (*unate_vec)[varIdx] += NEG_UNATE;
                if( *pData == '1' ) (*unate_vec)[varIdx] += POS_UNATE;
                ++varIdx;
            }
            else
            {
                if( *pData == '0' ) isMaxterm = true;
                if( *pData == '1' ) isMaxterm = false;
            }
            ++pData;
        }
        ++pData;
    }
    
    /// if SOP is defiend by 0 outputs
    if( isMaxterm )
    {
        for( auto& u : *unate_vec ) u = !u;
    }
}

static void print_sop_unateness(Abc_Ntk_t* pNtk)
{
    Abc_Obj_t* pObj;
    int i;
    std::vector<Unateness> unate_vec;
    std::vector<Abc_Obj_t*> fanin_vec( 8, nullptr );
    
    Abc_NtkForEachNode(pNtk, pObj, i)
    {
        int nFanins;
        Abc_Obj_t* pFanin;
        Abc_ObjForEachFanin(pObj, pFanin, nFanins)
        {
            if( nFanins > fanin_vec.size() )
            {
                fanin_vec.resize( nFanins );
            }
            fanin_vec[nFanins] = pFanin;
        }
        
        if( nFanins==0 ) continue;
        if( Abc_NtkHasSop(pNtk) )
        {
            /// SOP (pData) is just a string
            char* pData = (char*)pObj->pData;
            compute_unateness( pData, nFanins, &unate_vec );
            std::cout << "node " << Abc_ObjName( pObj ) << ":" << std::endl;
            dump_unateness( unate_vec, fanin_vec, POS_UNATE );
            dump_unateness( unate_vec, fanin_vec, NEG_UNATE );
            dump_unateness( unate_vec, fanin_vec, BINATE );
        }
    }
}

static void HelpCommandPrintSOPUnate()
{  
    Abc_Print(-2, "usage: lsv_print_sopunate [-h]\n");
    Abc_Print(-2, "\t        report SOP unateness for each node\n");
    Abc_Print(-2, "\t-h    : print the command usage\n");
}

int CommandPrintSOPUnate(Abc_Frame_t* pAbc, int argc, char** argv)
{
    Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    Extra_UtilGetoptReset();
    while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
        case 'h':
            HelpCommandPrintSOPUnate();
            return 1;
        default:
            HelpCommandPrintSOPUnate();
            return 1;
    }
    }
    if (!pNtk) {
        Abc_Print(-1, "Empty network.\n");
        return 1;
    }
    
    print_sop_unateness(pNtk);
    return 0;
}

}   /// end of namespace lsv
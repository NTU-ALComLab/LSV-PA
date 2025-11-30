#include "lsv.h"

void Lsv_Init(Abc_Frame_t * pAbc)
{
    Cmd_CommandAdd(pAbc, "LSV", "lsv_unate_bdd", Lsv_CommandUnateBdd, 0);
    
}


void Lsv_End(Abc_Frame_t * pAbc)
{
    
}
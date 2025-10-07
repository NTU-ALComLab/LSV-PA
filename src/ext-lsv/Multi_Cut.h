#pragma once
// input : lsv_printmocut k l
extern "C"{
    #include "base/abc/abc.h"
    #include "base/main/main.h"
    #include "base/main/mainInt.h"
}

#ifdef __cplusplus
extern "C"
{
#endif

int Abc_CommandLsvPrintMoCut(Abc_Frame_t *pAbc, int argc, char **argv);
#ifdef __cplusplus
}
#endif

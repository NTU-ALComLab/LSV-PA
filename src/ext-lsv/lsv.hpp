#ifndef LSV_HPP
#define LSV_HPP

#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <vector>
#include <iostream>
#include <map>
#include "sat/cnf/cnf.h"
#include "sat/bsat/satSolver2.h"
#include "proof/fra/fra.h"

using namespace std;

int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
int Lsv_CommandPrintSopunate(Abc_Frame_t* pAbc, int argc, char** argv);
int Lsv_CommandPrintPounate(Abc_Frame_t* pAbc, int argc, char** argv);
void Lsv_NtkPrintNodes(Abc_Ntk_t* pNtk);
void Lsv_NtkPrintSopunate(Abc_Ntk_t* pNtk);
void Lsv_NtkPrintPounate(Abc_Ntk_t* pNtk1, Abc_Ntk_t* pNtk2);
Abc_Ntk_t* Lsv_constructCircuit(Abc_Ntk_t* pNtk1, Abc_Ntk_t* pNtk2);
Abc_Ntk_t * Lsv_NtkMiterInt( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int fComb, int nPartSize, int fImplic, int fMulti );
void Lsv_NtkMiterFinalize( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, Abc_Ntk_t * pNtkMiter, int fComb, int nPartSize, int fImplic, int fMulti );
Abc_Obj_t * Lsv_AigMiter( Abc_Aig_t * pMan, Vec_Ptr_t * vPairs, int fImplic );
Abc_Obj_t * Lsv_AigMiter_rec( Abc_Aig_t * pMan, Abc_Obj_t ** ppObjs, int nObjs );

#endif
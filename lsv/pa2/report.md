# LSV-PA2: Unateness checking of global PI/PO

- [Implementation](#Implementation)
- [Experiments](#Experiments)
- [Questions](#Questions)
- [Future Works](#Future-Works)

## Implementation
The SAT-based implementation derives the fanin cone of each PO and checks the unateness of each PI with respect to that PO. By doing this, the SAT solver does not need to consider the clauses that encode the relations of logic gates outside the fanin cone, which improves the efficiency. The following code snippet describes the algorithm.

```cpp
Abc_NtkForEachPo( pNtk, pPo, i ) {

    // create fanin cone, CNFs, and SAT solver
    pNtkCone = Abc_NtkCreateCone( pNtk, Abc_ObjFanin0(pPo), Abc_ObjName(pPo), 1 );
    pMan = Abc_NtkToDar( pNtkCone, 0, 0 );
    Cnf_Dat_t * pCnf0 = Cnf_Derive( pMan, Aig_ManCoNum(pMan) );
    Cnf_Dat_t * pCnf1 = Cnf_DataDup( pCnf0 );
    Cnf_DataLift( pCnf1, pCnf0->nVars );
    sat_solver * pSat = (sat_solver *)Cnf_DataWriteIntoSolver( pCnf0, 1, 0 );
    Cnf_DataWriteIntoSolverInt( pSat, pCnf1, 1, 0 );
    
    ...
```

For each PO, we first create the fanin cone of it. We use `Abc_NtkCreateCone` with the last argument as `1`, which let us include __all PIs__ rather than only the supports of this PO. We have to include all PIs to ensure that the IDs are the same as the original circuit.

Next, we create the Aig manager `pMan` with `AbcNtkToDar`, and generate the CNF of the cone using `Cnf_Derive`. To get a copy of the CNF and avoid conflict of variables, we use `Cnf_DataDup` and lift the variables by the number of variables of the original CNF (`pCnf0->nVars`) using `Cnf_DataLift`. To write the CNF into a SAT solver (`pSat`), we first use `Cnf_DataWriteIntoSolver` to write the original CNF (`pCnf0`), and use `Cnf_DataWriteIntoSolverInt` to write the lifted CNF (`pCnf1`) into the `pSat`.

Now, the SAT solver `pSat` contains the formulas of two identical circuits of the fanin cone of the current PO. Below, we add clauses to enforce the equivalence of the PIs of the two circuits.

```cpp
    ...
    
    // add equivalence clauses
    int PiNum = Abc_NtkPiNum( pNtk );
    int enableStart = pSat->size;
    sat_solver_setnvars( pSat, enableStart + PiNum );
    Abc_NtkForEachPi( pNtkCone, pPi, j ) {
      int PiID = Aig_ObjId( (Aig_Obj_t *)pPi->pCopy );
      int PiVar0 = pCnf0->pVarNums[ PiID ];
      int PiVar1 = pCnf1->pVarNums[ PiID ];
      int enableVar = enableStart + j;
      sat_solver_add_buffer_enable( pSat, PiVar0, PiVar1, enableVar, 0 );
    }
      
    ...
```

Since there are `PiNum` PIs, we allocate `PiNum` enabling variables using `sat_solver_setnvars`. For each PI, we use `sat_solver_add_buffer_enable` to encode the equivalence relation as a clause and add it into `pSat`. To obtain the corresponding variable of a PI, we take advantage of the `Id` stored in `Aig_Obj_t` that is accessed through `pCopy`. The corresponding variable can then be obtained as the `Id`th entry of `pVarNums`.
We next set the assumptions.
```cpp
    ...
    
    // set assumptions
    int assumpNum = PiNum + 4;
    int Pi0 = PiNum  , Pi1 = PiNum+1;
    int Po0 = PiNum+2, Po1 = PiNum+3;
    lit assump[assumpNum];
    // enable all equivalence clauses
    for (j = 0; j < PiNum; ++j)
      assump[j] = toLitCond( enableStart + j, 0 );
    
    ...
```

The number of total assumption literals is `PiNum + 4`, including `PiNum` enabling literals, `2` PI literals, and `2` PO literals. When finding the unateness of a PI, we have to fix the value of the corresponding PIs in both circuits to `0` and `1`. We enable all such clauses here and later disable the considering clause when solving. Below, we describe the solving process.

```cpp
    ...
    
    Abc_Obj_t * pConePo = Abc_NtkPo( pNtkCone, 0 );
    int PoID = Aig_ObjId( (Aig_Obj_t *)Abc_ObjFanin0(pConePo)->pCopy );
    Abc_NtkForEachPi( pNtkCone, pPi, j ) {
      // if Pi is not in cone
      if ( !Abc_NodeIsTravIdCurrent( pPi ) ) {
        Vec_PtrPush( posUnateVec, pPi );
        Vec_PtrPush( negUnateVec, pPi );
        continue;
      }

      assump[j] = lit_neg( assump[j] );
      int PiID = Aig_ObjId( (Aig_Obj_t *)pPi->pCopy );
      bool isBinate = true;

      // assign Pi0 = 0, Pi1 = 1
      assump[Pi0] = toLitCond( pCnf0->pVarNums[ PiID ], 1 );
      assump[Pi1] = toLitCond( pCnf1->pVarNums[ PiID ], 0 );

      // check negative unate: assign Po0 = 0, Po1 = 1
      assump[Po0] = toLitCond( pCnf0->pVarNums[ PoID ], 1 );
      assump[Po1] = toLitCond( pCnf1->pVarNums[ PoID ], 0 );
      if (sat_solver_simplify( pSat ) == l_False ||
          sat_solver_solve( pSat, assump, assump + assumpNum, 0, 0, 0, 0 ) == l_False) {
        isBinate = false;
        Vec_PtrPush( negUnateVec, pPi );
      }
      
      // check positive unate: assign Po0 = 1, Po1 = 0
      assump[Po0] = lit_neg( assump[Po0] );
      assump[Po1] = lit_neg( assump[Po1] );
      if (sat_solver_simplify( pSat ) == l_False ||
          sat_solver_solve( pSat, assump, assump + assumpNum, 0, 0, 0, 0 ) == l_False) {
        isBinate = false;
        Vec_PtrPush( posUnateVec, pPi );
      }

      if (isBinate) Vec_PtrPush( binateVec, pPi );
 
      assump[j] = lit_neg( assump[j] );
    }
    
    ...
    // output unate, binate inputs
```

For each PI, we check respectively whether it is negative unate or positive unate with respect to the PO. To check the unateness of a PI, we disable the equivalence-relation clause related to the PI and leave the others enabled. 

We first assign `0` and `1` to the PI of the first and second circuit respectively. To check whether a PI is negative (positive) unate, we further assign `0` (`1`) and `1` (`0`) to the PO of the first and second circuit, and invoke the SAT solver with the assumptions. If it returns UNSAT, the PI is negative (positive) unate to the PO. If the PI is not positive or negative unate, it is considered binate.

Note that PIs not in the cone does not affect the value of the PO. Thus, it is both positive and negative unate to the PO, and can be skipped to improve the efficiency. Since `Abc_NtkCreateCone` updates the traversal ID of each traversed objects, by checking the traversal ID, we can efficiently distinguish whether a PI is in the fanin cone of the PO. This is done in line 7 to 11 in the above code. This technique helped solve 2 more cases among the 13 cases.

## Experiments

The experiments were run on a Intel(R) Core(TM) i7-8700 CPU at 3.20GHz. The time limit is set to 600 seconds.
| Benchmark     | `print_unate` | `lsv_print_pounate(mine)` | `lsv_print_pounate(ref)` |
| ------------- | -------------:| -------------------------:| ------------------------:|
| arbiter.aig   |          3.76 |                      4.34 |                     4.28 |
| cavlc.aig     |          0.01 |                      0.03 |                     0.03 |
| ctrl.aig      |          0.02 |                      0.03 |                     0.02 |
| dec.aig       |          0.02 |                      0.07 |                     0.08 |
| i2c.aig       |          0.04 |                      0.08 |                     0.09 |
| int2float.aig |          0.02 |                      0.02 |                     0.03 |
| mem_ctrl.aig  |         13.11 |                     106.5 |                   121.21 |
| priority.aig  |          0.04 |                      0.12 |                     0.09 |
| router.aig    |          0.02 |                      0.03 |                     0.04 |
| adder.aig     |          0.16 |                      2.40 |                     2.61 |
| bar.aig       |         13.72 |                      2.18 |                     2.19 |
| max.aig       |            TO |                      47.5 |                    47.09 |
| sin.aig       |            TO |                     10.83 |                    10.82 |


## Questions

- Can your implementation solve the remaining 7 test cases (possibly with a longer time limit)?
    - The implementation cannot solve the 7 cases within 300s and 600s. 
- How does your implementation compare to the BDD-based command `print_unate` in ABC?
    - See [Experiments](#Experiments) for comparison. `print_unate` tend to be faster on simpler cases, but fails to give answer on harder cases, such as arithmetic circuits.
- What are the differences between random control and arithmetic circuits? Which category is more challenging?
    - Considering the experiments and the remaining 7 test cases, arithmetic circuits seems to be more challenging than random control circuits.

## Future Works
For future works, circuit simulation could be added before SAT solving to quickly detect non-unateness of inputs. 


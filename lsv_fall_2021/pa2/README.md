## Programming Assignment 2 

### Submission Guidelines
Please send a pull request to the branch named with your student ID during the submission periods: 2021/12/24 11:00-13:00.  
Please develop your code under `src/ext-lsv`. (For those who develop your PA1 in `ext_<your_student_ID>`, please move your code to `src/ext-lsv` and remove `ext_<your_student_ID>`.

### OR Bi-Decomposition of Functions
Write a procedure in ABC that decides whether each circuit PO `f(X)` is OR bi-decomposable. 
Integrate this procedure into ABC, so that after reading in a circuit by the command `read`, running the command `lsv_or_bidec` would invoke your code.
A function `f(X)` is OR bi-decomposable under a variable partition of its support `X = { XA | XB | XC }` if `f` can be written as `f(X)=fA(XA,XC)+fB(XB,XC)`. Your goal is to find a non-trivial variable partition such that `f` is OR bi-decomposable under this variable partition. 
You can refer to [README.pdf](./README.pdf) or [the paper](https://ieeexplore.ieee.org/document/4555896) for further details. 

The format of your printing message is as follows.
```
PO <po1-name> support partition: 1
210200001101
PO <po2-name> support partition: 0
PO <po3-name> support partition: 1
212111000
```
Print lines of `PO <po-name>...` according to the order of `Abc_NtkForEachPo()`.
For each PO, use `Abc_NtkCreateCone()` to extract the cone of the PO and its support set. 
In each line of `PO <po-name> support partition:`, print the names  of POs  returned  by  function `Abc_ObjName()`. Print  `0`  after  `support partition:` if there is no valid non-trivial partition; 
print `1` if there is a valid non-trivial partition, and print the partition you find in the next line.

We use an integer string to represent the variable partition. 
Let `0` represents `x ∈ XC`,  `1`  represents `x ∈ XB`,  `2`  represents `x ∈ XA`.  
For  example,  the  string `212111000` indicates that the first support variable is in `XA`, the second in `XB`,the third in `XA`, . . . , the last in `XC`.


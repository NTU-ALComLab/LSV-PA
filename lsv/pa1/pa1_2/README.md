# LSV pa1-2

## problem (a)

1. logic network in AIG (by command `aig`) vs. structurally hashed AIG (by command strash)

    * logic network in AIG by `aig` is still a logic network, instead every node is represented by an local AIG,
    on the other hand, structurally hashed AIG by command `strash` is a global AIG representing the whole function.

    * With the 4 bit full adder example, using the command `print_stats`, we can see that we still have 8 node
    for the logic network in AIG representing the logic network node, and a level of 4. In the contrary, we only
    have and gate in the structurally hashed AIG but with 13 levels.

2. logic network in bdd (by command `bdd`) vs. collapsed BDD (by command collapse)

    - Similar to the previous comparison, logic network in bdd is a logic network with every node represented by
    a local BDD, and collapsed BDD is a global BDD representing the whole function.

    - Similarly, we use the command `print_stats` the see the difference. We have 5 nodes instead of 8 nodes and
    1 level instead of 4 level comparing logic network in BDD vs collapsed BDD.

## problem (b)

- We can use only the command `logic` to convert structurally hashed AIG to a logic network with node function
expressed in SOP.

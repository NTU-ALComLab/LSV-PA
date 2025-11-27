module test (
    x, y, z, w1, w2
);
    input x;
    input y;
    input z;
    output w1, w2;
    wire tmp1;
    wire tmp2;
    assign tmp1 = x ^ y;
    assign w1 = !(tmp1 ^ z);

    assign tmp2 = x & ~y;
    assign w2 = tmp2 | z;
endmodule
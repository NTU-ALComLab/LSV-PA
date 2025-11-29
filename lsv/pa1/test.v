module test (
    x, y, z, w
);
    input x;
    input y;
    input z;
    output w;
    wire tmp1;
    // wire tmp2;
    assign tmp1 = x ^ y;
    assign w = tmp1 | z;
endmodule
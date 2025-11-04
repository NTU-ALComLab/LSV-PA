module alu_ref (input a1, a0, b1, b0, c, output [2:0] y);
  wire [1:0] A = {a1,a0};
  wire [1:0] B = {b1,b0};
  assign y = (c==0) ? (A+B) : (A-B);
endmodule

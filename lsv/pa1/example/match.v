// Benchmark "./lsv/pa1/example" written by ABC on Sun Oct 19 16:12:43 2025

module \./lsv/pa1/example  ( 
    pi0, pi1, pi2,
    po0, po1, po2, po3  );
  input  pi0, pi1, pi2;
  output po0, po1, po2, po3;
  wire new_n8, new_n9, new_n13;
  INVx1_ASAP7_75t_R         g0(.A(pi0), .Y(new_n8));
  INVx1_ASAP7_75t_R         g1(.A(pi1), .Y(new_n9));
  NOR2xp33_ASAP7_75t_R      g2(.A(new_n8), .B(new_n9), .Y(po0));
  NOR2xp33_ASAP7_75t_R      g3(.A(pi1), .B(new_n8), .Y(po1));
  NOR3xp33_ASAP7_75t_R      g4(.A(new_n9), .B(pi0), .C(pi2), .Y(po2));
  INVx1_ASAP7_75t_R         g5(.A(pi2), .Y(new_n13));
  NOR3xp33_ASAP7_75t_R      g6(.A(new_n9), .B(new_n13), .C(pi0), .Y(po3));
endmodule

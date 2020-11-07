`include "defines.v"

module assertions(
// INPUTS
input logic clk, rst, freeze, brTaken,
input logic [`FORW_SEL_LEN-1:0] brOffset,
// OUTPUTS
input logic [`WORD_LEN-1:0] instruction, PC);

default clocking c0 @(posedge clk); endclocking;
default disable iff (rst);

test_prop: cover property ( brTaken ##1 !brTaken);



endmodule
		

`include "defines.v"

module assertions(
input logic clk,
input logic [`EXE_CMD_LEN-1:0] EXE_CMD,
input logic [`FORW_SEL_LEN-1:0] val1_sel, val2_sel, ST_val_sel,
input logic [`WORD_LEN-1:0] val1, val2, ALU_res_MEM, result_WB, ST_value_in, ALUResult, ST_value_out
);

default clocking c0 @(posedge clk); endclocking;

add_cover: cover property ( EXE_CMD inside {`EXE_ADD, `EXE_SUB, `EXE_AND, `EXE_OR, `EXE_NOR, `EXE_XOR, `EXE_SLA, `EXE_SLL, `EXE_SRA, `EXE_SRL });



endmodule
		

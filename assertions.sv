`include "defines.v"

`define FPV_ARITH_OPS {`OP_ADD, `OP_SUB, `OP_SLA, `OP_SRA}
`define FPV_ARITHIMM_OPS {`OP_ADDI, `OP_SUBI}
`define FPV_LOG_OPS {`OP_AND, `OP_OR, `OP_NOR, `OP_XOR, `OP_SLL, `OP_SRL}
`define FPV_MEM_OPS {`OP_LD, `OP_ST}
`define FPV_BR_OPS {`OP_BEZ, `OP_BNE, `OP_JMP}
`define FPV_OTHER_OPS {`OP_NOP}

`define FPV_TEST_OPS {`OP_ADD, `OP_SUB, `OP_SLA, `OP_SRA, `OP_ADDI, `OP_SUBI, `OP_AND, `OP_OR, `OP_NOR, `OP_XOR, `OP_SLL, `OP_SRL, `OP_LD, `OP_ST}

`define FPV_EXE_CMD {`EXE_ADD, `EXE_SUB, `EXE_AND, `EXE_OR, `EXE_NOR, `EXE_XOR, `EXE_SLA, `EXE_SLL, `EXE_SRA, `EXE_SRL, `EXE_NO_OPERATION}

/*
module assertions(
input logic clk,
input logic [`EXE_CMD_LEN-1:0] EXE_CMD,
input logic [`FORW_SEL_LEN-1:0] val1_sel, val2_sel, ST_val_sel,
input logic [`WORD_LEN-1:0] val1, val2, ALU_res_MEM, result_WB, ST_value_in, ALUResult, ST_value_out
);

default clocking c0 @(posedge clk); endclocking;

add_cover: cover property ( EXE_CMD inside {`EXE_ADD, `EXE_SUB, `EXE_AND, `EXE_OR, `EXE_NOR, `EXE_XOR, `EXE_SLA, `EXE_SLL, `EXE_SRA, `EXE_SRL });



endmodule
*/

module fpv_controller(opCode, branchEn, EXE_CMD, Branch_command, Is_Imm, ST_or_BNE, WB_EN, MEM_R_EN, MEM_W_EN, hazard_detected, clk);

  input logic clk;
  input logic hazard_detected;
  input logic [`OP_CODE_LEN-1:0] opCode;
  input logic branchEn;
  input logic [`EXE_CMD_LEN-1:0] EXE_CMD;
  input logic [1:0] Branch_command;
  input logic Is_Imm, ST_or_BNE, WB_EN, MEM_R_EN, MEM_W_EN;

default clocking c0 @(posedge clk); endclocking;

// Cover that the operations under test when provided to the CU, generates one of the control signals

CU_cover: cover property ( (opCode inside `FPV_TEST_OPS && hazard_detected == 1'b0) ##1 (EXE_CMD inside `FPV_EXE_CMD) && (Is_Imm || WB_EN || MEM_R_EN || MEM_W_EN) );

// Cover ADD then ADDI operations to look at the waveforms
CU_cover_add: cover property (opCode == `OP_ADD && hazard_detected == 1'b0);
CU_cover_addi: cover property (opCode == `OP_ADDI && hazard_detected == 1'b0);

// Cover ADD, ADDI, AND, LD & ST back to back to look at waveforms
CU_cover_add_addi_and_ld_st: cover property (opCode == `OP_ADD && hazard_detected == 1'b0 ##1 opCode == `OP_ADDI && hazard_detected == 1'b0 ##1 opCode == `OP_AND && hazard_detected == 1'b0 ##1 opCode == `OP_LD && hazard_detected == 1'b0 ##1 opCode == `OP_ST && hazard_detected == 1'b0 );

// Cover ADD with hazard detected
CU_cover_add_hazard_add: cover property ( (opCode == `OP_ADD && hazard_detected == 1'b0) ##1 (opCode == `OP_ADD && hazard_detected == 1'b1) ##1 (opCode == `OP_ADD && hazard_detected == 1'b0) );

// Cover hazard detection

//CU_cover_hazard_detected: cover property ( hazard_detected == 1'b1 );

// Assume only those operations which are under test

CU_assume_ops: assume property (opCode inside `FPV_TEST_OPS);


// Assert arithemtic operations generating correct control signals

CU_add_assert: assert property ((opCode == `OP_ADD && hazard_detected == 1'b0) |=> (EXE_CMD == `EXE_ADD) && !Is_Imm && WB_EN && !MEM_R_EN && !MEM_W_EN);
CU_sub_assert: assert property ((opCode == `OP_SUB && hazard_detected == 1'b0) |=> (EXE_CMD == `EXE_SUB) && !Is_Imm && WB_EN && !MEM_R_EN && !MEM_W_EN);
CU_sla_assert: assert property ((opCode == `OP_SLA && hazard_detected == 1'b0) |=> (EXE_CMD == `EXE_SLA) && !Is_Imm && WB_EN && !MEM_R_EN && !MEM_W_EN);
CU_sra_assert: assert property ((opCode == `OP_SRA && hazard_detected == 1'b0) |=> (EXE_CMD == `EXE_SRA) && !Is_Imm && WB_EN && !MEM_R_EN && !MEM_W_EN);

// Assert logical operations generating correct control signals

CU_and_assert: assert property ((opCode == `OP_AND && hazard_detected == 1'b0) |=> (EXE_CMD == `EXE_AND) && !Is_Imm && WB_EN && !MEM_R_EN && !MEM_W_EN);
CU_or_assert: assert property ((opCode == `OP_OR && hazard_detected == 1'b0) |=> (EXE_CMD == `EXE_OR) && !Is_Imm && WB_EN && !MEM_R_EN && !MEM_W_EN);
CU_nor_assert: assert property ((opCode == `OP_NOR && hazard_detected == 1'b0) |=> (EXE_CMD == `EXE_NOR) && !Is_Imm && WB_EN && !MEM_R_EN && !MEM_W_EN);
CU_xor_assert: assert property ((opCode == `OP_XOR && hazard_detected == 1'b0) |=> (EXE_CMD == `EXE_XOR) && !Is_Imm && WB_EN && !MEM_R_EN && !MEM_W_EN);
CU_sll_assert: assert property ((opCode == `OP_SLL && hazard_detected == 1'b0) |=> (EXE_CMD == `EXE_SLL) && !Is_Imm && WB_EN && !MEM_R_EN && !MEM_W_EN);
CU_srl_assert: assert property ((opCode == `OP_SRL && hazard_detected == 1'b0) |=> (EXE_CMD == `EXE_SRL) && !Is_Imm && WB_EN && !MEM_R_EN && !MEM_W_EN);

// Assert arithmetic immediate operations generating correct control signals

CU_addi_assert: assert property ((opCode == `OP_ADDI && hazard_detected == 1'b0) |=> (EXE_CMD == `EXE_ADD) && Is_Imm && WB_EN && !MEM_R_EN && !MEM_W_EN);
CU_subi_assert: assert property ((opCode == `OP_SUBI && hazard_detected == 1'b0) |=> (EXE_CMD == `EXE_SUB) && Is_Imm && WB_EN && !MEM_R_EN && !MEM_W_EN);

// Assert memory operations generating correct control signals

CU_ld_assert: assert property ((opCode == `OP_LD && hazard_detected == 1'b0) |=> (EXE_CMD == `EXE_ADD) && Is_Imm && WB_EN && MEM_R_EN && !MEM_W_EN);
CU_st_assert: assert property ((opCode == `OP_ST && hazard_detected == 1'b0) |=> (EXE_CMD == `EXE_ADD) && Is_Imm && !WB_EN && !MEM_R_EN && MEM_W_EN);

// Assert that no writing can be done when hazard is detected

CU_hazard_detected: assert property ( ##1 (hazard_detected == 1'b1) |=> (EXE_CMD == `EXE_NO_OPERATION) && !WB_EN && !MEM_W_EN);

endmodule

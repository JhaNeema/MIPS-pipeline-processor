`include "defines.v"

`define FPV_ARITH_OPS {`OP_ADD, `OP_SUB, `OP_SLA, `OP_SRA}
`define FPV_ARITHIMM_OPS {`OP_ADDI, `OP_SUBI}
`define FPV_LOG_OPS {`OP_AND, `OP_OR, `OP_NOR, `OP_XOR, `OP_SLL, `OP_SRL}
`define FPV_MEM_OPS {`OP_LD, `OP_ST}
`define FPV_BR_OPS {`OP_BEZ, `OP_BNE, `OP_JMP}
`define FPV_OTHER_OPS {`OP_NOP}

`define FPV_TEST_OPS {`OP_ADD, `OP_SUB, `OP_SLA, `OP_SRA, `OP_ADDI, `OP_SUBI, `OP_AND, `OP_OR, `OP_NOR, `OP_XOR, `OP_SLL, `OP_SRL, `OP_LD, `OP_ST}

`define FPV_EXE_CMD {`EXE_ADD, `EXE_SUB, `EXE_AND, `EXE_OR, `EXE_NOR, `EXE_XOR, `EXE_SLA, `EXE_SLL, `EXE_SRA, `EXE_SRL, `EXE_NO_OPERATION}


module fpv_exememstage(clk, rst, EXE_CMD_EXE, val1_sel, val2_sel, ST_val_sel, val1_EXE, val2_EXE, WB_result, ST_value_EXE, PC_EXE, dest_EXE, MEM_R_EN_EXE, MEM_W_EN_EXE, WB_EN_EXE, PC_MEM, dataMem_out_MEM, dest_MEM, WB_EN_MEM, ALURes_MEM, ALURes_EXE, ST_value_EXE2MEM, ST_value_MEM, MEM_R_EN_MEM, MEM_W_EN_MEM);

	input clk;
	input rst;
	input [`EXE_CMD_LEN-1:0] EXE_CMD_EXE;
	input [`FORW_SEL_LEN-1:0] val1_sel;
	input [`FORW_SEL_LEN-1:0] val2_sel;
	input [`FORW_SEL_LEN-1:0] ST_val_sel;
	input [`WORD_LEN-1:0] val1_EXE;
	input [`WORD_LEN-1:0] val2_EXE;
	input [`WORD_LEN-1:0] WB_result;
	input [`WORD_LEN-1:0] ST_value_EXE;
	input [`WORD_LEN-1:0] PC_EXE;
	input [`REG_FILE_ADDR_LEN-1:0] dest_EXE;
	input MEM_R_EN_EXE;
	input MEM_W_EN_EXE;
	input WB_EN_EXE;
	input [`WORD_LEN-1:0] ALURes_MEM;
	input [`WORD_LEN-1:0] ALURes_EXE;
	input [`WORD_LEN-1:0] ST_value_EXE2MEM;
	input [`WORD_LEN-1:0] ST_value_MEM;
	input MEM_R_EN_MEM;
	input MEM_W_EN_MEM;
	input [`WORD_LEN-1:0] PC_MEM;
	input [`WORD_LEN-1:0] dataMem_out_MEM;
	input [`REG_FILE_ADDR_LEN-1:0] dest_MEM;
	input WB_EN_MEM;
	
	default clocking c0 @(posedge clk); endclocking;
	default disable iff (rst);
	
	property opexemem(opcode, opres);
		logic [`WORD_LEN-1:0] alures; 
		((EXE_CMD_EXE == opcode) && (val1_sel == 0) && (val2_sel == 0), alures = opres) |=> ALURes_MEM == alures;
	endproperty
	
	add_cover: cover property ( EXE_CMD_EXE inside `FPV_TEST_OPS);
	
	add_assert: assert property ( opexemem(`EXE_ADD, (val1_EXE + val2_EXE)) );
	and_assert: assert property ( opexemem(`EXE_AND, (val1_EXE & val2_EXE))  );

endmodule


module fpv_exestage(
	input logic clk,
	input logic [`EXE_CMD_LEN-1:0] EXE_CMD,
	input logic [`FORW_SEL_LEN-1:0] val1_sel, val2_sel, ST_val_sel,
	input logic [`WORD_LEN-1:0] val1, val2, ALU_res_MEM, result_WB, ST_value_in, ALUResult, ST_value_out
);

	default clocking c0 @(posedge clk); endclocking;

	add_cover: cover property ( EXE_CMD inside `FPV_TEST_OPS );
	
	add_assert: assert property ( (EXE_CMD == `EXE_ADD) && (val1_sel == 0) && (val2_sel == 0)  |-> ALUResult == (val1 + val2));
	and_assert: assert property ( (EXE_CMD == `EXE_AND) && (val1_sel == 0) && (val2_sel == 0)  |-> ALUResult == (val1 & val2));

endmodule


module fpv_hazard(forward_EN, is_imm, ST_or_BNE, src1_ID, src2_ID, dest_EXE, WB_EN_EXE, dest_MEM, WB_EN_MEM, MEM_R_EN_EXE, branch_comm, hazard_detected);
	input logic [`REG_FILE_ADDR_LEN-1:0] src1_ID, src2_ID;
	input logic [`REG_FILE_ADDR_LEN-1:0] dest_EXE, dest_MEM;
	input logic [1:0] branch_comm;
	input logic forward_EN, WB_EN_EXE, WB_EN_MEM, is_imm, ST_or_BNE, MEM_R_EN_EXE;
	input logic hazard_detected;
	
	logic clk;
	
	default clocking c0 @(posedge clk); endclocking;
	  
	// Booleans constructs
	let RAW_src1_IDEXE = (src1_ID == dest_EXE) && WB_EN_EXE;
	let RAW_src2valid_IDEXE = (src2_ID == dest_EXE) && ((~is_imm) || ST_or_BNE) && WB_EN_EXE;
	
	let RAW_src1_IDMEM = (src1_ID == dest_MEM) && WB_EN_MEM;
	let RAW_src2valid_IDMEM = (src2_ID == dest_MEM) && ((~is_imm) || ST_or_BNE) && WB_EN_MEM;
	
	let RAW = RAW_src1_IDEXE || RAW_src2valid_IDEXE || RAW_src1_IDMEM || RAW_src2valid_IDMEM;
	let noRAW = !RAW_src1_IDEXE && !RAW_src2valid_IDEXE && !RAW_src1_IDMEM && !RAW_src2valid_IDMEM;
	
	// Cover different types of RAW hazard waveforms
	HDU_noRAW_RAW_src1_IDEXE_noRAW: cover property (noRAW ##1 RAW_src1_IDEXE ##1 noRAW);
	HDU_noRAW_RAW_src2valid_IDEXE_noRAW: cover property (noRAW ##1 RAW_src2valid_IDEXE ##1 noRAW);
	HDU_noRAW_RAW_src1_IDMEM_noRAW: cover property (noRAW ##1 RAW_src1_IDMEM ##1 noRAW);
	HDU_noRAW_RAW_src2valid_IDMEM_noRAW: cover property (noRAW ##1 RAW_src2valid_IDMEM ##1 noRAW);
	  
	// Cover that hazard_detected can be asserted and deasserted
	HDU_hazard_toggle: cover property( hazard_detected ##1 !hazard_detected ##1 hazard_detected);
	
	// Cover RAW and noRAW waveforms
	HDU_noRAW_RAW_noRAW: cover property (noRAW ##1 RAW ##1 noRAW);

	// Assume no forwarding
	HDU_no_forward: assume property(forward_EN == 0 );
	
	// Assume src1 and src2 are different registers
	HDU_src1_src2_not_same: assume property(src1_ID != src2_ID);

	// Assert that src1 in ID is the destination of EXE and will be written back in WB, then RAW hazard & hazard detected
	HDU_src1_IDEXE_RAW: assert property( RAW_src1_IDEXE |->  hazard_detected );
	// Assert that  src2 in ID is the destination of EXE and will be written back in WB, then RAW hazard & hazard detected
	HDU_src2_IDEXE_RAW: assert property( RAW_src2valid_IDEXE |->  hazard_detected );
	// Assert that  src1 in ID will be written back in MEM, then RAW hazard & hazard detected
	HDU_src1_IDMEM_RAW: assert property( RAW_src1_IDMEM |->  hazard_detected );
	// Assert that  src2 in ID will be written back in MEM, then RAW hazard & hazard detected
	HDU_src2_IDMEM_RAW: assert property( RAW_src2valid_IDMEM |->  hazard_detected );
	// Assert any RAW hazard will have hazard detected
	HDU_RAW_assert: assert property( RAW |-> hazard_detected );
	
	// Assert that any other condition is not a RAW hazard
	HDU_noRAW_assert: assert property( noRAW |-> !hazard_detected );
	
	// Assert that hazard detected is only triggered by a RAW hazard
	HDU_hazard_triggered: assert property (hazard_detected |-> RAW);
	
endmodule


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

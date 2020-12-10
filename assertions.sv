`include "defines.v"

`define FPV_TEST_OPS {`OP_ADD, `OP_SUB, `OP_SLA, `OP_SRA, `OP_ADDI, `OP_SUBI, `OP_AND, `OP_OR, `OP_NOR, `OP_XOR, `OP_SLL, `OP_SRL, `OP_LD, `OP_ST}
`define FPV_WB_OPS {`OP_ADD, `OP_SUB, `OP_SLA, `OP_SRA, `OP_ADDI, `OP_SUBI, `OP_AND, `OP_OR, `OP_NOR, `OP_XOR, `OP_SLL, `OP_SRL, `OP_LD}
`define FPV_MEM_OPS {`OP_LD, `OP_ST}
`define FPV_NONMEM_OPS {`OP_ADD, `OP_SUB, `OP_SLA, `OP_SRA, `OP_ADDI, `OP_SUBI, `OP_AND, `OP_OR, `OP_NOR, `OP_XOR, `OP_SLL, `OP_SRL}
`define FPV_EXE_CMD {`EXE_ADD, `EXE_SUB, `EXE_AND, `EXE_OR, `EXE_NOR, `EXE_XOR, `EXE_SLA, `EXE_SLL, `EXE_SRA, `EXE_SRL, `EXE_NO_OPERATION}

module fpv_stages(
	input clk,
	input rst,
	input forward_EN,
	input [`WORD_LEN-1:0] PC_IF, PC_ID, PC_EXE, PC_MEM,
	input [`WORD_LEN-1:0] inst_IF, inst_ID,
	input [`WORD_LEN-1:0] reg1_ID, reg2_ID, ST_value_EXE, ST_value_EXE2MEM, ST_value_MEM,
	input [`WORD_LEN-1:0] val1_ID, val1_EXE,
	input [`WORD_LEN-1:0] val2_ID, val2_EXE,
	input [`WORD_LEN-1:0] ALURes_EXE, ALURes_MEM, ALURes_WB,
	input [`WORD_LEN-1:0] dataMem_out_MEM, dataMem_out_WB,
	input [`WORD_LEN-1:0] WB_result,
	input [`REG_FILE_ADDR_LEN-1:0] dest_EXE, dest_MEM, dest_WB, // dest_ID = instruction[25:21] thus nothing declared
	input [`REG_FILE_ADDR_LEN-1:0] src1_ID, src2_regFile_ID, src2_forw_ID, src2_forw_EXE, src1_forw_EXE,
	input [`EXE_CMD_LEN-1:0] EXE_CMD_ID, EXE_CMD_EXE,
	input [`FORW_SEL_LEN-1:0] val1_sel, val2_sel, ST_val_sel,
	input [1:0] branch_comm,
	input Br_Taken_ID, IF_Flush, Br_Taken_EXE,
	input MEM_R_EN_ID, MEM_R_EN_EXE, MEM_R_EN_MEM, MEM_R_EN_WB,
	input MEM_W_EN_ID, MEM_W_EN_EXE, MEM_W_EN_MEM,
	input WB_EN_ID, WB_EN_EXE, WB_EN_MEM, WB_EN_WB,
	input hazard_detected, is_imm, ST_or_BNE
);
	// Opcode from the instruction to allow easier viewing in waveform
	logic [5:0] opcode = inst_ID[31:26];
	
	default clocking c0 @(posedge clk); endclocking;
	default disable iff (rst);
	
	// Properties for operations being processed by the MIPS pipeline from ID to WB stages
	
	// Property for arithmetic, immdeiate and logical operation processing by the MIPS pipeline from ID to WB stage
	property op_arith_logical(op_code, exe_code, opres);
		logic [`WORD_LEN-1:0] alures; 
		(inst_ID[31:26] == op_code) |=> ((EXE_CMD_EXE == exe_code) && (val1_sel == 0) && (val2_sel == 0) && !MEM_R_EN_EXE, alures = opres) |-> ALURes_EXE == alures ##1 ALURes_MEM == alures ##1 ((WB_result == alures) && WB_EN_WB );
	endproperty
	
	// Property for load operation processing by the MIPS pipeline from ID to WB stage
	property op_mem_ld;
		logic [`WORD_LEN-1:0] alures; 
		(inst_ID[31:26] == `OP_LD) |=> ((EXE_CMD_EXE == `EXE_ADD) && (val1_sel == 0) && (val2_sel == 0) && MEM_R_EN_EXE, alures = val1_EXE + val2_EXE) |-> ALURes_EXE == alures ##1 (ALURes_MEM == alures) && MEM_R_EN_MEM ##1 ((WB_result == dataMem_out_WB) && WB_EN_WB ) ;
	endproperty
	
	// Property for store operation processing by the MIPS pipeline from ID to MEM stage
	property op_mem_st;
		logic [`WORD_LEN-1:0] alures; 
		(inst_ID[31:26] == `OP_ST) |=> ((EXE_CMD_EXE == `EXE_ADD) && (val1_sel == 0) && (val2_sel == 0) && MEM_W_EN_EXE, alures = val1_EXE + val2_EXE) |-> ALURes_EXE == alures ##1 (ALURes_MEM == alures) && MEM_W_EN_MEM ;
	endproperty
	
	// --- COVERS --- //
	
	// Cover waveforms for single arithmetic, logical, immediate and memory operation
	// Cover AND operation
	op_and_true_cover: cover property ( inst_ID[31:26] == `OP_AND && (val1_ID == 1 && val2_ID == 1) && (hazard_detected == 0) );
	op_and_false_cover: cover property ( inst_ID[31:26] == `OP_AND && (val1_ID == 0 && val2_ID == 1) && (hazard_detected == 0) );
	
	// Cover ADD operation
	op_add_cover: cover property ( inst_ID[31:26] == `OP_ADD && (val1_ID == 1 && val2_ID == 2) && (hazard_detected == 0) );
	// Cover SUB operation
	op_sub_cover: cover property ( inst_ID[31:26] == `OP_SUB && (val1_ID == 9 && val2_ID == 2) && (hazard_detected == 0) );
	// Cover SLA operation
	op_sla_cover: cover property ( inst_ID[31:26] == `OP_SLA && (val1_ID == 9 && val2_ID == 1) && (hazard_detected == 0) );
	// Cover SRA operation
	op_sra_cover: cover property ( inst_ID[31:26] == `OP_SRA && (val1_ID == 9 && val2_ID == 1) && (hazard_detected == 0) );
	
	
	// Cover ADDI operation
	op_addi_cover: cover property ( inst_ID[31:26] == `OP_ADDI && (val1_ID == 5 && val2_ID == 6) && (hazard_detected == 0) );
	// Cover LD operation
	op_ld_cover: cover property ( inst_ID[31:26] == `OP_LD && (val1_ID == 4 && val2_ID != 3) && (hazard_detected == 0) );
	// Cover ST operation
	op_st_cover: cover property ( inst_ID[31:26] == `OP_ST && (val1_ID == 5 && val2_ID == 4) && (hazard_detected == 0) );
	
	// Cover back to back operations (ADD, ADDI, AND, LD & ST)
	backtoback_cover: cover property ( ( inst_ID[31:26] == `OP_ADD && (val1_ID == 1 && val2_ID == 2) && (hazard_detected == 0) ) ##1 ( inst_ID[31:26] == `OP_ADDI && (val1_ID == 5 && val2_ID == 6) && (hazard_detected == 0) ) ##1 ( inst_ID[31:26] == `OP_AND && (val1_ID == 1 && val2_ID == 1) && (hazard_detected == 0) ) ##1 ( inst_ID[31:26] == `OP_LD && (val1_ID == 4 && val2_ID != 3) && (hazard_detected == 0) ) ##1 ( inst_ID[31:26] == `OP_ST && (val1_ID == 5 && val2_ID == 4) && (hazard_detected == 0) ) );
	
	// --- ASSUMPTIONS --- //
	
	// Assume only operations which are being verified are input to the design
	fpv_ops_assume: assume property ( inst_ID[31:26] inside `FPV_TEST_OPS);
	
	// Assume that cutpoints src1 and src2 are not the same
	src1_src2_notsame_assume: assume property ( src1_ID != src2_regFile_ID );
	
	// Assume no forwarding
	nofwd_assume: assume property ( forward_EN == 0 );
	
	// --- ASSERTIONS --- //
	
	// Liveness for operations which do register write, memory read or memory write. Write happens only when no RAW hazards.
	WB_liveness: assert property ( (inst_ID[31:26] inside `FPV_WB_OPS) && !hazard_detected |=> s_eventually(WB_EN_WB) );
	MEMR_liveness: assert property ( inst_ID[31:26] == `OP_LD |=> s_eventually(MEM_R_EN_MEM) );
	MEMW_liveness: assert property ( inst_ID[31:26] == `OP_ST && !hazard_detected |=> s_eventually(MEM_W_EN_MEM) );
	
	// Safety to make sure memory is never written and read simultaneously
	MEMRW_safety: assert property (not(MEM_W_EN_MEM && MEM_R_EN_MEM));
	// Safety to make sure non-memory operations never access memory
	NonMEM_ops_safety: assert property ( inst_ID[31:26] inside `FPV_NONMEM_OPS |=> !MEM_R_EN_EXE && !MEM_W_EN_EXE );
	
	
	// Assert arithmetic operations give appropriate results: ADD, SUB
	add_assert: assert property ( op_arith_logical(`OP_ADD, `EXE_ADD, (val1_EXE + val2_EXE)) );
	sub_assert: assert property ( op_arith_logical(`OP_SUB, `EXE_SUB, (val1_EXE - val2_EXE)) );
	sla_assert: assert property ( op_arith_logical(`OP_SLA, `EXE_SLA, (val1_EXE << val2_EXE)) );
	sra_assert: assert property ( op_arith_logical(`OP_SRA, `EXE_SRA, (val1_EXE >> val2_EXE)) );
	
	// Assert arithmetic immediate operations give appropriate results: ADDI, SUBI
	addi_assert: assert property ( op_arith_logical(`OP_ADDI, `EXE_ADD, (val1_EXE + val2_EXE)) );
	subi_assert: assert property ( op_arith_logical(`OP_SUBI, `EXE_SUB, (val1_EXE - val2_EXE)) );
	
	// Assert logical operations give appropriate results: AND, OR, XOR
	and_assert: assert property ( op_arith_logical(`OP_AND, `EXE_AND, (val1_EXE & val2_EXE)) );
	or_assert: assert property ( op_arith_logical(`OP_OR, `EXE_OR, (val1_EXE | val2_EXE)) );
	xor_assert: assert property ( op_arith_logical(`OP_XOR, `EXE_XOR, (val1_EXE ^ val2_EXE)) );
	nor_assert: assert property ( op_arith_logical(`OP_NOR, `EXE_NOR, ~(val1_EXE | val2_EXE)) );
	sll_assert: assert property ( op_arith_logical(`OP_SLL, `EXE_SLL, val1_EXE <<< val2_EXE) );
	srl_assert: assert property ( op_arith_logical(`OP_SRL, `EXE_SRL, val1_EXE >>> val2_EXE) );
	
	// Assert memory operations
	ld_assert: assert property ( op_mem_ld );
	st_assert: assert property ( op_mem_st );
	
	
	

endmodule //fpv_stages


module fpv_exestage(
	input logic clk,
	input logic [`EXE_CMD_LEN-1:0] EXE_CMD,
	input logic [`FORW_SEL_LEN-1:0] val1_sel, val2_sel, ST_val_sel,
	input logic [`WORD_LEN-1:0] val1, val2, ALU_res_MEM, result_WB, ST_value_in, ALUResult, ST_value_out
);

	default clocking c0 @(posedge clk); endclocking;
	
	
	// Properties for operations being processed by the MIPS pipeline from ID to WB stages
	
	// Property for arithmetic, immdeiate and logical operation processing by the MIPS pipeline from ID to WB stage
	property op_arith_logical(exe_code, alures);
		(EXE_CMD == exe_code) && (val1_sel == 0) && (val2_sel == 0) |-> ALUResult == alures;
	endproperty
	
	// --- COVER --- //
	
	// Cover back-to-back operations
	op_cover: cover property ( EXE_CMD inside `FPV_TEST_OPS ##1 EXE_CMD inside `FPV_TEST_OPS );
	
	// --- ASSERTIONS --- //
	
	// Assert arithmetic operations give appropriate results: ADD, SUB
	add_assert: assert property ( op_arith_logical(`EXE_ADD, (val1 + val2)) );
	sub_assert: assert property ( op_arith_logical(`EXE_SUB, (val1 - val2)) );
	sla_assert: assert property ( op_arith_logical(`EXE_SLA, (val1 << val2)) );
	sra_assert: assert property ( op_arith_logical(`EXE_SRA, (val1 >> val2)) );
	
	// Assert arithmetic immediate operations give appropriate results: ADDI, SUBI
	addi_assert: assert property ( op_arith_logical(`EXE_ADD, (val1 + val2)) );
	subi_assert: assert property ( op_arith_logical(`EXE_SUB, (val1 - val2)) );
	
	// Assert logical operations give appropriate results: AND, OR, XOR
	and_assert: assert property ( op_arith_logical(`EXE_AND, (val1 & val2)) );
	or_assert: assert property ( op_arith_logical(`EXE_OR, (val1 | val2)) );
	xor_assert: assert property ( op_arith_logical(`EXE_XOR, (val1 ^ val2)) );
	nor_assert: assert property ( op_arith_logical(`EXE_NOR, ~(val1 | val2)) );
	sll_assert: assert property ( op_arith_logical(`EXE_SLL, val1 <<< val2) );
	srl_assert: assert property ( op_arith_logical(`EXE_SRL, val1 >>> val2) );
	
	// Assert memory operations - uses ADD to calculate address

endmodule //fpv_exestage


module fpv_hazard(
	input logic [`REG_FILE_ADDR_LEN-1:0] src1_ID, src2_ID,
	input logic [`REG_FILE_ADDR_LEN-1:0] dest_EXE, dest_MEM,
	input logic [1:0] branch_comm,
	input logic forward_EN, WB_EN_EXE, WB_EN_MEM, is_imm, ST_or_BNE, MEM_R_EN_EXE,
	input logic hazard_detected
);
	
	logic clk;
	
	default clocking c0 @(posedge clk); endclocking;
	  
	// Booleans for RAW hazards
	
	// RAW hazard when same register used as source in ID and destination in EXE
	let RAW_src1_IDEXE = (src1_ID == dest_EXE) && WB_EN_EXE;
	
	// RAW hazard when same register used as 2nd source in ID (which is valid) and destination in EXE
	let RAW_src2valid_IDEXE = (src2_ID == dest_EXE) && ((~is_imm) || ST_or_BNE) && WB_EN_EXE;
	
	// RAW hazard when same register used as source in ID and destination in MEM
	let RAW_src1_IDMEM = (src1_ID == dest_MEM) && WB_EN_MEM;
	
	// RAW hazard when same register used as 2nd source in ID (which is valid) and destination in MEM
	let RAW_src2valid_IDMEM = (src2_ID == dest_MEM) && ((~is_imm) || ST_or_BNE) && WB_EN_MEM;
	
	// All RAW hazards
	let RAW = RAW_src1_IDEXE || RAW_src2valid_IDEXE || RAW_src1_IDMEM || RAW_src2valid_IDMEM;
	
	// All non RAW hazard combination
	let noRAW = !RAW_src1_IDEXE && !RAW_src2valid_IDEXE && !RAW_src1_IDMEM && !RAW_src2valid_IDMEM;
	
	// --- COVERS --- //
	
	// Cover different types of RAW hazard waveforms
	HDU_noRAW_RAW_src1_IDEXE_noRAW: cover property (noRAW ##1 RAW_src1_IDEXE ##1 noRAW);
	HDU_noRAW_RAW_src2valid_IDEXE_noRAW: cover property (noRAW ##1 RAW_src2valid_IDEXE ##1 noRAW);
	HDU_noRAW_RAW_src1_IDMEM_noRAW: cover property (noRAW ##1 RAW_src1_IDMEM ##1 noRAW);
	HDU_noRAW_RAW_src2valid_IDMEM_noRAW: cover property (noRAW ##1 RAW_src2valid_IDMEM ##1 noRAW);
	  
	// Cover that hazard_detected can be asserted and deasserted
	HDU_hazard_toggle: cover property( hazard_detected ##1 !hazard_detected ##1 hazard_detected);
	
	// Cover RAW and noRAW waveforms
	HDU_noRAW_RAW_noRAW: cover property (noRAW ##1 RAW ##1 noRAW);
	
	// --- ASSERTIONS --- //

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
	
endmodule //fpv_hazard


module fpv_controller(
	input logic hazard_detected,
	input logic [`OP_CODE_LEN-1:0] opCode,
	input logic branchEn,
	input logic [`EXE_CMD_LEN-1:0] EXE_CMD,
	input logic [1:0] Branch_command,
	input logic Is_Imm, ST_or_BNE, WB_EN, MEM_R_EN, MEM_W_EN
);
	
	logic clk;

	default clocking c0 @(posedge clk); endclocking;

	// --- COVER --- //
	
	// Cover that the operations under verification when provided to the CU, generates one of the control signals
	CU_cover: cover property ( (opCode inside `FPV_TEST_OPS && hazard_detected == 1'b0) ##1 (EXE_CMD inside `FPV_EXE_CMD) && (Is_Imm || WB_EN || MEM_R_EN || MEM_W_EN) );

	// Cover ADD then ADDI operations to look at the waveforms
	CU_cover_add: cover property (opCode == `OP_ADD && hazard_detected == 1'b0);
	CU_cover_addi: cover property (opCode == `OP_ADDI && hazard_detected == 1'b0);
	CU_cover_ld: cover property (opCode == `OP_LD && hazard_detected == 1'b0);
	CU_cover_st: cover property (opCode == `OP_ST && hazard_detected == 1'b0);
	CU_cover_and: cover property (opCode == `OP_AND && hazard_detected == 1'b0);

	// Cover ADD, ADDI, AND, LD & ST back to back to look at waveforms
	CU_cover_add_addi_and_ld_st: cover property (opCode == `OP_ADD && hazard_detected == 1'b0 ##1 opCode == `OP_ADDI && hazard_detected == 1'b0 ##1 opCode == `OP_AND && hazard_detected == 1'b0 ##1 opCode == `OP_LD && hazard_detected == 1'b0 ##1 opCode == `OP_ST && hazard_detected == 1'b0 );

	// Cover ADD with hazard detected
	CU_cover_add_hazard_add: cover property ( (opCode == `OP_ADD && hazard_detected == 1'b0) ##1 (opCode == `OP_ADD && hazard_detected == 1'b1) ##1 (opCode == `OP_ADD && hazard_detected == 1'b0) );

	// Cover hazard detection can be detected
	CU_cover_hazard_detected: cover property ( hazard_detected == 1'b1 );

	// --- ASSERTIONS --- //

	// Assert arithemtic operations generating correct control signals
	CU_add_assert: assert property ((opCode == `OP_ADD && hazard_detected == 1'b0) |-> (EXE_CMD == `EXE_ADD) && !Is_Imm && WB_EN && !MEM_R_EN && !MEM_W_EN);
	CU_sub_assert: assert property ((opCode == `OP_SUB && hazard_detected == 1'b0) |-> (EXE_CMD == `EXE_SUB) && !Is_Imm && WB_EN && !MEM_R_EN && !MEM_W_EN);
	CU_sla_assert: assert property ((opCode == `OP_SLA && hazard_detected == 1'b0) |-> (EXE_CMD == `EXE_SLA) && !Is_Imm && WB_EN && !MEM_R_EN && !MEM_W_EN);
	CU_sra_assert: assert property ((opCode == `OP_SRA && hazard_detected == 1'b0) |-> (EXE_CMD == `EXE_SRA) && !Is_Imm && WB_EN && !MEM_R_EN && !MEM_W_EN);

	// Assert logical operations generating correct control signals
	CU_and_assert: assert property ((opCode == `OP_AND && hazard_detected == 1'b0) |-> (EXE_CMD == `EXE_AND) && !Is_Imm && WB_EN && !MEM_R_EN && !MEM_W_EN);
	CU_or_assert: assert property ((opCode == `OP_OR && hazard_detected == 1'b0) |-> (EXE_CMD == `EXE_OR) && !Is_Imm && WB_EN && !MEM_R_EN && !MEM_W_EN);
	CU_nor_assert: assert property ((opCode == `OP_NOR && hazard_detected == 1'b0) |-> (EXE_CMD == `EXE_NOR) && !Is_Imm && WB_EN && !MEM_R_EN && !MEM_W_EN);
	CU_xor_assert: assert property ((opCode == `OP_XOR && hazard_detected == 1'b0) |-> (EXE_CMD == `EXE_XOR) && !Is_Imm && WB_EN && !MEM_R_EN && !MEM_W_EN);
	CU_sll_assert: assert property ((opCode == `OP_SLL && hazard_detected == 1'b0) |-> (EXE_CMD == `EXE_SLL) && !Is_Imm && WB_EN && !MEM_R_EN && !MEM_W_EN);
	CU_srl_assert: assert property ((opCode == `OP_SRL && hazard_detected == 1'b0) |-> (EXE_CMD == `EXE_SRL) && !Is_Imm && WB_EN && !MEM_R_EN && !MEM_W_EN);

	// Assert arithmetic immediate operations generating correct control signals
	CU_addi_assert: assert property ((opCode == `OP_ADDI && hazard_detected == 1'b0) |-> (EXE_CMD == `EXE_ADD) && Is_Imm && WB_EN && !MEM_R_EN && !MEM_W_EN);
	CU_subi_assert: assert property ((opCode == `OP_SUBI && hazard_detected == 1'b0) |-> (EXE_CMD == `EXE_SUB) && Is_Imm && WB_EN && !MEM_R_EN && !MEM_W_EN);

	// Assert memory operations generating correct control signals
	CU_ld_assert: assert property ((opCode == `OP_LD && hazard_detected == 1'b0) |-> (EXE_CMD == `EXE_ADD) && Is_Imm && WB_EN && MEM_R_EN && !MEM_W_EN);
	CU_st_assert: assert property ((opCode == `OP_ST && hazard_detected == 1'b0) |-> (EXE_CMD == `EXE_ADD) && Is_Imm && !WB_EN && !MEM_R_EN && MEM_W_EN);

	// Assert that no writing can be done when hazard is detected (with property simplification)
	CU_hazard_detected_p1: assert property ( ##1 (hazard_detected == 1'b1) |-> (EXE_CMD == `EXE_NO_OPERATION));
	CU_hazard_detected_p2: assert property ( ##1 (hazard_detected == 1'b1) |-> !WB_EN);
	CU_hazard_detected_p3: assert property ( ##1 (hazard_detected == 1'b1) |-> !MEM_W_EN);

endmodule //fpv_controller

`include "defines.v"

module controller_non_combo (opCode, branchEn, EXE_CMD, Branch_command, Is_Imm, ST_or_BNE, WB_EN, MEM_R_EN, MEM_W_EN, hazard_detected);
  input hazard_detected;
  input [`OP_CODE_LEN-1:0] opCode;
  output branchEn;
  output [`EXE_CMD_LEN-1:0] EXE_CMD;
  output [1:0] Branch_command;
  output Is_Imm, ST_or_BNE, WB_EN, MEM_R_EN, MEM_W_EN;

  assign EXE_CMD = ~(hazard_detected) ? ((opCode == `OP_ADD || opCode == `OP_ADDI || opCode == `OP_LD || opCode == `OP_ST) ? `EXE_ADD : (opCode == `OP_SUB || opCode == `OP_SUBI) ? `EXE_SUB : (opCode == `OP_AND) ? `EXE_AND : (opCode == `OP_OR) ? `EXE_OR : (opCode == `OP_NOR) ? `EXE_NOR : (opCode == `OP_XOR) ? `EXE_XOR : (opCode == `OP_SLA) ? `EXE_SLA : (opCode == `OP_SLL) ? `EXE_SLL : (opCode == `OP_SRA) ? `EXE_SRA : (opCode == `OP_SRL) ? `EXE_SRL : `EXE_NO_OPERATION) : `EXE_NO_OPERATION;
  
  assign WB_EN = ~(hazard_detected) ? ((opCode == `OP_ADD || opCode == `OP_SUB || opCode == `OP_AND || opCode == `OP_OR || opCode == `OP_NOR || opCode == `OP_XOR || opCode == `OP_SLA || opCode == `OP_SLL || opCode == `OP_SRA || opCode == `OP_SRL || opCode == `OP_ADDI || opCode == `OP_SUBI || opCode == `OP_LD) ? 1 : 0) : 0;
  
  assign MEM_W_EN = ~(hazard_detected) ? ((opCode == `OP_ST) ? 1 : 0) : 0;
  
  assign Is_Imm = (opCode == `OP_ADDI || opCode == `OP_SUBI || opCode == `OP_LD || opCode == `OP_ST || opCode == `OP_BEZ || opCode == `OP_BNE || opCode == `OP_JMP) ? 1 : 0;
  
  assign ST_or_BNE = (opCode == `OP_LD || opCode == `OP_ST || opCode == `OP_BNE) ? 1 : 0;
  
  assign MEM_R_EN = (opCode == `OP_LD) ? 1 : 0;
  
  assign Branch_command = (opCode == `OP_BEZ || opCode == `OP_BNE || opCode == `OP_JMP) ? 1 : 0 ;
  
  assign branchEn = (opCode == `OP_BEZ || opCode == `OP_BNE || opCode == `OP_JMP) ? 1 : 0;
  
  
  /*always @ ( * ) begin
    if (hazard_detected == 0) begin
      {branchEn, EXE_CMD, Branch_command, Is_Imm, ST_or_BNE, WB_EN, MEM_R_EN, MEM_W_EN} <= 0;
      case (opCode)
        // operations writing to the register file
        `OP_ADD: begin EXE_CMD <= `EXE_ADD; WB_EN <= 1; end
        `OP_SUB: begin EXE_CMD <= `EXE_SUB; WB_EN <= 1; end
        `OP_AND: begin EXE_CMD <= `EXE_AND; WB_EN <= 1; end
        `OP_OR:  begin EXE_CMD <= `EXE_OR;  WB_EN <= 1; end
        `OP_NOR: begin EXE_CMD <= `EXE_NOR; WB_EN <= 1; end
        `OP_XOR: begin EXE_CMD <= `EXE_XOR; WB_EN <= 1; end
        `OP_SLA: begin EXE_CMD <= `EXE_SLA; WB_EN <= 1; end
        `OP_SLL: begin EXE_CMD <= `EXE_SLL; WB_EN <= 1; end
        `OP_SRA: begin EXE_CMD <= `EXE_SRA; WB_EN <= 1; end
        `OP_SRL: begin EXE_CMD <= `EXE_SRL; WB_EN <= 1; end
        // operations using an immediate value embedded in the instruction
        `OP_ADDI: begin EXE_CMD <= `EXE_ADD; WB_EN <= 1; Is_Imm <= 1; end
        `OP_SUBI: begin EXE_CMD <= `EXE_SUB; WB_EN <= 1; Is_Imm <= 1; end
        // memory operations
        `OP_LD: begin EXE_CMD <= `EXE_ADD; WB_EN <= 1; Is_Imm <= 1; ST_or_BNE <= 1; MEM_R_EN <= 1; end
        `OP_ST: begin EXE_CMD <= `EXE_ADD; Is_Imm <= 1; MEM_W_EN <= 1; ST_or_BNE <= 1; end
        // branch operations
        `OP_BEZ: begin EXE_CMD <= `EXE_NO_OPERATION; Is_Imm <= 1; Branch_command <= `COND_BEZ; branchEn <= 1; end
        `OP_BNE: begin EXE_CMD <= `EXE_NO_OPERATION; Is_Imm <= 1; Branch_command <= `COND_BNE; branchEn <= 1; ST_or_BNE <= 1; end
        `OP_JMP: begin EXE_CMD <= `EXE_NO_OPERATION; Is_Imm <= 1; Branch_command <= `COND_JUMP; branchEn <= 1; end
        default: {branchEn, EXE_CMD, Branch_command, Is_Imm, ST_or_BNE, WB_EN, MEM_R_EN, MEM_W_EN} <= 0;
      endcase
    end
    else if (hazard_detected ==  1) begin
      // preventing any writes to the register file or the memory
      //{EXE_CMD, WB_EN, MEM_W_EN} <= 0;
	  EXE_CMD <= `EXE_NO_OPERATION; 
	  WB_EN <= 0; 
	  MEM_W_EN <= 0;
    end
  end*/
endmodule // controller

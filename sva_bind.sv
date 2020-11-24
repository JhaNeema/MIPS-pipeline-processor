//bind EXEStage assertions check1(clk, EXE_CMD, val1_sel, val2_sel, ST_val_sel, val1, val2, ALU_res_MEM, result_WB, ST_value_in, ALUResult, ST_value_out);
bind controller fpv_controller fpv_model_cont(opCode, branchEn, EXE_CMD, Branch_command, Is_Imm, ST_or_BNE, WB_EN, MEM_R_EN, MEM_W_EN, hazard_detected, clk);
//bind MIPS_Processor assertions_pipeline fpv_model(clk, rst, forward_EN);


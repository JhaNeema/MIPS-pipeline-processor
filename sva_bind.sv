//bind EXEStage assertions check1(clk, EXE_CMD, val1_sel, val2_sel, ST_val_sel, val1, val2, ALU_res_MEM, result_WB, ST_value_in, ALUResult, ST_value_out);
bind controller_verif fpv_controller fpv_model_cont(.*);
//bind MIPS_Processor assertions_pipeline fpv_model(clk, rst, forward_EN);


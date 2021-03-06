# Define clocks
netlist clock clk -period 10 
netlist clock hazard.fpv_model_hdu.clk -period 10 
netlist clock IDStage.controller.fpv_model_cont.clk -period 10 

# Constrain rst
formal netlist constraint rst 1'b0 

# blackboxes
netlist blackbox dataMem
netlist blackbox instructionMem

# cutpoints
netlist cutpoint IDStage.src1
netlist cutpoint IDStage.src2_reg_file
netlist cutpoint IF2IDReg.instruction

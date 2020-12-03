# Define clocks
netlist clock clk -period 10 

# Constrain rst
formal netlist constraint rst 1'b0 

netlist blackbox dataMem
netlist blackbox instructionMem
netlist cutpoint IDStage.src1
netlist cutpoint IDStage.src2_reg_file
#netlist blackbox MIPS_Processor.IF2IDReg

# Define clocks
netlist clock clk -period 10 

# Constrain rst
formal netlist constraint rst 1'b0 

netlist blackbox dataMem
#netlist blackbox MIPS_Processor.IF2IDReg

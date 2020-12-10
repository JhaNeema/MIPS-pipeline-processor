help:
	@echo "targets: clean compile formal debug"
	@echo -e "\t clean \t\t cleans project files"
	@echo -e "\t compile \t cleans project files, compiles model & FPV"
	@echo -e "\t formal \t cleans project files, compiles model & FPV, displays FPV results in command line"
	@echo -e "\t debug \t\t cleans project files, compiles model & FPV, displays FPV results in command line, and runs debug session in GUI"

compile: clean
	@echo "Creating project..."
	vlib work
	vmap work work
	@echo "Compiling model & FPV files..."
	vlog ./modules/*.v ./modules/*/*.v ./defines.v ./topLevelCircuit.v
	vlog -sv -mfcu -cuname my_bind_sva ./sva_bind.sv ./assertions.sv

formal: clean compile
	@echo "Starting FPV..."
	qverify -c -od Output_Results -do "\
		do qs_files/directives.tcl; \
		formal compile -d MIPS_Processor -cuname my_bind_sva \
			-target_cover_statements; \
		formal verify -init qs_files/myinit.init \
		-timeout 5m -auto_constraint_off; \
		exit"

debug: clean compile formal
	@echo "Compiling FPV debug station..."
	qverify Output_Results/formal_verify.db &

clean:
	@echo "Cleaning files..."
	qverify_clean
	\rm -rf work modelsim.ini *.wlf *.log replay* transcript *.db
	\rm -rf Output_Results *.tcl 
	\rm -rf .visualizer


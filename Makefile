
run: clean compile formal
mips: clean compile formal debug
exe: clean compile formal_exe debug
hdu: clean compile formal_hdu debug
cu: clean compile formal_cu debug


compile:
	vlib work
	vmap work work
	vlog ./modules/*.v ./modules/*/*.v ./defines.v ./topLevelCircuit.v
	vlog -sv -mfcu -cuname my_bind_sva ./sva_bind.sv ./assertions.sv

formal:
	qverify -c -od Output_Results -do "\
		do qs_files/directives.tcl; \
		formal compile -d MIPS_Processor -cuname my_bind_sva \
			-target_cover_statements; \
		formal verify -init qs_files/myinit.init \
		-timeout 5m -auto_constraint_off; \
		exit"
	
formal_exe:
	qverify -c -od Output_Results -do "\
		do qs_files/directives.tcl; \
		formal compile -d EXEStage -cuname my_bind_sva \
			-target_cover_statements; \
		formal verify -init qs_files/myinit.init \
		-timeout 5m -auto_constraint_off; \
		exit"
		
formal_hdu:
	qverify -c -od Output_Results -do "\
		do qs_files/directives.tcl; \
		formal compile -d hazard_detection -cuname my_bind_sva \
			-target_cover_statements; \
		formal verify \
		-timeout 5m -auto_constraint_off; \
		exit"

formal_cu:
	qverify -c -od Output_Results -do "\
		do qs_files/directives.tcl; \
		formal compile -d controller_non_combo -cuname my_bind_sva \
			-target_cover_statements; \
		formal verify -init qs_files/myinit.init \
		-timeout 5m -auto_constraint_off; \
		exit"

debug: 
	qverify Output_Results/formal_verify.db &

clean:
	qverify_clean
	\rm -rf work modelsim.ini *.wlf *.log replay* transcript *.db
	\rm -rf Output_Results *.tcl 
	\rm -rf .visualizer

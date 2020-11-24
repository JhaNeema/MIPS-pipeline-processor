
run: clean compile formal_cu debug

compile:
	vlib work
	vmap work work
	vlog ./modules/*.v ./modules/*/*.v ./defines.v ./topLevelCircuit.v
	vlog -sv -mfcu -cuname my_bind_sva ./sva_bind.sv ./assertions.sv

formal_cu:
	qverify -c -od Output_Results -do "\
		do qs_files/directives.tcl; \
		formal compile -d controller -cuname my_bind_sva \
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


bind MIPS_Processor.IDStage.controller fpv_controller fpv_model_cont(.*);
bind MIPS_Processor.hazard fpv_hazard fpv_model_hdu(.*);
bind MIPS_Processor.EXEStage fpv_exestage fpv_model_exe(.*);
bind MIPS_Processor fpv_stages fpv_model_mips(.*);
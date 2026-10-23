theory Check_Channels
  imports HHL_Algorithm_Channels.Program_Channels
begin

ML_file "../project_checks.ML"

ML \<open>Project_Checks.run {name = "Channels", audit = ["Vern_Paulsen_QC_3_10", "Vern_Paulsen_QC_3_10_Lmat", "Vern_Paulsen_QC", "HHL_Algorithm", "HHL_Algorithm_Channels"], allow = [], targets = ["HHL_Algorithm_Channels"], ignore = [], strict = true} \<^theory>\<close>

end

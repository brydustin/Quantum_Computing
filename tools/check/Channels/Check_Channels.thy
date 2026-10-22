theory Check_Channels
  imports Vern_Paulsen_QC_Channels.Program_Channels
begin

ML_file "../project_checks.ML"

ML \<open>Project_Checks.run {name = "Channels", audit = ["Vern_Paulsen_QC_3_10", "Vern_Paulsen_QC_3_10_Lmat", "Vern_Paulsen_QC", "Vern_Paulsen_QC_Algorithms", "Vern_Paulsen_QC_Channels"], allow = [], targets = ["Vern_Paulsen_QC_Channels"], ignore = [], strict = true} \<^theory>\<close>

end

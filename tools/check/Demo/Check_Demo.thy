theory Check_Demo
  imports Vern_Paulsen_QC_Demo.HHL_Demo
begin

ML_file "../project_checks.ML"

ML \<open>Project_Checks.run {name = "Demo", audit = ["Vern_Paulsen_QC_3_10", "Vern_Paulsen_QC_3_10_Lmat", "Vern_Paulsen_QC", "Vern_Paulsen_QC_Algorithms", "Vern_Paulsen_QC_Demo"], allow = [], targets = ["Vern_Paulsen_QC_Demo"], ignore = [], strict = true} \<^theory>\<close>

end

theory Check_Sylvester
  imports Vern_Paulsen_QC_Sylvester.Day05_Sylvester_Criterion
begin

ML_file "../project_checks.ML"

ML \<open>Project_Checks.run {name = "Sylvester", audit = ["Vern_Paulsen_QC_3_10", "Vern_Paulsen_QC_Sylvester"], allow = [], targets = ["Vern_Paulsen_QC_Sylvester"], ignore = [], strict = true} \<^theory>\<close>

end

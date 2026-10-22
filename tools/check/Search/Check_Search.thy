theory Check_Search
  imports Vern_Paulsen_QC_Search.HHL_Search_Bound
begin

ML_file "../project_checks.ML"

ML \<open>Project_Checks.run {name = "Search", audit = ["Vern_Paulsen_QC_Search"], allow = ["Types_To_Sets.cancel_type_definition"], targets = ["Vern_Paulsen_QC_Search"], ignore = [], strict = true} \<^theory>\<close>

end

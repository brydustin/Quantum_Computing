theory Check_Search
  imports HHL_Algorithm_Search.HHL_Search_Bound
begin

ML_file "../project_checks.ML"

ML \<open>Project_Checks.run {name = "Search", audit = ["HHL_Algorithm_Search"], allow = ["Types_To_Sets.cancel_type_definition"], targets = ["HHL_Algorithm_Search"], ignore = [], strict = true} \<^theory>\<close>

end

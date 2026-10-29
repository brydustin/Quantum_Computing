theory Check_Search
  imports Quantum_Search_Bound.HHL_Search_Bound
begin

ML_file "../project_checks.ML"

ML \<open>Project_Checks.run {name = "Search", audit = ["Quantum_Search_Bound"], allow = ["Types_To_Sets.cancel_type_definition"], targets = ["Quantum_Search_Bound"], ignore = [], strict = true} \<^theory>\<close>

end

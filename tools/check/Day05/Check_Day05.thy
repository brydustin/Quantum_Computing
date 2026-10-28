theory Check_Day05
  imports Quantum_Computing_CP_Maps.Day05_Sylvester_Criterion
begin

ML_file "../project_checks.ML"

ML \<open>Project_Checks.run {name = "Day05", audit = ["Quantum_Computing_CP_Maps"], allow = [], targets = ["Quantum_Computing_CP_Maps.Day05_Sylvester_Criterion"], ignore = [], strict = true} \<^theory>\<close>

end

theory Check_Day05
  imports Quantum_Computing_by_VP_Day05.Day05_Sylvester_Criterion
begin

ML_file "../project_checks.ML"

ML \<open>Project_Checks.run {name = "Day05", audit = ["Quantum_Computing_by_VP_3_10", "Quantum_Computing_by_VP_Day05"], allow = [], targets = ["Quantum_Computing_by_VP_Day05"], ignore = [], strict = true} \<^theory>\<close>

end

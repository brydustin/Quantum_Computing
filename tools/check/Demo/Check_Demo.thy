theory Check_Demo
  imports HHL_Algorithm_Demo.HHL_Demo
begin

ML_file "../project_checks.ML"

ML \<open>Project_Checks.run {name = "Demo", audit = ["Quantum_Computing_by_VP_3_10", "Quantum_Computing_by_VP_3_10_Lmat", "Quantum_Computing_by_VP", "HHL_Algorithm", "HHL_Algorithm_Demo"], allow = [], targets = ["HHL_Algorithm_Demo"], ignore = [], strict = true} \<^theory>\<close>

end

theory Check_Demo
  imports HHL_Algorithm_Demo.HHL_Demo
begin

ML_file "../project_checks.ML"

ML \<open>Project_Checks.run {name = "Demo", audit = ["Quantum_Computing_CP_Maps", "HHL_Algorithm", "HHL_Algorithm_Demo"], allow = [], targets = ["HHL_Algorithm_Demo"], ignore = [], strict = true} \<^theory>\<close>

end

theory Check_Channels
  imports HHL_Algorithm_Channels.Program_Channels
begin

ML_file "../project_checks.ML"

ML \<open>Project_Checks.run {name = "Channels", audit = ["Quantum_Computing_by_VP_Basics", "Quantum_Computing_by_VP_Typed_Matrices", "Quantum_Computing_by_VP", "HHL_Algorithm", "HHL_Algorithm_Channels"], allow = [], targets = ["HHL_Algorithm_Channels"], ignore = [], strict = true} \<^theory>\<close>

end

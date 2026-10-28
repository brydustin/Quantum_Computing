theory Check_Channels
  imports HHL_Algorithm_Channels.Program_Channels
begin

ML_file "../project_checks.ML"

ML \<open>Project_Checks.run {name = "Channels", audit = ["Quantum_Computing_CP_Maps", "HHL_Algorithm", "HHL_Algorithm_Channels"], allow = [], targets = ["HHL_Algorithm_Channels"], ignore = [], strict = true} \<^theory>\<close>

end

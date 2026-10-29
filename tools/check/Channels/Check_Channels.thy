theory Check_Channels
  imports Quantum_Hoare_Logic_Channels.Program_Channels
begin

ML_file "../project_checks.ML"

ML \<open>Project_Checks.run {name = "Channels", audit = ["Quantum_Computing_CP_Maps", "HHL_Algorithm", "Quantum_Hoare_Logic_Channels"], allow = [], targets = ["Quantum_Hoare_Logic_Channels"], ignore = [], strict = true} \<^theory>\<close>

end

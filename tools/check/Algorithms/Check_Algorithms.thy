theory Check_Algorithms
  imports HHL_Algorithm.HHL_All_Elementary HHL_Algorithm.HHL_Sparse_Circuit
    HHL_Algorithm.HHL_Optimality HHL_Algorithm.QPE_Program
    HHL_Algorithm.HHL_Suzuki
begin

ML_file "../project_checks.ML"

ML \<open>Project_Checks.run {name = "Algorithms", audit = ["Quantum_Computing_CP_Maps", "Hermitian_Functional_Calculus", "HHL_Algorithm"], allow = [], targets = ["HHL_Algorithm"], ignore = [], strict = true} \<^theory>\<close>

text \<open>The functional calculus against the notes: overlaps of two independent entries, reported only.\<close>

ML \<open>Project_Checks.run {name = "HFC_Notes", audit = [], allow = [], targets = ["Hermitian_Functional_Calculus"], ignore = ["HHL_Algorithm"], strict = false} \<^theory>\<close>

end

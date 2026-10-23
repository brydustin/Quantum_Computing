theory Check_Algorithms
  imports Vern_Paulsen_QC_Algorithms.HHL_All_Elementary Vern_Paulsen_QC_Algorithms.HHL_Sparse_Circuit
    Vern_Paulsen_QC_Algorithms.HHL_Optimality Vern_Paulsen_QC_Algorithms.QPE_Program
    Vern_Paulsen_QC_Algorithms.HHL_Suzuki
begin

ML_file "../project_checks.ML"

ML \<open>Project_Checks.run {name = "Algorithms", audit = ["Vern_Paulsen_QC_3_10", "Vern_Paulsen_QC_3_10_Lmat", "Vern_Paulsen_QC", "Hermitian_Functional_Calculus", "Vern_Paulsen_QC_Algorithms"], allow = [], targets = ["Vern_Paulsen_QC_Algorithms"], ignore = [], strict = true} \<^theory>\<close>

text \<open>The functional calculus against the notes: overlaps of two independent entries, reported only.\<close>

ML \<open>Project_Checks.run {name = "HFC_Notes", audit = [], allow = [], targets = ["Hermitian_Functional_Calculus"], ignore = ["Vern_Paulsen_QC_Algorithms"], strict = false} \<^theory>\<close>

end

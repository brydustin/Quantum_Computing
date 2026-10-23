theory Check_HFC
  imports Hermitian_Functional_Calculus.Suzuki_Error Hermitian_Functional_Calculus.Matrix_Sums
begin

ML_file "../project_checks.ML"

ML \<open>Project_Checks.run {name = "HFC", audit = ["Hermitian_Functional_Calculus"], allow = [], targets = ["Hermitian_Functional_Calculus"], ignore = [], strict = true} \<^theory>\<close>

end

theory Check_HFC_AFP
  imports Hermitian_Functional_Calculus.Suzuki_Error Hermitian_Functional_Calculus.Matrix_Sums
    Commuting_Hermitian.Commuting_Hermitian Projective_Measurements.Projective_Measurements
    Two_Hermitian_Results.Sylvester_Criterion
begin

text \<open>The functional calculus against the AFP's other spectral theory of complex matrices.\<close>

ML_file "../project_checks.ML"

ML \<open>Project_Checks.run {name = "HFC_AFP", audit = [], allow = [], targets = ["Hermitian_Functional_Calculus"], ignore = [], strict = false} \<^theory>\<close>

end

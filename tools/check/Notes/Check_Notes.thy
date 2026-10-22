theory Check_Notes
  imports
    Vern_Paulsen_QC_3_10.Basic_Math
    Vern_Paulsen_QC_3_10.Quantum_Computing_3_10
    Vern_Paulsen_QC_3_10.Matrix_Typed
    Vern_Paulsen_QC_3_10.Essential_Functional_Analysis
    Vern_Paulsen_QC_3_10_Lmat.Lmat_Euclidean
    Vern_Paulsen_QC_3_10_Lmat.Separable_Cone
    Vern_Paulsen_QC.Quantum_Computing11
    Vern_Paulsen_QC.Day23_ChoiExtremeUCP
    Vern_Paulsen_QC.Day24_Separability
    Vern_Paulsen_QC.QC_Prelims
    Vern_Paulsen_QC.Day12_Counting_Probability
    Vern_Paulsen_QC.Day18_Positive_Maps
    Vern_Paulsen_QC.Day22_Kraus_Independence
    Vern_Paulsen_QC.Day28_Horodecki_Peres
    Vern_Paulsen_QC.Day30_BitFlip_Code
    Vern_Paulsen_QC.Day32_Pauli_Expansion
    Vern_Paulsen_QC.Day21_Unitary_Freedom
    Vern_Paulsen_QC.Day32_Recovery_Proposition
    Vern_Paulsen_QC.Day22_Minimal_Kraus
    Vern_Paulsen_QC.Day34_Knill_Laflamme
    Vern_Paulsen_QC.Day20_Choi_Rank
    Vern_Paulsen_QC.Day34_KL_Sufficiency
    Vern_Paulsen_QC.Day33_Shor_Code
    Vern_Paulsen_QC.Day17_Environment_Model
    Vern_Paulsen_QC.Day24_Operator_Systems
    Vern_Paulsen_QC.Day25_Arveson_Correspondence
    Vern_Paulsen_QC.Day26_Arveson_Extension
    Vern_Paulsen_QC.Day27_Positive_Map_Criterion
    Vern_Paulsen_QC.Day02_11_Supplement
    Vern_Paulsen_QC.Day29_Classical_Codes
    Vern_Paulsen_QC.Day31_Code_Fidelity
    Vern_Paulsen_QC.Day32_Y_Code
    Vern_Paulsen_QC.Day19_Choi_TP_Unital
    Vern_Paulsen_QC.Day23_Extremality_Examples
    Vern_Paulsen_QC.Day25_Unital_Functional_Norm
    Vern_Paulsen_QC.Day26_CP_Factorization
    Vern_Paulsen_QC.Day27_Entangled_Examples
    Vern_Paulsen_QC.Day05_Cholesky_Examples
    Vern_Paulsen_QC.Day10_15_Supplement
    Vern_Paulsen_QC.Day04_29_Supplement
    Vern_Paulsen_QC.Day21_Ranges
    Vern_Paulsen_QC.Day06_Schmidt_Rank
    Vern_Paulsen_QC.Day22_Adjoint_Maps
    Vern_Paulsen_QC.Day23_Choi3_UCP
    Vern_Paulsen_QC.Day16_Block_Form
    Vern_Paulsen_QC.Day22_UCP_Compact
    Vern_Paulsen_QC.Day06_15_Universal
    Vern_Paulsen_QC.Day21_Average_Conjecture
    Vern_Paulsen_QC.Day21_Average_Two
begin

ML_file "../project_checks.ML"

ML \<open>Project_Checks.run {name = "Notes", audit = ["Vern_Paulsen_QC_3_10", "Vern_Paulsen_QC_3_10_Lmat", "Vern_Paulsen_QC"], allow = [],
  targets = ["Vern_Paulsen_QC_3_10", "Vern_Paulsen_QC_3_10_Lmat", "Vern_Paulsen_QC"], ignore = [], strict = false} \<^theory>\<close>

end

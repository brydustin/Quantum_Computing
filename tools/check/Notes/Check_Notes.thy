theory Check_Notes
  imports
    Quantum_Computing_by_VP_3_10.Basic_Math
    Quantum_Computing_by_VP.Day02_11_Supplement
    Quantum_Computing_by_VP_3_10.Quantum_Computing_3_10
    Quantum_Computing_by_VP.Day04_29_Supplement
    Quantum_Computing_by_VP.Day05_Cholesky_Examples
    Quantum_Computing_by_VP.Day06_15_Universal
    Quantum_Computing_by_VP.Day06_Schmidt_Rank
    Quantum_Computing_by_VP.Day10_15_Supplement
    Quantum_Computing_by_VP.Quantum_Computing11
    Quantum_Computing_by_VP.Day12_Counting_Probability
    Quantum_Computing_by_VP.Day16_Block_Form
    Quantum_Computing_by_VP.Day17_Environment_Model
    Quantum_Computing_by_VP.Day18_Positive_Maps
    Quantum_Computing_by_VP.Day19_Choi_TP_Unital
    Quantum_Computing_by_VP.Day20_Choi_Rank
    Quantum_Computing_by_VP.Day21_Average_Conjecture
    Quantum_Computing_by_VP.Day21_Average_Two
    Quantum_Computing_by_VP.Day21_Ranges
    Quantum_Computing_by_VP.Day21_Unitary_Freedom
    Quantum_Computing_by_VP.Day22_Adjoint_Maps
    Quantum_Computing_by_VP.Day22_Kraus_Independence
    Quantum_Computing_by_VP.Day22_Minimal_Kraus
    Quantum_Computing_by_VP.Day22_UCP_Compact
    Quantum_Computing_by_VP.Day23_Choi3_UCP
    Quantum_Computing_by_VP.Day23_ChoiExtremeUCP
    Quantum_Computing_by_VP.Day23_Extremality_Examples
    Quantum_Computing_by_VP.Day24_Operator_Systems
    Quantum_Computing_by_VP.Day24_Separability
    Quantum_Computing_by_VP.Day25_Arveson_Correspondence
    Quantum_Computing_by_VP.Day25_Unital_Functional_Norm
    Quantum_Computing_by_VP_3_10.Matrix_Typed
    Quantum_Computing_by_VP.Day26_Arveson_Extension
    Quantum_Computing_by_VP.Day26_CP_Factorization
    Quantum_Computing_by_VP_3_10_Lmat.Separable_Cone
    Quantum_Computing_by_VP.Day27_Entangled_Examples
    Quantum_Computing_by_VP.Day27_Positive_Map_Criterion
    Quantum_Computing_by_VP.Day28_Horodecki_Peres
    Quantum_Computing_by_VP.Day29_Classical_Codes
    Quantum_Computing_by_VP.Day30_BitFlip_Code
    Quantum_Computing_by_VP.Day31_Code_Fidelity
    Quantum_Computing_by_VP.Day32_Pauli_Expansion
    Quantum_Computing_by_VP.Day32_Recovery_Proposition
    Quantum_Computing_by_VP.Day32_Y_Code
    Quantum_Computing_by_VP.Day33_Shor_Code
    Quantum_Computing_by_VP.Day34_KL_Sufficiency
    Quantum_Computing_by_VP.Day34_Knill_Laflamme
    Quantum_Computing_by_VP_3_10.Essential_Functional_Analysis
    Quantum_Computing_by_VP_3_10_Lmat.Lmat_Euclidean
    Quantum_Computing_by_VP.QC_Prelims
begin

ML_file "../project_checks.ML"

ML \<open>Project_Checks.run {name = "Notes", audit = ["Quantum_Computing_by_VP_3_10", "Quantum_Computing_by_VP_3_10_Lmat", "Quantum_Computing_by_VP"], allow = [],
  targets = ["Quantum_Computing_by_VP_3_10", "Quantum_Computing_by_VP_3_10_Lmat", "Quantum_Computing_by_VP"], ignore = [], strict = true} \<^theory>\<close>

end

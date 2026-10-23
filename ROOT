chapter AFP

session Quantum_Computing_by_VP_3_10 in "." = Isabelle_Marries_Dirac +
  options [document = false, quick_and_dirty = false, timeout = 3600]
  sessions
    Quantum_Fourier_Transform
    "HOL-Hahn_Banach"
    "HOL-Analysis"
  theories
    "HOL-Analysis.Euclidean_Space"
    "HOL-Analysis.L2_Norm"
    "HOL-Analysis.Elementary_Metric_Spaces"
    "HOL-Analysis.Topology_Euclidean_Space"
    Basic_Math
    Quantum_Computing_3_10
    "HOL-Hahn_Banach.Hahn_Banach"
    Matrix_Typed
    Essential_Functional_Analysis

session Quantum_Computing_by_VP_3_10_Lmat in "Lmat" = Quantum_Computing_by_VP_3_10 +
  options [document = false, quick_and_dirty = false, timeout = 3600]
  theories
    Lmat_Euclidean
    Separable_Cone

session Quantum_Computing_by_VP in Day11 = Quantum_Computing_by_VP_3_10_Lmat +
  description "
    Vern Paulsen's lecture notes on quantum computing and completely positive maps
    (Houston, 2011), formalised lecture by lecture."
  options [document = pdf, document_output = "output",
           document_variants = "document=/proof,/ML",
           quick_and_dirty = false, timeout = 3600]
  theories
    Day02_11_Supplement
    Day04_29_Supplement
    Day05_Cholesky_Examples
    Day06_15_Universal
    Day06_Schmidt_Rank
    Day10_15_Supplement
    Quantum_Computing11
    Day12_Counting_Probability
    Day16_Block_Form
    Day17_Environment_Model
    Day18_Positive_Maps
    Day19_Choi_TP_Unital
    Day20_Choi_Rank
    Day21_Average_Conjecture
    Day21_Average_Two
    Day21_Ranges
    Day21_Unitary_Freedom
    Day22_Adjoint_Maps
    Day22_Kraus_Independence
    Day22_Minimal_Kraus
    Day22_UCP_Compact
    Day23_Choi3_UCP
    Day23_ChoiExtremeUCP
    Day23_Extremality_Examples
    Day24_Operator_Systems
    Day24_Separability
    Day25_Arveson_Correspondence
    Day25_Unital_Functional_Norm
    Day26_Arveson_Extension
    Day26_CP_Factorization
    Day27_Entangled_Examples
    Day27_Positive_Map_Criterion
    Day28_Horodecki_Peres
    Day29_Classical_Codes
    Day30_BitFlip_Code
    Day31_Code_Fidelity
    Day32_Pauli_Expansion
    Day32_Recovery_Proposition
    Day32_Y_Code
    Day33_Shor_Code
    Day34_KL_Sufficiency
    Day34_Knill_Laflamme
    QC_Prelims
    QC_Notes_Overview
  document_theories
    Quantum_Computing_by_VP_3_10.Basic_Math
    Quantum_Computing_by_VP_3_10.Quantum_Computing_3_10
    Quantum_Computing_by_VP_3_10.Matrix_Typed
    Quantum_Computing_by_VP_3_10.Essential_Functional_Analysis
    Quantum_Computing_by_VP_3_10_Lmat.Lmat_Euclidean
    Quantum_Computing_by_VP_3_10_Lmat.Separable_Cone
  document_files
    "root.tex"

session Quantum_Computing_by_VP_Day05 in "Day05" = Two_Hermitian_Results +
  description "
    D5-1: the leading principal minors test, imported from the AFP entry Two_Hermitian_Results
    (separate session: that entry loads HOL-Analysis and HOL-Probability)."
  options [document = pdf, document_output = "output",
           document_variants = "document=/proof,/ML",
           quick_and_dirty = false, timeout = 3600]
  sessions
    Quantum_Computing_by_VP_3_10
  theories
    Day05_Sylvester_Criterion
  document_files
    "root.tex"

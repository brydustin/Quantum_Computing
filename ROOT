chapter AFP

session Vern_Paulsen_QC_3_10 in "." = Isabelle_Marries_Dirac +
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

session Vern_Paulsen_QC_3_10_Lmat in "Lmat" = Vern_Paulsen_QC_3_10 +
  options [document = false, quick_and_dirty = false, timeout = 3600]
  theories
    Lmat_Euclidean
    Separable_Cone

session Vern_Paulsen_QC in Day11 = Vern_Paulsen_QC_3_10_Lmat +
  description "
    Vern Paulsen's lecture notes on quantum computing and completely positive maps
    (Houston, 2011), formalised lecture by lecture."
  options [document = pdf, document_output = "output",
           document_variants = "document=/proof,/ML",
           quick_and_dirty = false, timeout = 3600]
  theories
    Quantum_Computing11
    Day23_ChoiExtremeUCP
    Day24_Separability
    QC_Prelims
    Day12_Counting_Probability
    Day18_Positive_Maps
    Day22_Kraus_Independence
    Day28_Horodecki_Peres
    Day30_BitFlip_Code
    Day32_Pauli_Expansion
    Day21_Unitary_Freedom
    Day32_Recovery_Proposition
    Day22_Minimal_Kraus
    Day34_Knill_Laflamme
    Day20_Choi_Rank
    Day34_KL_Sufficiency
    Day33_Shor_Code
    Day17_Environment_Model
    Day24_Operator_Systems
    Day25_Arveson_Correspondence
    Day26_Arveson_Extension
    Day27_Positive_Map_Criterion
    Day02_11_Supplement
    Day29_Classical_Codes
    Day31_Code_Fidelity
    Day32_Y_Code
    Day19_Choi_TP_Unital
    Day23_Extremality_Examples
    Day25_Unital_Functional_Norm
    Day26_CP_Factorization
    Day27_Entangled_Examples
    Day05_Cholesky_Examples
    Day10_15_Supplement
    Day04_29_Supplement
    Day21_Ranges
    Day06_Schmidt_Rank
    Day22_Adjoint_Maps
    Day23_Choi3_UCP
    Day16_Block_Form
    Day22_UCP_Compact
    Day06_15_Universal
    Day21_Average_Conjecture
    Day21_Average_Two
    QC_Notes_Overview
  document_theories
    Vern_Paulsen_QC_3_10.Basic_Math
    Vern_Paulsen_QC_3_10.Quantum_Computing_3_10
    Vern_Paulsen_QC_3_10.Matrix_Typed
    Vern_Paulsen_QC_3_10.Essential_Functional_Analysis
    Vern_Paulsen_QC_3_10_Lmat.Lmat_Euclidean
    Vern_Paulsen_QC_3_10_Lmat.Separable_Cone
  document_files
    "root.tex"

session Vern_Paulsen_QC_Sylvester in "Sylvester" = Two_Hermitian_Results +
  description "
    D5-1: Sylvester's criterion, imported from the AFP entry Two_Hermitian_Results
    (separate session: that entry loads HOL-Analysis and HOL-Probability)."
  options [document = pdf, document_output = "output",
           document_variants = "document=/proof,/ML",
           quick_and_dirty = false, timeout = 3600]
  sessions
    Vern_Paulsen_QC_3_10
  theories
    Day05_Sylvester_Criterion
  document_files
    "root.tex"

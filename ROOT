chapter AFP

session Vern_Paulsen_QC_3_10 in "." = Isabelle_Marries_Dirac +
  options [quick_and_dirty = false, timeout = 3600]
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
  options [quick_and_dirty = false, timeout = 3600]
  theories
    Lmat_Euclidean
    Separable_Cone

session Vern_Paulsen_QC in Day11 = Vern_Paulsen_QC_3_10_Lmat +
  options [quick_and_dirty = false, timeout = 3600]
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

session Vern_Paulsen_QC_Algorithms in "Algorithms" = Vern_Paulsen_QC_3_10 +
  description "
    Part VI: Quantum Algorithms, beyond the notes: functional calculus,
    phase estimation and the HHL algorithm."
  options [quick_and_dirty = false, timeout = 3600]
  theories
    Hermitian_Functional_Calculus
    Phase_Estimation
    QFT_Fourier
    HHL
    HHL_Approximate

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

session Vern_Paulsen_QC_Notes in "notes_doc" = Vern_Paulsen_QC +
  description "
    Paulsen's lecture notes, formalised: the document session that typesets
    all project theories with proofs folded (document/output/document.pdf)."
  options [document = pdf, document_output = "output",
           document_variants = "document=/proof,/ML",
           quick_and_dirty = false, timeout = 3600]
  sessions
    Vern_Paulsen_QC_Algorithms
  theories
    QC_Notes_Overview
  document_theories
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
    Vern_Paulsen_QC_Algorithms.Hermitian_Functional_Calculus
    Vern_Paulsen_QC_Algorithms.Phase_Estimation
    Vern_Paulsen_QC_Algorithms.QFT_Fourier
    Vern_Paulsen_QC_Algorithms.HHL
    Vern_Paulsen_QC_Algorithms.HHL_Approximate
  document_files
    "root.tex"

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
    Day06_15_Universal
    Day21_Average_Conjecture
    Day21_Average_Two

session Hermitian_Functional_Calculus in "Hermitian_Functional_Calculus" = Isabelle_Marries_Dirac +
  description "
    The functional calculus of Hermitian matrices, time evolution, and the
    Lie-Trotter and Suzuki product formulas with explicit error bounds."
  options [quick_and_dirty = false, timeout = 3600]
  sessions
    "HOL-Analysis"
    QHLProver
  theories
    Hermitian_Functional_Calculus
    Matrix_Sums
    Trotter_Product_Formula
    Suzuki_Order
    Suzuki_Error

session Vern_Paulsen_QC_Algorithms in "Algorithms" = Vern_Paulsen_QC_3_10 +
  description "
    Part VI: Quantum Algorithms, beyond the notes: phase estimation and the HHL algorithm."
  options [quick_and_dirty = false, timeout = 3600]
  sessions
    QHLProver
    Hermitian_Functional_Calculus
  theories
    Phase_Estimation
    QFT_Fourier
    HHL
    HHL_Approximate
    HHL_Window
    HHL_Simulation
    HHL_Complete
    HHL_Filter
    HHL_Filter_Bounds
    HHL_Runtime
    HHL_Reduction
    HHL_Rectangular
    HHL_Discussion
    HHL_Optimality
    QPE_Register
    HHL_Trajectory
    HHL_Program
    HHL_Gates
    HHL_Preconditioned
    HHL_Termination
    HHL_Paper_Program
    HHL_Gate_Refinements
    HHL_Uniform_Rotation
    HHL_State_Preparation
    HHL_Sparse_Split
    HHL_Sparse_Circuit
    HHL_All_Elementary
    HHL_Suzuki
    QPE_Precision
    QPE_Program

session Vern_Paulsen_QC_Demo in "Demo" = Vern_Paulsen_QC_Algorithms +
  description "
    The HHL circuit executed on a 2x2 system with exact arithmetic in Q(sqrt 2)
    (separate session: the AFP entry Real_Impl replaces the code setup of the reals)."
  options [document = pdf, document_output = "output",
           document_variants = "document=/proof,/ML",
           quick_and_dirty = false, timeout = 3600]
  sessions
    Real_Impl
  theories
    HHL_Demo
  document_files
    "root.tex"

session Vern_Paulsen_QC_Channels in "Channels" = Vern_Paulsen_QC +
  description "
    Loop-free QHLProver programs are channels: Kraus operators read off the program,
    the meaning is their Kraus map, completely positive and trace preserving (the notes'
    Lectures 19-33 applied to the programs of Part VI)."
  options [document = pdf, document_output = "output",
           document_variants = "document=/proof,/ML",
           quick_and_dirty = false, timeout = 3600]
  sessions
    Vern_Paulsen_QC_Algorithms
  theories
    Program_Channels
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

session Vern_Paulsen_QC_Search in "Search" = Compressed_Oracles +
  description "
    H-20: the quantum search lower bound behind HHL's Theorem 4(2), imported from the AFP entry
    Compressed_Oracles (separate session: that entry builds on Complex_Bounded_Operators)."
  options [document = pdf, document_output = "output",
           document_variants = "document=/proof,/ML",
           quick_and_dirty = false, timeout = 3600]
  theories
    HHL_Search_Bound
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
    Hermitian_Functional_Calculus
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
    Vern_Paulsen_QC.Day06_15_Universal
    Vern_Paulsen_QC.Day21_Average_Conjecture
    Vern_Paulsen_QC.Day21_Average_Two
    Hermitian_Functional_Calculus.Hermitian_Functional_Calculus
    Hermitian_Functional_Calculus.Matrix_Sums
    Hermitian_Functional_Calculus.Trotter_Product_Formula
    Hermitian_Functional_Calculus.Suzuki_Order
    Hermitian_Functional_Calculus.Suzuki_Error
    Vern_Paulsen_QC_Algorithms.Phase_Estimation
    Vern_Paulsen_QC_Algorithms.QFT_Fourier
    Vern_Paulsen_QC_Algorithms.HHL
    Vern_Paulsen_QC_Algorithms.HHL_Approximate
    Vern_Paulsen_QC_Algorithms.HHL_Window
    Vern_Paulsen_QC_Algorithms.HHL_Simulation
    Vern_Paulsen_QC_Algorithms.HHL_Complete
    Vern_Paulsen_QC_Algorithms.HHL_Filter
    Vern_Paulsen_QC_Algorithms.HHL_Filter_Bounds
    Vern_Paulsen_QC_Algorithms.HHL_Runtime
    Vern_Paulsen_QC_Algorithms.HHL_Reduction
    Vern_Paulsen_QC_Algorithms.HHL_Rectangular
    Vern_Paulsen_QC_Algorithms.HHL_Discussion
    Vern_Paulsen_QC_Algorithms.HHL_Optimality
    Vern_Paulsen_QC_Algorithms.QPE_Register
    Vern_Paulsen_QC_Algorithms.HHL_Trajectory
    Vern_Paulsen_QC_Algorithms.HHL_Program
    Vern_Paulsen_QC_Algorithms.HHL_Gates
    Vern_Paulsen_QC_Algorithms.HHL_Preconditioned
    Vern_Paulsen_QC_Algorithms.HHL_Termination
    Vern_Paulsen_QC_Algorithms.HHL_Paper_Program
    Vern_Paulsen_QC_Algorithms.HHL_Gate_Refinements
    Vern_Paulsen_QC_Algorithms.HHL_Uniform_Rotation
    Vern_Paulsen_QC_Algorithms.HHL_State_Preparation
    Vern_Paulsen_QC_Algorithms.HHL_Sparse_Split
    Vern_Paulsen_QC_Algorithms.HHL_Sparse_Circuit
    Vern_Paulsen_QC_Algorithms.HHL_All_Elementary
    Vern_Paulsen_QC_Algorithms.HHL_Suzuki
    Vern_Paulsen_QC_Algorithms.QPE_Precision
    Vern_Paulsen_QC_Algorithms.QPE_Program
  document_files
    "root.tex"

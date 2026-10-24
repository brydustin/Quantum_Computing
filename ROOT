chapter AFP

session Quantum_Computing_by_VP_Basics in "." = Isabelle_Marries_Dirac +
  description "
    Days 1--10 of the notes, with the typed matrices and the Hahn--Banach theorem of Day 25."
  options [document = pdf, quick_and_dirty = false, timeout = 3600]
  sessions
    Quantum_Fourier_Transform
    "HOL-Hahn_Banach"
    "HOL-Analysis"
  theories
    "HOL-Analysis.Euclidean_Space"
    "HOL-Analysis.L2_Norm"
    "HOL-Analysis.Elementary_Metric_Spaces"
    "HOL-Analysis.Topology_Euclidean_Space"
    Day01_Inner_Product
    Day02_Trace_Projections
    Unitary_Tensor_Algebra
    Day03_Unitary_Matrices
    Day04_Hermitian_Matrices
    Day05_Positivity_Tests
    Day06_Tensor_Products
    Day07_Postulates
    Day08_Measurements
    Day09_POVMs_Entanglement
    Day10_Quantum_Gates
    "HOL-Hahn_Banach.Hahn_Banach"
    Matrix_Typed
    Essential_Functional_Analysis
    Day25_Hahn_Banach

session Quantum_Computing_by_VP_Typed_Matrices in "Lmat" = Quantum_Computing_by_VP_Basics +
  description "
    Matrices of fixed dimension as a Euclidean space, and the separable cone: closed, with
    entanglement witnesses (Days 26--28)."
  options [document = pdf, quick_and_dirty = false, timeout = 3600]
  theories
    Lmat_Euclidean
    Separable_Cone

session Quantum_Computing_by_VP in Day11 = Quantum_Computing_by_VP_Typed_Matrices +
  description "
    Vern Paulsen's lecture notes on quantum computing and completely positive maps
    (Houston, 2011), formalised lecture by lecture."
  options [document = pdf, document_output = "output",
           document_variants = "document=/proof,/ML",
           quick_and_dirty = false, timeout = 3600]
  theories
    Day02_Projection_Basis
    Day04_Hermitian_Converse
    Day05_Cholesky_Examples
    Day05_Direct_Sum_Basis
    Day06_Tensor_Coordinates
    Day06_Schmidt_Rank
    Day06_15_Universal
    Day08_Indistinguishable_States
    Day09_Bell_Measurement
    Day10_Superdense_Coding
    Day11_Gates_No_Cloning
    Day11_SWAP_Circuit
    Day11_CCNOT_Table
    Day12_Quantum_Parallelism
    Day12_Counting_Probability
    Day13_Density_Matrices
    Day14_Pure_States
    Day14_Composite_Ensembles
    Day15_Partial_Traces
    Day15_Partial_Trace_A
    Day16_Density_Postulates
    Day16_Block_Form
    Day17_Quantum_Noise
    Day17_Environment_Model
    Day18_CP_Maps
    Day18_Positive_Maps
    Day19_Choi_Theorem
    Day19_Choi_Positivity
    Day19_Choi_TP_Unital
    Day20_Positive_Functionals
    Day20_Choi_Rank
    Day21_Kraus_Rank
    Day21_Unitary_Freedom
    Day21_Ranges
    Day21_Average_Conjecture
    Day21_Average_Two
    Day22_Convex_Sets
    Day22_Kraus_Independence
    Day22_Minimal_Kraus
    Day22_Adjoint_Maps
    Day22_UCP_Compact
    Day23_ChoiExtremeUCP
    Day23_Choi3_UCP
    Day23_Extremality_Examples
    Day24_Operator_Systems
    Day25_Arveson_Correspondence
    Day25_Unital_Functional_Norm
    Day26_Arveson_Extension
    Day26_CP_Factorization
    Day26_Separability
    Day27_Positive_Map_Criterion
    Day27_Entangled_Examples
    Day28_Horodecki_Peres
    Day29_Error_Correction
    Day29_Classical_Codes
    Day29_Subspace_Codes
    Day30_Error_Probabilities
    Day30_BitFlip_Code
    Day31_Bit_Flip_Channel
    Day31_Code_Fidelity
    Day32_Phase_Flip_Code
    Day32_Pauli_Expansion
    Day32_Y_Code
    Day32_Recovery_Proposition
    Day33_Shor_Code
    Day34_Knill_Laflamme
    Day34_KL_Sufficiency
    Quantum_Channels
    QC_Prelims
    QC_Notes_Overview
  document_theories
    Quantum_Computing_by_VP_Basics.Day01_Inner_Product
    Quantum_Computing_by_VP_Basics.Day02_Trace_Projections
    Quantum_Computing_by_VP_Basics.Unitary_Tensor_Algebra
    Quantum_Computing_by_VP_Basics.Day03_Unitary_Matrices
    Quantum_Computing_by_VP_Basics.Day04_Hermitian_Matrices
    Quantum_Computing_by_VP_Basics.Day05_Positivity_Tests
    Quantum_Computing_by_VP_Basics.Day06_Tensor_Products
    Quantum_Computing_by_VP_Basics.Day07_Postulates
    Quantum_Computing_by_VP_Basics.Day08_Measurements
    Quantum_Computing_by_VP_Basics.Day09_POVMs_Entanglement
    Quantum_Computing_by_VP_Basics.Day10_Quantum_Gates
    Quantum_Computing_by_VP_Basics.Matrix_Typed
    Quantum_Computing_by_VP_Basics.Essential_Functional_Analysis
    Quantum_Computing_by_VP_Basics.Day25_Hahn_Banach
    Quantum_Computing_by_VP_Typed_Matrices.Lmat_Euclidean
    Quantum_Computing_by_VP_Typed_Matrices.Separable_Cone
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
    Quantum_Computing_by_VP_Basics
  theories
    Day05_Sylvester_Criterion
  document_files
    "root.tex"

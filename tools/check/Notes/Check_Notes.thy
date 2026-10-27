theory Check_Notes
  imports
    Quantum_Computing_by_VP.Day01_Inner_Product
    Quantum_Computing_by_VP.Day02_Trace_Projections
    Quantum_Computing_by_VP.Day03_Unitary_Matrices
    Quantum_Computing_by_VP.Day04_Hermitian_Matrices
    Quantum_Computing_by_VP.Day05_Positivity_Tests
    Quantum_Computing_by_VP.Day06_Tensor_Products
    Quantum_Computing_by_VP.Day07_Postulates
    Quantum_Computing_by_VP.Day08_Measurements
    Quantum_Computing_by_VP.Day09_POVMs_Entanglement
    Quantum_Computing_by_VP.Day09_Bell_Measurement
    Quantum_Computing_by_VP.Day10_Quantum_Gates
    Quantum_Computing_by_VP.Day11_Gates_No_Cloning
    Quantum_Computing_by_VP.Day12_Quantum_Parallelism
    Quantum_Computing_by_VP.Day13_Density_Matrices
    Quantum_Computing_by_VP.Day14_Pure_States
    Quantum_Computing_by_VP.Day15_Partial_Traces
    Quantum_Computing_by_VP.Day16_Block_Form
    Quantum_Computing_by_VP.Day17_Quantum_Noise
    Quantum_Computing_by_VP.Day18_CP_Maps
    Quantum_Computing_by_VP.Day19_Choi_Theorem
    Quantum_Computing_by_VP.Day20_Positive_Functionals
    Quantum_Computing_by_VP.Day21_Unitary_Freedom
    Quantum_Computing_by_VP.Day21_Average_Conjecture
    Quantum_Computing_by_VP.Day22_Minimal_Kraus
    Quantum_Computing_by_VP.Day22_UCP_Compact
    Quantum_Computing_by_VP.Day23_Choi_Extreme_Points
    Quantum_Computing_by_VP.Day23_Extremality_Examples
    Quantum_Computing_by_VP.Day24_Operator_Systems
    Quantum_Computing_by_VP.Day25_Hahn_Banach
    Quantum_Computing_by_VP.Day25_Arveson_Correspondence
    Quantum_Computing_by_VP.Day25_Unital_Functional_Norm
    Quantum_Computing_by_VP.Day26_Arveson_Extension
    Quantum_Computing_by_VP.Day26_Separability
    Quantum_Computing_by_VP.Day27_Detecting_Entanglement
    Quantum_Computing_by_VP.Day28_Entanglement_Witnesses
    Quantum_Computing_by_VP.Day29_Error_Correction
    Quantum_Computing_by_VP.Day30_Bit_Flip_Code
    Quantum_Computing_by_VP.Day31_Bit_Flip_Channel
    Quantum_Computing_by_VP.Day32_Phase_Flip_Code
    Quantum_Computing_by_VP.Day32_Recovery_Proposition
    Quantum_Computing_by_VP.Day33_Shor_Code
    Quantum_Computing_by_VP.Day34_Knill_Laflamme
    Quantum_Computing_by_VP.Quantum_Channels
    Essential_Functional_Analysis.Matrix_Lemmas
    Essential_Functional_Analysis.Unitary_Tensor_Algebra
    Essential_Functional_Analysis.Matrix_Typed
    Essential_Functional_Analysis.Lmat_Euclidean
begin

ML_file "../project_checks.ML"

ML \<open>Project_Checks.run {name = "Notes", audit = ["Essential_Functional_Analysis", "Quantum_Computing_by_VP"], allow = [],
  targets = ["Essential_Functional_Analysis", "Quantum_Computing_by_VP"], ignore = [], strict = true} \<^theory>\<close>

end

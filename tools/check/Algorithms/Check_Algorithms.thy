theory Check_Algorithms
  imports HHL_Algorithm.HHL_All_Elementary HHL_Algorithm.HHL_Sparse_Circuit
    HHL_Algorithm.HHL_Optimality HHL_Algorithm.QPE_Program
    HHL_Algorithm.HHL_Suzuki HHL_Algorithm.Program_Channels
    HHL_Algorithm.Reversible_Gates HHL_Algorithm.Bit_Compare HHL_Algorithm.Comparator_Scan
    HHL_Algorithm.Bennett_Uncompute HHL_Algorithm.Comparator_Registers HHL_Algorithm.Register_Swap
    HHL_Algorithm.Two_Comparisons HHL_Algorithm.Sort_Flag HHL_Algorithm.Comparator_Clean
    HHL_Algorithm.Comparator_Permutation HHL_Algorithm.Toffoli_Gates HHL_Algorithm.Gate_Routing
    HHL_Algorithm.Reversible_Compile HHL_Algorithm.Comparator_Gates HHL_Algorithm.Clean_Ancillas
    HHL_Algorithm.Simulation_Comparator HHL_Algorithm.Entry_Rotation HHL_Algorithm.Entry_Oracle
    HHL_Algorithm.Distant_Diagonals HHL_Algorithm.Rotation_Stage_Gates HHL_Algorithm.Entry_Gates
    HHL_Algorithm.Diagonal_Oracle HHL_Algorithm.Simulation_Rounded HHL_Algorithm.Simulation_Oracles
    HHL_Algorithm.Prep_Rounded HHL_Algorithm.Prep_Angle_Oracle HHL_Algorithm.Multi_Controlled_NOT
    HHL_Algorithm.Prep_Sparse HHL_Algorithm.Incrementer HHL_Algorithm.Cycle_Laplacian
    HHL_Algorithm.Wire_Gates HHL_Algorithm.Wire_Placement HHL_Algorithm.Shifted_Laplacian
    HHL_Algorithm.Controlled_Laplacian HHL_Algorithm.Phase_Estimation_Gates
    HHL_Algorithm.Gate_List_Placement HHL_Algorithm.HHL_Stage_Counts HHL_Algorithm.HHL_Laplacian
    HHL_Algorithm.HHL_Laplacian_Sparse
begin

ML_file "../project_checks.ML"

ML \<open>Project_Checks.run {name = "Algorithms", audit = ["Quantum_Computing_CP_Maps", "Hermitian_Functional_Calculus", "HHL_Algorithm"], allow = [], targets = ["HHL_Algorithm"], ignore = [], strict = true} \<^theory>\<close>

text \<open>The functional calculus against the notes: overlaps of two independent entries, reported only.\<close>

ML \<open>Project_Checks.run {name = "HFC_Notes", audit = [], allow = [], targets = ["Hermitian_Functional_Calculus"], ignore = ["HHL_Algorithm"], strict = false} \<^theory>\<close>

end

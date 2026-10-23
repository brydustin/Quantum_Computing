(*
  Title:   QC_Notes_Overview.thy
  Author:  Dustin Bryant
  Front matter of the generated document: reading guide for the formalised notes.
*)
theory QC_Notes_Overview
  imports
    Quantum_Computing_by_VP_3_10.Day01_Inner_Product
    Quantum_Computing_by_VP_3_10.Day02_Trace_Projections
    Quantum_Computing_by_VP.Day02_Projection_Basis
    Quantum_Computing_by_VP_3_10.Day03_Unitary_Matrices
    Quantum_Computing_by_VP_3_10.Day04_Hermitian_Matrices
    Quantum_Computing_by_VP.Day04_Hermitian_Converse
    Quantum_Computing_by_VP_3_10.Day05_Positivity_Tests
    Quantum_Computing_by_VP.Day05_Cholesky_Examples
    Quantum_Computing_by_VP.Day05_Direct_Sum_Basis
    Quantum_Computing_by_VP_3_10.Day06_Tensor_Products
    Quantum_Computing_by_VP.Day06_Tensor_Coordinates
    Quantum_Computing_by_VP.Day06_Schmidt_Rank
    Quantum_Computing_by_VP.Day06_15_Universal
    Quantum_Computing_by_VP_3_10.Day07_Postulates
    Quantum_Computing_by_VP_3_10.Day08_Measurements
    Quantum_Computing_by_VP.Day08_Indistinguishable_States
    Quantum_Computing_by_VP_3_10.Day09_POVMs_Entanglement
    Quantum_Computing_by_VP.Day09_Bell_Measurement
    Quantum_Computing_by_VP_3_10.Day10_Quantum_Gates
    Quantum_Computing_by_VP.Day10_Superdense_Coding
    Quantum_Computing_by_VP.Day11_Gates_No_Cloning
    Quantum_Computing_by_VP.Day11_SWAP_Circuit
    Quantum_Computing_by_VP.Day11_CCNOT_Table
    Quantum_Computing_by_VP.Day12_Quantum_Parallelism
    Quantum_Computing_by_VP.Day12_Counting_Probability
    Quantum_Computing_by_VP.Day13_Density_Matrices
    Quantum_Computing_by_VP.Day14_Pure_States
    Quantum_Computing_by_VP.Day14_Composite_Ensembles
    Quantum_Computing_by_VP.Day15_Partial_Traces
    Quantum_Computing_by_VP.Day15_Partial_Trace_A
    Quantum_Computing_by_VP.Day16_Density_Postulates
    Quantum_Computing_by_VP.Day16_Block_Form
    Quantum_Computing_by_VP.Day17_Quantum_Noise
    Quantum_Computing_by_VP.Day17_Environment_Model
    Quantum_Computing_by_VP.Day18_CP_Maps
    Quantum_Computing_by_VP.Day18_Positive_Maps
    Quantum_Computing_by_VP.Day19_Choi_Theorem
    Quantum_Computing_by_VP.Day19_Choi_Positivity
    Quantum_Computing_by_VP.Day19_Choi_TP_Unital
    Quantum_Computing_by_VP.Day20_Positive_Functionals
    Quantum_Computing_by_VP.Day20_Choi_Rank
    Quantum_Computing_by_VP.Day21_Kraus_Rank
    Quantum_Computing_by_VP.Day21_Unitary_Freedom
    Quantum_Computing_by_VP.Day21_Ranges
    Quantum_Computing_by_VP.Day21_Average_Conjecture
    Quantum_Computing_by_VP.Day21_Average_Two
    Quantum_Computing_by_VP.Day22_Convex_Sets
    Quantum_Computing_by_VP.Day22_Kraus_Independence
    Quantum_Computing_by_VP.Day22_Minimal_Kraus
    Quantum_Computing_by_VP.Day22_Adjoint_Maps
    Quantum_Computing_by_VP.Day22_UCP_Compact
    Quantum_Computing_by_VP.Day23_ChoiExtremeUCP
    Quantum_Computing_by_VP.Day23_Choi3_UCP
    Quantum_Computing_by_VP.Day23_Extremality_Examples
    Quantum_Computing_by_VP.Day24_Operator_Systems
    Quantum_Computing_by_VP_3_10.Day25_Hahn_Banach
    Quantum_Computing_by_VP.Day25_Arveson_Correspondence
    Quantum_Computing_by_VP.Day25_Unital_Functional_Norm
    Quantum_Computing_by_VP.Day26_Arveson_Extension
    Quantum_Computing_by_VP.Day26_CP_Factorization
    Quantum_Computing_by_VP.Day26_Separability
    Quantum_Computing_by_VP.Day27_Positive_Map_Criterion
    Quantum_Computing_by_VP.Day27_Entangled_Examples
    Quantum_Computing_by_VP.Day28_Horodecki_Peres
    Quantum_Computing_by_VP.Day29_Error_Correction
    Quantum_Computing_by_VP.Day29_Classical_Codes
    Quantum_Computing_by_VP.Day29_Subspace_Codes
    Quantum_Computing_by_VP.Day30_Error_Probabilities
    Quantum_Computing_by_VP.Day30_BitFlip_Code
    Quantum_Computing_by_VP.Day31_Bit_Flip_Channel
    Quantum_Computing_by_VP.Day31_Code_Fidelity
    Quantum_Computing_by_VP.Day32_Phase_Flip_Code
    Quantum_Computing_by_VP.Day32_Pauli_Expansion
    Quantum_Computing_by_VP.Day32_Y_Code
    Quantum_Computing_by_VP.Day32_Recovery_Proposition
    Quantum_Computing_by_VP.Day33_Shor_Code
    Quantum_Computing_by_VP.Day34_Knill_Laflamme
    Quantum_Computing_by_VP.Day34_KL_Sufficiency
    Quantum_Computing_by_VP.Quantum_Channels
    Quantum_Computing_by_VP_3_10.Unitary_Tensor_Algebra
    Quantum_Computing_by_VP.QC_Prelims
    Quantum_Computing_by_VP_3_10.Matrix_Typed
    Quantum_Computing_by_VP_3_10.Essential_Functional_Analysis
    Quantum_Computing_by_VP_3_10_Lmat.Lmat_Euclidean
    Quantum_Computing_by_VP_3_10_Lmat.Separable_Cone
begin

section \<open>Reading guide\<close>

text \<open>
Paulsen's course had five parts: (I) basic mathematics, (II) an introduction to
quantum computing, (III) the theory of completely positive maps, (IV) entanglement
and entanglement witnesses, (V) quantum error correction.  The theories follow the
lectures: lecture $n$ is the theory \texttt{Day}$nn$\texttt{\_}\dots{} that restates the notes,
followed by the theories that complete it (they close the gaps recorded by the audits; the
remaining unformalised items are listed in \texttt{NOTES\_AUDIT.md}).  A theory completing an
early lecture may use results of later ones; it is still printed with its lecture.

\begin{center}
\begin{tabular}{rp{0.85\linewidth}}
\textbf{Day} & \textbf{Theories}\\\hline
1 & \texttt{Day01\_Inner\_Product}\\
2 & \texttt{Day02\_Trace\_Projections}, \texttt{Day02\_Projection\_Basis}\\
3 & \texttt{Day03\_Unitary\_Matrices}\\
4 & \texttt{Day04\_Hermitian\_Matrices}, \texttt{Day04\_Hermitian\_Converse}\\
5 & \texttt{Day05\_Positivity\_Tests}, \texttt{Day05\_Cholesky\_Examples}, \texttt{Day05\_Direct\_Sum\_Basis}, \texttt{Day05\_Sylvester\_Criterion} (separate session)\\
6 & \texttt{Day06\_Tensor\_Products}, \texttt{Day06\_Tensor\_Coordinates}, \texttt{Day06\_Schmidt\_Rank}, \texttt{Day06\_15\_Universal}\\
7 & \texttt{Day07\_Postulates}\\
8 & \texttt{Day08\_Measurements}, \texttt{Day08\_Indistinguishable\_States}\\
9 & \texttt{Day09\_POVMs\_Entanglement}, \texttt{Day09\_Bell\_Measurement}\\
10 & \texttt{Day10\_Quantum\_Gates}, \texttt{Day10\_Superdense\_Coding}\\
11 & \texttt{Day11\_Gates\_No\_Cloning}, \texttt{Day11\_SWAP\_Circuit}, \texttt{Day11\_CCNOT\_Table}\\
12 & \texttt{Day12\_Quantum\_Parallelism}, \texttt{Day12\_Counting\_Probability}\\
13 & \texttt{Day13\_Density\_Matrices}\\
14 & \texttt{Day14\_Pure\_States}, \texttt{Day14\_Composite\_Ensembles}\\
15 & \texttt{Day15\_Partial\_Traces}, \texttt{Day15\_Partial\_Trace\_A}\\
16 & \texttt{Day16\_Density\_Postulates}, \texttt{Day16\_Block\_Form}\\
17 & \texttt{Day17\_Quantum\_Noise}, \texttt{Day17\_Environment\_Model}\\
18 & \texttt{Day18\_CP\_Maps}, \texttt{Day18\_Positive\_Maps}\\
19 & \texttt{Day19\_Choi\_Theorem}, \texttt{Day19\_Choi\_Positivity}, \texttt{Day19\_Choi\_TP\_Unital}\\
20 & \texttt{Day20\_Positive\_Functionals}, \texttt{Day20\_Choi\_Rank}\\
21 & \texttt{Day21\_Kraus\_Rank}, \texttt{Day21\_Unitary\_Freedom}, \texttt{Day21\_Ranges}, \texttt{Day21\_Average\_Conjecture}, \texttt{Day21\_Average\_Two}\\
22 & \texttt{Day22\_Convex\_Sets}, \texttt{Day22\_Kraus\_Independence}, \texttt{Day22\_Minimal\_Kraus}, \texttt{Day22\_Adjoint\_Maps}, \texttt{Day22\_UCP\_Compact}\\
23 & \texttt{Day23\_ChoiExtremeUCP}, \texttt{Day23\_Choi3\_UCP}, \texttt{Day23\_Extremality\_Examples}\\
24 & \texttt{Day24\_Operator\_Systems}\\
25 & \texttt{Day25\_Hahn\_Banach}, \texttt{Day25\_Arveson\_Correspondence}, \texttt{Day25\_Unital\_Functional\_Norm}\\
26 & \texttt{Day26\_Arveson\_Extension}, \texttt{Day26\_CP\_Factorization}, \texttt{Day26\_Separability}\\
27 & \texttt{Day27\_Positive\_Map\_Criterion}, \texttt{Day27\_Entangled\_Examples}\\
28 & \texttt{Day28\_Horodecki\_Peres}\\
29 & \texttt{Day29\_Error\_Correction}, \texttt{Day29\_Classical\_Codes}, \texttt{Day29\_Subspace\_Codes}\\
30 & \texttt{Day30\_Error\_Probabilities}, \texttt{Day30\_BitFlip\_Code}\\
31 & \texttt{Day31\_Bit\_Flip\_Channel}, \texttt{Day31\_Code\_Fidelity}\\
32 & \texttt{Day32\_Phase\_Flip\_Code}, \texttt{Day32\_Pauli\_Expansion}, \texttt{Day32\_Y\_Code}, \texttt{Day32\_Recovery\_Proposition}\\
33 & \texttt{Day33\_Shor\_Code}\\
34 & \texttt{Day34\_Knill\_Laflamme}, \texttt{Day34\_KL\_Sufficiency}\\
\end{tabular}
\end{center}

The last part holds what the lectures build on or lead to: \texttt{Quantum\_Channels} (standard
channels beyond the notes), \texttt{Unitary\_Tensor\_Algebra} (unitary and Kronecker-product
algebra), \texttt{QC\_Prelims} (lemmas shared by the completing theories), \texttt{Matrix\_Typed},
\texttt{Essential\_Functional\_Analysis} and \texttt{Lmat\_Euclidean} (typed matrices,
Hilbert--Schmidt analysis, Carath\'eodory), and \texttt{Separable\_Cone} (the proofs behind
\texttt{Day26\_Separability}).  The companion AFP entries \emph{Hermitian Functional Calculus} and
\emph{HHL Algorithm} go beyond the notes: the functional calculus and product formulas, quantum
phase estimation and the HHL algorithm.
\<close>

section \<open>Conventions\<close>

text \<open>
\<^item> Vectors in $\C^n$ are \<^typ>\<open>complex Matrix.vec\<close> with \<^term>\<open>dim_vec v = n\<close>; matrices in
  $M_{m,n}$ are \<^typ>\<open>complex Matrix.mat\<close> with \<^term>\<open>A \<in> carrier_mat m n\<close>
  (the Jordan-Normal-Form library).  Dimensions are hypotheses, not types, except
  in the typed wrapper \<open>lmat\<close> used for the topological arguments of Part~IV.
\<^item> The physicists' adjoint $X^\dagger = X^*$ is \<^term>\<open>A\<^sup>\<dagger>\<close>; $\braket{y}{x}$ is
  \<^term>\<open>\<langle>y|x\<rangle>\<close> (conjugate-linear in the first slot, as in the notes);
  $\ketbra{v}{w}$ is \<^term>\<open>v \<oslash> w\<close>; the Hilbert--Schmidt inner product
  $\langle Y|X\rangle = \Tr(Y^*X)$ is \<^term>\<open>\<langle>\<langle>Y|X\<rangle>\<rangle>\<close>; the matrix unit
  $E_{ij}\in M_{m,n}$ is \<^term>\<open>E\<lbrakk>i,j ; m,n\<rbrakk>\<close>.
\<^item> Indices start at $0$, as the physicists in the notes prefer: the canonical basis
  of $\C^n$ is $\ket{0},\dots,\ket{n-1}$, formally \<^term>\<open>unit_vec n i\<close>.
\<^item> $\sum_i \ketbra{v_i}{v_i}$ for a list of vectors is \<^term>\<open>outer_sum n vs\<close>
  $= V V^\dagger$ with $V$ the matrix whose columns are the $v_i$.
\<^item> Tensor products are Kronecker products: \<^term>\<open>tensor_vec v w\<close> and
  \<^term>\<open>A \<Otimes> B\<close>, with the first factor as the major index.
\<^item> Kraus sums $\sum_i W_i X W_i^\dagger$ over a list are \<^term>\<open>kraus_map_dim d Ws X\<close>.
\<close>

text \<open>
Verification status.  All theories build with \<open>quick_and_dirty = false\<close>; there are
no \<open>sorry\<close>s and no axioms beyond those of Isabelle/HOL and the imported libraries.
\<close>

end

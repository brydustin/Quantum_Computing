(*
  Title:   QC_Notes_Overview.thy
  Author:  Dustin Bryant
  Front matter of the generated document: reading guide for the formalised notes.
*)
theory QC_Notes_Overview
  imports
    Quantum_Computing_CP_Maps.Day01_Inner_Product
    Quantum_Computing_CP_Maps.Day02_Trace_Projections
    Quantum_Computing_CP_Maps.Day03_Unitary_Matrices
    Quantum_Computing_CP_Maps.Day04_Hermitian_Matrices
    Quantum_Computing_CP_Maps.Day05_Positivity_Tests
    Quantum_Computing_CP_Maps.Day05_Sylvester_Criterion
    Quantum_Computing_CP_Maps.Day06_Tensor_Products
    Quantum_Computing_CP_Maps.Day07_Postulates
    Quantum_Computing_CP_Maps.Day08_Measurements
    Quantum_Computing_CP_Maps.Day09_POVMs_Entanglement
    Quantum_Computing_CP_Maps.Day09_Bell_Measurement
    Quantum_Computing_CP_Maps.Day10_Quantum_Gates
    Quantum_Computing_CP_Maps.Day11_Gates_No_Cloning
    Quantum_Computing_CP_Maps.Day12_Quantum_Parallelism
    Quantum_Computing_CP_Maps.Day13_Density_Matrices
    Quantum_Computing_CP_Maps.Day14_Pure_States
    Quantum_Computing_CP_Maps.Day15_Partial_Traces
    Quantum_Computing_CP_Maps.Day16_Block_Form
    Quantum_Computing_CP_Maps.Day17_Quantum_Noise
    Quantum_Computing_CP_Maps.Day18_CP_Maps
    Quantum_Computing_CP_Maps.Day19_Choi_Theorem
    Quantum_Computing_CP_Maps.Day20_Positive_Functionals
    Quantum_Computing_CP_Maps.Day21_Unitary_Freedom
    Quantum_Computing_CP_Maps.Day21_Average_Conjecture
    Quantum_Computing_CP_Maps.Day22_Minimal_Kraus
    Quantum_Computing_CP_Maps.Day22_UCP_Compact
    Quantum_Computing_CP_Maps.Day23_Choi_Extreme_Points
    Quantum_Computing_CP_Maps.Day23_Extremality_Examples
    Quantum_Computing_CP_Maps.Day24_Operator_Systems
    Quantum_Computing_CP_Maps.Day25_Hahn_Banach
    Quantum_Computing_CP_Maps.Day25_Arveson_Correspondence
    Quantum_Computing_CP_Maps.Day25_Unital_Functional_Norm
    Quantum_Computing_CP_Maps.Day26_Arveson_Extension
    Quantum_Computing_CP_Maps.Day26_Separability
    Quantum_Computing_CP_Maps.Day27_Detecting_Entanglement
    Quantum_Computing_CP_Maps.Day28_Entanglement_Witnesses
    Quantum_Computing_CP_Maps.Day29_Error_Correction
    Quantum_Computing_CP_Maps.Day30_Bit_Flip_Code
    Quantum_Computing_CP_Maps.Day31_Bit_Flip_Channel
    Quantum_Computing_CP_Maps.Day32_Phase_Flip_Code
    Quantum_Computing_CP_Maps.Day32_Recovery_Proposition
    Quantum_Computing_CP_Maps.Day33_Shor_Code
    Quantum_Computing_CP_Maps.Day34_Knill_Laflamme
    Quantum_Computing_CP_Maps.Quantum_Channels
begin

section \<open>Reading guide\<close>

text \<open>
Paulsen's course had five parts: (I) basic mathematics (Days 1--7), (II) an introduction to
quantum computing (Days 8--17), (III) completely positive maps (Days 18--23), (IV) operator
systems, Arveson's theorems and entanglement (Days 24--28), (V) quantum error correction
(Days 29--34).  The theories follow the lectures: lecture $n$ is the theory
\texttt{Day}$nn$\texttt{\_}\dots{}, which restates the notes of that day and proves what they
state; some lectures continue in a further theory, for a long development or for material that
later lectures should not import (Sylvester's criterion brings in another AFP entry's names, the
Bell measurement short names like $e_0$).  Every theory builds only on earlier lectures.  A
result that the notes state before the tools of its proof are available is proved on the first
day that has them, and its statement says where: Choi's rank theorem, stated on
Day 20, is proved on Day 22 from the independence of minimal Kraus representations, and
Day 2's characterisation of orthogonal projections waits for the Hermitian matrices of Day 4.
The unformalised items are listed in \texttt{NOTES\_AUDIT.md}.

\begin{center}
\begin{tabular}{rp{0.85\linewidth}}
\textbf{Day} & \textbf{Theories}\\\hline
1 & \texttt{Day01\_Inner\_Product}\\
2 & \texttt{Day02\_Trace\_Projections}\\
3 & \texttt{Day03\_Unitary\_Matrices}\\
4 & \texttt{Day04\_Hermitian\_Matrices}\\
5 & \texttt{Day05\_Positivity\_Tests}, \texttt{Day05\_Sylvester\_Criterion}\\
6 & \texttt{Day06\_Tensor\_Products}\\
7 & \texttt{Day07\_Postulates}\\
\hline
8 & \texttt{Day08\_Measurements}\\
9 & \texttt{Day09\_POVMs\_Entanglement}, \texttt{Day09\_Bell\_Measurement}\\
10 & \texttt{Day10\_Quantum\_Gates}\\
11 & \texttt{Day11\_Gates\_No\_Cloning}\\
12 & \texttt{Day12\_Quantum\_Parallelism}\\
13 & \texttt{Day13\_Density\_Matrices}\\
14 & \texttt{Day14\_Pure\_States}\\
15 & \texttt{Day15\_Partial\_Traces}\\
16 & \texttt{Day16\_Block\_Form}\\
17 & \texttt{Day17\_Quantum\_Noise}\\
\hline
18 & \texttt{Day18\_CP\_Maps}\\
19 & \texttt{Day19\_Choi\_Theorem}\\
20 & \texttt{Day20\_Positive\_Functionals}\\
21 & \texttt{Day21\_Unitary\_Freedom}, \texttt{Day21\_Average\_Conjecture}\\
22 & \texttt{Day22\_Minimal\_Kraus}, \texttt{Day22\_UCP\_Compact}\\
23 & \texttt{Day23\_Choi\_Extreme\_Points}, \texttt{Day23\_Extremality\_Examples}\\
\hline
24 & \texttt{Day24\_Operator\_Systems}\\
25 & \texttt{Day25\_Hahn\_Banach}, \texttt{Day25\_Arveson\_Correspondence}, \texttt{Day25\_Unital\_Functional\_Norm}\\
26 & \texttt{Day26\_Arveson\_Extension}, \texttt{Day26\_Separability}\\
27 & \texttt{Day27\_Detecting\_Entanglement}\\
28 & \texttt{Day28\_Entanglement\_Witnesses}\\
\hline
29 & \texttt{Day29\_Error\_Correction}\\
30 & \texttt{Day30\_Bit\_Flip\_Code}\\
31 & \texttt{Day31\_Bit\_Flip\_Channel}\\
32 & \texttt{Day32\_Phase\_Flip\_Code}, \texttt{Day32\_Recovery\_Proposition}\\
33 & \texttt{Day33\_Shor\_Code}\\
34 & \texttt{Day34\_Knill\_Laflamme}\\
\end{tabular}
\end{center}

The last part, \texttt{Quantum\_Channels}, collects standard channels beyond the notes.  What the
lectures build on but do not teach is the parent session \emph{Essential Functional Analysis}:
general matrix lemmas (\texttt{Matrix\_Lemmas}), unitary and Kronecker-product algebra
(\texttt{Unitary\_Tensor\_Algebra}), and matrices of fixed dimension as a type, with the
Hilbert--Schmidt norm (\texttt{Matrix\_Typed}) and the structure of a Euclidean space
(\texttt{Lmat\_Euclidean}).  The companion AFP entries \emph{Hermitian Functional Calculus} and
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

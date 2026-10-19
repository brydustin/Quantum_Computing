(*
  Title:   QC_Notes_Overview.thy
  Author:  Dustin Bryant
  Front matter of the generated document: reading guide for the formalised notes.
*)
theory QC_Notes_Overview
  imports
    Vern_Paulsen_QC.Day23_ChoiExtremeUCP
    Vern_Paulsen_QC.Day24_Separability
    Vern_Paulsen_QC.Day12_Counting_Probability
    Vern_Paulsen_QC.Day18_Positive_Maps
    Vern_Paulsen_QC.Day22_Kraus_Independence
    Vern_Paulsen_QC.Day28_Horodecki_Peres
    Vern_Paulsen_QC.Day30_BitFlip_Code
    Vern_Paulsen_QC.Day32_Pauli_Expansion
    Vern_Paulsen_QC.Day21_Unitary_Freedom
begin

section \<open>Reading guide\<close>

text \<open>
Paulsen's course had five parts: (I) basic mathematics, (II) an introduction to
quantum computing, (III) the theory of completely positive maps, (IV) entanglement
and entanglement witnesses, (V) quantum error correction.  The formal development
keeps the mathematics of the notes but is organised by theory, since later lectures
reuse earlier infrastructure.  The table gives the correspondence.

\begin{center}
\begin{tabular}{lll}
\textbf{Lectures} & \textbf{Topic} & \textbf{Theory}\\\hline
1--2   & inner products, matrix units, trace, projections, Parseval & \isa{Basic{\isacharunderscore}Math}\\
3--10  & unitaries, Schur, Hermitian and positive matrices, tensor products, postulates, POVMs, gates & \isa{Quantum{\isacharunderscore}Computing{\isacharunderscore}{\isadigit{3}}{\isacharunderscore}{\isadigit{1}}{\isadigit{0}}}\\
11--22 & no-cloning, oracles, density matrices, partial traces, CP maps, Choi's theorem, adjoints, convexity & \isa{Quantum{\isacharunderscore}Computing{\isadigit{1}}{\isadigit{1}}}\\
23     & extreme points of CPTP/UCP maps (Choi's Theorem~3), CP Radon--Nikodym & \isa{Day{\isadigit{2}}{\isadigit{3}}{\isacharunderscore}ChoiExtremeUCP}\\
25     & Hahn--Banach on matrix spaces & \isa{Matrix{\isacharunderscore}Typed}\\
--     & Hilbert--Schmidt analysis, Carath\'eodory, typed matrices as a Euclidean space & \isa{Essential{\isacharunderscore}Functional{\isacharunderscore}Analysis}, \isa{Lmat{\isacharunderscore}Euclidean}\\
26--28 & separable cone, separating hyperplanes, entanglement witnesses & \isa{Separable{\isacharunderscore}Cone}, \isa{Day{\isadigit{2}}{\isadigit{4}}{\isacharunderscore}Separability}\\
29--32 & classical codes, bit/phase-flip channels, fidelity, Pauli algebra & \isa{Quantum{\isacharunderscore}Computing{\isadigit{1}}{\isadigit{1}}}\\
\end{tabular}
\end{center}

Lectures 24 and 26 (operator systems, Arveson's extension theorem and
correspondence), the Choi-rank theorem and unitary freedom of Kraus
representations (lectures 20--21), and the Shor code and Knill--Laflamme
conditions (lectures 32--34) are not formalised; see \texttt{NOTES\_AUDIT.md}.
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

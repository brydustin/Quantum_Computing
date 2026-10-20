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
    Vern_Paulsen_QC.Day32_Recovery_Proposition
    Vern_Paulsen_QC.Day22_Minimal_Kraus
    Vern_Paulsen_QC.Day34_Knill_Laflamme
    Vern_Paulsen_QC.Day20_Choi_Rank
    Vern_Paulsen_QC.Day34_KL_Sufficiency
    Vern_Paulsen_QC.Day33_Shor_Code
    Vern_Paulsen_QC.Day17_Environment_Model
    Vern_Paulsen_QC.Day27_Positive_Map_Criterion
    Vern_Paulsen_QC.Day02_11_Supplement
    Vern_Paulsen_QC.Day29_Classical_Codes
    Vern_Paulsen_QC.Day31_Code_Fidelity
    Vern_Paulsen_QC.Day32_Y_Code
    Vern_Paulsen_QC_Algorithms.HHL
    Vern_Paulsen_QC_Algorithms.QFT_Fourier
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
29--32 & classical codes, bit/phase-flip channels, fidelity, Pauli algebra & \isa{Quantum{\isacharunderscore}Computing{\isadigit{1}}{\isadigit{1}}}\\\hline
12     & $H^{\otimes N}\ket{0\cdots0}$, the counting probability & \texttt{Day12\_Counting\_Probability}\\
17     & the environment model of noise, $\tr_E(U(\rho\otimes\ketbra\varphi\varphi)U^*)=\sum W_i\rho W_i^*$ & \texttt{Day17\_Environment\_Model}\\
17--18 & densities to densities iff positive and TP; the transpose & \texttt{Day18\_Positive\_Maps}\\
20     & $\crk(\Phi)=\rank P_\Phi$ & \texttt{Day20\_Choi\_Rank}\\
21     & rank-one decompositions and Kraus representations up to an isometry (Choi 2) & \texttt{Day21\_Unitary\_Freedom}\\
22     & $\crk(\Phi)\le n$ for extreme maps; minimal Kraus lists are independent & \texttt{Day22\_Kraus\_Independence}, \texttt{Day22\_Minimal\_Kraus}\\
24     & operator systems, $M_p(S)$, completely positive maps on $S$ & \texttt{Day24\_Operator\_Systems}\\
24--25 & Arveson: CP $\iff$ $d$-positive $\iff$ $S_\Phi\ge0$; the correspondence $\Phi\leftrightarrow S_\Phi$ & \texttt{Day25\_Arveson\_Correspondence}\\
26     & Arveson's extension theorem; Kraus form on operator systems & \texttt{Day26\_Arveson\_Extension}\\
27--28 & positive maps and separability: $f(\mathrm{Sep})\ge0\iff\Phi_f$ positive, the positive-map criterion & \texttt{Day27\_Positive\_Map\_Criterion}\\
28     & the two-qubit Horodecki--Peres criterion & \texttt{Day28\_Horodecki\_Peres}\\
30     & the three-qubit bit-flip code and its recovery theorem & \texttt{Day30\_BitFlip\_Code}\\
32--33 & Pauli expansion of unitaries; the general recovery proposition & \texttt{Day32\_Pauli\_Expansion}, \texttt{Day32\_Recovery\_Proposition}\\
32--33 & the nine-qubit Shor code and Shor's theorem & \texttt{Day33\_Shor\_Code}\\
34     & Knill--Laflamme: states vs.\ $PXP$, Theorem~1 (both directions), closure & \texttt{Day34\_Knill\_Laflamme}, \texttt{Day34\_KL\_Sufficiency}\\\hline
2--11  & basis-independent projections, tensor coordinates, non-orthogonal states, a Bell measurement, SWAP from CNOTs & \texttt{Day02\_11\_Supplement}\\
29--30 & the notes' Hamming code, the $[7,4,3]$ code, undetected-error probabilities & \texttt{Day29\_Classical\_Codes}\\
31     & the bit-flip code against independent flips: $R\circ E$, minimum fidelities & \texttt{Day31\_Code\_Fidelity}\\
32     & the code for $Y$ flips; codes with orthogonal error images & \texttt{Day32\_Y\_Code}\\\hline
--     & functional calculus $g(A)$ for Hermitian $A$; $e^{itA}$, $A^{-1}$ & \texttt{Hermitian\_Functional\_Calculus}\\
--     & Fourier matrix, phase kickback, phase estimation (exact; $\ge4/\pi^2$) & \texttt{Phase\_Estimation}\\
--     & the AFP circuit \<open>ordered_QFT\<close> is the Fourier matrix $F_{2^n}$ & \texttt{QFT\_Fourier}\\
--     & the HHL algorithm: output state, $Ax=b$, success $\ge1/\kappa^2$, non-Hermitian $A$ & \texttt{HHL}\\
\end{tabular}
\end{center}

The theories of the second and third blocks (shared lemmas in \texttt{QC\_Prelims}) close
the gaps recorded by the first and second audits; the remaining unformalised items are listed in
\texttt{NOTES\_AUDIT.md}.  The last block, Part~VI, goes beyond the notes (session
\texttt{Vern\_Paulsen\_QC\_Algorithms}).
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

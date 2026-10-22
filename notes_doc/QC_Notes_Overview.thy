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
    Vern_Paulsen_QC_Algorithms.HHL_Sparse_Circuit
    Vern_Paulsen_QC_Algorithms.HHL_All_Elementary
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
2--11  & basis-independent projections, a basis of $V\oplus W$, tensor coordinates, non-orthogonal states, a Bell measurement, SWAP from CNOTs & \texttt{Day02\_11\_Supplement}\\
29--30 & the notes' Hamming code, the $[7,4,3]$ code, undetected-error probabilities & \texttt{Day29\_Classical\_Codes}\\
31     & the bit-flip code against independent flips: $R\circ E$, minimum fidelities & \texttt{Day31\_Code\_Fidelity}\\
32     & the code for $Y$ flips; codes with orthogonal error images & \texttt{Day32\_Y\_Code}\\
19     & trace preservation and unitality read off the Choi matrix & \texttt{Day19\_Choi\_TP\_Unital}\\
23     & extreme and non-extreme CPTP maps: $U^*XU$, averages, $\Tr(X)I/d$, diagonals & \texttt{Day23\_Extremality\_Examples}\\
25     & a unital functional is positive iff it has norm one & \texttt{Day25\_Unital\_Functional\_Norm}\\
5      & Sylvester's criterion, imported from the AFP (separate session and PDF, see Day~5) & \texttt{Day05\_Sylvester\_Criterion}\\
5      & Cholesky's algorithm on the notes' two $3\times3$ examples; the rank-one decomposition & \texttt{Day05\_Cholesky\_Examples}\\
22     & the adjoint $\Phi^*$ of a linear map; $\Gamma(\Phi)=\Phi^*$ is an affine bijection UCP $\to$ CPTP & \texttt{Day22\_Adjoint\_Maps}\\
22     & UCP$(M_n,M_d)$ is compact (in Choi coordinates) & \texttt{Day22\_UCP\_Compact}\\
6, 15  & universal properties: bilinear maps factor uniquely through $v\otimes w$; $\Gamma(R\otimes T)=R\otimes T$ determines $\Gamma$ & \texttt{Day06\_15\_Universal}\\
21     & the conjecture D21-2 stated; Fourier mixing, measurement maps, Horn's lemma, diagonal-valued maps; form (i) false & \texttt{Day21\_Average\_Conjecture}\\
23     & Choi's Theorem~3 for unital maps, via the adjoint & \texttt{Day23\_Choi3\_UCP}\\
16     & $H_A\otimes H_B\cong H_A^{(p)}$ isometrically; $X=\sum X_{ij}\otimes E_{ij}$; block action, partial traces & \texttt{Day16\_Block\_Form}\\
6, 10  & the Schmidt rank: rank $1$ iff a product state, entangled iff rank $>1$ & \texttt{Day06\_Schmidt\_Rank}\\
10--15 & superdense coding table, the CCNOT truth table, the partial trace over $A$ & \texttt{Day10\_15\_Supplement}\\
4--29  & converse Hermitian tests, composite ensembles, Choi's four conditions, subspace codes & \texttt{Day04\_29\_Supplement}\\
4, 21  & $0\le ww^*\le P\Rightarrow w\in R(P)$; $R(\sum w_lw_l^*)=\operatorname{span}\{w_l\}$; $\sum v_iv_i^*>0$ iff the $v_i$ span & \texttt{Day21\_Ranges}\\
26     & CP maps as $V^*\psi(X)V$ with $\psi$ UCP and as $\psi(VXV^*)$ with $\psi$ CPTP & \texttt{Day26\_CP\_Factorization}\\
27     & the transpose detects $\left(\begin{smallmatrix}E_{ii}&E_{ij}\\ E_{ji}&E_{jj}\end{smallmatrix}\right)$ and $(E_{ij})$ as entangled & \texttt{Day27\_Entangled\_Examples}\\\hline
--     & functional calculus $g(A)$ for Hermitian $A$; $e^{itA}$, $A^{-1}$ & \texttt{Hermitian\_Functional\_Calculus}\\
--     & Fourier matrix, phase kickback, phase estimation (exact; $\ge4/\pi^2$) & \texttt{Phase\_Estimation}\\
--     & the AFP circuit \<open>ordered_QFT\<close> is the Fourier matrix $F_{2^n}$ & \texttt{QFT\_Fourier}\\
--     & the HHL algorithm: output state, $Ax=b$, success $\ge1/\kappa^2$, non-Hermitian $A$ & \texttt{HHL}\\
--     & inexact phase estimation: the error identity; for the clamped circuit and every $b$, $\norm{\text{output}-\text{ideal}}^2\le\frac{\pi^2}{Nt_0^2}\bigl(\frac{\theta^4}{C^2(1-\theta^2)}+\frac{16}{\lambda_{\min}^2}\bigr)\norm b^2$ & \texttt{HHL\_Approximate}\\
--     & sine-window register: amplitudes decay like $1/(N\delta)^2$; for every $b$, $\norm{\text{output}-\text{ideal}}^2\le\bigl(\frac{8\pi^2(2+\pi^2)\theta^4}{N^2t_0^2C^2(1-\theta^2)}+\frac{512\pi^6}{N^3t_0^4\lambda_{\min}^4}\bigr)\norm b^2$, so $N\sim1/\varepsilon$ suffices & \texttt{HHL\_Window}\\
--     & circuits with oracle calls: HHL makes $2(N-1)$ calls of $e^{iAt_0}$; an oracle $V$ with $\norm{Vv-e^{iAt_0}v}\le\eta\norm v$ moves the output by at most (calls)$\cdot\eta$; end to end $\norm{\text{output}-\text{ideal}}\le(\varepsilon+2(N-1)\eta)\norm b$ & \texttt{HHL\_Simulation}\\
--     & readout by post-selection, stable to $2\delta/(C\norm{A^{-1}b})$; amplitude amplification ($k$ rounds give $\sin^2((2k+1)\theta)$); the complete algorithm: success $\ge1-p$ with $k\le\pi^2/(4Ct_0)$ rounds and $(2k+1)\cdot2(N-1)$ oracle calls & \texttt{HHL\_Complete}\\
--     & the paper's filter functions and flag register; Lemma 2; Lemma 3 with the corrected constant $\pi^2$ & \texttt{HHL\_Filter}\\
--     & Theorem 1 of the HHL paper for every $b$: errors $O(\kappa/t)$, $t$ the total evolution time & \texttt{HHL\_Filter\_Bounds}\\
--     & (A32), BHMT averaging, run time in the paper's normalisation: $t=O(\kappa/\varepsilon)$, $O(\kappa)$ rounds & \texttt{HHL\_Runtime}\\
--     & the reduction from circuits to matrix inversion (Section III): $A^{-1}$, $\kappa\le2T+1$, post-selection probability $\ge1/10$ & \texttt{HHL\_Reduction}\\
--     & rectangular $A$ (App.~A4): $\left(\begin{smallmatrix}0&A\\A^*&0\end{smallmatrix}\right)$, its pseudo-inverse gives the minimum-norm and the least-squares solution & \texttt{HHL\_Rectangular}\\
--     & Section IV: $f(A)\ket b$, stability of $\langle x|M|x\rangle$, sampling, $k$ copies, the SWAP test, estimation with $3/\varepsilon^2$ samples, preconditioning & \texttt{HHL\_Discussion}\\
--     & Theorems 4--6 (App.~A5): the $M_0$ measurement, the Hermitian dilation, the first-qubit embedding, the speedup iteration and the exponent bounds; the search lower bound is imported from the AFP (separate session) & \texttt{HHL\_Optimality}\\
--     & the clock register: $H^{\otimes n}\ket{0\cdots0}$ and $F\ket0$ are uniform (AFP \texttt{Isabelle\_Marries\_Dirac}), and $H^{\otimes n}$ resets it & \texttt{QPE\_Register}\\
--     & the HHL circuit gate by gate: the state after each of the eight gates, for every $\ket b$ & \texttt{HHL\_Trajectory}\\
--     & HHL as a program of quantum Hoare logic (AFP \texttt{QHLProver}): initialisation, state preparation, circuit, measurement, repeat-until-success; success probability, correctness, termination & \texttt{HHL\_Program}\\
--     & the program in elementary gates: $H^{\otimes k}$ as $k$ Hadamards, one controlled $U^{2^j}$ per clock qubit, $F$ as the AFP gate-level Fourier circuit; same theorems; $(2k^3+16k+6)/3$ gates & \texttt{HHL\_Gates}\\
--     & the program on a preconditioned system $BAx=Bb$ via the Hermitian dilation of $BA$: output $\hat x$ for $Ax=b$, success probability $\ge(C/\norm{BA})^2$ & \texttt{HHL\_Preconditioned}\\
--     & the repeat-until-success loop terminates with probability one (total correctness); it exits after $m$ failed rounds with probability $(1-p)^mp$ in the target state; expected rounds $1/p$, $p=C^2\norm{A^{-1}b}^2$ & \texttt{HHL\_Termination}\\
--     & the paper's regime as programs: window register, inexact eigenvalues, approximate oracle, filtered version; fidelity triples, termination, amplitude amplification as a program & \texttt{HHL\_Paper\_Program}\\
--     & the rotation as one ancilla rotation per clock value; window state by one reflection; elementary Fourier gates in the amplified circuit & \texttt{HHL\_Gate\_Refinements}\\
--     & the rotation stage as a uniformly controlled rotation: Walsh--Hadamard angles, parity chains of nearest-neighbour CNOT/SWAP gates; the program and the paper-regime circuits with only elementary gates, oracle calls, $U_b$ and rotations controlled by the last clock qubit & \texttt{HHL\_Uniform\_Rotation}\\
--     & state preparation by $k$ levels of uniformly controlled rotations, all gates elementary; the sine window; the paper-regime programs with only elementary gates, controlled ancilla rotations, $U_b$ and oracle calls & \texttt{HHL\_State\_Preparation}\\
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

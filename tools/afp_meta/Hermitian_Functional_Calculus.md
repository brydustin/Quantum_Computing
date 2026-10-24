# AFP submission: Hermitian_Functional_Calculus

Fields of the submission form at https://isa-afp.org/submission/

- **Title:** The Functional Calculus of Hermitian Matrices and Product Formulas
- **Short name:** Hermitian_Functional_Calculus
- **Author:** Dustin Bryant (brydustin@gmail.com)
- **Topics (suggested):** Mathematics/Algebra; Mathematics/Analysis; Computer science/Algorithms/Quantum computing
- **License:** BSD
- **Archive:** `Hermitian_Functional_Calculus.tar.gz` (the folder `Hermitian_Functional_Calculus/`)
- **Depends on (AFP):** Jordan_Normal_Form, Isabelle_Marries_Dirac, QHLProver; Isabelle: HOL-Analysis (L2_Norm only)

## Abstract

For a Hermitian matrix $A$ and a function $g:\mathbb{R}\to\mathbb{C}$ we define $g(A)$ as the
matrix that multiplies every eigenvector of $A$ with eigenvalue $\lambda$ by $g(\lambda)$, and
prove the algebra of this functional calculus: it is linear in $g$, $g(A)\,h(A)=(gh)(A)$,
$g(A)^*=\bar g(A)$, $g(A)^k=(g^k)(A)$, $g(f(A))=(g\circ f)(A)$ for real $f$, $g(A)$ is unitary when
$|g|=1$ on the spectrum, and $g(A)$ depends only on the values of $g$ on the spectrum. Special cases are the time evolution $e^{itA}$, with $e^{isA}e^{itA}=e^{i(s+t)A}$, and the
inverse. On top of it we verify the Lie–Trotter product formula with an explicit error bound,
$\|(e^{itH_1/r}\cdots e^{itH_m/r})^r-e^{it(H_1+\dots+H_m)}\|\le 2(mLt)^2/r$ for Hermitian $H_j$ of
norm at most $L$, and Suzuki's higher-order product formulas: the order conditions (palindromic
formulas have odd order; Suzuki's recursion $S_{2k+2}$ agrees with $e^{itH}$ up to degree $2k+2$
of the Taylor expansion) and the error bound
$r(2|F|+1)(\Lambda|t|/r)^{2k+3}e^{\Lambda|t|/r}/(2k+3)!$ for $r$ steps of a formula with $|F|$
factors and total weight $\Lambda$. The matrices are those of Jordan_Normal_Form; the spectral
theorem is derived from the Schur decomposition of QHLProver.

## Comment for the editors

- Builds with Isabelle2025-2 and the AFP of 2026-04-09 in about 30 s; no `sorry`, no oracles
  (checked with `Thm_Deps.all_oracles` over all theorems).
- The entry uses QHLProver's `hermitian` and Schur decomposition and IMD's adjoint $M^\dagger$,
  `unitary` and vector norm; QHLProver's and IMD's names `unitary`, `inner_prod` clash, and the
  theories import Complex_Matrix before Quantum so that `unitary` is IMD's. IMD's gate constants
  `X, Y, Z, H, S, T` are hidden (open) so that matrix variables of these names can be used.
- A redundancy check against the AFP (Jordan_Normal_Form, IMD, QHLProver, Commuting_Hermitian,
  Projective_Measurements, Two_Hermitian_Results) finds one duplicate: the two-line lemma
  `dagger_adjoint` (IMD's dagger is QHLProver's adjoint), which Projective_Measurements also
  proves; importing Projective_Measurements (and with it HOL-Probability) for it seemed excessive.
- Six short lemmas also occur in the entry Quantum_Computing_by_VP (submitted at the same time):
  `dagger_carrier`, `unitary_dagger`, `unitary_mult`, `cpx_vec_length_smult`, `one_smult_mat`,
  `unitary_square_dim`.
  Neither entry imports the other, so both state them.
- We found no matrix exponential on Jordan_Normal_Form matrices and no Trotter or Suzuki
  formula in the AFP. Matrices_for_ODEs has the exponential of real square matrices (HOL-Analysis
  types); the time evolution here is defined through the spectral decomposition instead.
- The theory `Functional_Calculus_Overview` imports all parts; its section "Using the entry"
  (first in the document) lists the main constants and lemmas, with two worked examples.
- This entry is used by the entry HHL_Algorithm (submitted at the same time).

# Functional-analysis facts used by Vern_Paulsen_QC, and what the AFP already offers

Date: 2026-10-18.  Local AFP mirror: `afp-2026-04-09` (registered via `-d .../afp-2026-04-09/thys`).
Online check of the AFP topic pages (Mathematics/Analysis, Quantum computing) on
2026-10-18: the only functional-analysis entry newer than the mirror is
*The Gelfand–Naimark–Segal Construction* (Mar 2026, C*-algebras on top of
`Complex_Bounded_Operators`).  No AFP entry covers Choi's theorem, CP
Radon–Nikodym, extreme points of CPTP maps, or Horodecki witnesses.

## 1. What the project uses (all proved, no `sorry`, no oracles — see §4)

| Project fact | Where | Representation |
|---|---|---|
| Schur triangularisation → spectral theorem for hermitian matrices, `psd ⟺` non-negative eigenvalues, `psd_kraus_decomp` (`P = Σ vᵢvᵢ†`), `psd_sqrt` | `Quantum_Computing_3_10.thy` | JNF `complex Matrix.mat` |
| Hilbert–Schmidt inner product / norm on matrices, parallelogram, entry bounds, HS-Cauchy ⇒ convergent (completeness), hermitian/psd cones closed | `Essential_Functional_Analysis.thy` §1–§5 | JNF matrices |
| Carathéodory for conic combinations of matrices (`caratheodory_matrix_cone`) | `Essential_Functional_Analysis.thy` §6 | JNF matrices + `vec_space` dimension bound |
| Hahn–Banach extension of real-part functionals, with norm bound (`matrix_hahn_banach_lmat*`) | `Matrix_Typed.thy` (via `HOL-Hahn_Banach`) | typed wrapper `lmat` |
| `lmat` as `real_inner` / `euclidean_space` / `heine_borel` | `Lmat_Euclidean.thy` | `('a,'k,'l) lmat` |
| Separable cone closed & compact pieces, separating hyperplane, entanglement witnesses (Horodecki) | `Separable_Cone.thy`, `Day24_Separability.thy` | `lmat` + `HOL-Analysis.separating_hyperplane_closed_point` |
| Loewner kernel inclusion (`loewner_ker_subset`), Moore–Penrose pseudoinverse of a hermitian spectral decomposition (`pinv_list`, `A_Aplus_A_eq`, `A_Aplus_B_eq_B`), dominated-PSD parametrisation (`dominated_outer_sum_param`), CP Radon–Nikodym (`cp_radon_nikodym_choi/_linear`), Choi's theorem 3 on extreme CPTP maps | `Day23_ChoiExtremeUCP.thy` | JNF matrices |

## 2. AFP entries with overlapping content

| AFP entry (date) | What it has | Representation | Reusable here? |
|---|---|---|---|
| `Jordan_Normal_Form` (already imported) | `Schur_Decomposition` (`schur_theorem`, used by the project), `Gram_Schmidt`, `DL_Rank`, `Spectral_Radius`, `VS_Connect` | `complex mat` | Yes — already the base. |
| `Isabelle_Marries_Dirac` (already imported) | `dagger`, `unitary`, kets/bras, gates, tensor products, `unitary_unit_col` | `complex mat` | Yes — already the base. |
| `QHLProver` (2019) | `positive` (= project `psd`, proved hermitian in `positive_is_hermitian`), `positive_iff_decomp` (`A = M M†`), `lowner_le` (Loewner order on matrices), `unitary_schur_decomposition`, `normal_complex_mat_has_spectral_decomposition`, `hermitian_eigenvalue_real`, Loewner-increasing limits (`lowner_lub_*`) | `complex mat` (JNF) with its own `adjoint`, `inner_prod` | Partly. Same matrix type, but its `adjoint`/`hermitian` names clash with IMD's `dagger`/project `hermitian`; importing it would mean renaming or qualifying.  Useful if a Loewner-limit argument is ever needed. |
| `Projective_Measurements` (2021) | `Linear_Algebra_Complements`: `projector`, `rank_1_proj`, `sum_mat_positive`, Kronecker helpers; CHSH inequality | `complex mat`, locale `cpx_sq_mat` | Marginal; the project has its own `outer_prod`/`outer_sum` API. |
| `Commuting_Hermitian` (2022) | `hermitian_real_diag_sorted`, simultaneous diagonalisation `commuting_hermitian_family_diag`, `Spectral_Theory_Complements` | `complex mat` (JNF) | Only if commuting families are needed (not in Paulsen's notes). |
| `Two_Hermitian_Results` (2024) | Sylvester's criterion, Courant–Fischer, Cauchy interlacing, Schur complement determinant | `complex mat` (JNF) | Not needed by the notes. |
| `Complex_Bounded_Operators` (2021) | `cblinfun` bounded operators, adjoints, unitaries, projections `Proj`, Loewner order on operators, BLT extension; `Cblinfun_Matrix` bridge to JNF matrices | type-level finite dims, `'a ⇒ᶜᴸ 'b` | Different world.  A bridge exists (`mat_of_cblinfun`), but every project statement is quantified over `n` (`carrier_mat n n`), which the type-indexed operators cannot express without `With_Type`-style tricks. |
| `Hilbert_Space_Tensor_Product` (2024) | `Positive_Operators` (`sqrt_op`, `abs_op`, polar decomposition, `sandwich_mono`), `Trace_Class` (`trace_class`, `hilbert_schmidt` typedef, HS norm), `Spectral_Theorem` (compact operators), `Partial_Trace`, `Von_Neumann_Algebras`, double commutant | `cblinfun` | Same caveat as above; conceptually covers the HS-space material of `Essential_Functional_Analysis`, but not over `complex mat`. |
| `Kraus_Maps` (Jun 2025) | `kraus_family`, `kraus_map`, composition, tensor, `km_trace_preserving`, complete measurements, infinite sums | `trace_class` operators on `chilbert_space` | No Choi matrix, no CP⇔Kraus theorem, no Radon–Nikodym; built on `cblinfun`.  The project's Day 11/23 results are not in it. |
| `Banach_Steinhaus` (2020), `Lp` (2016) | uniform boundedness; Lᵖ spaces | real/complex normed spaces | Not needed (finite-dimensional setting). |
| `Gelfand_Naimark_Segal` (Mar 2026, not in local mirror) | C*-algebra class + locale, GNS representation | abstract class / `cblinfun` example | Not needed for the notes; relevant only for an operator-algebraic reformulation. |
| `HOL-Hahn_Banach` (distribution, already imported) | Hahn–Banach for real vector spaces as locales | locale-based | Already used by `Matrix_Typed`. |
| `HOL-Analysis` (distribution) | `separating_hyperplane_closed_point`, `_closed_0`, `_compact_closed_*`, `convex_hull_caratheodory`, `caratheodory_aff_dim` | `euclidean_space` types | Already used by `Separable_Cone` through the `lmat` instances. The conic Carathéodory in `Essential_Functional_Analysis` was proved directly because HOL-Analysis only has the convex-hull form. |

## 3. Assessment

* Everything in §1 is proved locally; nothing is imported as an axiom.
* The matrix-level results of Day 23 (CP Radon–Nikodym, dominated-PSD
  parametrisation via the pseudoinverse, Choi's extreme-point theorem) and
  Day 24–28 (Horodecki witness criterion) have no AFP counterpart in any
  representation.  They are candidates for an AFP submission on top of
  `Jordan_Normal_Form` + `Isabelle_Marries_Dirac`.
* The only AFP material that could replace project lemmas without changing
  the matrix representation is in `QHLProver` (`positive`, `lowner_le`,
  `positive_iff_decomp`); switching would cost a rename pass and buy little,
  so it is not recommended now.
* `Complex_Bounded_Operators` / `Hilbert_Space_Tensor_Product` / `Kraus_Maps`
  are the modern general-Hilbert-space stack.  They are the right target if
  the development is ever generalised beyond finite dimensions, but they are
  not a drop-in for anything here.

## 4. Verification status (2026-10-18)

* Active sessions (`ROOT`): `Vern_Paulsen_QC_3_10`, `Vern_Paulsen_QC_3_10_Lmat`,
  `Vern_Paulsen_QC`.  All build with `quick_and_dirty = false`.
* `grep sorry` over the active theories: 0 (the one `sorry` in
  `Quantum_Computing_3_10.thy` is inside a block comment).
* Oracle audit: an auxiliary theory importing `Day23_ChoiExtremeUCP`,
  `Day24_Separability` and `Essential_Functional_Analysis` ran
  `Thm_Deps.all_oracles` on the main theorems.  With `quick_and_dirty = true`
  this reports `Pure.skip_proof` on everything downstream of a `fun` or
  `record` (Isabelle's `Goal.prove_sorry` cheats on package-internal
  proofs in that mode); with `quick_and_dirty = false` it reports none.
* Not part of the build: `Quantum_Computing.thy` (old monolith; its 5
  `sorry` tokens are all inside comments) and `Quantum_Computing_OLD.thy`.

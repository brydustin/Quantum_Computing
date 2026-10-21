# Formalisation diary

Findings that the formalisation revealed about the notes, recorded as they happen.
The per-item record is `NOTES_AUDIT.md`; this file keeps the observations behind it.

## Gap-closure push, 2026-10-19 (remaining items)

- **Day 32 recovery proposition (D32-4).** The notes assume the error operators U_i are
  unitary.  The proof only uses PU_i*U_jP = δ_ij P (the case i = j holds for unitaries).
  `recovery_setting` now states this weaker hypothesis; `recovery_setting_unitaries`
  recovers the notes' form.
- **Knill–Laflamme sufficiency (D34-2 ⟸).** With the weaker recovery proposition, the
  standard construction needs no extension of partial isometries to unitaries: α is
  Hermitian (from P ≠ 0); diagonalise α = u diag(d) u*; the mixed errors F_k = Σ_i u_ik E_i
  give the same channel (`kraus_mix_same_map`), satisfy PF_k*F_lP = δ_kl d_k P, have d_k ≥ 0
  (trace argument), Σ d_k = Tr α = 1, and F_kP = 0 when d_k = 0.  The recovery map is
  `recovery_ops` for the F_k/√d_k with d_k > 0.  (`Day34_KL_Sufficiency`.)
- **Day 32 orthogonality proposition (D32-5) is false as stated.** "Distinct 1-Paulis U ≠ W
  give UV ⊥ WV" fails: Z_1 ≠ Z_2 as operators, yet Z_1|0_L⟩ = Z_2|0_L⟩ (unit vector), so
  ⟨Z_1|0_L⟩, Z_2|0_L⟩⟩ = 1 (`shor_notes_Z1_Z2`).  The notes fix this on Day 33 by keeping only
  Z_1, Z_4, Z_7 and proving Z_1v = Z_2v = Z_3v on V (D33-1, `shor_Z_coincide`).
- **Count in Day 33.** The orthogonal family is V, X_1V..X_9V, Y_1V..Y_9V, Z_1V, Z_4V, Z_7V:
  22 subspaces (the "3·9+1" counts the 28 tensors, not the subspaces).  Our own commentary
  had said "28 orthogonal subspaces"; corrected.
- **Shor code proof technique.** Never compute in 512 dimensions: `qubit_op (3b+s) U` =
  `blk b (bop s U)` (tensor associativity), the code words are triple tensors of the block
  vectors |m⟩ ± |7−m⟩, each error moves one block label, inner products factor
  (`tensor_inner_prod`), and orthogonality of all 22 images is distinctness of 44 labels
  (`code_simp`, 1 s).  Shor's theorem then follows from the recovery proposition and the
  Pauli expansion identity.  (`Day33_Shor_Code`.)
- **Environment model (D17-3).** Proved as stated, with the index of ℂ^m⊗ℂ^p read as a·p+i
  (the notes' block form indexes blocks by the environment; the identity is the same up to
  this ordering).  Only ⟨φ|φ⟩ = 1 and U*U = I are used.  (`Day17_Environment_Model`.)
- **Arveson's extension theorem (D26-2), a different route.** The notes extend the state S_Φ
  by Hahn–Banach and need two lemmas (D25-4: a unital functional is positive iff it has norm
  one; D26-1: reduction to the unital case).  The formalisation extends the positive
  functional S_Φ directly: separate the positive definite cone from ker S_Φ (plus the
  anti-Hermitian part) with `separating_hyperplane_set_0` in the typed matrix space; the
  extension is X ↦ Tr(DX) with D ≥ 0 (`positive_functional_extension`).  No norms, no unital
  reduction.  Dimensions are CARD of finite types, as in `Separable_Cone`.
- **A latent issue in the Day 11–22 theory.** QC11 lemmas such as `block_of_mat_index`,
  `block_of_mat_carrier`, `amplification_index`, `amplification_carrier` are stated with a free
  `X`, which is Isabelle_Marries_Dirac's Pauli constant, so they hold only for that one matrix.
  The Arveson theories use their own general versions (`block_of_mat_idx`,
  `block_of_mat_carrier'`, `amplification_idx`, `amplification_carrier'`).  Resolved by the
  renaming below: the QC11 lemmas are now general.

## Second gap-closure push, 2026-10-19 (examples and small propositions)

- **Day 29 "Hamming [7,1,3]" (D29-3) is not single-error-correcting.** The notes' code (seven
  data bits, checks a₀+a₁+a₂+a₃, a₀+a₁+a₄+a₅, a₀+a₂+a₄+a₆) detects one error but has distance 2:
  the word e₄ is at distance 1 from 0 and from the code word e₄+e₇ (`notes_hamming_ambiguous_word`,
  `notes_hamming_not_correcting`).  The standard [7,4,3] code corrects one error
  (`hamming74_corrects_one_error`).  Single-flip detection is proved by linearity over Z₂
  (c+eᵢ is a code word iff eᵢ is), not by enumerating 128×10 cases.
- **Day 30 comparison (D30-1).** The repetition code beats the parity code for all 0 < p < 1,
  not only p < ½ (`repetition_better_than_parity`).
- **Day 31 formula for R∘E (D31-2) holds only on the code space.** For Y off the code space it
  fails, e.g. R(|100⟩⟨100|) = |000⟩⟨000|.  `three_bit_code_recovery` states it for ψψ* with ψ in
  the code space, which is what the fidelity comparison (D31-4) uses.
- **Day 32 Y code (D32-2)** is an instance of a general lemma: a code with orthonormal basis
  whose unitary errors have mutually orthogonal images of the basis is corrected by one CPTP
  map (`orthogonal_images_recovery`, `orthogonal_images_correct`).
- **Day 6 coordinates (D6-3)** are proved for any basis (columns of an invertible matrix),
  with the inverse in place of the adjoint; the sum Σ x_j⊗f_j is written as in `schmidt_rank`.
- **Transcription error in `QC_Notes_overleaf.tex`.** The SWAP equation on PDF p.37 showed the
  identity on the left and CNOT′ as the third factor; the PDF has SWAP = CNOT·CNOT′·CNOT
  (`SWAP_three_CNOTs`).  Fixed.

## Gate names, 2026-10-19

- **Single-letter gate constants hidden.** Isabelle_Marries_Dirac's `X`, `Y`, `Z`, `H`, `S`, `T`
  captured free variables of those names in lemma statements (the QC11 issue above, and
  `adjoint_inner`/`herm_bound` while proving D25-4).  `Basic_Math` now hides them
  (`hide_const (open)`); they remain `Quantum.X` etc.  A theory that imports an
  Isabelle_Marries_Dirac theory directly gets the names back on merge, so only `Basic_Math`
  imports that library (now including `No_Cloning`, whose simp rules are removed there: one
  of them, `eq_from_inner_prod` with conclusion `v = w`, made a plain `simp` in
  `Day02_11_Supplement` run for over 50 minutes).
- **Project names.** `pauli_X/Y/Z`, `H_gate`, `S_gate` are renamed `Pauli_X/Y/Z`, `Hadamard`,
  `Phase_S` (lemma names follow, e.g. `Pauli_X_carrier`).  `Pauli_Y` keeps the Day 32 sign, the
  negative of the library's `Y`.

## Part VI: Quantum Algorithms (beyond the notes), 2026-10-19

- Separate session `Vern_Paulsen_QC_Algorithms` (directory `Algorithms/`, parent
  `Vern_Paulsen_QC_3_10`), so the notes' formalisation and its audit stay closed.  Target: HHL.
- **Functional calculus** (`Hermitian_Functional_Calculus`).  g(A) is defined by its action on
  eigenvectors (Av = λv ⟹ g(A)v = g(λ)v), which determines it because the eigenvectors span;
  no interpolation or independence-of-decomposition argument is needed.  It equals
  U diag(g∘D) U* for every spectral decomposition, is multiplicative, (g(A))* = ḡ(A), and only
  depends on g on the spectrum.  Instances: e^{itA} (unitary, group and power laws) and A⁻¹
  (`herm_inv`; the pseudo-inverse when 0 is an eigenvalue, since 1/0 = 0 in HOL).
- **Phase estimation** (`Phase_Estimation`).  The Fourier matrix F_N (entries ω^{jk}/√N) is
  defined directly and proved unitary from the roots-of-unity sum; the AFP
  `Quantum_Fourier_Transform` gives the circuit's output only in product form, so the bridge
  `ordered_QFT n = F_{2^n}` is a separate (open) step.  Controlled powers Σ_k |k⟩⟨k| ⊗ U^k and
  phase kickback; output (F*⊗I)·CU·(uniform ⊗ u) = (Σ_j α_j|j⟩) ⊗ u with
  α_j = (1/N)Σ_k e^{2πik(φ−j/N)}; exact case φ = j₀/N gives |j₀⟩; otherwise the outcome nearest
  Nφ (mod N) has probability ≥ 4/π² (Jordan's inequality, |e^{ix}−1| = 2|sin(x/2)|).
- Proof hygiene learned here: `simp` on `carrier_vec_def`/carrier facts and on conditional
  lemmas passed as simp rules can loop; a periodicity lemma f φ = f (φ−1) loops under `simp`.
- **HHL** (`HHL`).  Space register ⊗ (system ⊗ ancilla), so phase estimation is reused with
  U = e^{it₀A} ⊗ I₂.  Circuit W*·CR·W with W = (F*⊗I)·CU and CR = Σ_k |k⟩⟨k| ⊗ I ⊗ R(C/λ_k),
  λ_k = 2πk/(t₀N) (block-diagonal operators `ctrl_blocks`, with adjoint, product, unitarity).
  Assumption (exact HHL): every eigenvalue of A is some λ_k with 0 < k < N.  Theorem `hhl`:
  output = uniform ⊗ (√(I−C²A⁻²) b ⊗ |0⟩ + C A⁻¹b ⊗ |1⟩), proved on eigenvectors and extended
  by `eigvec_mat_eqI` (matrices agreeing on all eigenvectors are equal), so no vector sums over
  an eigenbasis are needed.  `hhl_solution`: x = A⁻¹b solves Ax = b, the ancilla-|1⟩ part is
  C·(uniform ⊗ x ⊗ |1⟩) with squared norm C²‖x‖².  `hhl_success_bound`: spectrum in [C, Λ] gives
  C²‖A⁻¹b‖² ≥ (C/Λ)²‖b‖², i.e. 1/κ² for C = λ_min (via `mat_fun_psd`: g ≥ 0 on the spectrum
  makes g(A) positive).  Register values k ≥ N/2 encode negative eigenvalues 2π(k−N)/(t₀N)
  (`reg_eig`, same phase), so A need only be invertible Hermitian; `herm_embed` handles a general
  invertible A via [[0, A], [A*, 0]] with Ã⁻¹(b ⊕ 0) = 0 ⊕ x.  Open: the non-exact (ε) version and
  the AFP QFT bridge (done below).
- **The notes PDF was missing 23 theories.**  `root.tex` only `\input` the original theories, so
  everything added by the gap-closure pushes (Day 2–11 supplement, Days 12–34 theories) was
  listed in the overview table but never typeset.  All are now input by lecture, and Part VI is
  typeset as its own part (159 → 229 pages).  Their section titles contain math that lualatex
  cannot put into PDF bookmarks (`\rangle` etc.); `\pdfstringdefDisableCommands` in `root.tex`
  gives plain-text bookmark forms.
- **AFP Fourier circuit = Fourier matrix** (`QFT_Fourier`).  The AFP's correctness theorem gives
  the output as a Kronecker product ⊗_{l=1}^n (|0⟩ + e^{2πij/2^l}|1⟩)/√2^n; by induction on the
  list [a..b], its k-th entry is e^{2πijk/2^b} (the binary digits of k pick the factors), so
  `ordered_QFT n = fourier (2^n)` and phase estimation runs on the AFP circuit.

## Third gap-closure pass, 2026-10-19 (D19-3, D23-4, D25-4)

- **Day 19 Choi-matrix form of TP/unital (D19-3).**  Trace preserving iff Tr R_ij = δ_ij, unital
  iff Σ_i R_ii = I, with R_ij = Φ(E_ij) the blocks of the Choi matrix (`choi_block`); proved
  through the expansion X = Σ x_ij E_ij (`lin_expansion`) and matrix sums `msum`.
- **Day 23 examples (D23-4).**  Two of the notes' four claims need hypotheses: the average
  ½(U₁*XU₁ + U₂*XU₂) is not extreme when U₁, U₂ are linearly independent
  (`avg2_not_extreme`), but is extreme when U₂ = zU₁ with |z| = 1 (`avg2_proportional_extreme`);
  and X ↦ Tr(X)I_d is not trace preserving — the CPTP map is X ↦ Tr(X)I_d/d (`tr_kraus_map`),
  not extreme for d ≥ 2.  U*XU is extreme and the diagonal map is not (n ≥ 2).
- **Day 25 norm proposition (D25-4), a different route.**  For f(I) = 1 on an operator system,
  positive iff ‖f‖ = 1.  The notes use the spectral theorem; the formalisation avoids it:
  for P ≥ 0, P² ≤ ‖P‖P via `psd_sqrt`, and ‖P − sI + itI‖² ≤ s² + t² gives the bound, with
  Hermitian/anti-Hermitian parts handled by `herm_bound`.  Norms are the operator norm on
  the carrier (`op_norm`, a `Sup` over the unit ball) and `fun_norm`.
- **Audit after this pass:** ✓134 ~22 ✗3 –11 of 170 (D23-4 is ~ because of the corrected
  hypotheses).  Remaining ✗: D26-1, D27-2, D5-1.
- **Inexact phase estimation** (`HHL_Approximate`).  Register sums Σ_j |j⟩ ⊗ f_j (`reg_sum`):
  block operators act branch by branch, branches are orthogonal.  For an eigenvector u with
  eigenvalue λ not a register value, W(u_N ⊗ u ⊗ w) = α ⊗ u ⊗ w for every ancilla w, so
  output − ideal = W*(Σ_j α_j |j⟩ ⊗ u ⊗ (R(C/λ_j)|0⟩ − R(C/λ)|0⟩)) and
  ‖output − ideal‖² = ‖u‖² Σ_j |α_j|² ((√(1−c_j²) − √(1−c²))² + (c_j − c)²), c_j = C/λ_j, c = C/λ
  (`hhl_approx_error`, `hhl_approx_error_real`): an exact identity, no inequality.  For the
  bound: Σ_j |α_j|² = 1 (`pe_amp_sum_sq`, α = F*b with b unit) and |α_j| ≤ 1/(2N|δ_j|) for
  δ_j = φ − j/N (`pe_amp_tail`).  Still open: combining them with a Lipschitz bound on
  c ↦ R(c)|0⟩ (which needs C/λ bounded away from 1) into an explicit ε(N, t₀, κ).
- **The clamp is necessary.**  For register values λ_k < C the rotation R(C/λ_k) is not unitary
  (HOL's √ of a negative is negative) and the branch error |α_k|²‖R(C/λ_k)|0⟩ − R(c)|0⟩‖² is of
  order (C/λ_k)²/(N δ_k)², not small; the physical circuit uses the angle max(−1, min(1, C/λ_k))
  (`hhl_circuit_clamped`, same as `hhl_circuit` on exact eigenvalues ≥ C).
- **The error bound** (`hhl_clamped_error_bound`).  For an eigenvector u with eigenvalue
  λ ≥ 2C/θ (0 < θ < 1) and t₀λ ≤ π/2: ‖output − u_N ⊗ u ⊗ R(C/λ)|0⟩‖² ≤
  ‖u‖² (π²/(N t₀²)) (θ⁴/(C²(1−θ²)) + 16/λ²).  Proof: per branch |α_k|²d_k² ≤ b₁ + b₂ with
  b₁ = π²θ⁴/(N²t₀²C²(1−θ²)) on good branches (tail bound × Lipschitz, the δ_k² cancels) and
  b₂ = 4/(Nφ)² on the others (weight ≤ 1/(Nφ)², distance ≤ 2; the negative half uses the
  periodicity α_k(φ) = α_k(φ+1)); sum over N branches.  Crude compared with the HHL paper's
  filter-function analysis, but explicit and checked.
- **Every right-hand side** (`hhl_clamped_bound`).  The naive extension of the eigenvector bound to
  b = Σ β_j u_j by the triangle inequality loses a factor √n.  Instead: the error vectors
  E u_j = W*(Σ_k α_k^{(j)} |k⟩ ⊗ u_j ⊗ (…)) of distinct eigenvectors are orthogonal
  (`hhl_err_orth`, from ⟨u_i|u_j⟩ = 0 and the branch structure, whatever the angles), so
  U*E*EU is diagonal with entries ‖E u_j‖² ≤ ε², hence ε²I − E*E = U diag(ε² − ‖E u_j‖²) U* is
  positive (`psd_U_diag_Udag`) and ‖E b‖² ≤ ε²‖b‖² (`orth_image_bound`, a general lemma).  The
  ideal output is the exact-HHL output of theorem `hhl` (matrix `lift_mat n u G₀ G₁`), so the
  theorem reads: output of the clamped circuit on u_N ⊗ b ⊗ |0⟩ is within ε‖b‖ of
  u_N ⊗ (√(I−C²A⁻²) b ⊗ |0⟩ + C A⁻¹b ⊗ |1⟩), ε² = (π²/(N t₀²))(θ⁴/(C²(1−θ²)) + 16/λ_min²).


## Fourth gap-closure pass, 2026-10-20 (D26-1, D27-2, D5-1): no gaps left

- **Day 26 factorisations (D26-1), a different route** (`Day26_CP_Factorization`).  The notes
  compress Φ to the range of P = Φ(I) (using −‖H‖P ≤ Φ(H) ≤ ‖H‖P) and get the CPTP form by
  duality.  Here both come from the Kraus form Φ(X) = Σ W_i X W_i* on the operator system
  (`arveson_kraus`) and the block embeddings B_i : ℂⁿ → ℂ^{kn} (`blk_emb`), isometries with
  orthogonal ranges and Σ B_iB_i* = I (`blk_emb_gram`).  Unital form: ψ(X) = Σ B_iXB_i*,
  V = stack of the W_i* (`kraus_stack_dag`), V*B_i = W_i, so V*ψ(X)V = Φ(X) by
  `kraus_map_dim_compose` and V*V = Φ(I) (`cp_unital_factor`; ψ is UCP on all of M_n).  CPTP
  form: ψ(Y) = Σ B_i*YB_i, V = stack of the W_i, B_i*V = W_i (`cp_tp_factor`).  A zero Kraus
  operator is prepended so that r = kn > 0.
- **Day 27 examples (D27-2)** (`Day27_Entangled_Examples`).  Both examples are (E_{f(a)f(b)})_{a,b}
  for an injective f (`unit_blocks`), = |v⟩⟨v| with v = Σ e_a ⊗ e_{f(a)}, so positive.  The
  partial transpose has entries [l = f(a)][k = f(b)]; at h = e_0⊗e_{f(1)} − e_1⊗e_{f(0)} its
  quadratic form is −2, so by `positive_map_separable` the matrix is not separable.  The notes'
  (E_ij) is `choi_seed n` (`choi_seed_unit_blocks`).
- **Sylvester's criterion (D5-1), imported** (`Sylvester/Day05_Sylvester_Criterion`, session
  `Vern_Paulsen_QC_Sylvester`).  The AFP entry `Two_Hermitian_Results` proves it for QHLProver's
  `Complex_Matrix.hermitian` (adjoint A = A) and its own `positive_definite` (quadratic form
  > 0 in the complex order).  Bridges: dagger = `mat_adjoint` (via QHLProver's `adjoint_def`),
  `pd ⟺ positive_definite`.  Lessons:
  * the project's `hermitian` and `pd` are `Quantum_Computing_3_10.hermitian`/`pd`, not
    IMD's theory `Quantum` (which has only `dagger`, `inner_prod`); qualify both sides;
  * QHLProver's `inner_prod` is an abbreviation (w ∙c v), IMD's a constant: no clash, but
    printing shows both as `inner_prod`;
  * `quadratic_form_def` is [simp] in the entry; `simp add: … carrier_vecI` on a goal that
    instantiates a quantified definition hung (> 30 s): use `blast` after `unfolding` and
    supply dimensions by `carrier_matD`;
  * the entry's import closure includes all of HOL-Analysis and HOL-Probability (via
    Projective_Measurements and Commuting_Hermitian); its heap takes ≈ 15 min and is only
    saved when it is the parent of the requested session (or with `-b`); `eval_at` cannot
    load that closure from source (Scala-backed `export_code`/bibtex commands fail);
  * Isabelle accepts a `document_theories` entry only if the document session imports it or it
    lies in its ancestry, so including the bridge in the main PDF would load the closure in
    every notes build: the bridge has its own document (`notes_doc/Sylvester_Criterion.pdf`)
    and the main document states the criterion in the Day 5 text (user's choice).
  * editing a theory while a build that includes it is running makes the build fail with
    "Incoherent digest" for that file.
- **Day 5 Cholesky examples (D5-3)**, at the user's request although counted as illustrations
  (`Day05_Cholesky_Examples`).  One step: `chol_R` (p_{i1}p_{1j}/p_{11}) and `chol_next` (P − R
  without its zero first row and column); `chol_test` (psd P ⟺ psd (chol_next P)) restates
  `cholesky_reduction` using p_{1j} = conj p_{j1}.  Every matrix of the notes is checked entry by
  entry (`mat3_eqI`, `mat2_eqI` reduce to i, j ∈ {0,1,2}; `simp` with `mat_of_rows_list_def`
  evaluates the entries).  Matrices have no executable equality here (no `equal` instance for
  `mat`), so `code_simp` cannot decide them.  `simp` expands `⊘` into ket·bra and `vec_of_list`
  into `vCons`: state rank-one terms through `outer_prod_of_list` (|l⟩⟨l| = (l_i conj l_j)).
- **Variant rows D10-1, D11-2, D15-6** (`Day10_15_Supplement`).  Superdense coding with the notes'
  explicit matrices (`sd_op`); the fourth, [[0,1],[−1,0]], is ZX, not XZ as the audit had it.
  Proving the four cases in one lemma with k and i both split took > 2 min; four separate lemmas
  take 1.6 s each.  CCNOT: |a⟩⊗|b⟩⊗|c⟩ = e_{4a+2b+c} (`tensor_unit_vec`) and CCNOT e_k = e_{k'}
  with 6, 7 exchanged; `auto simp: CCNOT_def unit_vec_def` with symbolic r, k ran > 40 s, the
  explicit entry formula plus `cases "k = 6"; cases "k = 7"; cases "r = k"` takes 0.1 s.  The CNOT
  table was already complete (`CNOT_00`…`CNOT_11`).  The A-side partial trace is the B-side one
  after exchanging the factors: `partial_trace_A_as_B` with σ(i m + k) = k p + i (`swap_index`,
  inverse `swap_index p m`); `perm_conj` keeps trace, Hermiticity and positivity, so all three
  A-side lemmas follow from the B side.
- **Variant rows D4-1, D14-5, D19-1, D29-4** (`Day04_29_Supplement`).  D4-1: (b)⟹(a) from
  H = UDU* and D* = D; (c)⟹(a) via U = mat_of_cols of the eigenbasis, HU = UD.  D19-1: the
  plan entry claimed Day19 already had "n-positive ⟹ Choi psd"; it did not.  It follows from
  `choi_matrix_as_amplification` and psd (E_ij) (Day27's `unit_blocks_psd`); `choi_four_conditions`
  ties CP, n-positivity, psd Choi and Kraus form.  D14-5: the composite ensemble
  {p_i q_j, ψ_i⊗φ_j} (`product_ensemble`) and |ψ⊗φ⟩⟨ψ⊗φ| = |ψ⟩⟨ψ|⊗|φ⟩⟨φ| (`outer_sum_tensor`).
  D29-4: distance of a subspace code = least nonzero weight; unique decoding within t errors
  when the distance is ≥ 2t+1 (the decoding statement behind `corrects_errors`).  Traps: `χ` is
  reserved syntax (HOL-Analysis vectors); sums over pairs need `split_def`, not
  `case_prod_beta`; `index_tensor_mat` needs explicit dimensions `[of _ n n _ m m]` when used
  backwards.
- **D21-4, ranges of positive matrices** (`Day21_Ranges`).  Core lemma `hermitian_perp_ker_in_range`:
  for Hermitian P = UDU*, w ⊥ ker P gives (U*w)_i = ⟨Ue_i|w⟩ = 0 whenever D_i = 0 (Ue_i ∈ ker P),
  so h = U z with z_i = (U*w)_i / D_i (0 where D_i = 0) solves Ph = w.  Then 0 ≤ ww* ≤ P ⟹
  w ∈ R(P) (with `loewner_ker_subset`) and R(Σ w_l w_l*) = col_span (V*x = 0 on ker P).  Traps
  again: `simp add: carrier_vecI` hung (> 60 s); explicit `assoc_mult_mat_vec[OF …, symmetric]`
  and `one_mult_mat_vec` are instant; no JNF lemma for M *v 0 — prove by `eq_vecI`.
- **D4-8 in the notes' form** (`pd_iff_span_all`, in `Day21_Ranges`): pd (Σ v v*) ⟺ col_span = ℂⁿ;
  ⟹ by `hermitian_perp_ker_in_range` (trivial kernel) and `outer_sum_range`, ⟸ via
  `pd_iff_spanning` (x in the span and ⊥ every v_i gives ⟨x|x⟩ = ⟨V*x|c⟩ = 0).  The `simp add:
  carrier_vecI` hang struck a third time.
- **Schmidt rank (D6-4), a definition bug** (`Day06_Schmidt_Rank`).  `schmidt_rank` was
  `Min {k. a representation of length k exists}`; that set is infinite (pad with 0 ⊗ 0) and `Min`
  of an infinite set is unspecified, so nothing could be proved about it.  Now `LEAST`.  Results:
  a length-n representation always exists (u = Σ e_i ⊗ u_i, via `tensor_combination_index`),
  rank 0 iff u = 0, for u ≠ 0 rank 1 iff product, entangled iff rank > 1 (D9-3 had claimed this
  without proof), Bell state rank 2.  Traps: `LeastI[OF …]` has multiple unifiers — give
  `[where P = …]`; `metis` with many facts hung — explicit steps instead.
- **D5-5, basis of V ⊕ W** (in `Day02_11_Supplement`): with "basis" = invertible column matrix (the
  D6-3 convention), the column matrix of (v_i,0), (0,w_j) is `four_block_mat V 0 0 W`, inverse
  `four_block_mat V⁻¹ 0 0 W⁻¹` by `mult_four_block_mat` (needs `right_mult_zero_mat` facts).
- **Min on infinite sets, the other uses**: `code_distance` takes `Min` over the distances in a
  code; correct for every finite code (all uses), unspecified only for infinite sets of words.
  The other `Min` (Essential_Functional_Analysis) is over a finite set.
- **D22-5, Γ(Φ) = Φ*** (`Day22_Adjoint_Maps`).  The adjoint existed only for Kraus maps; now
  Φ*(Y)_ij = ⟨Φ(E_ij)|Y⟩ for any linear Φ, with ⟨Y|ΦX⟩ = ⟨Φ*Y|X⟩ (from `lin_expansion`),
  uniqueness by testing with E_ij, Φ** = Φ, agreement with `kraus_adjoint_dim`, and the UCP ⟷ CPTP
  correspondence through Kraus forms and `cp_unital_iff_adjoint_tp`.  Γ is a bijection only up to
  agreement on M_n (maps are total functions); `UCP` lacks linearity, so it is assumed.  Traps:
  `simp_all add: sum.swap` loops — reorder nested sums with explicit `sum.swap` steps; an
  `obtains` lemma whose case has a ⋀-premise leaves goals after `rule` — state it with ∃ and
  `blast`; `fix X` without a type gives `'a mat` — annotate `complex Matrix.mat`.
- **D23-1, Choi's Theorem 3 in the notes' UCP form** (`Day23_Choi3_UCP`).  The Day 23 author had
  left the UCP form open and named the duality route; with Day 22's adjoint it goes through:
  `ucp_pair_mid` mirrors `cptp_pair_mid`; Γ maps midpoints both ways (differences survive because
  Φ** = Φ); the Kraus operators of Φ* are the W_i*, linearly independent with the W_i (entrywise,
  Σ c_k W_k* = 0 gives Σ conj(c_k) W_k = 0), and unital Φ makes them a trace-preserving Kraus
  family.  Traps: `blast+` over a large unfolded definition took 10-12 s per call — project the
  conjuncts with `simp`; `blast` cannot find the coefficient function conj ∘ c — apply the
  hypothesis `[OF fz]` to the named fact; after `intro allI impI` the pending goal is the
  innermost `c k = 0`.  Also: `foldr_add_index` in Day26_CP_Factorization duplicates QC_Prelims'
  `foldr_add_mat_index_rect` (left as is).
- **D16-2, block form** (`Day16_Block_Form`).  With A-major indices: coordinates h_i = (v_{ap+i})_a
  (`vcomp`), blocks X_ij = (X_{ap+i,bp+j})_{ab} (`bblock`); one reindexing lemma
  Σ_{r<mp} f r = Σ_b Σ_j f (bp+j) gives the isometry, the expansion and the block action; the
  decomposition X = Σ X_ij ⊗ E_ij and its uniqueness are entry computations with a double-delta
  lemma.  Traps: names `block_decomposition` (Day25) and `tensor_unit_index` (HHL) already taken;
  index variables without a type annotation are generic, and `{..<q}` is then not known finite
  (sum.delta fails) — annotate `nat`; lighter imports lose simp facts the scratch relied on —
  give carriers explicitly.
- **D22-4, UCP compact** (`Day22_UCP_Compact`), stated in Choi coordinates since maps carry no
  topology: the linear UCP maps' Choi matrices are exactly {P ≥ 0 : Σ_i P_ii = I_d} (inverse Choi
  map `choi_inv`), a closed set (entry sums are continuous: `continuous_on_unwrap_lm_index`) inside
  d·{P ≥ 0, Tr P = 1}, compact by `compact_unit_trace_psd_lmat`.  Traps: `simp add:
  sum.distrib[symmetric]` hung — prove sums equal with `intro sum.cong refl` (bounds in context)
  and then `sum.distrib`; `Tr_lmat_scaleR` already existed (Separable_Cone).
- **Audit after this pass:** ✓153 ~7 ✗0 –10 of 170.  The 7 variants are deliberate: different route
  (D23-3, D26-2), concrete model (D6-1, D15-3), or the notes need a hypothesis / are wrong (D5-2,
  D23-4, D32-5).  D21-2 (the conjecture) is held for a possible proof attempt.  D21-2 (the notes' conjecture on averages of
  UCP maps) is kept in mind for a possible proof attempt.
- **Sharper HHL constants** (`HHL_Window`).  The uniform register gives squared error O(1/N), i.e.
  N ~ 1/ε².  With the sine window ψ_τ = √(2/N) sin(π(τ+½)/N) the amplitude is
  (√2/N) Σ_τ sin(a τ + a/2) e^{iτx}, a = π/N; writing sin as a difference of exponentials and
  using N a = π the two geometric sums collapse to |Σ| ≤ |sin(a/2)|/(|sin((x+a)/2)||sin((x−a)/2)|)
  (`window_sum_bound`), and Jordan-type bounds on the sines give |α| ≤ 2√2π³/(N²x²) for
  2π/N ≤ |x| ≤ π.  Error sum: good branches cost K·w(Nφ − k)/N² with w(t) = 2 near (|t| < 1, at
  most two k) and π²/(2t²) far (Σ 1/(y−k)² ≤ 4 by reindexing through ⌊|y−k|⌋ onto Σ 1/(m+1)² ≤ 2);
  clamped and negative branches have |δ| ≥ φ/2 and |α|² ≤ π²/(2N⁴(φ/2)⁴) (the crude |α|² ≤ 2
  covers |δ| < 1/N since π² ≥ 4).  Result: ε² ≤ (8π²(2+π²)θ⁴/(N²t₀²C²(1−θ²)) + 512π⁶/(N³t₀⁴λ⁴))
  per eigenvector and for every b (orthogonality argument reused with ψ in place of u_N).  The
  phase-estimation context of `HHL_Approximate` is duplicated with a general register state ψ
  (about 250 lines) rather than refactoring the verified theory.  Traps: `M` is an implicit
  structure name here (rename bound sets); `Max` needs `Lattices_Big.Max`; `term` is reserved;
  `pi_gt3` does not exist (use `pi_ge_two`); field_simps leaves π·π·π·π·π·π vs π^6 — unfold
  π^6 = π²·π⁴ first; `[of …]` on lemmas with `fixes y` before an implicit N picks the wrong
  order — use `[where …]`.
- **The surrounding algorithm** (`HHL_Simulation`, `HHL_Complete`).  A tiny circuit language
  (`Gate M | Call P d | Seq a b`, oracle on the blocks with P k) with semantics, call count and
  syntactic adjoint; `sem_robust`: if the oracle is η-close (‖Ov − O'v‖ ≤ η‖v‖) every circuit is
  calls·η-close — induction, using that the gates are unitary.  Controlled powers are a chain of
  N−1 calls (block k receives O^min(k,j)), so HHL = Prep; W; R; W* has 2(N−1) calls and equals the
  verified clamped circuit for O = e^{iAt₀}⊗I.  Closeness lifts through ⊗I₂ by splitting vectors
  into even/odd halves, and through adjoints of unitaries.  Readout: ‖a/‖a‖ − b/‖b‖‖ ≤ 2‖a−b‖/‖b‖
  plus post-selection (`post1`, odd indices = ancilla 1).  Amplitude amplification in the plane
  span{g,h} with diagonal ±1 reflections (`sign_diag`), so unitarity is an entry computation;
  U(2|0⟩⟨0|−I)U* = 2|Uе₀⟩⟨Uе₀| − I.  `hhl_complete`: success ≥ 1 − p after k ≤ π²/(4Ct₀) rounds and
  (2k+1)·2(N−1) oracle calls, post-selected state within 2(ε+2(N−1)η)/(C‖A⁻¹b‖) of the answer.
  Traps: `simp add: carrier_vec_def` hangs exactly like `carrier_vecI` — use `rule carrier_vecI`;
  `O` and `R` are reserved/constant names (rename the oracle V, the rotation stage Rg);
  trailing `\<^sup>\<dagger>` still needs parentheses; context definitions (`comb`) export
  with the context assumptions, so use `comb_def[OF …]`.
- **Audit against the HHL paper** (table H-1..H-23 in NOTES_AUDIT, Part VI).  **Lemma 3 of the paper
  is false as stated**: |f−f̃|² + |g−g̃|² ≤ c κ²(λ−λ̃)²(f²+g²) with c = π²/2 fails on [1/2κ, 1/κ);
  the proof writes f²+g² = 1/2 there but it is 1/4 (f = ½ sin, g = ½ cos).  Numerically the sup of
  the ratio is π² (attained as λ̃ → λ in the middle region); proved with c = π² (`lemma3`).  Lemma 2
  (π/2)κ-Lipschitz holds and is sharp.  Proof route for Lemma 3 in the mixed case λ ≥ 1/κ > λ̃:
  triangle through 1/κ and clip λ̃ at 1/2κ, then the inequality reduces to q ≤ (π−1)/π · (1/κ).
- **Theorem 1 of the paper** (`HHL_Filter`, `HHL_Filter_Bounds`).  d-level flag circuit (error
  identity copied from the two-level one with 2 → d); the register eigenvalues' offsets from
  λ are bounded by 3× the wrapped distance; window weights summed over points with pairwise
  non-zero integer differences (floor-injectivity).  Post-selection commutes with phase
  estimation because W is "flag-diagonal" (entries vanish between different flag values);
  exact Pythagoras for maps sending an eigenbasis to orthogonal vectors (`orth_image_eq`) gives
  the relative bound for every b.  Constants: (1) 9π⁴(4+2π²)κ²/(Nt₀)², (2)/(3) ρ = 6π²√(4+2π²)κ/(Nt₀),
  normalised error 2ρ.  Traps: in theories that load HOL-Analysis, `inner_prod_def` and
  `mult.assoc`/`mult.commute` resolve to Product_Vector / Matrix_Tensor facts — use
  `Quantum.inner_prod_def`, `mult_ac`, `algebra_simps`; `OF` with a ⋀-premise like
  `G: ⋀k. k < N ⟹ G k ∈ …` instantiates G higher-order (λk. G (?f k)) — give `[where G = G]`;
  `where` on a variable named t0 needs `?t0.0`; literal `1 = 0` inside an `if` needs `(1::nat)`.
- **Paper counts convention**: the totals (forty-seven theories, 1 553 results) exclude Part VI;
  Part VI's lines/results go in the table caption.  Two earlier commits had added Part VI rows to
  the totals; corrected.
- **HHL_Runtime.**  (A32) from the window-sum identity with sin y ≥ y − y³/6 (Maclaurin n = 3);
  the paper's hypothesis δ ≤ T/10 is not needed, δ ≤ T suffices.  The paper's unknown-p
  amplification ("doubling until ≥ κ gives constant success") is a paraphrase of BHMT; the
  precise result is the averaging lemma Σ_{k<M} sin²((2k+1)θ)/M = ½ − sin(4Mθ)/(4M sin 2θ),
  proved by the telescoping 2 sin 2θ cos((4k+2)θ) = sin(4(k+1)θ) − sin(4kθ).  The run-time
  theorem `hhl_paper_runtime` composes Theorem 1(3), the success bound ‖A⁻¹b‖ ≥ ‖b‖ for ‖A‖ ≤ 1,
  and flag amplification.  Trap: a `metis order_trans` step took 61 s — state the chain.
- **HHL_Reduction** (Section III / App. A5).  Clock unitary U on C^{3T} ⊗ C^m defined entrywise;
  its block action U(Σ|c⟩f_c) = Σ|c⟩V_{c−1}f_{c−1}.  Instead of U^{3T} = I and matrix power
  series, the solution x of (I − e^{−1/T}U)x = |0⟩ψ is written down blockwise
  (x_c = e^{−c/T}W_cψ/(1 − e^{−3})) and checked; the only cycle fact needed is W_{3T} = I.
  Norm bounds from U norm-preserving give uniqueness and κ ≤ coth(1/2T) ≤ 2T + 1.  1/10 bound
  via e^{−2} ≥ (15/16)^{32} ≥ 1/8 and e^{−2}(9 − e^{−2}) ≥ 8e^{−2} ≥ 1.  **Paper errata**: the
  undo gates are U*_{T+1−t} (paper: U*_{3T+1−t}, out of range); App. A5's κ ≤ 2T is false for even
  T (κ = coth(1/2T) > 2T, eigenvalue −1 of the clock shift).  Traps: in a theory with several
  contexts, constants and abbreviations from earlier contexts (e.g. `D`) clash with variable
  names; definitions made in a context with assumptions export with those assumptions —
  wrap them in lemmas inside the context (`dim_ket0`, `prev_zero`, `W_zero`) and use
  `rule X[OF T0 Ug]`, never `unfolding X[OF …]` with a ⋀-premise.

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
  makes g(A) positive).  Open: the non-exact (ε) version, the Hermitian embedding of non-Hermitian A, and the AFP QFT bridge.


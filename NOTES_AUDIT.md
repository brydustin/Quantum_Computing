# Audit: Paulsen's lecture notes vs. the Isabelle formalisation

Source of truth: `QC_Notes.pdf` (Vern Paulsen, *Lectures on Quantum Computing and
Completely Positive Maps*, Houston, Fall 2011; notes by Brandon Lee), transcribed in
`QC_Notes_overleaf.tex`.  Formalisation: the nine theories of the sessions
`Quantum_Computing_by_VP_3_10`, `Quantum_Computing_by_VP_3_10_Lmat`, `Quantum_Computing_by_VP` (see `ROOT`).

Verification status (2026-10-19): all sessions build
with `quick_and_dirty = false`; no `sorry`, no `axiomatization`, no `oops`; a
`Thm_Deps.all_oracles` check of all theorems reports no oracles, except that the search bound imported from AFP `Compressed_Oracles` (session `HHL_Algorithm_Search`) inherits the Types-To-Sets rule `cancel_type_definition`.  `tools/check_all.sh` reruns the build, this audit and the redundancy checks (`tools/check/`).  The theorem on
unambiguous discrimination (D8-3), formerly kept in a comment block with a `sorry`, is now
proved (`lin_indep_states_unambiguous`); the priority-A gap list and B1 below were closed in
the same pass.

Lecture numbering: Day k is the k-th lecture in the notes (Day 1 = 22 Aug 2011,
Day 34 = 18 Nov 2011).  Status codes:

| code | meaning |
|---|---|
| ✓ | formalised, statement faithful to the notes |
| ~ | formalised in a variant form (explained in the row) |
| ✗ | not formalised (gap) |
| – | deliberately not formalised: narrative, history, numerical example, or classical aside |

Theory abbreviations: BM = `Basic_Math`, QC3 = `Quantum_Computing_3_10`,
MT = `Matrix_Typed`, EFA = `Essential_Functional_Analysis`, LE = `Lmat/Lmat_Euclidean`,
SC = `Lmat/Separable_Cone`, QC11 = `Day11/Quantum_Computing11`,
D23 = `Day11/Day23_ChoiExtremeUCP`, D24 = `Day11/Day24_Separability`; gap-closure theories
(2026-10-19, all in `Day11/`): D12 = `Day12_Counting_Probability`, D18 = `Day18_Positive_Maps`,
D22 = `Day22_Kraus_Independence`, D28 = `Day28_Horodecki_Peres`, D30 = `Day30_BitFlip_Code`,
D32 = `Day32_Pauli_Expansion`, D21 = `Day21_Unitary_Freedom`, D32R = `Day32_Recovery_Proposition`,
D22M = `Day22_Minimal_Kraus`, RA = `Day21_Average_Conjecture`, RA2 = `Day21_Average_Two`, D34 = `Day34_Knill_Laflamme`, D20 = `Day20_Choi_Rank`, D34S = `Day34_KL_Sufficiency`, D33 = `Day33_Shor_Code`, D17 = `Day17_Environment_Model`, OS = `Day24_Operator_Systems`, AC = `Day25_Arveson_Correspondence`, AE = `Day26_Arveson_Extension`, PMC = `Day27_Positive_Map_Criterion`, with shared lemmas in `QC_Prelims`; second gap-closure pass: S211 = `Day02_11_Supplement`, CC = `Day29_Classical_Codes`, CF = `Day31_Code_Fidelity`, YC = `Day32_Y_Code`; third pass: CTU = `Day19_Choi_TP_Unital`, EE = `Day23_Extremality_Examples`, UFN = `Day25_Unital_Functional_Norm`; fourth pass: CPF = `Day26_CP_Factorization`, EEX = `Day27_Entangled_Examples`, SYL = `Day05/Day05_Sylvester_Criterion` (session `Quantum_Computing_by_VP_Day05`), CE = `Day05_Cholesky_Examples`, S1015 = `Day10_15_Supplement`, S0429 = `Day04_29_Supplement`, RG = `Day21_Ranges`, SR = `Day06_Schmidt_Rank`, AM = `Day22_Adjoint_Maps`, C3U = `Day23_Choi3_UCP`, BF = `Day16_Block_Form`, UC = `Day22_UCP_Compact`.

---

## Part I: Basic math (Days 1–7)

### Day 1 (22 Aug): overview, inner products
| id | notes | formal | status |
|---|---|---|---|
| D1-1 | computing overview, course overview, references | – | – |
| D1-2 | inner product on ℂⁿ, sesquilinearity, positivity | library `inner_prod` (IMD); BM `inner_prod_sum`; QC3 `inner_prod_right_add'`, `_right_smult'`, `_left_smult'`, `_left_minus'`, `cpx_vec_length_zero_iff`, `cpx_vec_length_smult` | ✓ |
| D1-3 | Hilbert space (abstract definition) | not needed: all spaces are ℂⁿ or M_{n,k} | – |
| D1-4 | M_{n,k} with ⟨Y\|X⟩ = Σ ȳ_{ij} x_{ij} ≅ ℂ^{nk} | BM `hs_inner_prod` (+ `hs_inner_prod_cnj`, `_right_add`, `_right_smult`, `_left_smult`, `_self_real`, `_self_nonneg`, `_eq_zero_imp`); isomorphism with ℂ^{nk} not stated | ✓ |

### Day 2 (24 Aug): bases, matrices, trace, bra-ket, projections, Parseval
| id | notes | formal | status |
|---|---|---|---|
| D2-1 | x = Σ⟨e_i\|x⟩e_i | BM `parseval` (general ONB; e_i is the special case) | ✓ |
| D2-2 | matrix units E_{ij} are an ONB of M_{n,m}; X = Σ⟨E_{ij}\|X⟩E_{ij} | BM `mat_unit_orthonormal`, `mat_unit_expansion`, `mat_unit_hs_expansion` | ✓ |
| D2-3 | conjugate, transpose, adjoint; matrix product | library (`dagger`, `transpose_mat`, `*`) | ✓ |
| D2-4 | trace Tr | BM `Tr`, `Tr_add`, `Tr_smult`, `Tr_cyclic`, `Tr_unitary_conjugation`, `hs_inner_prod_as_trace` | ✓ |
| D2-5 | bra-ket notation, \|x⟩⟨y\| = (x_i ȳ_j), Σ\|e_i⟩⟨e_i\| = I | QC3 `outer_prod` (⊘), `outer_prod_index`, `outer_prod_mult_vec`; BM `completeness_relation`, `cols_mat_dagger_right` | ✓ |
| D2-6 | linear maps are matrices ⟨e_i\|Te_j⟩ | library; QC3 `inner_unit_T_unit` | ✓ |
| D2-7 | P = Σ\|v_i⟩⟨v_i\| projects onto V; x − Px ⊥ V; unique decomposition | BM `outer_sum`, `outer_sum_apply`, `residual_orthogonal`, `orthogonal_decomposition`, `orthogonal_decomposition_unique`, `outer_sum_orthogonal_zero` | ✓ |
| D2-8 | P does not depend on the ONB chosen for V | S211 `outer_sum_basis_independent`: two orthonormal lists with the same column span (`col_span`) have the same `outer_sum` | ✓ |
| D2-9 | Parseval ‖v‖² = Σ\|⟨v_i\|v⟩\|² | BM `parseval_norm` | ✓ |
| D2-10 | P² = P, P = P* | BM `outer_sum_idempotent`, `outer_sum_hermitian` | ✓ |
| D2-11 | Theorem: P² = P = P* ⟹ P is the orthogonal projection onto range P | QC11 `projection`, `projection_fixes_range`, `projection_annihilates_orthogonal` | ✓ |

### Day 3 (31 Aug): unitaries, Householder, Schur
| id | notes | formal | status |
|---|---|---|---|
| D3-1 | U unitary iff U*U = I | library `unitary` (bundles U*U = I and UU* = I); Basic_Math `unitary_inv_l_dimcol`, `unitary_inv_r_dimrow` | ✓ |
| D3-2 | TFAE (a) unitary (b) invertible with U⁻¹ = U* (c) UU* = I (d) U* unitary (e) columns ONB (f) rows ONB (g) isometry (h) inner-product preserving | (a)⟹(b) `unitary_invertible`; (a)⟺(c) by definition; (a)⟹(d) `unitary_dagger` (converse by applying it to U*); (a)⟹(e) `unitary_cols_orthonormal`, (e)⟹(a) BM `orthonormal_mat_unitary`; (a)⟹(f) `unitary_rows_orthonormal`; (a)⟹(g) `unitary_isometry`; (a)⟹(h) `unitary_preserves_inner_prod`; (g)⟹(a) `unitary_of_isometry`, (h)⟹(a) `unitary_of_inner_prod_preserving` | ✓ |
| D3-3 | Householder U_w = I − 2P_w is unitary (‖w‖ = 1) | QC3 `householder`, `householder_outer_prod`, `householder_hermitian`, `householder_unitary` | ✓ |
| D3-4 | Schur's lemma: ‖x‖ = ‖y‖ ⟹ ∃w, θ. U_w x = e^{iθ} y | QC3 `schur_lemma` | ✓ |
| D3-5 | Schur's theorem: U*AU upper triangular | QC3 `schur_theorem` | ✓ |
| D3-6 | Tr A = Σ eigenvalues (roots of the characteristic polynomial) | QC3 `trace_eq_sum_eigenvalues` | ✓ |

### Day 4 (2 Sep): Hermitian and positive matrices
| id | notes | formal | status |
|---|---|---|---|
| D4-1 | Hermitian TFAE (a) H = H* (b) U*HU = D real diagonal (c) ONB of eigenvectors, real eigenvalues (d) ⟨x\|Hx⟩ ∈ ℝ | (a)⟹(b) `hermitian_spectral_decomp`; (b)⟹(c) `hermitian_spectral_decomp_right` + `unitary_cols_orthonormal`; (a)⟺(d) `hermitian_iff_real_quad_form`; real eigenvalues `hermitian_real_eigenvalues`.  (b)⟹(a) S0429 `unitary_real_diag_imp_hermitian`; (c)⟹(a) S0429 `eigenbasis_real_imp_hermitian` | ✓ |
| D4-2 | Lemma: ⟨x\|Tx⟩ = 0 ∀x ⟹ T = 0 (fails over ℝ) | QC3 `quadratic_form_zero` (remark on ℝ not needed) | ✓ |
| D4-3 | P ≥ 0 iff ⟨x\|Px⟩ ≥ 0; P > 0 iff > 0 for x ≠ 0 | QC3 `psd`, `pd` (with `hermitian P` as an explicit conjunct); the notes' form is `psd_iff_quad_form_nonneg` | ✓ |
| D4-4 | P ≥ 0 iff P = P* and all eigenvalues ≥ 0 | QC3 `psd_iff_nonneg_eigenvalues` | ✓ |
| D4-5 | Corollary: P > 0 iff P = P* and all eigenvalues > 0 | QC3 `pd_iff_pos_eigenvalues` | ✓ |
| D4-6 | P ≥ 0 iff P = Σ\|v_i⟩⟨v_i\| | QC3 `psd_kraus_decomp` (⟹), `outer_sum_psd` (⟸) | ✓ |
| D4-7 | Key: ⟨x\|Px⟩ = Σ\|⟨v_i\|x⟩\|² | QC3 `inner_prod_outer_sum_general` (as ⟨V*x\|V*x⟩) | ✓ |
| D4-8 | P = Σ\|v_i⟩⟨v_i\| > 0 iff span{v_i} = ℂⁿ | QC3 `pd_iff_spanning` (no nonzero x ⊥ all v_i); RG `pd_iff_span_all` (the notes' form: pd ⟺ `col_span n vs = carrier_vec n`) | ✓ |

### Day 5 (7 Sep): tests for positivity, direct sums, block matrices
| id | notes | formal | status |
|---|---|---|---|
| D5-1 | leading principal minors test (stated, no proof) | SYL `pd_iff_leading_minors_pos`: for Hermitian P ∈ M_n, pd P ⟺ det P_k > 0 for all k ≤ n (P_k = `lps P k`); `pd_iff_leading_minors_real_pos` (each minor real and positive).  Not reproved: imported from AFP `Two_Hermitian_Results` (`Sylvester_Criterion.sylvester_criterion`) via the bridges `hermitian_iff_Complex_Matrix_hermitian` and `pd_iff_positive_definite`.  Separate session `Quantum_Computing_by_VP_Day05` with its own PDF (`notes_doc/Quantum_Computing_by_VP_Day05.pdf`), since the entry loads HOL-Analysis, HOL-Probability and QHLProver; the criterion is stated in the Day 5 text of the main document | ✓ |
| D5-2 | Cholesky reduction: P ≥ 0 iff P − p_{i1}p_{1j}/p_{11} ≥ 0 | QC3 `cholesky_reduction` (adds the hypothesis p₁₁ > 0 that the notes leave implicit) | ~ |
| D5-3 | two 3×3 numerical examples | CE `notes_example_1` ([[1,2,3],[2,4,5],[3,5,7]] is Hermitian and not ≥ 0) and `notes_example_2` ([[4,2,3],[2,5,6],[3,6,8]] ≥ 0), every intermediate matrix of the notes checked (`notes_P1_R`, `notes_P1_diff`, `notes_P1_next`, `notes_P2_R`, `notes_P2_diff`, `notes_Q2_R`, `notes_Q2_diff`, `notes_Q2_next`) through one Cholesky step `chol_R`/`chol_next` and the test `chol_test` (from `cholesky_reduction`); the remark on rank-one sums: `notes_P2_rank_one_sum` | ✓ |
| D5-4 | direct sum V ⊕ W, inner product | QC3 `direct_sum_vec` (⊕ᵥ, JNF's `@v`), `direct_sum_inner_prod`; dimension: JNF `index_append_vec` | ✓ |
| D5-5 | basis of V ⊕ W, dim(V ⊕ W) = dim V + dim W | JNF `index_append_vec`; S211 `direct_sum_basis_is_basis` (bases of ℂⁿ and ℂᵏ, i.e. lists with invertible column matrix as in D6-3, give the basis (v_i,0), (0,w_j) of ℂⁿ ⊕ ℂᵏ with n + k elements; the column matrix is block diagonal, `direct_sum_basis_block`) | ✓ |
| D5-6 | block matrices act on (v, w) | QC3 `block_mat_apply` | ✓ |

### Day 6 (9 Sep): tensor products
| id | notes | formal | status |
|---|---|---|---|
| D6-1 | bilinear maps, universal property (axiom) | concrete Kronecker model `tensor_vec` with bilinearity `tensor_vec_bilinear_left/right`, `tensor_vec_smult_left/right`; the universal property: every bilinear β: ℂⁿ×ℂᵐ → ℂᵖ is L(v⊗w) for a unique linear L (`tensor_universal_property_vec`; forms: `tensor_universal_property`) in `Day06_15_Universal` | ✓ |
| D6-2 | {e_i ⊗ f_j} basis; dim(X ⊗ Y) = dim X · dim Y | QC3 `tensor_vec_dim`, `tensor_onb` (ONB version, Day 7) | ✓ |
| D6-3 | unique x_j with u = Σ x_j ⊗ f_j; X ⊗ Y ≅ X ⊕ ⋯ ⊕ X | S211 `tensor_right_coordinates`, `tensor_left_coordinates` (any basis: the column matrix is invertible; Σ x_j ⊗ f_j is `tensor_combination`, the sum form of `schmidt_rank`); the isomorphism is `tensor_iso_direct_sum` (bijection) with `tensor_combination_add_left`, `tensor_combination_smult_left` (linearity) | ✓ |
| D6-4 | Schmidt rank | QC3 `schmidt_rank` (the least length of a representation by elementary tensors; corrected from `Min` to `LEAST`, since `Min` of the infinite set of lengths is unspecified); SR `schmidt_repr_exists` (a representation of length n exists), `schmidt_rank_zero_iff`, `schmidt_rank_one_iff_product` (for u ≠ 0: rank 1 iff a product), `schmidt_rank_bell_state` (= 2) | ✓ |

### Day 7 (12 Sep): tensor products of Hilbert spaces; postulates 1–3
| id | notes | formal | status |
|---|---|---|---|
| D7-1 | ⟨h₁⊗k₁\|h₂⊗k₂⟩ = ⟨h₁\|h₂⟩⟨k₁\|k₂⟩ | QC3 `tensor_inner_prod` | ✓ |
| D7-2 | tensor of ONBs is an ONB | QC3 `tensor_onb` | ✓ |
| D7-3 | Postulate 1: states are unit vectors | QC3 `quantum_state` | ✓ |
| D7-4 | Postulate 2: unitary evolution | QC3 `evolve`, `unitary_preserves_state` | ✓ |
| D7-5 | Postulate 3: measurement operators, p_m(ψ) = ‖M_mψ‖², Σ M_m*M_m = I, post-measurement state | QC3 `measurement_system`, `meas_prob`, `measurement_probs_sum_one`, `post_meas_state` | ✓ |

## Part II: Introduction to quantum computing (Days 8–17)

### Day 8 (14 Sep): distinguishing states, expected values
| id | notes | formal | status |
|---|---|---|---|
| D8-1 | orthogonal states are perfectly distinguishable | QC3 `orthogonal_states_distinguishable` | ✓ |
| D8-2 | non-orthogonal states cannot be: p₁(ψ₂) ≥ \|α\|² > 0 | S211 `nonorthogonal_outcome_prob` (\|⟨ψ₁\|ψ₂⟩\|² ≤ p_i(ψ₂) whenever p_i(ψ₁) = 1), `nonorthogonal_not_distinguishable`; via `meas_sum_norm` (Σ‖M_l v‖² = ‖v‖²) | ✓ |
| D8-3 | Theorem: linearly independent states admit unambiguous discrimination (M₀,…,M_n) | QC3 `lin_indep_states_unambiguous` (replaces a commented-out attempt that contained a `sorry`); linear independence is `lin_indep_vecs`; the inconclusive outcome is listed last | ✓ |
| D8-4 | P^{1/2} for P ≥ 0 | QC3 `psd_sqrt_exists`; `psd_sqrt` is now defined as a choice of square root with `psd_sqrt_props` (carrier, psd, Q·Q = P) | ✓ |
| D8-5 | expected value E = ⟨ψ\|Hψ⟩ with H = Σ λ_m M_m*M_m Hermitian | QC3 `observable`, `observable_hermitian`, `expected_value_eq_quad_form` | ✓ |

### Day 9 (16 Sep): POVMs, composite systems, entanglement
| id | notes | formal | status |
|---|---|---|---|
| D9-1 | POVM {P_m}, P_m ≥ 0, Σ P_m = I; M_m = P_m^{1/2} is a measurement system | QC3 `povm`, `measurement_induces_povm`, `povm_from_sqrt`, `povm_prob` | ✓ |
| D9-2 | Postulate 4: composite state ψ₁ ⊗ ψ₂ | QC3 `tensor_of_states_is_state` | ✓ |
| D9-3 | two-photon example; entangled iff Schmidt rank > 1 | QC3 `entangled` (defined as "not a product"), `bell_state_entangled`; SR `entangled_iff_schmidt_rank` (for u ≠ 0) | ✓ |
| D9-4 | R ⊗ T exists uniquely; (R₁⊗T₁)(R₂⊗T₂) = R₁R₂ ⊗ T₁T₂; (R⊗T)* = R*⊗T* | library `tensor_mat`; BM `tensor_mat_mult`, `tensor_mat_unitary`; (R⊗T)* = R*⊗T* is IMD's `hermite_cnj_of_tensor` | ✓ |
| D9-5 | p^{AB}_m(ψ⊗φ) = p^A_m(ψ) | QC3 `composite_measurement_prob`, `tensor_mat_vec_mult` | ✓ |
| D9-6 | eavesdropping example p₀(γ) = ½ with Bell state | S211 `bell_measurement` (p₀ = p₁ = ½, post-measurement states e₀⊗e₀, e₁⊗e₁, then B's outcome has probability 1), `proj_measurement_system` | ✓ |

### Day 10 (19 Sep): superdense coding, gates
| id | notes | formal | status |
|---|---|---|---|
| D10-1 | superdense coding: the four Bell states from γ by I, Z, X, XZ | S1015 `superdense_coding` ((M_k ⊗ I)γ = k-th Bell state for the notes' four matrices `sd_op k`: I, diag(1,−1), [[0,1],[1,0]], [[0,1],[−1,0]]; these are I, Z, X and ZX by `sd_op_paulis`, so the audit's "XZ" is ZX), `superdense_coding_orthonormal` (the four results are orthonormal) | ✓ |
| D10-2 | one-qubit gates X, Z, Y, H, S | QC11 `Pauli_X/Y/Z` (+ unitary, involution, products), QC3 `Hadamard`, `hadamard_e0/e1`, `Phase_S`, `Phase_S_unitary` | ✓ |
| D10-3 | "H² = X" | the notes are wrong here (corrected on Day 11 to H² = I); formal `hadamard_squared` proves H² = I | ✓ |
| D10-4 | classical gates AND/OR/XOR/NAND/NOR, Pierce/Sheffer remarks | – | – |
| D10-5 | CNOT matrix, unitary | library `CNOT`; QC3 `CNOT_unitary`, `CNOT_00`, `CNOT_01`, `CNOT_10`, `CNOT_11` | ✓ |
| D10-6 | Toffoli CCNOT, unitary | QC11 `CCNOT`, `CCNOT_unitary`, `CCNOT_inv` | ✓ |

### Day 11 (21 Sep): corrections, circuits, no-cloning
| id | notes | formal | status |
|---|---|---|---|
| D11-1 | H² = I, He₀, He₁, Xe₀, Xe₁ | QC3 `hadamard_squared`, `hadamard_e0`, `hadamard_e1`; X on basis vectors via `Pauli_X_ket_plus/minus` only | ✓ |
| D11-2 | CNOT, CCNOT truth tables | QC3 `CNOT_00`, `CNOT_01`, `CNOT_10`, `CNOT_11` (the full CNOT table); S1015 `CCNOT_basis` (CCNOT\|a,b,c⟩ = \|a,b,c ⊕ ab⟩) and `CCNOT_truth_table` (the notes' eight rows) | ✓ |
| D11-3 | circuit diagrams; SWAP = CNOT·CNOT′·CNOT | S211 `SWAP_three_CNOTs` (`SWAP` from the AFP entry Quantum_Fourier_Transform), `SWAP_basis`, `CNOT'_basis`; the diagrams themselves are notation | ✓ |
| D11-4 | CNOT clones the computational basis | QC3 `CNOT_00`, `CNOT_10` | ✓ |
| D11-5 | No-cloning theorem | QC11 `is_cloner`, `no_cloning` (proof via two non-orthogonal states, `two_states_nontrivial_inner_prod`; the notes use −ψ) | ✓ |

### Day 12 (23 Sep): quantum parallelism
| id | notes | formal | status |
|---|---|---|---|
| D12-1 | H^{⊗N}\|0…0⟩ = 2^{−N/2} Σ_J \|J⟩ | D12 `hadamard_uniform_N` (`tensor_pow_mat Hadamard N *v tensor_pow_vec (unit_vec 2 0) N = uniform_vec N`), with `uniform_tensor_e0_as_sum` the Σ_J form; QC11 `hadamard_e0` is N = 1 | ✓ |
| D12-2 | oracle U_f(e_J ⊗ e_i) = e_J ⊗ e_{i+f(J)} exists and is unitary | QC11 `oracle_unitary`, `oracle_exists` | ✓ |
| D12-3 | Proposition: p₀(ψ) = \|⟨γ\|ψ⟩\|² for P₀ = \|γ⟩⟨γ\| | QC3 `rank_one_meas_prob`, `meas_prob_quad_form` | ✓ |
| D12-4 | counting: p₀(U_f(x⊗e₀)) = (M/2^N)² with M = #{J : f(J) = 0} | D12 `counting_probability`: for any unitary U acting as the oracle on the basis vectors e_J⊗e_i, `meas_prob (γ ⊘ γ) (U *v γ) = (count_zeros f N / 2^N)²` with γ = x⊗e₀ | ✓ |
| D12-5 | Bernoulli-trial remark | – | – |

### Day 13 (26 Sep): ensembles, density matrices
| id | notes | formal | status |
|---|---|---|---|
| D13-1 | ensemble {p_i, ψ_i} | QC11 `ensemble` | ✓ |
| D13-2 | p_α(ensemble) = Σ p_i ‖M_α ψ_i‖² = Tr(M_α*M_α ρ) | QC11 `pure_state_prob_trace`, `ensemble_prob_trace_eq` | ✓ |
| D13-3 | a vector in H_A ⊗ H_E behaves like an ensemble (environment motivation) | ✗ (narrative; the partial-trace theorem D15-6 is the rigorous form) | – |
| D13-4 | measurements see \|ψ⟩⟨ψ\| only: \|e^{iθ}ψ⟩⟨e^{iθ}ψ\| = \|ψ⟩⟨ψ\| | QC11 `pure_density_smult_unit` | ✓ |
| D13-5 | ‖γ‖² = Tr\|γ⟩⟨γ\| | QC11 `Tr_outer_sum_single`, `Tr_outer_sum_single` | ✓ |
| D13-6 | density matrix of an ensemble | QC11 `ensemble_density`, `density_matrix`, `ensemble_density_is_dm` | ✓ |

### Day 14 (28 Sep): which matrices are density matrices; pure states; composite ensembles
| id | notes | formal | status |
|---|---|---|---|
| D14-1 | ρ is the density matrix of some ensemble iff ρ ≥ 0, Tr ρ = 1; spectral ensemble | QC11 `density_matrix_iff_ensemble`, `spectral_ensemble_exists`, `density_matrix_characterisation` | ✓ |
| D14-2 | non-uniqueness remark (ρ = XX*) | – | – |
| D14-3 | ensembles representing \|ψ⟩⟨ψ\| consist of multiples of ψ (pure states) | QC11 `pure_ensemble_parallel`, `pure_density_iff_idempotent` | ✓ |
| D14-4 | \|ψ⊗φ⟩⟨ψ⊗φ\| = \|ψ⟩⟨ψ\| ⊗ \|φ⟩⟨φ\| | QC11 `tensor_pure_density` | ✓ |
| D14-5 | composite ensemble density Σ p_i q_l (…⊗…) is a density matrix | QC11 `density_matrix_tensor` (product of two densities); S0429 `composite_density_is_dm`: for ensembles {p_i,ψ_i}, {q_j,φ_j}, Σ p_i q_j \|ψ_i⟩⟨ψ_i\| ⊗ \|φ_j⟩⟨φ_j\| (`composite_density`) is a density matrix, being the density of the ensemble {p_i q_j, ψ_i⊗φ_j} (`product_ensemble_ensemble`, `composite_density_eq`, via `outer_sum_tensor`) | ✓ |

### Day 15 (30 Sep): traces, L(H_A)⊗L(H_B) ≅ L(H_A⊗H_B), partial trace
| id | notes | formal | status |
|---|---|---|---|
| D15-1 | Tr A = Σ⟨u_i\|Au_i⟩ for any ONB | QC11 `trace_via_onb` | ✓ |
| D15-2 | Tr(R ⊗ T) = Tr R · Tr T | QC11 `trace_tensor` | ✓ |
| D15-3 | Γ : L(H_A) ⊗ L(H_B) → L(H_A ⊗ H_B) is an isomorphism | QC11 `operator_tensor_space_isomorphism` (coordinate model M_{m²,p²}); `Day06_15_Universal`: Γ(R⊗T) = R⊗T on elementary tensors (`gamma_elementary`), and Γ is the unique linear map with this property (`gamma_unique`, since the unit matrices are elementary tensors, `unit_mat_op_elem`) | ✓ |
| D15-4 | partial traces tr_B(R⊗T) = Tr(T) R, tr_A(R⊗T) = Tr(R) T | QC11 `partial_trace_B`, `partial_trace_A` (block formulas of Day 16), `partial_trace_B_tensor`, `partial_trace_A_tensor` | ✓ |
| D15-5 | p_α(ρ) = Tr((M*M ⊗ I)ρ) = Tr(M*M ρ^A) | QC11 `partial_trace_measurement` | ✓ |
| D15-6 | Tr ρ^A = Tr ρ; ρ ≥ 0 ⟹ ρ^A ≥ 0 | QC11 `partial_trace_B_trace`, `partial_trace_B_hermitian`, `partial_trace_B_is_density`; S1015 `partial_trace_A_trace`, `partial_trace_A_hermitian`, `partial_trace_A_is_density`, from the B side through `partial_trace_A_as_B` (exchange of the factors by the index permutation `swap_index`; `perm_conj` preserves trace, Hermiticity and positivity) | ✓ |

### Day 16 (3 Oct): partial traces in block form; postulates 1′–4′
| id | notes | formal | status |
|---|---|---|---|
| D16-1 | tr_B((X_{ij})) = Σ X_{ii}, tr_A((X_{ij})) = (Tr X_{ij}) | these are the formal definitions `partial_trace_B/A` (A-major Kronecker indexing) | ✓ |
| D16-2 | H_A ⊗ H_B ≅ H_A^{(p)}, L(H_A⊗H_B) ≅ M_p(L(H_A)) | BF `vec_to_mat_cols_expansion` (v = Σ h_i ⊗ e_i with h_i the i-th column of `vec_to_mat m p v`), `vec_to_mat_cols_inner_prod` (⟨v\|w⟩ = Σ ⟨h_i\|k_i⟩: the identification is isometric), `tensor_block_decomposition` (X = Σ X_ij ⊗ E_ij with blocks `bblock`) and `tensor_block_decomposition_unique`, `bblock_action` ((Xv)_i = Σ_j X_ij h_j), `partial_trace_B_blocks`, `partial_trace_A_blocks`; f_i = e_i, A-major indices | ✓ |
| D16-3 | Postulates 1′ (density matrices), 2′ (UρU*), 3′ (p_α = Tr(M*Mρ)) | QC11 `density_matrix`; `unitary_conj_channel_preserves_density_matrix`, `conjugation_channel`; `ensemble_prob_trace`, `meas_map_density` | ✓ |
| D16-4 | Postulate 4′: ρ₁ ⊗ ρ₂ is a density matrix | QC11 `psd_tensor`, `density_matrix_tensor` | ✓ |

### Day 17 (5 Oct): measurement maps, noise, axiomatic channels
| id | notes | formal | status |
|---|---|---|---|
| D17-1 | measurement map M(ρ) = Σ M_α ρ M_α* maps densities to densities | QC11 `meas_map`, `meas_map_psd`, `meas_map_density` | ✓ |
| D17-2 | stochastic matrices, Markov chains | – | – |
| D17-3 | environment model: tr_E(U(ρ ⊗ \|φ⟩⟨φ\|)U*) = Σ W_i ρ W_i*, Σ W_i*W_i = I | D17 `environment_model` (U unitary on ℂ^m⊗ℂ^p, ⟨φ\|φ⟩ = 1, tr_E = `partial_trace_B m p`, W_i = `env_kraus m p U φ i` with entries Σ_k U_{(a,i),(c,k)} φ_k; both the identity and `kraus_operators`) | ✓ |
| D17-4 | Proposition: Φ maps densities to densities iff positive and trace-preserving | D18 `density_preserving_iff_positive_tp` (linear Φ, n > 0) | ✓ |
| D17-5 | definition of completely positive | QC11 `p_positive`, `completely_positive` | ✓ |
| D17-6 | Choi–Kraus: CPTP iff Φ(X) = Σ E_i X E_i*, Σ E_i*E_i = I | QC11 `choi_kraus_cptp` | ✓ |

## Part III: Completely positive maps (Days 18–23)

### Day 18 (7 Oct): theory of CP maps
| id | notes | formal | status |
|---|---|---|---|
| D18-1 | X = (P₁−P₂) + i(P₃−P₄) with P_i ≥ 0 | QC11 `hermitian_decomp_psd`, `matrix_decomp_psd` | ✓ |
| D18-2 | positive maps; densities to densities iff positive and TP | `positive_map`; proposition = D17-4, D18 `density_preserving_iff_positive_tp` | ✓ |
| D18-3 | p-positive, completely positive, Φ^{(p)}((X_{ij})) = (Φ(X_{ij})) | QC11 `p_positive`, `completely_positive`, `amplification`, `amplification_index` | ✓ |
| D18-4 | Example: transpose on M₂ is positive but not 2-positive | D18 `transpose_positive_map`, `transpose_not_2_positive` (witness (E_{ij}) = `choi_seed 2`, test vector (0,1,−1,0)), `transpose_not_completely_positive` | ✓ |

### Day 19 (10 Oct): Choi's theorem
| id | notes | formal | status |
|---|---|---|---|
| D19-1 | Choi: (1) CP ⟺ (2) n-positive ⟺ (3) P_Φ = (Φ(E_{ij})) ≥ 0 ⟺ (4) Φ(X) = Σ B_i X B_i* | QC11 `choi_matrix`, `choi_theorem` ((1)⟺(3)), `choi_psd_if_cp`, `kraus_rep_of_psd_choi` ((3)⟹(4)), `kraus_is_cp`/`kraus_cp_no_tp` ((4)⟹(1)).  (2)⟹(3) S0429 `choi_psd_if_n_positive`; all four conditions together: S0429 `choi_four_conditions` | ✓ |
| D19-2 | Notes: Choi–Kraus representation, Choi–Jamiołkowski matrix, CP ↔ M_n(M_d)⁺ | `choi_matrix_kraus_eq` (D23), `choi_theorem` | ✓ |
| D19-3 | TP iff Tr(R_{ij}) = δ_{ij}; unital iff Σ R_{ii} = I (Choi-matrix form) | CTU `choi_trace_preserving_iff`, `choi_unital_iff` (blocks of the Choi matrix via `block_of_mat`; `choi_cptp_iff`, `choi_ucp_iff`) | ✓ |

### Day 20 (12 Oct): functionals, adjoints, Choi rank
| id | notes | formal | status |
|---|---|---|---|
| D20-1 | φ : M_n → ℂ positive ⟺ CP ⟺ (φ(E_{ij})) ≥ 0 | QC11 `positive_scalar_is_cp` (positive ⟹ CP; the rest is `choi_theorem` with d = 1) | ✓ |
| D20-2 | Φ* for Φ(X) = Σ A_i X A_i* is Y ↦ Σ A_i* Y A_i; Φ CP ⟺ Φ* CP; Φ UCP ⟺ Φ* CPTP | QC11 `kraus_adjoint_dim`, `kraus_adjoint_correct`, `adjoint_cp_from_kraus`, `cp_unital_iff_adjoint_tp` | ✓ |
| D20-3 | Choi rank cr(Φ) | QC11 `choi_rank` | ✓ |
| D20-4 | Theorem: cr(Φ) = rank(P_Φ); Lemma rank((E_{ij})) = 1 | D20 `choi_rank_eq_rank` (`choi_rank n d Φ = vec_space.rank (n*d) (choi_matrix n d Φ)` for CP Φ, n d > 0), via `rank_outer_sum_le`, `rank_ge_indep_in_colspace` and the minimal-representation independence of D22-1; the rank-one lemma for (E_{ij}) is not stated separately | ✓ |

### Day 21 (14 Oct): Kraus rank bound, unitary freedom (Choi 2)
| id | notes | formal | status |
|---|---|---|---|
| D21-1 | CP maps have Kraus representations with K ≤ nd terms | QC11 `kraus_rank_bound`, `choi_rank_le` | ✓ |
| D21-2 | conjecture on averages of UCP maps | RA `D21_2` states it for Kraus maps (every CP map is one): a unital Φ : M_n → M_d is the average of n unital maps with ≤ d Kraus operators each (`ra_split`).  It is the strong Ruskai–Audenaert conjecture for the dual channel M_d → M_n, open in general (Kumar–Wolf 2026 prove d = 2 by Borsuk–Ulam).  Proved: the case n = 2 (RA2 `ra_two`, after Bacon–Smolin–Wolf: off-diagonal Choi block R₁KR₂* with K a contraction, `wide_factor`, `bessel_rows`, and K = (U₁+U₂)/2 through a singular value decomposition, `svd_square`, `contraction_avg`); Fourier mixing B_{lj} = Σ_m ω^{lm} A_{mj} settles every map whose Kraus operators split into n groups with Σ_j A_{mj}A_{m'j}* = 0 (`fourier_split`); measurement maps X ↦ Σ_i X_ii Q_i (`ra_measurement`); Horn's lemma, every density matrix is the average of n pure states (`horn_lemma`, the case d = 1); maps with diagonal values (`ra_cq`).  The notes' form (i) is false as written (n = 2, d = 1: no trace-preserving M_2 → ℂ of Choi rank 1, `notes_form_i_false`); its correct dual form has the dimensions exchanged | ✓ (statement; open in general) |
| D21-3 | T injective ⟹ T* onto; v_i independent ⟹ v_i v_j* independent | D21 `outer_prods_lin_indep` (v_i independent ⟹ the r² matrices v_i v_j* independent over ℂ, via dual vectors `dual_vectors_exist` from the Gram inverse); the T injective ⟹ T* onto remark is not used | ✓ |
| D21-4 | 0 ≤ ww* ≤ P ⟹ w ∈ range P; range of Σ w_l w_l* | RG `dominated_rank_one_in_range` and `outer_sum_range` (R(Σ w_l w_l*) = `col_span`), both from `hermitian_perp_ker_in_range` (for Hermitian P, w ⊥ ker P ⟹ w ∈ R(P), via the spectral decomposition) and D23 `loewner_ker_subset` | ✓ |
| D21-5 | Theorem: two rank-one decompositions of P are related by an isometry U | D21 `rank_one_decomp_isometry`: if VV* = WW* with the columns of V independent (the notes: rank P = r) then W = V Uᵗ for an m × r isometry U; `rank_one_decomp_isometry_cols` gives w_l = Σ_j α_{lj} v_j | ✓ |
| D21-6 | Choi 2: unitary freedom of Kraus representations | D21 `choi_2_unitary_freedom`: Σ V_j X V_j* = Σ W_l X W_l* on M_n with the V_j linearly independent ⟹ W_l = Σ_j α_{lj} V_j with (α_{lj}) an isometry (proof through the Choi matrix and D21-5) | ✓ |

### Day 22 (17 Oct): minimal Kraus representations, convexity, UCP/CPTP
| id | notes | formal | status |
|---|---|---|---|
| D22-1 | minimal (r = cr Φ) Kraus operators are linearly independent | D22M `minimal_kraus_rep_lin_indep` (a Kraus list of length cr Φ is `lin_indep_complex_mat`; proof: a dependence is rotated by a unitary with prescribed first row into a representation with a zero operator, `kraus_mix_same_map`) | ✓ |
| D22-2 | convex sets, extreme points, convex hull, affine maps | QC11 `convex_set_mat`, `extreme_point_mat`, `affine_map_mat` | ✓ |
| D22-3 | Krein–Milman (stated) | – (available as HOL-Analysis `Krein_Milman_Minkowski`) | – |
| D22-4 | UCP(M_n,M_d) convex and compact | QC11 `UCP`, `UCP_convex`; UC `compact_ucp`: in Choi coordinates (the Choi matrix is a linear bijection L(M_n,M_d) → M_{nd}; `choi_inv` is its inverse) the linear UCP maps form exactly `ucp_choi_set` = {P ≥ 0 : Σ_i P_ii = I_d} (`ucp_choi_image`), which is compact (`compact_ucp_choi_set`: closed, and inside d times the compact unit-trace PSD set) | ✓ |
| D22-5 | CPTP convex; Γ(Φ) = Φ* affine bijection UCP → CPTP | QC11 `CPTP`, `CPTP_convex`; AM `map_adjoint` (Φ*(Y)_ij = ⟨Φ(E_ij)\|Y⟩, `map_adjoint_correct`: ⟨Y\|Φ X⟩ = ⟨Φ*Y\|X⟩), `adjoint_ucp_imp_cptp`, `adjoint_cptp_imp_ucp`, `map_adjoint_adjoint` (Φ** = Φ, so Γ is bijective with Γ⁻¹ = Γ, up to agreement on M_n), `map_adjoint_affine`; linearity is assumed since `UCP` does not record it | ✓ |
| D22-6 | Choi 3 (statement) and corollaries: extreme ⟹ cr(Φ) ≤ d; CPTP version | see D23; corollary: D22 `extreme_CPTP_kraus_length_le` (r ≤ n for a Kraus representation with independent products) and `extreme_CPTP_choi_rank_le` (cr Φ ≤ n for extreme CPTP Φ: M_n → M_d, the notes' d) | ✓ |

### Day 23 (19 Oct): proof of Choi's Theorem 3, examples
| id | notes | formal | status |
|---|---|---|---|
| D23-1 | Choi 3: Φ UCP with minimal Kraus rep (V_i) is extreme iff {V_i*V_j} linearly independent | C3U `choi_theorem_3_ucp`: for Φ ∈ UCP with Φ(X) = Σ W_i X W_i* (W_i = V_i* in the notes' notation) and the W_i linearly independent, `extreme_UCP_carrier` ⟺ linear independence of the products W_j W_i* (= V_j* V_i); from D23 `choi_theorem_3_cptp_iff` (the CPTP form) through the duality of D22-5 (`extreme_UCP_iff_adjoint`: Γ maps midpoint decompositions both ways; `lin_indep_complex_mat_dagger`, `kraus_operators_dagger_of_unital`).  "Minimal" is replaced by linear independence, which minimal representations have (D22M `minimal_kraus_rep_lin_indep`); extremality is the carrier-point notion (functions on `complex Matrix.mat` are only constrained on `carrier_mat n n`) | ✓ |
| D23-2 | forward direction via perturbation ψ_± | D23 `choi_theorem_3_cptp_reverse_carrier` (perturbation `kraus_quad_map`, `small_eps_psd`, `sym_or_antisym_witness`) | ✓ |
| D23-3 | reverse direction via Choi 2 | D23 `choi_theorem_3_cptp_forward_complex` via CP Radon–Nikodym (`cp_radon_nikodym_linear`, `dominated_outer_sum_param`) instead of Choi 2 | ~ |
| D23-4 | Examples: U*XU extreme; ½(U₁*XU₁+U₂*XU₂) not; Tr(X)I not; diag not | EE `unitary_conjugation_extreme`, `avg2_not_extreme` (needs U₁, U₂ linearly independent; `avg2_proportional_extreme` otherwise), `tr_map_not_extreme` (the map is X ↦ Tr(X)I_d/d), `diag_not_extreme` | ~ |

## Part IV: Operator systems, Arveson, entanglement (Days 24–28)

### Day 24 (24 Oct): operator systems, Arveson's extension and correspondence
| id | notes | formal | status |
|---|---|---|---|
| D24-1 | operator systems, M_p(S), CP maps on S | OS `operator_system`, `Mp`, `p_positive_on`, `cp_on` (ampliation = QC11 `amplification`), `Mp_operator_system` (the note: M_p(S) is an operator system), `cp_on_full` (S = M_n gives QC11 `completely_positive`) | ✓ |
| D24-2 | X ∈ S is a combination of four positives in S | OS `operator_system_four_positives` (via `herm_bound`: −cI ≤ H ≤ cI from the spectral decomposition) | ✓ |
| D24-3 | Arveson's extension theorem (statement, corollary) | AE `arveson_extension` (CP Φ on S ⊆ M_n extends to a CP Ψ on M_n), corollary `arveson_kraus` (Φ(X) = Σ W_i X W_i* on S); n, d are cardinalities of finite types, as in SC | ✓ |
| D24-4 | S_Φ and Arveson: CP ⟺ d-positive ⟺ S_Φ positive | AC `arveson_functional` (S_Φ), `arveson_cp_iff` (both equivalences; (3)⟹(1) by the congruence Y = A*XA with A = (v_r^t) ⊗ I, `conj_block`) | ✓ |

### Day 25 (26 Oct): Arveson correspondence, Hahn–Banach
| id | notes | formal | status |
|---|---|---|---|
| D25-1 | f ↦ Φ_f, S_Φ ↔ Φ mutual inverses; CP(S,M_d) ≅ P(M_d(S),ℂ) affinely | AC `arveson_map` (Φ_f), `arveson_functional_of_map`, `arveson_map_of_functional`, `arveson_correspondence` (onto the positive functionals), `arveson_functional_affine`, `arveson_functional_unital` (unital ↦ state) | ✓ |
| D25-2 | bounded functionals, ‖f‖ | MT `bounded_clinear_functional_on` | ✓ |
| D25-3 | Hahn–Banach: norm-preserving extension of a bounded linear functional | MT `matrix_hahn_banach_lmat`, `matrix_hahn_banach_lmat_with_bound` (complex HB on matrix spaces, derived from HOL-Hahn_Banach via Bohnenblust–Sobczyk) | ✓ |
| D25-4 | Proposition: f(I) = 1 ⟹ (f positive iff ‖f‖ = 1) | UFN `unital_positive_iff_norm_one` (operator norm `op_norm`, functional norm `fun_norm`; proved without the spectral theorem via P² ≤ ‖P‖P) | ✓ |

### Day 26 (28 Oct): Arveson extension proof; separability defined
| id | notes | formal | status |
|---|---|---|---|
| D26-1 | CP Φ with Φ(I) = P is V*ψ(X)V with ψ UCP; CP Φ = ψ(VXV*) with ψ CPTP | CPF `cp_unital_factor` (Φ CP on an operator system S ⊆ M_n: Φ(X) = V*ψ(X)V on S with ψ UCP on all of M_n and V*V = Φ(I)), `cp_tp_factor` (Φ CP on M_n: Φ(X) = ψ(VXV*) with ψ CPTP).  Proved from the Kraus form on S (AE `arveson_kraus`) with the block embeddings B_i (Σ B_iB_i* = I, `blk_emb_gram`) instead of compressing to the range of P and dualising | ✓ |
| D26-2 | Arveson extension theorem (proof) | ~ : AE `arveson_extension` by a different route: S_Φ is extended to a positive functional on M_d(M_n) directly (`positive_functional_extension`: separate the positive definite cone from ker S_Φ with HOL-Analysis `separating_hyperplane_set_0` in the typed matrix space, giving X ↦ Tr(DX) with D ≥ 0), so neither the norm proposition D25-4 nor the reduction D26-1 to the unital case is needed | ~ |
| D26-3 | separable density matrix Σ p_l \|ψ_l⟩⟨ψ_l\| ⊗ \|φ_l⟩⟨φ_l\|; entangled otherwise | SC `separable_lmat_gen`, `separable_cone_lmat`, `Sprime`; D24 `separable_density_iff_in_convex_hull_Sprime` (= SC `separable_density_iff_in_convex_hull_Sprime`: for density matrices, cone membership ⟺ convex combination of product densities) | ✓ |

### Day 27 (31 Oct): positive maps detect entanglement; convex cones
| id | notes | formal | status |
|---|---|---|---|
| D27-1 | Φ positive, R separable ⟹ Φ^{(r)}(R) ≥ 0 | PMC `positive_map_separable` (for the separable cone of SC; generators by `amplification_tensor`: Φ^{(r)}(Q⊗P) = Q⊗Φ(P)) | ✓ |
| D27-2 | Examples of entangled matrices via the transpose | EEX `entangled_example_2` ([[E_ii, E_ij],[E_ji, E_jj]] ∈ M_2(M_n), i ≠ j, with its four blocks), `entangled_example_choi_seed` ((E_ij) = `choi_seed n`, n ≥ 2): both positive and not in the separable cone; general form `unit_blocks_entangled` for (E_{f(a)f(b)}), via `unit_blocks_partial_transpose_not_psd` (test vector e_0⊗e_{f(1)} − e_1⊗e_{f(0)}, value −2) and PMC `positive_map_separable` | ✓ |
| D27-3 | f(Sep) ≥ 0 iff Φ_f positive | PMC `positive_map_iff_sep_nonneg` (via `quad_arveson_map`: ⟨w\|Φ_f(P)w⟩ = r f((w̄_i w_j) ⊗ P)) | ✓ |
| D27-4 | cones; separation of a point from a closed convex set / closed cone | HOL-Analysis `separating_hyperplane_closed_point`; SC `separable_cone_lmat_closed`, `separable_cone_lmat_separating_hyperplane` | ✓ |

### Day 28 (2 Nov): entanglement witnesses, Horodecki, Peres
| id | notes | formal | status |
|---|---|---|---|
| D28-1 | the separable matrices form a closed cone in the Hermitian matrices | SC `separable_cone_lmat_closed`, `separable_cone_lmat_hermitian`, `separable_cone_lmat_convex_cone` | ✓ |
| D28-2 | real functional f with f(R) < 0 ≤ f(C); complexification f̃ | SC `separable_cone_lmat_separating_hyperplane`, `hermitian_witness_from_lmat`, `entanglement_witness_hermitian'` | ✓ |
| D28-3 | Theorem: R ≥ 0 separable iff Φ^{(r)}(R) ≥ 0 for all positive Φ : M_n → M_r | PMC `separable_iff_positive_maps` (for Hermitian R; from the witness form SC `separable_iff_witness` through Φ_f with f = Tr(W·)) | ✓ |
| D28-4 | strict witnesses for density matrices | SC `entanglement_witness_strict`, `entanglement_witness_for_density` | ✓ (beyond the notes) |
| D28-5 | Horodecki–Peres: for v ∈ ℂ²⊗ℂ², separable iff partial transpose of \|v⟩⟨v\| ≥ 0 | D28 `horodecki_peres_two_qubits`: psd (id⊗t)(\|v⟩⟨v\|) ⟷ v = α⊗β (pure states: separable = product); `horodecki_peres_entangled`; witness value −2\|v₀v₃−v₁v₂\|² (`partial_transpose_witness_value`) | ✓ |

## Part V: Error correction (Days 29–34)

### Day 29 (7 Nov): classical codes
| id | notes | formal | status |
|---|---|---|---|
| D29-1 | repetition code | QC11 `repetition_encode`, `hamming_dist_repetition_doubles`, `hamming_weight_repetition_encode` | ✓ |
| D29-2 | parity check detects one error | QC11 `parity_check_encode`, `parity_check_detects_one_error` | ✓ |
| D29-3 | Hamming [7,1,3] code | CC: the notes' code (`notes_hamming_encode`) detects one error (`notes_hamming_detects_one_error`) but has distance 2 and cannot correct one (`notes_hamming_ambiguous_word`, `notes_hamming_not_correcting`); the standard [7,4,3] code corrects one error (`hamming74_unique_decoding`, `hamming74_corrects_one_error`) | ✓ |
| D29-4 | Hamming weight, distance of a code, subspace codes | QC11 `hamming_weight`, `hamming_dist`, `code_distance`, `corrects_errors`; S0429 `hamming_dist_triangle`, `subspace_code_distance` (for a code closed under addition mod 2 the distance is the least weight of a nonzero word), `corrects_errors_unique_decoding` (distance ≥ 2t+1: at most one code word within distance t of any received word) | ✓ |
| D29-5 | left inverses, cyclic codes | – | – |

### Day 30 (9 Nov): error probabilities; three-qubit bit-flip code
| id | notes | formal | status |
|---|---|---|---|
| D30-1 | undetected-error probabilities, majority rule | CC `repetition_undetected_prob`, `parity_undetected_prob`, `repetition_better_than_parity` (all 0 < p < 1; the notes say p < ½), `majority_uncorrected_prob` | ✓ |
| D30-2 | encoding a\|0⟩+b\|1⟩ ↦ a\|000⟩+b\|111⟩ | QC11 `encode_mat` | ✓ |
| D30-3 | syndrome projections P₀…P₃, Σ P_i = I | D30 `syndrome_proj`, `syndrome_proj_sum`, `syndrome_proj_idem`, `syndrome_proj_hermitian`; flips `flip_bit_mat` = the tensors X⊗I⊗I, … (`flips_as_tensors`) | ✓ |
| D30-4 | recovery map R is CPTP and R(\|ψ_i⟩⟨ψ_i\|) = \|ψ⟩⟨ψ\| for ≤ 1 error | D30 `recovery_map_CPTP`, `bit_flip_code_recovery` (four statements: no error and a flip on each qubit) | ✓ |

### Day 31 (11 Nov): operator viewpoint, fidelity
| id | notes | formal | status |
|---|---|---|---|
| D31-1 | error map E(Y) = (1−p)Y + pXYX is CPTP | QC11 `bit_flip_channel`, `_trace_preserving`, `_psd`, `_CPTP`, `_UCP` | ✓ |
| D31-2 | R∘E on the encoded state; code better iff p ≤ ½ | CF `three_bit_code_recovery` (R(E(ψψ*)) = c₁ψψ* + c₂φφ* for ψ in the code space), `three_bit_code_better_iff`; the notes' formula for a general Y fails off the code space | ✓ |
| D31-3 | fidelity F = \|⟨ψ′\|ψ⟩\| = √Tr(ρρ′); F = √⟨ψ\|R∘E(\|ψ⟩⟨ψ\|)ψ⟩ | QC11 `fidelity`, `fidelity_pure_states`, `fidelity_self`, `fidelity_orthogonal` | ✓ |
| D31-4 | min F = √(1−p) (do nothing) vs √((1−p)³+3p(1−p)²) (code) | CF `nothing_min_fidelity`, `code_min_fidelity` (lower bounds attained at e₀ resp. its encoding) | ✓ |

### Day 32 (14 Nov): phase-flip code, Shor code, Pauli magic
| id | notes | formal | status |
|---|---|---|---|
| D32-1 | \|±⟩, Z\|+⟩ = \|−⟩, phase-flip code \|0⟩ ↦ \|+++⟩ | QC11 `ket_plus`, `ket_minus`, `Pauli_Z_ket_plus/minus`, `ket_plus_minus_orthog`; the code words \|+++⟩, \|−−−⟩ are `phase_code_zero`/`phase_code_one` (renamed from `shor_zero`/`shor_one` in the audit pass) | ✓ |
| D32-2 | Y-version with β = Y\|+⟩ | YC `y_code_corrects` (one CPTP map corrects every single Y flip on a\|+++⟩ + b\|βββ⟩), from the general `orthogonal_images_recovery` | ✓ |
| D32-3 | Shor code \|0_L⟩, \|1_L⟩ ∈ ℂ^{2⁹}; Shor's theorem | D33 `shor_cw_notes` (the code words), `shor_code_theorem`: one CPTP R with R(Ũ\|ψ⟩⟨ψ\|Ũ*) = \|ψ⟩⟨ψ\| for every 2×2 unitary U, every position i < 9 (Ũ = `qubit_op i U` = I⊗…⊗U⊗…⊗I) and every ψ = a\|0_L⟩ + b\|1_L⟩; via `pauli_decomp`, D32 `pauli_expansion_unitary` and D32R `recovery_linear_combination` | ✓ |
| D32-4 | Proposition: U_iV mutually orthogonal ⟹ CPTP recovery R exists | D32R `recovery_ops_kraus_operators`, `recovery_map_CPTP'`, `recovery_single_error` (hypotheses bundled as `recovery_setting n P Us`: P projection, PU_i*U_jP = δ_ij P; for unitaries this is the notes' hypothesis, `recovery_setting_unitaries`) | ✓ |
| D32-5 | 1-Pauli operators; orthogonality of their images of V | false as stated: D33 `shor_notes_Z1_Z2` (Z₁ ≠ Z₂ but ⟨Z₁\|0_L⟩, Z₂\|0_L⟩⟩ = 1); the notes correct it on Day 33 (D33-1) | ~ |
| D32-6 | Pauli magic: I, X, Y, Z orthogonal with norm √2 | QC11 `pauli_orthogonal`, `pauli_norm` | ✓ |
| D32-7 | U = a₀I + a₁X + a₂Y + a₃Z unitary ⟹ Σ\|a_i\|² = 1 | D32 `pauli_expansion_unitary` | ✓ |

### Day 33 (16 Nov): Shor code recovery
| id | notes | formal | status |
|---|---|---|---|
| D33-1 | V, X_iV, Y_iV, Z_1V, Z_4V, Z_7V orthogonal (22 subspaces of the 3·9+1 = 28 tensors); Z₁v = Z₂v = Z₃v on V | D33 `shor_orthogonal_images` (PU_i*U_jP = 0 for the 22 errors `shor_errors`; computed block by block: nine qubits = three blocks of three, `qubit_op_blk`, labels decided by `code_simp`), `shor_Z_coincide` | ✓ |
| D33-2 | recovery R corrects every single-qubit unitary error | D33 `shor_code_theorem`, from D32R `recovery_linear_combination` (for ψ ∈ V and φ = Σ_i a_i U_i ψ, R(\|φ⟩⟨φ\|) = (Σ\|a_i\|²)\|ψ⟩⟨ψ\|) | ✓ |

### Day 34 (18 Nov): Knill–Laflamme conditions
| id | notes | formal | status |
|---|---|---|---|
| D34-1 | R∘E fixes \|ψ⟩⟨ψ\| on V iff it fixes PXP | D34 `recovery_states_iff_PXP` (via `psd_PXP_decomp_in_range` and the decomposition of X into four positives) | ✓ |
| D34-2 | Theorem 1: correctable iff PE_i*E_jP = α_{ij}P | D34S `knill_laflamme` (the iff). ⟹ D34 `knill_laflamme_necessity` (via Choi 2 applied to the two Kraus representations {P} and {A_lE_iP} of X ↦ PXP, `kl_kraus_scalars`); ⟸ D34S `knill_laflamme_sufficiency` (α Hermitian, diagonalised by `hermitian_spectral_decomp`; the mixed errors F_k = Σ_i u_ik E_i give the same channel and satisfy PF_k*F_lP = δ_kl d_k P (`kl_mix_bracket`); the F_k/√d_k with d_k > 0 satisfy the hypotheses of the recovery proposition) | ✓ |
| D34-3 | Theorem 2: closure under linear combinations of the errors | D34 `knill_laflamme_closure`: if R∘E fixes PXP and G_i = Σ_j g_{ij}E_j with Σ G_i*G_i = I (`kraus_mix`), then R∘G fixes PXP | ✓ |

---

## Part VI: Quantum Algorithms (beyond the notes)

Not part of the notes and not counted in the rows above.  Two sessions, prepared as separate AFP
entries: `Hermitian_Functional_Calculus` (directory `Hermitian_Functional_Calculus/`: the functional
calculus, `Matrix_Sums`, `Trotter_Product_Formula`, `Suzuki_Order`, `Suzuki_Error`; built on the AFP
alone, with QHLProver's spectral theorem) and `HHL_Algorithm` (directory `Algorithms/`, with the
sessions `HHL_Algorithm_Demo`, `_Channels`, `_Search`).  The notes form the third entry,
`Quantum_Computing_by_VP`.  `tools/afp_export.sh` assembles the three entries.

| Theory | Content |
|---|---|
| `Hermitian_Functional_Calculus` | g(A) for Hermitian A via eigenvectors; = U diag(g∘D) U*; multiplicative, adjoint, unitary for \|g\|=1; e^{itA}; A⁻¹ |
| `Phase_Estimation` | Fourier matrix unitary; controlled powers, phase kickback; output state for any register state (`phase_estimation_reg`), the uniform one as a case; exact case; success ≥ 4/π² |
| `QFT_Fourier` | the AFP `ordered_QFT n` equals `fourier (2^n)`, so phase estimation runs on the AFP circuit |
| `QPE_Precision` | the textbook precision of phase estimation (Nielsen–Chuang §5.2.1): the error of outcome j measured on the circle ℝ/ℤ (`circ_dist`); α_j is 1-periodic in φ (`pe_amp_int`); \|α_j\| ≤ 1/(2N d_j) (`pe_amp_circ_tail`); points above e > 1 at mutual distance ≥ 1 have Σ 1/y² ≤ 1/(e−1) (`sum_inv_sq_spaced`); outcomes with N d_j > e have probability ≤ 1/(2(e−1)) (`pe_tail_bound`, Eq. (5.34)), so those within e have ≥ 1 − 1/(2(e−1)) (`pe_tail_good`); Σ_j \|α_j\|² = 1 is `pe_amp_sum_sq` of `HHL_Approximate`; t = n + ⌈log₂(2 + 1/(2ε))⌉ clock qubits give φ within 2^{−n} with probability ≥ 1 − ε (`pe_precision`); the nearest value round(Nφ) mod N is within 1/(2N) on the circle (`pe_round_dist`) and has probability ≥ 4/π² for every φ (`pe_amp_near`); the same for the circuit (`phase_estimation_tail`, `phase_estimation_precision`) |
| `QPE_Program` | phase estimation as a QHLProver program: initialise, prepare an eigenvector u = U_u\|0⟩, H^{⊗k}, controlled powers, F† (`qpe_program`); the clock projector Π_J (`clock_proj`, a quantum predicate); the exact weakest precondition {(Σ_{j∈J} \|α_j\|²) I} qpe {Π_J} (`qpe_total`) and the exact probability Σ_{j∈J} \|α_j\|² tr ρ on every input (`qpe_prob`); as triples: exact phases read with certainty (`qpe_exact_total`), the nearest value with probability ≥ 4/π² (`qpe_nearest_total`), the tail (`qpe_tail_total`) and the number of clock qubits (`qpe_precision_total`); the same program in elementary gates (k Hadamards, one controlled U^{2^j} per clock qubit, the inverted AFP Fourier circuit; `qpe_elem_gates`, `qpe_elem_kinds`, `qpe_elem_circuit`, `qpe_elem_total`); triples of an initialised circuit depend only on its matrix (`init_circuit_transfer`) |
| `HHL_Approximate` | the circuit on an eigenvector for any register state ψ and d-level flag gates G_k: ‖output − ideal‖² = ‖u‖² Σ_j \|α_j\|² ‖G_j\|0⟩ − h‖² (`flag_error`), error vectors of orthogonal eigenvectors are orthogonal (`flag_err_orth`); for the rotated qubit flag ‖output − ideal‖² = ‖u‖² Σ_j \|α_j\|² ‖R(f_j)\|0⟩ − R(c)\|0⟩‖² (`hhl_approx_error_real`); Σ_j \|α_j\|² = 1; \|α_j\| ≤ 1/(2N\|δ_j\|); for the clamped circuit, λ ≥ 2C/θ and t₀λ ≤ π/2: ‖output − ideal‖² ≤ ‖u‖² (π²/(N t₀²)) (θ⁴/(C²(1−θ²)) + 16/λ²) (`hhl_clamped_error_bound`); for every b, with the spectrum in [λ_min, π/(2t₀)] and λ_min ≥ 2C/θ: ‖output − exact-HHL output‖² ≤ (π²/(N t₀²)) (θ⁴/(C²(1−θ²)) + 16/λ_min²) ‖b‖² (`hhl_clamped_bound`, via orthogonality of the eigenvectors' error vectors) |
| `HHL_Window` | register prepared in the sine window ψ_τ = √(2/N) sin(π(τ+½)/N); \|α_j\|² ≤ π²/(2N⁴δ_j⁴) for 1/N ≤ \|δ_j\| ≤ ½ (`win_amp_tail`, from a closed form of the window sum); for every b, under the hypotheses of `hhl_clamped_bound`: ‖output − exact-HHL output‖² ≤ (8π²(2+π²)θ⁴/(N²t₀²C²(1−θ²)) + 512π⁶/(N³t₀⁴λ_min⁴)) ‖b‖² (`hhl_window_bound`), so ‖output − exact-HHL output‖ ≤ ε‖b‖ once N ≥ Q/ε (`hhl_window_precision`) |
| `HHL_Simulation` | circuits of fixed gates and controlled oracle calls (`qcirc`, `sem`, `calls`); controlled powers with N−1 calls (`sem_pchain_ctrl_pow`); HHL as a circuit with 2(N−1) calls equal to the clamped circuit (`hhl_sim_exact`); each call adds at most η (`sem_robust`), so an oracle V with ‖Vv − e^{iAt₀}v‖ ≤ η‖v‖ moves the output by at most 2(N−1)η (`hhl_sim_robust`); the window state is a unit vector; end to end ‖output − exact-HHL output‖ ≤ (ε + 2(N−1)η)‖b‖ (`hhl_sim_window_error`) |
| `HHL_Complete` | readout: post-selection on the ancilla, success amplitude within δ of C‖A⁻¹b‖ and post-selected state within 2δ/(C‖A⁻¹b‖) of ψ ⊗ A⁻¹b/‖A⁻¹b‖ ⊗ \|1⟩ (`hhl_readout`); amplitude amplification: k rounds give success sin²((2k+1)θ) (`grover_success`, `amplitude_amplification`), k = ⌊π/(4θ)⌋ gives ≥ 1 − sin²θ (`grover_rounds`), as a circuit with (2k+1)·calls(u) calls, for post-selection on any set of flag values (`circuit_amplification`); the complete algorithm (state preparation, window, simulation oracle, amplification, readout) with success ≥ 1 − p, k ≤ π²/(4Ct₀) rounds and (2k+1)·2(N−1) oracle calls (`hhl_complete`) |
| `HHL_Filter` | the paper's filter functions f, g and flag state \|h(λ)⟩; Lemma 2 (`hflag_lipschitz`); Lemma 3 with the corrected constant π² (`lemma3`); Theorem 1(1),(2) on eigenvectors with the window register (`flag_window_eigen`, `flag_post_eigen`) |
| `HHL_Filter_Bounds` | Theorem 1 of the paper for every b: (1) `flag_bound`, (2) `flag_post_bound`, `flag_post_normalized`, (3) `flag_well_normalized`, `flag_H_well_conditioned`; Householder flag gates (`flag_gates_exist`) |
| `HHL_Runtime` | error metric (`unit_dist`); (A32) with the paper's constant (`win_amp_A32`); BHMT averaging (`bhmt_average`, `bhmt_quarter`); the flag circuit as an oracle circuit (`flag_full_exact`); run time in the paper's normalisation (`hhl_paper_runtime`) |
| `HHL_Reduction` | the circuit-to-matrix-inversion reduction of Section III: clock unitary (`red_U`), the solution of A x = \|0⟩ψ (`red_inverse`), norm bounds and κ ≤ 2T+1, clock post-selection probability ≥ 1/10, post-selected state ⊗ circuit output |
| `HHL_Rectangular` | App. A4: H = [[0,A],[A*,0]] for A ∈ ℂ^{M×N} is Hermitian, singular pairs give eigenvalues ±s, ker A gives the zero eigenspace; Jg(H)J = g(−H) for the parity J; the pseudo-inverse H⁺ maps b⊕0 to 0⊕x with A*Ax = A*b and x in the range of A* (`pinv_solution`): x solves Ax = b with minimum norm whenever a solution exists, and Ax is the projection of b on the range of A (`normal_eq_least_squares`) |
| `HHL_Discussion` | Section IV and App. A5: \|⟨x̃\|M\|x̃⟩ − ⟨x\|M\|x⟩\| ≤ 2‖M‖‖x̃ − x‖ (`expect_stable`); sampled distributions within 2‖x̃ − x‖ in ℓ¹ (`sample_dist_close`); k copies: entries of x^{⊗k} are k-fold products, ‖x̃^{⊗k} − x^{⊗k}‖ ≤ k‖x̃ − x‖ (`tpow_index`, `tpow_close`); the SWAP test circuit and Pr(0) = (1 + \|⟨ψ\|φ⟩\|²)/2 (`swap_test_output`, `swap_test_prob`, `had_blk_Hadamard`); Bernoulli sampling, Chebyshev, 3/ε² samples (`bern_samples`), matrix inversion estimation (`estimate_expectation`); left/right preconditioning and a counterexample to the paper's (AB)c = Bb (`paper_precondition_wrong`); App. A1's doubling schedule for unknown success probability (`doubling_schedule`, `doubling_schedule_kappa`) |
| `HHL_Optimality` | App. A5, Theorems 4–6: the M₀ measurement factorises as e^{−2}/(1+e^{−2}+e^{−4}) times the circuit's acceptance probability (`red_M0_prob`); the Hermitian dilation of A = I − e^{−1/T}U has the same condition-number bounds and solves (b,0) by (0,x) (`red_dilation`, `red_dilation_solution`); a permutation fixing 0 makes M₀ a first-qubit measurement (`first_half_perm`, `red_first_qubit`); the speedup iteration (`speedup_iteration`, `qubit_growth`, `corrected_rounds`, `speedup_collapse`); growth rates (`exp_beats_poly`, `rate_bound`); Theorems 4(2), 4(3), 5, 6 (`search_speedup_impossible`, `classical_simulation_poly`, `simon_exponents`, `count_state_prob`, `count_recover`, `parity_exponents`); errata lemmas `paper_rounds_insufficient`, `herm_embed_diag`, `paper_precision_insufficient` |
| `HHL_Search_Bound` (session `HHL_Algorithm_Search`) | the AFP `Compressed_Oracles` search bound restated as sN ≤ (5q+11)² (`search_query_bound`); exhaustive search finds a zero with probability ≥ 1/2 when \|X\| = \|Y\| (`card_zero_free`, `exhaustive_success`) |
| `HHL_Demo` (session `HHL_Algorithm_Demo`) | the HHL circuit executed on A = [[2,1],[1,2]], b = \|0⟩, three clock qubits, t₀ = π/4, C = 1, with exact arithmetic in ℚ(√2) from AFP `Real_Impl`: the gate list is the instance of `hhl_gates` (`demo_gates_eq`), its i-th prefix gives `hhl_states ! i` (`demo_trajectory`), the output is √2/3\|000⟩ + 2/3\|001⟩ + √2/3\|010⟩ − 1/3\|011⟩ (`demo_output`), and Theorem 7 holds with p = 5/9 (`demo_correct`, `demo_success`); `value [code] "demo_trace"` prints the nine states |
| `Program_Channels` (session `HHL_Algorithm_Channels`) | loop-free QHLProver programs are channels: Kraus operators read off the program (`kraus_of`, measurements via `meas_kraus`, sequences via the notes' `kraus_compose`), the meaning is their Kraus map (`denote_kraus`), the operators are complete (`kraus_of_operators`), hence `cptp_kraus_rep` (`program_channel`) and completely positive and trace preserving (`program_cptp`); the HHL program is an instance (`hhl_program_channel`) |
| `QPE_Register` | the phase-estimation register: H^{⊗n}\|0…0⟩ is the uniform state (`hadamard_layer_zero`, from AFP `Isabelle_Marries_Dirac`'s `iter_tensor_of_H_on_zero_tensor`), F\|0⟩ likewise (`fourier_zero`); H^{⊗n} is unitary, an involution, and resets the register (`hadamard_layer_uniform`) |
| `HHL_Trajectory` | the HHL circuit as eight gates (`hhl_gates`: prepare \|b⟩, H^{⊗k}, controlled e^{iAt₀j}, F†, controlled rotation, F, inverse controlled evolution, H^{⊗k}) and the state after each (`hhl_states`, `hhl_steps`) for every b: phase estimation leaves Σ_j \|j⟩⊗Π_j b with Π_j the spectral projector at λ_j (`traj_qpe`); the circuit takes \|000⟩ to \|0⟩⊗(G₀b⊗\|0⟩ + C A⁻¹b⊗\|1⟩) (`hhl_run`); all gates unitary (`hhl_gates_unitary`); ‖G₀b‖² + C²‖A⁻¹b‖² = 1 (`hhl_out_branches`) |
| `HHL_Program` | HHL as a program of the quantum while-language of AFP `QHLProver`, verified with its Hoare rules: initialisation (built from a measurement and swaps, `hoare_init`), gate sequences (`hoare_utrans_seq`, `hoare_run`), the generic `hoare_init_circuit_measure`; `hhl_program` = init; gates; measure the ancilla, `hhl_rus` = repeat until the ancilla reads 1. Proved: the per-gate trajectory (`hhl_step_triples`, `hhl_trajectory`); success probability ≥ C²‖A⁻¹b‖² (`hhl_success`, total: `hhl_success_total`); on success the state is exactly \|0⟩⊗A⁻¹b/‖A⁻¹b‖⊗\|1⟩ (`hhl_correct`, `hhl_correct_total`); the loop ends in that state (`hhl_rus_correct`, `hhl_rus_partial`); loop-free programs preserve the trace (`denote_trace_eq`) |
| `HHL_Gates` | the same program in elementary gates: H^{⊗k} as k single-qubit Hadamards (`had_gates`); the controlled evolution Σ_c \|c⟩⟨c\|⊗U^c as one controlled U^{2^j} per clock qubit (`ctrl_bit`, `ctrl_pow_qubits`), i.e. 2^k − 1 singly controlled U (`ctrl_pow_queries`); F as the AFP `Quantum_Fourier_Transform` circuit flattened into Hadamards, controlled phase rotations and swaps (`qft_circuit`, via `ordered_QFT_fourier`); every gate is a one- or two-qubit unitary on adjacent wires, a controlled U^{±2^j}, the \|b⟩ preparation or the controlled rotation (`hhl_elem_gate_kinds`); the gate list has the circuit of `hhl_gates` (`hhl_elem_circuit`), so success probability, correctness, the loop and termination carry over (`hhl_elem_success_total`, `hhl_elem_correct_total`, `hhl_elem_rus_partial`); stage-by-stage trajectory (`hhl_elem_stage_triples`, `hhl_elem_trajectory`). `HHL_Program`'s theorems are now stated for any gate list with that circuit (`hhl_prog_success` etc.); gate count 3·length = 2k³ + 16k + 6 (`length_hhl_elem_gates`; the AFP Fourier circuit has (k³+2k)/3 gates, `length_qft_circuit`, cubic because its controlled rotations are routed through nearest-neighbour swaps) |
| `HHL_Preconditioned` | the program on a preconditioned system: BAx = Bb with BA not Hermitian, run on the Hermitian dilation [[0,BA],[(BA)*,0]] with right-hand side Bb/‖Bb‖ ⊕ 0 (`pc_rhs`); on success the system register holds 0 ⊕ x/‖x‖ for the solution of Ax = b (`hhl_precond_correct`, `hhl_elem_precond_correct`, loop: `hhl_precond_rus`, `hhl_elem_precond_rus`); success probability C²‖x‖²/‖Bb‖² (`hhl_precond_success`), at least (C/s)² when ‖BAv‖ ≤ s‖v‖ (`hhl_elem_precond_bound`) |
| `HHL_Termination` | the repeat-until-success loop terminates with probability one: `hhl_rus_prog_total`, `hhl_rus_total`, `hhl_elem_rus_total` (total correctness {I} rus {\|t⟩⟨t\|}, needs C ≠ 0); after exactly m failed rounds it exits with probability (1−p)^m p in the target state, and is still running with probability (1−p)^m (`hhl_rus_prog_rounds`); expected rounds Σ(m+1)p(1−p)^m = 1/p (`hhl_rus_expected_rounds`), p = C²‖A⁻¹b‖². Generic: a loop whose body resets the state (`denote_init_circuit`) satisfies `while_reset_iter/exit/bound/total`; QHLProver has no total-correctness rule for loops, so this is derived from `denote_while_split` |
| `HHL_Paper_Program` | the paper's regime as QHLProver programs: the circuits of `HHL_Simulation` as gate lists (`qgates_sem`); generic fidelity triples {\|⟨t\|ψ⟩\|² I} prog {\|t⟩⟨t\|} (`hoare_prog_overlap`) and, for repeat-until-success, {\|⟨t\|ψ⟩\|²/p I} (`hoare_rus_overlap`, total); closeness e of the post-selected state gives fidelity 1 − e² (`fidelity_from_close`). Instances: window register, eigenvalues anywhere in the window, η-accurate oracle (`hhl_apx_program`: {(Ct₀/π)²(1−e²) I}, `hhl_apx_rus`: {(1−e²) I}, `hhl_apx_amplified`: amplitude amplification as a program, k ≤ π²/(4Ct₀) rounds); the filtered flag version in the run-time normalisation (`hhl_flag_program`: {(1/4κ)²(1−ε²) I}, `hhl_flag_rus`, `hhl_flag_amplified`: ≤ πκ rounds) |
| `HHL_Gate_Refinements` | the controlled rotation as 2^k ancilla rotations each controlled on one clock value (`vctrl`, `circuit_vctrl`, `rot_gates_circuit`); the program with it (`hhl_split_correct_total`, `hhl_split_success_total`, `hhl_split_rus_total`) and its gate kinds (`hhl_split_gate_kinds`: elementary, singly controlled U^{±2^j}, \|b⟩ preparation, value-controlled rotation); the window state by one Householder reflection (`win_reflection`, `win_prep_ok`; `hhl_apx_program_prepared`, `hhl_flag_program_prepared`); programs with equal circuits have equal denotations (`prog_meas_cong`, `meas_transfer`), so the Fourier gates of the paper-regime and amplified circuits become the AFP gate-level circuit (`fref`, `fine_gates_props`, `hhl_apx_fine`) |
| `HHL_Uniform_Rotation` | the rotation stage Σ_c \|c⟩⟨c\| ⊗ I ⊗ R(θ_c) as a uniformly controlled rotation: Walsh–Hadamard angles (`walsh_orth`, `walsh_inversion`, `ucr_angle`), one ancilla rotation and 2^k − 1 parity-controlled rotations (`ucr_circuit`); each parity is accumulated in the last clock qubit by nearest-neighbour CNOT/SWAP gates (`parity_chain_correct`), which are elementary (`pmat_lift2`, `cgate_elementary`), conjugating one rotation controlled by that qubit (`ctrl_conj`, `pblock_circuit`). The program with it: `hhl_fine_success_total`, `hhl_fine_correct_total`, `hhl_fine_rus_total`; gate kinds `hhl_fine_gate_kinds` (elementary, oracle calls C_jU^{±2^j}, U_b, ancilla rotations controlled by the last clock qubit). Paper regime and amplified circuits with Fourier transforms and filtered rotation in elementary gates: `fine2_gates_props`, `hhl_apx_fine2` |
| `HHL_State_Preparation` | state preparation for amplitudes a ≥ 0 by k levels of uniformly controlled rotations: block norms `pnorm`, angles `pangle` (`pangle_cos_sin`), one level `lev_step`, the cascade `cascade_prepares`; every gate elementary (`ctrl_blocks_tensor_right`, `ctrl_blocks_mod2`, `cv0_one_elementary`, `state_prep`); the sine window (`window_prep`); the full preparation with U_b (`win_prep_gates_props`); the paper-regime single run and repeat-until-success loop with preparation, Fourier transforms and rotation refined (`fine3_gates_props`, `hhl_apx_fine3`): every gate is elementary, an ancilla rotation controlled by the last clock qubit, the preparation of \|b⟩, or an oracle call (`full_prog_gates`) |
| `Trotter_Product_Formula` | the Lie–Trotter product formula with explicit error: for Hermitian H₁,…,H_m with ‖H_jv‖ ≤ L‖v‖, ‖(e^{itH₁/r}⋯e^{itH_m/r})^r v − e^{it(H₁+⋯+H_m)}v‖ ≤ 2(mLt)²/r ‖v‖ (`trotter`). Proved in the functional calculus: \|e^{ix}−1−ix\| ≤ x² (`cis_remainder`), ‖g(A)v‖ ≤ c‖v‖ when \|g\| ≤ c on the spectrum (`mat_fun_bound`), first order of one factor (`evolution_first_order`) and of a product (`tprod_first_order`), one step (`trotter_step`), errors add along powers of unitaries (`op_close_pow`) |
| `HHL_Sparse_Split` | an s-sparse Hermitian A is its diagonal plus 2s−1 Hermitian 1-sparse matrices: greedy edge colouring by involutions, a colour free at both ends of every new edge (`greedy_cover`); the parts (`one_sparse`, `colour_part`, `diag_part`) are Hermitian, bounded by the largest entry (`one_sparse_bound`, `sparse_parts_bounded`) and sum to A (`sparse_parts_sum`, `sparse_split`); with `trotter`, r rounds of the 2s part evolutions are within 8(sLt)²/r of e^{itA} (`sparse_trotter`) |
| `HHL_Sparse_Circuit` | the sparse simulation oracle as a verified circuit on \|x⟩\|y⟩\|b⟩: a colour oracle (any unitary with \|x,0,b⟩ ↦ \|x,q(x),b⟩; one exists, `colour_oracle_exists`), a comparator that sorts the pair into the ancilla (`cmp_gate`), an entry gate rotating the ancilla by e^{id[[0,a],[ā,0]]}, a = A_xy (`ent_gate`), and a diagonal phase gate (`dia_gate`); every gate is unitary (`ent_gate_unitary`, `dia_gate_unitary`, `sg_run_unitary`). Per colour the five gates map \|k,0,0⟩ to (e^{idH_c}\|k⟩)\|0,0⟩ (`colour_circ_basis`) with e^{idH_c} in closed form (`evolution_colour_part`); the gate list `sim_gates` intertwines with the Trotter product, V = (e^{idH_0}⋯)^r (`sim_intertwine`), and uses r(6s−2) queries (`sparse_simulation_circuit`: V unitary and 8(sLt)²/r-close to e^{itA}); colourings and oracles exist (`sparse_oracles_exist`); plugged into HHL: error (ε + 16(N−1)(sLt₀)²/r)‖b‖ (`hhl_sparse_window_error`) |
| `HHL_All_Elementary` | the last assumed gates removed for n = 2^s: ancilla rotations controlled by the last clock qubit routed by s adjacent swaps (`route`, `route_cv0`); diagonal unitaries in elementary gates, mean phases recursively and phase differences as a uniformly controlled rotation conjugated by a fixed one-qubit gate (`diag_gates_circuit`, `diag_gates_elementary`); every normalised \|b⟩ prepared in elementary gates (`bprep`); the exact-phase and paper-regime programs with every gate elementary or an oracle call (`hhl_elementary`, `hhl_apx_elementary`); exact universality from the spectral theorem, U = Π_k (I + (λ_k − 1) p_k p_k*) with each factor a phase on \|0⟩ conjugated by the preparation of p_k (`exact_universality`), so HHL programs with every gate elementary exist (`hhl_compiled`, `hhl_apx_compiled`; no gate-count bound) |
| `Matrix_Sums` | entries and scalar sums of QHLProver's finite matrix sums (`matrix_sum_index`, `matrix_sum_scalar`), shared by the program theories and the product formulas |
| `Suzuki_Order` | order conditions for product formulas: Taylor coefficients of e^{tY₁}⋯e^{tY_m} as convolutions of matrix sequences (`sconv`, `fcoef`, associativity `sconv_assoc`, `fcoef_append`, `fcoef_inverse`); a palindrome agreeing with e^{tX} below an even degree agrees in that degree (`sym_order`); five scaled copies cancel the next degree when Σc = 1 and Σc^q = 0 (`scaled_copies`); Strang has order 2 (`strang_order`) and Suzuki's recursion S_{2k+2} = S_{2k}(u)² S_{2k}(1−4u) S_{2k}(u)², u = 1/(4−4^{1/(2k+3)}), agrees with e^{itH} up to degree 2k+2 (`suzuki_order`) |
| `Suzuki_Error` + `HHL_Suzuki` | Suzuki's formulas with explicit error: \|e^z − Σ_{q≤P} z^q/q!\| ≤ \|z\|^{P+1}e^{\|z\|}/(P+1)! (`exp_tail`), e^{isH} against its Taylor polynomial (`evolution_taylor`), a product against the truncation of its coefficients (`sprod_approx`); one step (`suzuki_step`) and r steps: ‖S_{2k+2}(t/r)^r − e^{itH}‖ ≤ r(2\|F\|+1)(Λ\|t\|/r)^{2k+3}e^{Λ\|t\|/r}/(2k+3)! with \|F\| = 2·5^k m factors (`length_suzuki`) and Λ ≥ mL (`lam_suzuki`) (`suzuki_error`); for s-sparse A over the 2s parts of the colouring (`sparse_suzuki`); plugged into the HHL error bound (`hhl_suzuki_window_error`). Products of part evolutions, not circuits |
| `HHL` | circuit W*·CR·W with any angle function h; output h(A)b for every b (`fun_circuit_output`), exact HHL as h(x) = C/x (`hhl`); Ax = b for x = A⁻¹b, success probability C²‖x‖² ≥ 1/κ²; signed eigenvalues; non-Hermitian A via [[0,A],[A*,0]] |

Sharper constants: closed by `HHL_Window` (register size N ~ 1/ε instead of 1/ε²; the sine window is the optimal window of the HHL paper's filter-function analysis, here with explicit constants).  Surrounding algorithm: closed by `HHL_Simulation` and `HHL_Complete` (simulation enters as an η-accurate oracle; state preparation as a given unitary; readout and amplitude amplification proved; oracle calls counted).  Complexity theorems (Theorems 4–6): `HHL_Optimality`, up to the cited complexity-theoretic facts, with the search bound imported from the AFP in session `HHL_Algorithm_Search`.  Phase estimation: `QPE_Precision` proves the textbook tail bound and clock size, and `QPE_Program` verifies phase estimation as a program with exact weakest preconditions, at the gate level too.  Program verification: `HHL_Program` (quantum Hoare logic of AFP `QHLProver`) verifies an explicit HHL program end to end, from initialisation and state preparation to the ancilla measurement and a repeat-until-success loop; the clock-register gap (H^{⊗n}\|0⟩ uniform) is closed in `QPE_Register`.  `HHL_Gates` decomposes the program into elementary gates (one controlled U^{2^j} per clock qubit, the AFP gate-level QFT); `HHL_Preconditioned` runs it on a preconditioned system and returns the solution of the original one.  `HHL_Termination` proves that the repeat-until-success loop terminates with probability one, with the round-by-round exit probabilities and the expected number of rounds.  `HHL_Paper_Program` runs the paper's regime (window register, eigenvalues between grid points, approximate oracle, filtered version, amplitude amplification) as programs with fidelity postconditions; `HHL_Gate_Refinements` splits the controlled rotation per clock value, builds the window preparation from one reflection and puts elementary Fourier gates into the amplified circuit.  `HHL_Uniform_Rotation` puts the rotation stage itself into elementary gates (a uniformly controlled rotation from Walsh–Hadamard angles and nearest-neighbour parity chains), so the remaining non-elementary gates are the oracle calls, U_b and single-qubit rotations of the ancilla controlled by the last clock qubit.  `HHL_State_Preparation` prepares the sine window with elementary gates only (k levels of uniformly controlled rotations), so the same holds for the paper-regime programs.  `HHL_Trotter`, `HHL_Sparse_Split` and `HHL_Sparse_Circuit` build the evolution oracle from sparse access: a Trotter circuit of colour queries, comparators and entry gates whose action on ancilla-zero inputs is a unitary V within 8(sLt)²/r of e^{itA}, with r(6s−2) queries, plugged into the HHL error bound.  `Suzuki_Order` and `HHL_Suzuki` verify Suzuki's higher-order formulas, error O(\|t\|^{2k+3}/r^{2k+2}), for products of part evolutions (also for the sparse split) and plug them into the HHL error bound; only the first-order product is a verified circuit.  `HHL_All_Elementary` routes those ancilla rotations by swaps and prepares every \|b⟩ in elementary gates, so for n = 2^s every gate is elementary or an oracle call; by exact universality (spectral theorem plus state preparation) the oracle calls compile to elementary gates too, without a useful gate count.  `HHL_Demo` (session `HHL_Algorithm_Demo`) executes the circuit on a 2×2 system in exact arithmetic and proves that every computed state is the trajectory's.

### Audit against the HHL paper (Harrow, Hassidim, Lloyd, arXiv:0811.3171v3)

Each numbered result or claim of the paper and its formal counterpart.  ✓ formalised, ~ formalised
in a variant (stated), ✗ not yet, – out of scope (reason given).

| # | Paper | Formal counterpart | Status |
|---|---|---|---|
| H-1 | §II: exact algorithm, output ∝ A⁻¹\|b⟩ when eigenvalues are register values | `HHL`: `hhl` | ✓ |
| H-2 | §II eq. (1): non-Hermitian square A via [[0,A],[A†,0]] | `HHL`: `herm_embed` inverse | ✓ |
| H-3 | eq. (2)/(A1): the window state \|Ψ₀⟩ | `HHL_Window`: `win_state`, unit norm `win_state_norm` | ✓ |
| H-4 | eq. (3): conditional evolution and Fourier transform give Σ α_{k\|j} β_j \|k⟩\|u_j⟩ | `phase_estimation_reg`, `pe_amp_reg_formula` | ✓ |
| H-5 | §II: rotation, uncomputation, post-selection on 1 gives ∝ Σ β_j C/λ_j \|u_j⟩ | `hhl`, `hhl_readout` | ✓ |
| H-6 | §II: success probability Ω(1/κ²) | `hhl_success_bound` | ✓ |
| H-7 | §II/App. A1: amplitude amplification, O(κ) rounds, operators R_succ, R_init | `HHL_Complete`: `grover_prog`, `circuit_amplification`, `hhl_complete` | ✓ |
| H-8 | App. A1: unknown p̃, geometric schedule of rounds gives constant success with ≤ 4κ rounds | BHMT's averaging lemma (`bhmt_average`, `bhmt_quarter`: for k uniform below M ≥ 1/sin 2θ the mean success probability is ≥ 1/4) and the schedule itself (`doubling_schedule`: stages with k uniform below 1, 2, 4, …, 2^m, stopping at the first success, all fail with probability ≤ 3/4 once 2^m ≥ 1/(√2 sin θ), using < 2^{m+1} rounds; `doubling_schedule_kappa`: with sin θ ≥ 1/(4κ), stopping at the first power of two ≥ 2√2κ, fewer than 8√2κ rounds). The paper's 4κ depends on its unspecified constant in p̃ | ✓ |
| H-9 | §II/A1: run time Õ(κ(T_B + t₀s² log N)), t₀ = O(κ/ε), total Õ(κT_B + κ²s² log N/ε) | `hhl_paper_runtime` (spectrum in [1/κ, 1]): total evolution time t ≥ cκ/ε gives accuracy ε, success amplitude ≥ 1/(4κ), ≤ πκ amplification rounds with 2(N−1) calls each: O(κ) uses of B, total simulated time O(κ²/ε). The cited sparse simulation [3] is formalised in first-order form (`hhl_sparse_window_error`: r(6s−2) queries per oracle use for error 8(sLt₀)²/r); the higher-order formulas behind the paper's s² log N per unit time are not | ✓ |
| H-10 | App. A1: three-level flag register S (nothing/well/ill) and filter functions f, g (A3) | `HHL_Filter`: `filt_f`, `filt_g`, `hflag`, `flag_circuit`; gates exist (`flag_gates_exist`, Householder) | ✓ |
| H-11 | Lemma 2: λ ↦ \|h(λ)⟩ is (π/2)κ-Lipschitz | `hflag_lipschitz` (constant π/2, sharp) | ✓ |
| H-12 | Lemma 3: \|f−f̃\|² + \|g−g̃\|² ≤ c κ²δ²/t₀² (f²+g²) with c = π²/2 | `lemma3` with c = π², sharp (`lemma3_sharp`: every c < π² fails). The paper's c = π²/2 is false for every κ (`lemma3_paper_constant`: at λ = 1/2κ, λ̃ = 1/κ the sides are π²/32 and 1/2); on [1/2κ, 1/κ) its proof uses f²+g² = 1/2, but there f²+g² = 1/4 | ~ (paper wrong) |
| H-13 | Theorem 1(1): ‖Ũ − U‖ ≤ O(κ/t₀) (no post-selection) | `flag_bound`: ‖(Ũ−U)b‖² ≤ 9π⁴(4+2π²)κ²/(Nt₀)² ‖b‖² for every b (t = Nt₀ the total evolution time); per eigenvector `flag_window_eigen` | ✓ |
| H-14 | Theorem 1(2): post-selected on {well, ill}, error O(κ/t₀) | `flag_post_bound` (relative error ρ = 6π²√(4+2π²)κ/(Nt₀)), normalised states within 2ρ (`flag_post_normalized`) | ✓ |
| H-15 | Theorem 1(3): b in the well-conditioned subspace, post-selected on well, error O(κ/t₀) | `flag_well_normalized` (g(A)b = 0 ⇒ within 2ρ of f(A)b/‖f(A)b‖ ⊗ \|well⟩); `flag_H_well_conditioned`: f(A) = A⁻¹/(2κ) when the spectrum is ≥ 1/κ | ✓ |
| H-16 | (A23)–(A31): closed form of α_{k\|j} | `window_sum_bound` (its modulus) | ✓ |
| H-17 | (A32): \|α_{k\|j}\| ≤ 8π/δ² for 2π ≤ δ ≤ T/10 | `win_amp_A32`: 8π/δ² for 2π ≤ \|δ\| ≤ T (weaker hypothesis than the paper's) | ✓ |
| H-18 | App. A4: rectangular A, eigenstructure of H, minimum-norm solution (M ≤ N), projected solution (M ≥ N) | `HHL_Rectangular`: `herm_embed_hermitian` (`HHL`, for rectangular A), `H_singular_pair` (eigenvalues ±λ_j on (u_j, ±v_j)), `H_kernel` (zero eigenspace); `pinv_solution`: the algorithm's output H⁺(b⊕0) = 0⊕x with x = A*c, A*Ax = A*b, and x the minimum-norm solution when Ax = b is solvable; `normal_eq_least_squares`: ‖Ax − b‖ ≤ ‖Az − b‖ for all z, i.e. Ax is the projection of b on the range of A | ✓ |
| H-19 | §III eq. (4)–(5), (A34)–(A37): the circuit-to-matrix reduction U, A = I − Ue^{−1/T}, A⁻¹ = Σ U^k e^{−k/T}, κ = O(T), post-selection probability ≥ 1/10 | `HHL_Reduction`: `red_inverse` (A⁻¹(\|0⟩ψ) as the finite sum Σ_{c<3T} e^{−c/T}\|c⟩W_cψ/(1−e^{−3})), `red_solution_unique`, `red_A_bounds` and `red_kappa` (κ ≤ (1+e^{−1/T})/(1−e^{−1/T}) ≤ 2T+1), `red_clock_prob` (e^{−2}/(1+e^{−2}+e^{−4}) ≥ 1/10), `red_post_state` (clock ⊗ U_T⋯U_1ψ); (A34)–(A37) in `HHL_Optimality`: `red_M0_prob`, `red_dilation`, `red_first_qubit` (see H-20). Paper errata: the undo gates must be U*_{T+1−t} (the paper writes U*_{3T+1−t}); App. A5 claims κ ≤ 2T, but κ = coth(1/2T) > 2T when 3T is even | ~ (paper wrong in details) |
| H-20 | Theorems 4, 5, 6: BQP = PSPACE / BPP = BQP / BQP = PP consequences, oracle lower bounds | `HHL_Optimality`, each theorem up to the external fact it cites (the classes BQP, PSPACE, BPP, PP are not in the AFP; `Cook_Levin` has only P and NP). Thm 4(1): `speedup_iteration`, `qubit_growth` (n_i ≤ n_0 + i log 18 + (2/δ) log T_0), `corrected_rounds`, `speedup_collapse` (T_ℓ ≤ max(g^{2/δ}, 2): every n-qubit computation with T ≤ 2^{2n} gates gets a poly(n)-gate simulation; PSPACE ⊆ BQP then needs TQBF's PSPACE-completeness, not formalised). Thm 4(2): `search_speedup_impossible` with the search bound sN ≤ (5q+11)² imported from AFP `Compressed_Oracles` (`zero_finding_is_hard`) in session `HHL_Algorithm_Search` (`search_query_bound`, `exhaustive_success`). Thm 4(3): `classical_simulation_poly`. Thm 5: `simon_exponents` (3α+4β ≥ 1/2, classical Simon bound as hypothesis). Thm 6: `count_state_prob` (#SAT as a probability), `count_recover`, `counting_precision`, `parity_exponents` (α+β ≥ 1, parity bound as hypothesis). The reduction's measurement and embeddings: `red_M0_prob`, `red_dilation`, `red_dilation_solution`, `red_first_qubit`. Paper errata: the proof's m = (2/δ)log(2n)/log log n is too small for T_m ≤ n_0 (`paper_rounds_insufficient`; m ≥ (2/δ)ln(2n_0) works); (A34) cannot satisfy the demanded κ⁻¹I ≤ A ≤ I (zero diagonal, `herm_embed_diag`); in (A37) the top half of y is always 0, so the first qubit carries no information (fixed by permuting the whole dilation, `first_half_perm`); Thm 6(2)'s ε = 2^{−n−2} cannot separate C from C+1 after the clock factor ≤ 1/4 (`clock_quarter`, `paper_precision_insufficient`) | ~ (up to cited results; paper wrong in details) |
| H-21 | App. A5: matrix inversion estimation in Õ(log N κ²s²/ε³) by sampling | `HHL_Discussion`: `expect_stable` (accuracy ε/4 of \|x⟩ moves the measured bit's mean by ≤ ε/2), `bern_mean`, `bern_var`, `bern_chebyshev`, `bern_samples` (3/ε² samples: within ε/2 with probability ≥ 2/3), `estimate_expectation` (the two combined); the run time is 3/ε² runs of `hhl_paper_runtime` at accuracy ε/4. Paper erratum: it takes 1/(3ε²) samples, which is too few (`paper_sample_count_too_small`: ε = 1/4, p = 1/2, 6 samples fail with probability 11/16) | ~ (paper wrong in details) |
| H-22 | App. A: error metric ‖\|α⟩−\|β⟩‖ = √(2(1−Re⟨α\|β⟩)) for unit vectors | `unit_dist` | ✓ |
| H-23 | §IV: estimating ⟨x\|M\|x⟩, k-copy polynomials, sampling, f(A)\|b⟩, SWAP test, preconditioning, ill-conditioned flagging | `HHL`: `fun_circuit_output` (f(A)\|b⟩); `HHL_Discussion`: `expect_stable`, `tpow_index` and `tpow_close` (k copies), `sample_dist_close` (sampling), `swap_test_output`/`swap_test_prob` (SWAP test), `precond_left`/`precond_right`; flagging is `flag_post_bound`. Paper errata: (AB)c = Bb is not a preconditioned system (`paper_precondition_wrong`: its unique solution c has Ac ≠ b and A(Bc) ≠ b; correct are BAx = Bb or ABc = b, x = Bc); the displayed flagged state swaps λ_j < 1/κ and λ_j ≥ 1/κ | ~ (paper wrong in details) |

## Infrastructure not in the notes (formalised to make the above possible)
* BM: tensor-product algebra (`tensor_mat_mult`, `tensor_mat_unitary`), unitary algebra.
* EFA: Hilbert–Schmidt norm, completeness of M_n in HS norm, closedness of the Hermitian and PSD sets, Carathéodory for conic combinations of product matrices.
* MT, LE: typed-dimension matrices `lmat` with the HOL-Analysis `euclidean_space`/`heine_borel` tower, so that the HOL-Analysis separation and compactness theorems apply.
* SC: compactness of the product-density slice, closedness of the separable cone.
* D23: CP Radon–Nikodym via the Moore–Penrose pseudoinverse (`dominated_outer_sum_param`, `cp_radon_nikodym_linear`).

## Fidelity remarks (variants that are mathematically equivalent or stronger)
1. `psd`/`pd` carry `hermitian` explicitly (D4-3).  A lemma `psd_iff_quad_form_nonneg` making the notes' form explicit is cheap and worth adding.
2. `cholesky_reduction` assumes p₁₁ > 0 (D5-2); the notes' statement is false without it (take p₁₁ = 0).
3. The notes claim H² = X on Day 10 and correct it on Day 11; the formalisation proves H² = I.
4. Partial traces are defined by the block formulas of Day 16 with A-major Kronecker indexing; `partial_trace_B_tensor` and `partial_trace_A_tensor` show they agree with the Day 15 definition on elementary tensors.
5. Choi's Theorem 3 is formalised in the CPTP form with a fixed linearly independent Kraus list and the carrier-point notion of extremality (D23-1).
6. `extreme_CPTP` (raw function inequality) is provably vacuous; use `extreme_CPTP_carrier` (documented inside D23).
7. The entanglement theory is formalised in witness form (SC) and, through the Arveson correspondence, also in the notes' positive-map form (D28-3, `Day27_Positive_Map_Criterion`).
8. The three-qubit phase-flip code words were called `shor_zero`/`shor_one`; renamed `phase_code_zero`/`phase_code_one` (D32-1).
9. `psd_sqrt` was a placeholder constant equal to the zero matrix; now defined via `SOME` with `psd_sqrt_props` (D8-4).
10. `Day24_Separability` attributed the separability material to Days 24–28; the theorem prefixes now follow the notes (D26 definition of separability, D27 cone and separation, D28 closedness and witnesses).

## Gap list and plan
Priority A (cheap, improve fidelity) — ALL CLOSED in the 2026-10-18 pass:
A1 D3-2 converses: isometry ⟹ unitary is the library's `length_preserving_is_unitary` (Isabelle_Marries_Dirac); add a vector-form wrapper and the inner-product version.
A2 D4-5 `pd_iff_pos_eigenvalues`.
A3 D4-3 `psd_iff_quad_form_nonneg` (notes' definition).
A4 D8-4 redefine `psd_sqrt` via `SOME` with `psd_sqrt_props`. DONE.
A5 D10-5 `CNOT_01`, `CNOT_11`; D10-2 phase gate `Phase_S` unitary.
A6 D13-4 phase invariance of `pure_density`; D13-2 ensemble probability = Re Tr(M*M ρ).
A7 D12-3 rank-one measurement probability \|⟨γ\|ψ⟩\|².
A8 D8-5 expected value: Σ λ_m p_m(ψ) = ⟨ψ\|Hψ⟩, H Hermitian.
A9 D16-4/D14-5 `psd_tensor`, `density_matrix_tensor`.
A10 D23-1 complex-coefficient witness (`herm_witness_of_complex`, `mat_lin_indep_complex_neg_witness`) giving `choi_theorem_3_cptp_iff`: extreme ⟷ complex-linear independence. DONE.
A11 D2-11 Hermitian idempotent is the orthogonal projection onto its range (Pv = v for v = Px; Pw = 0 for w ⊥ range).
A12 D32-1 rename `shor_zero/one` → `phase_code_zero/one`. DONE.

Priority B (medium):
B1 D8-3 unambiguous discrimination of linearly independent states. DONE (`lin_indep_states_unambiguous`, new proof via dual vectors).
B2 D17-4/D18-2 density-preserving ⟺ positive ∧ trace-preserving. DONE (`Day18_Positive_Maps`).
B3 D19-1 n-positive ⟹ Choi matrix psd (DONE, `Day04_29_Supplement`); D19-3 Choi-matrix form of TP/unital (DONE, `Day19_Choi_TP_Unital`).
B4 D30-3/D30-4 three-qubit bit-flip code: syndrome projections, recovery map, correction of ≤ 1 error. DONE (`Day30_BitFlip_Code`).
B5 D32-7 Pauli expansion identity for unitaries. DONE (`Day32_Pauli_Expansion`).
B6 D11-3 SWAP from three CNOTs (DONE, `Day02_11_Supplement`); D10-1 superdense coding table (DONE, `Day10_15_Supplement`).
B7 D12-1/D12-4 N-fold Hadamard and the counting probability. DONE (`Day12_Counting_Probability`, proved directly with `tensor_pow_mat` rather than via AFP Deutsch_Jozsa).
B8 D15-6 A-side partial-trace lemmas (DONE, `Day10_15_Supplement`).
B9 D22-6 corollary cr(Φ) ≤ d for extreme maps. DONE (`Day22_Kraus_Independence`, via JNF `vec_space.li_le_dim`).

Priority C (substantial developments, recorded as open):
C1 D20-4 cr(Φ) = rank(P_Φ). DONE (`Day20_Choi_Rank`).
C2 D21-5/D21-6 unitary freedom of rank-one decompositions and Kraus representations (Choi 2). DONE (`Day21_Unitary_Freedom`, with D21-3); D22-1 DONE (`Day22_Minimal_Kraus`).
C3 D24–D26 operator systems, Arveson correspondence and extension theorem; D27-3, D28-3 positive-map criterion. DONE (`Day24_Operator_Systems`, `Day25_Arveson_Correspondence`, `Day26_Arveson_Extension`, `Day27_Positive_Map_Criterion`); D25-4 DONE (`Day25_Unital_Functional_Norm`), D26-1 DONE (`Day26_CP_Factorization`).
C4 D17-3 environment (Stinespring) model of noise. DONE (`Day17_Environment_Model`).
C5 D18-4, D27-2, D28-5 transpose examples and Horodecki–Peres. DONE (`Day18_Positive_Maps`, `Day27_Entangled_Examples`, `Day28_Horodecki_Peres`).
C6 D22-4 compactness of UCP (DONE, `Day22_UCP_Compact`, in Choi coordinates).
C7 D32–D34 Shor code and Knill–Laflamme conditions. Knill–Laflamme: D34-1, D34-3 and the necessity half of D34-2 DONE (`Day34_Knill_Laflamme`), the general recovery proposition D32-4/D33-2 DONE (`Day32_Recovery_Proposition`); the sufficiency half of D34-2 DONE (`Day34_KL_Sufficiency`); the Shor code D32-3, D33-1, D33-2 DONE (`Day33_Shor_Code`; D32-5 is false as stated). C7 closed.
C8 D5-1 Sylvester's criterion (DONE, `Day05_Sylvester_Criterion`, imported from the AFP); D29-3 Hamming code (DONE, `Day29_Classical_Codes`).

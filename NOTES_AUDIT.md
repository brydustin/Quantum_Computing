# Audit: Paulsen's lecture notes vs. the Isabelle formalisation

Source of truth: `QC_Notes.pdf` (Vern Paulsen, *Lectures on Quantum Computing and
Completely Positive Maps*, Houston, Fall 2011; notes by Brandon Lee), transcribed in
`QC_Notes_overleaf.tex`.  Formalisation: the nine theories of the sessions
`Vern_Paulsen_QC_3_10`, `Vern_Paulsen_QC_3_10_Lmat`, `Vern_Paulsen_QC` (see `ROOT`).

Verification status (2026-10-18): all three sessions build
with `quick_and_dirty = false`; no `sorry`, no `axiomatization`, no `oops`; a
`Thm_Deps.all_oracles` check of the main theorems reports no oracles.  The theorem on
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
D22M = `Day22_Minimal_Kraus`, D34 = `Day34_Knill_Laflamme`, D20 = `Day20_Choi_Rank`, D34S = `Day34_KL_Sufficiency`, with shared lemmas in `QC_Prelims`.

---

## Part I: Basic math (Days 1–7)

### Day 1 (22 Aug): overview, inner products
| id | notes | formal | status |
|---|---|---|---|
| D1-1 | computing overview, course overview, references | – | – |
| D1-2 | inner product on ℂⁿ, sesquilinearity, positivity | library `inner_prod` (IMD); BM `inner_prod_expand`; QC3 `inner_prod_right_add'`, `_right_smult'`, `_left_smult'`, `_left_minus'`, `cpx_vec_length_zero_iff`, `cpx_vec_length_smult` | ✓ |
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
| D2-8 | P does not depend on the ONB chosen for V | ✗ (needs a notion of span; low value) | ✗ |
| D2-9 | Parseval ‖v‖² = Σ\|⟨v_i\|v⟩\|² | BM `parseval_norm` | ✓ |
| D2-10 | P² = P, P = P* | BM `outer_sum_idempotent`, `outer_sum_hermitian` | ✓ |
| D2-11 | Theorem: P² = P = P* ⟹ P is the orthogonal projection onto range P | QC11 `projection`, `projection_fixes_range`, `projection_annihilates_orthogonal` | ✓ |

### Day 3 (31 Aug): unitaries, Householder, Schur
| id | notes | formal | status |
|---|---|---|---|
| D3-1 | U unitary iff U*U = I | library `unitary` (bundles U*U = I and UU* = I); QC3 `unitary_left_right` | ✓ |
| D3-2 | TFAE (a) unitary (b) invertible with U⁻¹ = U* (c) UU* = I (d) U* unitary (e) columns ONB (f) rows ONB (g) isometry (h) inner-product preserving | (a)⟹(b) `unitary_invertible`; (a)⟺(c) by definition; (a)⟹(d) `unitary_dagger_is_unitary` (converse by applying it to U*); (a)⟹(e) `unitary_cols_orthonormal`, (e)⟹(a) BM `orthonormal_mat_unitary`; (a)⟹(f) `unitary_rows_orthonormal`; (a)⟹(g) `unitary_isometry`; (a)⟹(h) `unitary_preserves_inner_prod`; (g)⟹(a) `unitary_of_isometry`, (h)⟹(a) `unitary_of_inner_prod_preserving` | ✓ |
| D3-3 | Householder U_w = I − 2P_w is unitary (‖w‖ = 1) | QC3 `householder`, `householder_outer_prod`, `householder_hermitian`, `householder_unitary` | ✓ |
| D3-4 | Schur's lemma: ‖x‖ = ‖y‖ ⟹ ∃w, θ. U_w x = e^{iθ} y | QC3 `schur_lemma` | ✓ |
| D3-5 | Schur's theorem: U*AU upper triangular | QC3 `schur_theorem` | ✓ |
| D3-6 | Tr A = Σ eigenvalues (roots of the characteristic polynomial) | QC3 `trace_eq_sum_eigenvalues` | ✓ |

### Day 4 (2 Sep): Hermitian and positive matrices
| id | notes | formal | status |
|---|---|---|---|
| D4-1 | Hermitian TFAE (a) H = H* (b) U*HU = D real diagonal (c) ONB of eigenvectors, real eigenvalues (d) ⟨x\|Hx⟩ ∈ ℝ | (a)⟹(b) `hermitian_spectral_decomp`; (b)⟹(c) `hermitian_spectral_decomp_right` + `unitary_cols_orthonormal`; (a)⟺(d) `hermitian_iff_real_quad_form`; real eigenvalues `hermitian_real_eigenvalues`.  (b)⟹(a) and (c)⟹(a) only implicitly (`diag_mat_of_real_hermitian`) | ~ |
| D4-2 | Lemma: ⟨x\|Tx⟩ = 0 ∀x ⟹ T = 0 (fails over ℝ) | QC3 `quadratic_form_zero` (remark on ℝ not needed) | ✓ |
| D4-3 | P ≥ 0 iff ⟨x\|Px⟩ ≥ 0; P > 0 iff > 0 for x ≠ 0 | QC3 `psd`, `pd` (with `hermitian P` as an explicit conjunct); the notes' form is `psd_iff_quad_form_nonneg` | ✓ |
| D4-4 | P ≥ 0 iff P = P* and all eigenvalues ≥ 0 | QC3 `psd_iff_nonneg_eigenvalues` | ✓ |
| D4-5 | Corollary: P > 0 iff P = P* and all eigenvalues > 0 | QC3 `pd_iff_pos_eigenvalues` | ✓ |
| D4-6 | P ≥ 0 iff P = Σ\|v_i⟩⟨v_i\| | QC3 `psd_kraus_decomp` (⟹), `outer_sum_psd` (⟸) | ✓ |
| D4-7 | Key: ⟨x\|Px⟩ = Σ\|⟨v_i\|x⟩\|² | QC3 `inner_prod_outer_sum_general` (as ⟨V*x\|V*x⟩) | ✓ |
| D4-8 | P = Σ\|v_i⟩⟨v_i\| > 0 iff span{v_i} = ℂⁿ | QC3 `pd_iff_spanning` (spanning phrased as: no nonzero x ⊥ all v_i) | ~ |

### Day 5 (7 Sep): tests for positivity, direct sums, block matrices
| id | notes | formal | status |
|---|---|---|---|
| D5-1 | leading principal minors test (stated, no proof) | ✗ (Sylvester's criterion; outside the notes' proofs) | ✗ |
| D5-2 | Cholesky reduction: P ≥ 0 iff P − p_{i1}p_{1j}/p_{11} ≥ 0 | QC3 `cholesky_reduction` (adds the hypothesis p₁₁ > 0 that the notes leave implicit) | ~ |
| D5-3 | two 3×3 numerical examples | – | – |
| D5-4 | direct sum V ⊕ W, inner product | QC3 `direct_sum_vec` (⊕ᵥ), `direct_sum_inner_prod`, `direct_sum_dim` | ✓ |
| D5-5 | basis of V ⊕ W, dim(V ⊕ W) = dim V + dim W | `direct_sum_dim` (vector form only) | ~ |
| D5-6 | block matrices act on (v, w) | QC3 `block_mat_apply` | ✓ |

### Day 6 (9 Sep): tensor products
| id | notes | formal | status |
|---|---|---|---|
| D6-1 | bilinear maps, universal property (axiom) | concrete Kronecker model `tensor_vec`; bilinearity `tensor_vec_bilinear_left/right`, `tensor_vec_smult_left/right` | ~ |
| D6-2 | {e_i ⊗ f_j} basis; dim(X ⊗ Y) = dim X · dim Y | QC3 `tensor_vec_dim`, `tensor_onb` (ONB version, Day 7) | ✓ |
| D6-3 | unique x_j with u = Σ x_j ⊗ f_j; X ⊗ Y ≅ X ⊕ ⋯ ⊕ X | ✗ (implicit in QC11 `operator_tensor_space_isomorphism` for operators) | ✗ |
| D6-4 | Schmidt rank | QC3 `schmidt_rank` (definition only) | ~ |

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
| D8-2 | non-orthogonal states cannot be: p₁(ψ₂) ≥ \|α\|² > 0 | ✗ | ✗ |
| D8-3 | Theorem: linearly independent states admit unambiguous discrimination (M₀,…,M_n) | QC3 `lin_indep_states_unambiguous` (replaces a commented-out attempt that contained a `sorry`); linear independence is `lin_indep_vecs`; the inconclusive outcome is listed last | ✓ |
| D8-4 | P^{1/2} for P ≥ 0 | QC3 `psd_sqrt_exists`; `psd_sqrt` is now defined as a choice of square root with `psd_sqrt_props` (carrier, psd, Q·Q = P) | ✓ |
| D8-5 | expected value E = ⟨ψ\|Hψ⟩ with H = Σ λ_m M_m*M_m Hermitian | QC3 `observable`, `observable_hermitian`, `expected_value_eq_quad_form` | ✓ |

### Day 9 (16 Sep): POVMs, composite systems, entanglement
| id | notes | formal | status |
|---|---|---|---|
| D9-1 | POVM {P_m}, P_m ≥ 0, Σ P_m = I; M_m = P_m^{1/2} is a measurement system | QC3 `povm`, `measurement_induces_povm`, `povm_from_sqrt`, `povm_prob` | ✓ |
| D9-2 | Postulate 4: composite state ψ₁ ⊗ ψ₂ | QC3 `tensor_of_states_is_state` | ✓ |
| D9-3 | two-photon example; entangled iff Schmidt rank > 1 | QC3 `entangled` (defined as "not a product"), `bell_state_entangled` | ✓ |
| D9-4 | R ⊗ T exists uniquely; (R₁⊗T₁)(R₂⊗T₂) = R₁R₂ ⊗ T₁T₂; (R⊗T)* = R*⊗T* | library `tensor_mat`; BM `tensor_mat_mult`, `tensor_mat_adjoint`, `tensor_mat_unitary` | ✓ |
| D9-5 | p^{AB}_m(ψ⊗φ) = p^A_m(ψ) | QC3 `composite_measurement_prob`, `tensor_mat_vec_mult` | ✓ |
| D9-6 | eavesdropping example p₀(γ) = ½ with Bell state | ✗ (example) | ✗ |

### Day 10 (19 Sep): superdense coding, gates
| id | notes | formal | status |
|---|---|---|---|
| D10-1 | superdense coding: the four Bell states from γ by I, Z, X, XZ | QC3 `bell_basis`, `bell_basis_orthonormal`; the action table ((Z⊗I)γ = … etc.) is not proved | ~ |
| D10-2 | one-qubit gates X, Z, Y, H, S | QC11 `pauli_X/Y/Z` (+ unitary, involution, products), QC3 `H_gate`, `hadamard_e0/e1`, `S_gate`, `S_gate_unitary` | ✓ |
| D10-3 | "H² = X" | the notes are wrong here (corrected on Day 11 to H² = I); formal `hadamard_squared` proves H² = I | ✓ |
| D10-4 | classical gates AND/OR/XOR/NAND/NOR, Pierce/Sheffer remarks | – | – |
| D10-5 | CNOT matrix, unitary | library `CNOT`; QC3 `CNOT_unitary`, `CNOT_00`, `CNOT_01`, `CNOT_10`, `CNOT_11` | ✓ |
| D10-6 | Toffoli CCNOT, unitary | QC11 `CCNOT`, `CCNOT_unitary`, `CCNOT_inv` | ✓ |

### Day 11 (21 Sep): corrections, circuits, no-cloning
| id | notes | formal | status |
|---|---|---|---|
| D11-1 | H² = I, He₀, He₁, Xe₀, Xe₁ | QC3 `hadamard_squared`, `hadamard_e0`, `hadamard_e1`; X on basis vectors via `pauli_X_ket_plus/minus` only | ✓ |
| D11-2 | CNOT, CCNOT truth tables | QC3 `CNOT_00`, `CNOT_10`; QC11 `CCNOT` definition | ~ |
| D11-3 | circuit diagrams; SWAP = CNOT·CNOT′·CNOT | ✗ | ✗ |
| D11-4 | CNOT clones the computational basis | QC3 `CNOT_00`, `CNOT_10` | ✓ |
| D11-5 | No-cloning theorem | QC11 `is_cloner`, `no_cloning` (proof via two non-orthogonal states, `two_states_nontrivial_inner_prod`; the notes use −ψ) | ✓ |

### Day 12 (23 Sep): quantum parallelism
| id | notes | formal | status |
|---|---|---|---|
| D12-1 | H^{⊗N}\|0…0⟩ = 2^{−N/2} Σ_J \|J⟩ | D12 `hadamard_uniform_N` (`tensor_pow_mat H_gate N *v tensor_pow_vec (unit_vec 2 0) N = uniform_vec N`), with `uniform_tensor_e0_as_sum` the Σ_J form; QC11 `hadamard_uniform_1` is N = 1 | ✓ |
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
| D13-5 | ‖γ‖² = Tr\|γ⟩⟨γ\| | QC11 `Tr_outer_sum_single`, `rank1_projection_trace_inner` | ✓ |
| D13-6 | density matrix of an ensemble | QC11 `ensemble_density`, `density_matrix`, `ensemble_density_is_dm` | ✓ |

### Day 14 (28 Sep): which matrices are density matrices; pure states; composite ensembles
| id | notes | formal | status |
|---|---|---|---|
| D14-1 | ρ is the density matrix of some ensemble iff ρ ≥ 0, Tr ρ = 1; spectral ensemble | QC11 `density_matrix_iff_ensemble`, `spectral_ensemble_exists`, `density_matrix_characterisation` | ✓ |
| D14-2 | non-uniqueness remark (ρ = XX*) | – | – |
| D14-3 | ensembles representing \|ψ⟩⟨ψ\| consist of multiples of ψ (pure states) | QC11 `pure_ensemble_parallel`, `pure_density_iff_idempotent` | ✓ |
| D14-4 | \|ψ⊗φ⟩⟨ψ⊗φ\| = \|ψ⟩⟨ψ\| ⊗ \|φ⟩⟨φ\| | QC11 `tensor_pure_density` | ✓ |
| D14-5 | composite ensemble density Σ p_i q_l (…⊗…) is a density matrix | QC11 `density_matrix_tensor` (for the product of two densities) | ~ |

### Day 15 (30 Sep): traces, L(H_A)⊗L(H_B) ≅ L(H_A⊗H_B), partial trace
| id | notes | formal | status |
|---|---|---|---|
| D15-1 | Tr A = Σ⟨u_i\|Au_i⟩ for any ONB | QC11 `trace_via_onb` | ✓ |
| D15-2 | Tr(R ⊗ T) = Tr R · Tr T | QC11 `trace_tensor` | ✓ |
| D15-3 | Γ : L(H_A) ⊗ L(H_B) → L(H_A ⊗ H_B) is an isomorphism | QC11 `operator_tensor_space_isomorphism`, `operator_tensor_space_isomorphic` (coordinate form M_{m²,p²} ≅ M_{mp}) | ~ |
| D15-4 | partial traces tr_B(R⊗T) = Tr(T) R, tr_A(R⊗T) = Tr(R) T | QC11 `partial_trace_B`, `partial_trace_A` (block formulas of Day 16), `partial_trace_B_tensor`, `partial_trace_A_tensor` | ✓ |
| D15-5 | p_α(ρ) = Tr((M*M ⊗ I)ρ) = Tr(M*M ρ^A) | QC11 `partial_trace_measurement` | ✓ |
| D15-6 | Tr ρ^A = Tr ρ; ρ ≥ 0 ⟹ ρ^A ≥ 0 | QC11 `partial_trace_B_trace`, `partial_trace_B_hermitian`, `partial_trace_B_is_density` (B-side only; A-side analogues missing) | ~ |

### Day 16 (3 Oct): partial traces in block form; postulates 1′–4′
| id | notes | formal | status |
|---|---|---|---|
| D16-1 | tr_B((X_{ij})) = Σ X_{ii}, tr_A((X_{ij})) = (Tr X_{ij}) | these are the formal definitions `partial_trace_B/A` (A-major Kronecker indexing) | ✓ |
| D16-2 | H_A ⊗ H_B ≅ H_A^{(p)}, L(H_A⊗H_B) ≅ M_p(L(H_A)) | QC11 `block_of_mat`, `amplification` (block action); isomorphism D15-3 | ~ |
| D16-3 | Postulates 1′ (density matrices), 2′ (UρU*), 3′ (p_α = Tr(M*Mρ)) | QC11 `density_matrix`; `unitary_conj_channel_preserves_density_matrix`, `conjugation_channel`; `ensemble_prob_trace`, `meas_map_density` | ✓ |
| D16-4 | Postulate 4′: ρ₁ ⊗ ρ₂ is a density matrix | QC11 `psd_tensor`, `density_matrix_tensor` | ✓ |

### Day 17 (5 Oct): measurement maps, noise, axiomatic channels
| id | notes | formal | status |
|---|---|---|---|
| D17-1 | measurement map M(ρ) = Σ M_α ρ M_α* maps densities to densities | QC11 `meas_map`, `meas_map_psd`, `meas_map_density` | ✓ |
| D17-2 | stochastic matrices, Markov chains | – | – |
| D17-3 | environment model: tr_E(U(ρ ⊗ \|φ⟩⟨φ\|)U*) = Σ W_i ρ W_i*, Σ W_i*W_i = I | ✗ | ✗ |
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
| D19-1 | Choi: (1) CP ⟺ (2) n-positive ⟺ (3) P_Φ = (Φ(E_{ij})) ≥ 0 ⟺ (4) Φ(X) = Σ B_i X B_i* | QC11 `choi_matrix`, `choi_theorem` ((1)⟺(3)), `choi_psd_if_cp`, `kraus_rep_of_psd_choi` ((3)⟹(4)), `kraus_is_cp`/`kraus_cp_no_tp` ((4)⟹(1)).  (2)⟹(3) not isolated: `choi_matrix_as_amplification` is the key step | ~ |
| D19-2 | Notes: Choi–Kraus representation, Choi–Jamiołkowski matrix, CP ↔ M_n(M_d)⁺ | `choi_matrix_kraus_eq` (D23), `choi_theorem` | ✓ |
| D19-3 | TP iff Tr(R_{ij}) = δ_{ij}; unital iff Σ R_{ii} = I (Choi-matrix form) | ✗ (TP/unital are characterised via Kraus lists instead: `kraus_is_trace_preserving`, `kraus_map_dim_one`) | ✗ |

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
| D21-2 | conjecture on averages of UCP maps | – | – |
| D21-3 | T injective ⟹ T* onto; v_i independent ⟹ v_i v_j* independent | D21 `outer_prods_lin_indep` (v_i independent ⟹ the r² matrices v_i v_j* independent over ℂ, via dual vectors `dual_vectors_exist` from the Gram inverse); the T injective ⟹ T* onto remark is not used | ✓ |
| D21-4 | 0 ≤ ww* ≤ P ⟹ w ∈ range P; range of Σ w_l w_l* | D23 `loewner_ker_subset` (kernel form: ker A ⊆ ker B when 0 ≤ B ≤ A) | ~ |
| D21-5 | Theorem: two rank-one decompositions of P are related by an isometry U | D21 `rank_one_decomp_isometry`: if VV* = WW* with the columns of V independent (the notes: rank P = r) then W = V Uᵗ for an m × r isometry U; `rank_one_decomp_isometry_cols` gives w_l = Σ_j α_{lj} v_j | ✓ |
| D21-6 | Choi 2: unitary freedom of Kraus representations | D21 `choi_2_unitary_freedom`: Σ V_j X V_j* = Σ W_l X W_l* on M_n with the V_j linearly independent ⟹ W_l = Σ_j α_{lj} V_j with (α_{lj}) an isometry (proof through the Choi matrix and D21-5) | ✓ |

### Day 22 (17 Oct): minimal Kraus representations, convexity, UCP/CPTP
| id | notes | formal | status |
|---|---|---|---|
| D22-1 | minimal (r = cr Φ) Kraus operators are linearly independent | D22M `minimal_kraus_rep_lin_indep` (a Kraus list of length cr Φ is `lin_indep_complex_mat`; proof: a dependence is rotated by a unitary with prescribed first row into a representation with a zero operator, `kraus_mix_same_map`) | ✓ |
| D22-2 | convex sets, extreme points, convex hull, affine maps | QC11 `convex_set_mat`, `extreme_point_mat`, `affine_map_mat` | ✓ |
| D22-3 | Krein–Milman (stated) | – (available as HOL-Analysis `Krein_Milman_Minkowski`) | – |
| D22-4 | UCP(M_n,M_d) convex and compact | QC11 `UCP`, `UCP_convex`; compactness ✗ | ~ |
| D22-5 | CPTP convex; Γ(Φ) = Φ* affine bijection UCP → CPTP | QC11 `CPTP`, `CPTP_convex`; affineness of Γ ✗ | ~ |
| D22-6 | Choi 3 (statement) and corollaries: extreme ⟹ cr(Φ) ≤ d; CPTP version | see D23; corollary: D22 `extreme_CPTP_kraus_length_le` (r ≤ n for a Kraus representation with independent products) and `extreme_CPTP_choi_rank_le` (cr Φ ≤ n for extreme CPTP Φ: M_n → M_d, the notes' d) | ✓ |

### Day 23 (19 Oct): proof of Choi's Theorem 3, examples
| id | notes | formal | status |
|---|---|---|---|
| D23-1 | Choi 3: Φ UCP with minimal Kraus rep (V_i) is extreme iff {V_i*V_j} linearly independent | D23 `choi_theorem_3_cptp` proves the CPTP form (the notes' corollary): for a CPTP Φ with Kraus representation (V_i) consisting of linearly independent operators, extreme (`extreme_CPTP_carrier`) ⟺ complex-linear independence of {V_j*V_i} (`choi_theorem_3_cptp_iff`; the perturbation step yields a real relation and `herm_witness_of_complex` converts a complex one).  Differences: (i) CPTP instead of UCP (the two are exchanged by Φ ↦ Φ*, D20-2); (ii) hypothesis "V_i linearly independent" replaces "r = cr Φ" (D22-1); (iii) extremality is the carrier-point notion, because functions on `complex Matrix.mat` are only constrained on `carrier_mat n n` | ~ |
| D23-2 | forward direction via perturbation ψ_± | D23 `choi_theorem_3_cptp_reverse_carrier` (perturbation `kraus_quad_map`, `small_eps_psd`, `sym_or_antisym_witness`) | ✓ |
| D23-3 | reverse direction via Choi 2 | D23 `choi_theorem_3_cptp_forward_complex` via CP Radon–Nikodym (`cp_radon_nikodym_linear`, `dominated_outer_sum_param`) instead of Choi 2 | ~ |
| D23-4 | Examples: U*XU extreme; ½(U₁*XU₁+U₂*XU₂) not; Tr(X)I not; diag not | ✗ | ✗ |

## Part IV: Operator systems, Arveson, entanglement (Days 24–28)

### Day 24 (24 Oct): operator systems, Arveson's extension and correspondence
| id | notes | formal | status |
|---|---|---|---|
| D24-1 | operator systems, M_p(S), CP maps on S | ✗ | ✗ |
| D24-2 | X ∈ S is a combination of four positives in S | ✗ (M_n case: `matrix_decomp_psd`) | ✗ |
| D24-3 | Arveson's extension theorem (statement, corollary) | ✗ | ✗ |
| D24-4 | S_Φ and Arveson: CP ⟺ d-positive ⟺ S_Φ positive | ✗ | ✗ |

### Day 25 (26 Oct): Arveson correspondence, Hahn–Banach
| id | notes | formal | status |
|---|---|---|---|
| D25-1 | f ↦ Φ_f, S_Φ ↔ Φ mutual inverses; CP(S,M_d) ≅ P(M_d(S),ℂ) affinely | ✗ | ✗ |
| D25-2 | bounded functionals, ‖f‖ | MT `bounded_clinear_functional_on` | ✓ |
| D25-3 | Hahn–Banach: norm-preserving extension of a bounded linear functional | MT `matrix_hahn_banach_lmat`, `matrix_hahn_banach_lmat_with_bound` (complex HB on matrix spaces, derived from HOL-Hahn_Banach via Bohnenblust–Sobczyk) | ✓ |
| D25-4 | Proposition: f(I) = 1 ⟹ (f positive iff ‖f‖ = 1) | ✗ | ✗ |

### Day 26 (28 Oct): Arveson extension proof; separability defined
| id | notes | formal | status |
|---|---|---|---|
| D26-1 | CP Φ with Φ(I) = P is V*ψ(X)V with ψ UCP; CP Φ = ψ(VXV*) with ψ CPTP | ✗ | ✗ |
| D26-2 | Arveson extension theorem (proof) | ✗ | ✗ |
| D26-3 | separable density matrix Σ p_l \|ψ_l⟩⟨ψ_l\| ⊗ \|φ_l⟩⟨φ_l\|; entangled otherwise | SC `separable_lmat_gen`, `separable_cone_lmat`, `Sprime`; D24 `D26_separable_density_iff_convex_combination` (= SC `separable_density_iff_in_convex_hull_Sprime`: for density matrices, cone membership ⟺ convex combination of product densities) | ✓ |

### Day 27 (31 Oct): positive maps detect entanglement; convex cones
| id | notes | formal | status |
|---|---|---|---|
| D27-1 | Φ positive, R separable ⟹ Φ^{(r)}(R) ≥ 0 | ✗ | ✗ |
| D27-2 | Examples of entangled matrices via the transpose | ✗ | ✗ |
| D27-3 | f(Sep) ≥ 0 iff Φ_f positive | ✗ (needs Arveson correspondence) | ✗ |
| D27-4 | cones; separation of a point from a closed convex set / closed cone | HOL-Analysis `separating_hyperplane_closed_point`; SC `separable_cone_lmat_closed`, `separable_cone_lmat_separating_hyperplane` | ✓ |

### Day 28 (2 Nov): entanglement witnesses, Horodecki, Peres
| id | notes | formal | status |
|---|---|---|---|
| D28-1 | the separable matrices form a closed cone in the Hermitian matrices | SC `separable_cone_lmat_closed`, `separable_cone_lmat_hermitian`, `separable_cone_lmat_convex_cone` | ✓ |
| D28-2 | real functional f with f(R) < 0 ≤ f(C); complexification f̃ | SC `separable_cone_lmat_separating_hyperplane`, `hermitian_witness_from_lmat`, `entanglement_witness_hermitian'` | ✓ |
| D28-3 | Theorem: R ≥ 0 separable iff Φ^{(r)}(R) ≥ 0 for all positive Φ : M_n → M_r | ~ : formalised in the witness form `separable_iff_witness`, `separable_density_iff_witness` (R separable iff every Hermitian W nonneg on the cone has Tr(WR) ≥ 0); the positive-map form needs the Arveson correspondence | ~ |
| D28-4 | strict witnesses for density matrices | SC `entanglement_witness_strict`, `entanglement_witness_for_density` | ✓ (beyond the notes) |
| D28-5 | Horodecki–Peres: for v ∈ ℂ²⊗ℂ², separable iff partial transpose of \|v⟩⟨v\| ≥ 0 | D28 `horodecki_peres_two_qubits`: psd (id⊗t)(\|v⟩⟨v\|) ⟷ v = α⊗β (pure states: separable = product); `horodecki_peres_entangled`; witness value −2\|v₀v₃−v₁v₂\|² (`partial_transpose_witness_value`) | ✓ |

## Part V: Error correction (Days 29–34)

### Day 29 (7 Nov): classical codes
| id | notes | formal | status |
|---|---|---|---|
| D29-1 | repetition code | QC11 `repetition_encode`, `hamming_dist_repetition_doubles`, `hamming_weight_repetition_encode` | ✓ |
| D29-2 | parity check detects one error | QC11 `parity_check_encode`, `parity_check_detects_one_error` | ✓ |
| D29-3 | Hamming [7,1,3] code | ✗ | ✗ |
| D29-4 | Hamming weight, distance of a code, subspace codes | QC11 `hamming_weight`, `hamming_dist`, `code_distance`, `corrects_errors` (definitions; `hamming_dist_zero`, `_symm`) | ~ |
| D29-5 | left inverses, cyclic codes | – | – |

### Day 30 (9 Nov): error probabilities; three-qubit bit-flip code
| id | notes | formal | status |
|---|---|---|---|
| D30-1 | undetected-error probabilities, majority rule | ✗ (elementary arithmetic) | ✗ |
| D30-2 | encoding a\|0⟩+b\|1⟩ ↦ a\|000⟩+b\|111⟩ | QC11 `encode_mat` | ✓ |
| D30-3 | syndrome projections P₀…P₃, Σ P_i = I | D30 `syndrome_proj`, `syndrome_proj_sum`, `syndrome_proj_idem`, `syndrome_proj_hermitian`; flips `flip_bit_mat` = the tensors X⊗I⊗I, … (`flips_as_tensors`) | ✓ |
| D30-4 | recovery map R is CPTP and R(\|ψ_i⟩⟨ψ_i\|) = \|ψ⟩⟨ψ\| for ≤ 1 error | D30 `recovery_map_CPTP`, `bit_flip_code_recovery` (four statements: no error and a flip on each qubit) | ✓ |

### Day 31 (11 Nov): operator viewpoint, fidelity
| id | notes | formal | status |
|---|---|---|---|
| D31-1 | error map E(Y) = (1−p)Y + pXYX is CPTP | QC11 `bit_flip_channel`, `_trace_preserving`, `_psd`, `_CPTP`, `_UCP` | ✓ |
| D31-2 | R∘E on the encoded state; code better iff p ≤ ½ | ✗ | ✗ |
| D31-3 | fidelity F = \|⟨ψ′\|ψ⟩\| = √Tr(ρρ′); F = √⟨ψ\|R∘E(\|ψ⟩⟨ψ\|)ψ⟩ | QC11 `fidelity`, `fidelity_pure_states`, `fidelity_self`, `fidelity_orthogonal` | ✓ |
| D31-4 | min F = √(1−p) (do nothing) vs √((1−p)³+3p(1−p)²) (code) | ✗ | ✗ |

### Day 32 (14 Nov): phase-flip code, Shor code, Pauli magic
| id | notes | formal | status |
|---|---|---|---|
| D32-1 | \|±⟩, Z\|+⟩ = \|−⟩, phase-flip code \|0⟩ ↦ \|+++⟩ | QC11 `ket_plus`, `ket_minus`, `pauli_Z_ket_plus/minus`, `ket_plus_minus_orthog`; the code words \|+++⟩, \|−−−⟩ are `phase_code_zero`/`phase_code_one` (renamed from `shor_zero`/`shor_one` in the audit pass) | ✓ |
| D32-2 | Y-version with β = Y\|+⟩ | ✗ | ✗ |
| D32-3 | Shor code \|0_L⟩, \|1_L⟩ ∈ ℂ^{2⁹}; Shor's theorem | ✗ | ✗ |
| D32-4 | Proposition: U_iV mutually orthogonal ⟹ CPTP recovery R exists | D32R `recovery_ops_kraus_operators`, `recovery_map_CPTP'`, `recovery_single_error` (hypotheses bundled as `recovery_setting n P Us`: P projection, PU_i*U_jP = δ_ij P; for unitaries this is the notes' hypothesis, `recovery_setting_unitaries`) | ✓ |
| D32-5 | 1-Pauli operators; orthogonality of their images of V | ✗ | ✗ |
| D32-6 | Pauli magic: I, X, Y, Z orthogonal with norm √2 | QC11 `pauli_orthogonal`, `pauli_norm` | ✓ |
| D32-7 | U = a₀I + a₁X + a₂Y + a₃Z unitary ⟹ Σ\|a_i\|² = 1 | D32 `pauli_expansion_unitary` | ✓ |

### Day 33 (16 Nov): Shor code recovery
| id | notes | formal | status |
|---|---|---|---|
| D33-1 | 28 orthogonal subspaces; Z₁v = Z₂v = Z₃v on V | ✗ | ✗ |
| D33-2 | recovery R corrects every single-qubit unitary error | D32R `recovery_linear_combination`: for ψ ∈ V and φ = Σ_i a_i U_i ψ, R(\|φ⟩⟨φ\|) = (Σ\|a_i\|²)\|ψ⟩⟨ψ\| (the general form; the Pauli instance is this with U_i = I, X, Y, Z) | ~ |

### Day 34 (18 Nov): Knill–Laflamme conditions
| id | notes | formal | status |
|---|---|---|---|
| D34-1 | R∘E fixes \|ψ⟩⟨ψ\| on V iff it fixes PXP | D34 `recovery_states_iff_PXP` (via `psd_PXP_decomp_in_range` and the decomposition of X into four positives) | ✓ |
| D34-2 | Theorem 1: correctable iff PE_i*E_jP = α_{ij}P | D34S `knill_laflamme` (the iff). ⟹ D34 `knill_laflamme_necessity` (via Choi 2 applied to the two Kraus representations {P} and {A_lE_iP} of X ↦ PXP, `kl_kraus_scalars`); ⟸ D34S `knill_laflamme_sufficiency` (α Hermitian, diagonalised by `hermitian_spectral_decomp`; the mixed errors F_k = Σ_i u_ik E_i give the same channel and satisfy PF_k*F_lP = δ_kl d_k P (`kl_mix_bracket`); the F_k/√d_k with d_k > 0 satisfy the hypotheses of the recovery proposition) | ✓ |
| D34-3 | Theorem 2: closure under linear combinations of the errors | D34 `knill_laflamme_closure`: if R∘E fixes PXP and G_i = Σ_j g_{ij}E_j with Σ G_i*G_i = I (`kraus_mix`), then R∘G fixes PXP | ✓ |

---

## Infrastructure not in the notes (formalised to make the above possible)
* BM: tensor-product algebra (`tensor_mat_mult`, `tensor_mat_adjoint`, `tensor_mat_unitary`), unitary algebra.
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
7. The entanglement theory is formalised in witness form rather than the positive-map form (D28-3); the two are equivalent via the Arveson correspondence, which is not formalised.
8. The three-qubit phase-flip code words were called `shor_zero`/`shor_one`; renamed `phase_code_zero`/`phase_code_one` (D32-1).
9. `psd_sqrt` was a placeholder constant equal to the zero matrix; now defined via `SOME` with `psd_sqrt_props` (D8-4).
10. `Day24_Separability` attributed the separability material to Days 24–28; the theorem prefixes now follow the notes (D26 definition of separability, D27 cone and separation, D28 closedness and witnesses).

## Gap list and plan
Priority A (cheap, improve fidelity) — ALL CLOSED in the 2026-10-18 pass:
A1 D3-2 converses: isometry ⟹ unitary is the library's `length_preserving_is_unitary` (Isabelle_Marries_Dirac); add a vector-form wrapper and the inner-product version.
A2 D4-5 `pd_iff_pos_eigenvalues`.
A3 D4-3 `psd_iff_quad_form_nonneg` (notes' definition).
A4 D8-4 redefine `psd_sqrt` via `SOME` with `psd_sqrt_props`. DONE.
A5 D10-5 `CNOT_01`, `CNOT_11`; D10-2 phase gate `S_gate` unitary.
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
B3 D19-1 n-positive ⟹ Choi matrix psd; D19-3 Choi-matrix form of TP/unital.
B4 D30-3/D30-4 three-qubit bit-flip code: syndrome projections, recovery map, correction of ≤ 1 error. DONE (`Day30_BitFlip_Code`).
B5 D32-7 Pauli expansion identity for unitaries. DONE (`Day32_Pauli_Expansion`).
B6 D11-3 SWAP from three CNOTs; D10-1 superdense coding table.
B7 D12-1/D12-4 N-fold Hadamard and the counting probability. DONE (`Day12_Counting_Probability`, proved directly with `tensor_pow_mat` rather than via AFP Deutsch_Jozsa).
B8 D15-6 A-side partial-trace lemmas.
B9 D22-6 corollary cr(Φ) ≤ d for extreme maps. DONE (`Day22_Kraus_Independence`, via JNF `vec_space.li_le_dim`).

Priority C (substantial developments, recorded as open):
C1 D20-4 cr(Φ) = rank(P_Φ). DONE (`Day20_Choi_Rank`).
C2 D21-5/D21-6 unitary freedom of rank-one decompositions and Kraus representations (Choi 2). DONE (`Day21_Unitary_Freedom`, with D21-3); D22-1 DONE (`Day22_Minimal_Kraus`).
C3 D24–D26 operator systems, Arveson correspondence and extension theorem; D27-3, D28-3 positive-map criterion.
C4 D17-3 environment (Stinespring) model of noise.
C5 D18-4, D27-2, D28-5 transpose examples and Horodecki–Peres. D18-4 and D28-5 DONE (`Day18_Positive_Maps`, `Day28_Horodecki_Peres`); D27-2 open.
C6 D22-4 compactness of UCP/CPTP.
C7 D32–D34 Shor code and Knill–Laflamme conditions. Knill–Laflamme: D34-1, D34-3 and the necessity half of D34-2 DONE (`Day34_Knill_Laflamme`), the general recovery proposition D32-4/D33-2 DONE (`Day32_Recovery_Proposition`); the sufficiency half of D34-2 DONE (`Day34_KL_Sufficiency`); the Shor code (D32-5, D33-1) remains open.
C8 D5-1 Sylvester's criterion; D29-3 Hamming code.

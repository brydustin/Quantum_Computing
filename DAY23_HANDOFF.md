> **FINAL STATUS (2026-10-18): closed.** `Day23_ChoiExtremeUCP.thy` has no
> `sorry`; `dominated_outer_sum_param` and `A_Aplus_B_eq_B` are proved
> (operator-level pseudoinverse argument, see `instructions.md`), so
> `cp_radon_nikodym_choi`/`_linear` and `choi_theorem_3_cptp*` are
> unconditional. The whole project builds with `quick_and_dirty = false`
> and the oracle audit is clean. Everything below is the historical
> handoff and is partly out of date.

# Day 23 / Choi's Theorem 3 — Focused Session Handoff

This document briefs a dedicated session for closing **Choi's Theorem 3**
in `Day23_ChoiExtremeUCP.thy`. Read it cold; everything you need
to start is here.

---

## Goal

Close the theorem

```isabelle
theorem choi_theorem_3_cptp:
  fixes Φ Vs
  assumes npos: "0 < n"  dpos: "0 < d"
      and Φ_in: "Φ ∈ CPTP n d"
      and rep:  "cptp_kraus_rep n d Φ Vs"
  shows "extreme_CPTP n d Φ ⟷ mat_lin_indep_real n (kraus_products Vs)"
```

at `Day23_ChoiExtremeUCP.thy:329` (line may shift). Currently `sorry`.

**Recommended order:** prove the **reverse direction**
(`¬ lin_indep ⟹ ¬ extreme`, contrapositive) first — it doesn't need
Radon–Nikodym. Then attempt the forward direction.

---

## Mathematical roadmap (reverse direction)

Given a non-trivial real linear dependence

> `Σ_{i,j<k} a_{ij} (V_j† · V_i) = 0`  in `M_n`,    `a` not all zero,

construct two CPTP maps `Φ_±` ≠ `Φ` with `Φ = ½(Φ_+ + Φ_-)`.

1. **Build the k×k coefficient matrix** `A` where `A_{ij} := a_{ij}`.
2. **Symmetrize** `A`: the products set `{V_j† V_i}` is closed under
   conjugate-transpose-with-index-swap, so the hermitian part
   `A_s = (A + A^T)/2` also gives a non-trivial dependence; the
   anti-hermitian part `A_a = (A - A^T)/2` does too. WLOG one of
   them is non-zero — work with that one (real symmetric).
3. **Choose ε** so that `T_± := I_k ± ε A` is PSD (eigenvalues all
   positive). Possible for any small enough `ε` since `T_±(0) = I`.
4. **Define the perturbed maps:**
   `Φ_±(X) := Σ_{i,j} (T_±)_{ij} V_i X V_j†`
   (this is what we call `kraus_quad_map d Vs T_± X` below).
5. **CP**: each `T_±` PSD ⟹ each `Φ_±` CP (Lemma A, see below).
6. **TP**: `Σ (T_±)_{ij} V_j† V_i = Σ V_i† V_i ± ε Σ a_{ij} V_j† V_i
                                       = I_n ± ε · 0 = I_n`. ✓
7. **Midpoint**: `½(Φ_+(X) + Φ_-(X)) = Σ ((T_+ + T_-)/2)_{ij} V_i X V_j†
                                       = Σ I_{ij} V_i X V_j† = Φ(X)`.
8. **Distinctness**: `Φ_+ ≠ Φ` iff there exists `X` with
   `Σ a_{ij} V_i X V_j† ≠ 0`. By Lemma B (`kraus_quad_map` is non-zero
   for some X iff the **Choi matrix** `V A V*` is non-zero, where
   `V := [V_0 | V_1 | ... | V_{k-1}]` block-row), and since A ≠ 0 and
   Vs has full row rank under minimality, this holds. **If Vs may
   be non-minimal, we additionally need to add the assumption that
   the Kraus list is minimal**, or pre-process Vs to drop linear
   redundancy.

---

## Lemmas needed

### Lemma A — PSD perturbation is CP

```isabelle
lemma kraus_perturbation_cp:
  assumes "∀V ∈ set Vs. V ∈ carrier_mat d n"
      and "T ∈ carrier_mat (length Vs) (length Vs)"
      and "psd T"
      and "0 < n"  "0 < d"
  shows "completely_positive n d (kraus_quad_map d Vs T)"
```

**Proof sketch:** Apply `psd_kraus_decomp` (in `Quantum_Computing_3_10.thy:3580`)
to write `T = Σ_l |u_l⟩⟨u_l|`. Then verify the rewrite

> `kraus_quad_map d Vs T X = Σ_l W_l X W_l†`    where `W_l := Σ_i (u_l)_i V_i`,

i.e., `kraus_quad_map d Vs T = kraus_map_dim d Ws` with `Ws := map (λu. Σ_i u_i V_i) us`.
CP follows from `kraus_cp_no_tp` (in `Quantum_Computing11.thy:5635`).

The rewrite is the heavy step: nested sums over `(i, j, l)`,
`Σ_l u_i u_j* = T_{ij}`, then exchange order of summation.

### Lemma B — kraus_quad_map vanishes iff Choi-block-matrix vanishes

```isabelle
lemma kraus_quad_map_zero_iff:
  assumes "∀V ∈ set Vs. V ∈ carrier_mat d n"
      and "T ∈ carrier_mat (length Vs) (length Vs)"
  shows "(∀X ∈ carrier_mat n n. kraus_quad_map d Vs T X = 0_m d d)
           ⟷ block_outer_form Vs T = 0_m (k*d) (k*d)"
```

(Need to define `block_outer_form` — the operator-valued "outer"
combining Vs and T.) Probably easier to prove directly:
`kraus_quad_map d Vs T = 0 ⟺ ∀ entries (r,c) zero` etc.

### Definition — `kraus_quad_map`

```isabelle
definition kraus_quad_map ::
  "nat ⇒ complex Matrix.mat list ⇒ complex Matrix.mat ⇒
       complex Matrix.mat ⇒ complex Matrix.mat" where
  "kraus_quad_map d Vs T X ≡
     foldr (λi acc1.
       foldr (λj acc2. T $$ (i, j) ⋅⇩m (Vs!i * X * (Vs!j)†) + acc2)
             [0..<length Vs] acc1)
           [0..<length Vs] (0⇩m d d)"
```

(Or factor through a `kraus_map_dim`-like recursion.)

### Helper — symmetric/anti-hermitian split of A

Given lin-dep coefficients `c : nat ⇒ real` from `mat_lin_indep_real`
negation, define `A_{ij} := c(i*k + j)` and prove:

```isabelle
lemma sym_or_antisym_witness:
  assumes "∃k < L. c k ≠ 0"  "L = length Vs * length Vs"
      and dep: "kraus_lin_combo Vs c = 0_m n n"
  shows "∃A. A ∈ carrier_mat k k ∧ hermitian A ∧ A ≠ 0_m k k ∧
              kraus_quad_zero Vs A"
```

where `kraus_quad_zero` says `Σ A_{ij} V_j† V_i = 0`.

### Helper — small ε keeps `I + εA` PSD

```isabelle
lemma small_eps_psd:
  assumes "A ∈ carrier_mat k k"  "hermitian A"
  shows "∃ε > 0. ∀δ. abs δ ≤ ε ⟶ psd (1_m k + complex_of_real δ ⋅m A)"
```

(Use spectral bound: ε := 1 / (1 + ‖A‖_op), where `‖A‖_op` is the
spectral norm. Or simpler: just take `ε := 1 / (1 + Σ|A_{ij}|)`.
The infinity-norm based bound is enough and avoids spectral theorem.)

---

## What is already in place (don't redo)

All in `Day23_ChoiExtremeUCP.thy`:

| Item                         | Status |
|------------------------------|--------|
| `extreme_UCP`, `extreme_CPTP` | ✅ defined |
| `ucp_kraus_rep`, `cptp_kraus_rep` | ✅ defined |
| `kraus_products`              | ✅ defined |
| `mat_lin_indep_real`          | ✅ defined |
| `kraus_map_dim_one`           | ✅ proved (eval at `1_m n`) |
| `ucp_has_kraus_rep`           | ✅ proved (UCP-Kraus existence) |
| `kraus_products_carrier`      | ✅ proved (typing) |
| `kraus_quad_map`, `kraus_quad_row` | ✅ defined (perturbation primitive) |
| `kraus_combo`                 | ✅ defined (linear combo `Σ u_i V_i`) |
| `kraus_quad_map_index`        | ✅ proved (double-sum entry formula) |
| `kraus_quad_map_add_Tm`       | ✅ proved (linearity in `T`) |
| `kraus_quad_map_outer_singleton` | ✅ proved (rank-1 identity) |
| `kraus_quad_map_outer_sum_eq_kraus_map_dim` | ✅ proved (sum decomp) |
| `amplification_cong`, `completely_positive_cong` | ✅ proved |
| `kraus_perturbation_cp`       | ✅ proved (**Lemma A**) |
| `inner_prod_add_right`, `inner_prod_smult_right` | ✅ proved (bilinearity of \<open>\<langle>_|_\<rangle>\<close>) |
| `hermitian_add`, `hermitian_one_mat`, `hermitian_smult_real` | ✅ proved |
| `quad_form_bound_by_entry_sum` | ✅ proved (entry-sum bound on \<open>\<bar>\<langle>x|Ax\<rangle>\<bar>\<close>) |
| `small_eps_psd`               | ✅ proved |
| `kraus_pair_sum`, `kraus_pair_row` | ✅ defined (dual sum \<open>\<Sum> A\<^sub>{ij} V\<^sub>j\<^sup>\<dagger> V\<^sub>i\<close>) |
| `kraus_pair_sum_index`, `kraus_pair_sum_add_A`, `kraus_pair_sum_smult_A` | ✅ proved |
| `kraus_pair_sum_dagger`       | ✅ proved (\<open>(...)\<^sup>\<dagger> = ...\<close> swapping coefficient indices) |
| `sym_or_antisym_witness`      | ✅ proved |
| `length_kraus_products`, `kraus_products_nth` | ✅ proved |
| `sum_split_prod_atLeastLessThan` | ✅ proved (\<open>\<Sum>\<^sub>{\<kappa><N*k}\<close> reindex) |
| `mat_lin_indep_real_neg_witness` | ✅ proved (the bridge) |
| `kraus_quad_map_smult_Tm`, `kraus_quad_map_one_eq_kraus_map_dim`, `kraus_pair_sum_one_eq_sum_wdag_w` | ✅ proved |
| `lin_indep_complex_mat`       | ✅ defined (minimality) |
| `lin_indep_zero_combo`, `kraus_quad_map_mat_unit_index` | ✅ proved (Lemma B helpers) |
| `kraus_quad_map_nonzero_witness` (Lemma B) | ✅ **proved** |
| `Tr_kraus_quad_map_eq`        | ✅ proved |
| `kraus_quad_map_is_TP`        | ✅ proved |
| **`choi_theorem_3_cptp_reverse`** | ✅ **proved (sorry-free!)** |
| `mat_lin_indep_complex`, `mat_lin_indep_complex_imp_real` | ✅ defined / proved |
| `extreme_CPTP_carrier` | ✅ defined (replaces vacuously-false `extreme_CPTP`) |
| `Tr_mat_unit_mult`, `mat_trace_pairing_unique` | ✅ proved |
| `cp_radon_nikodym_choi`, `cp_radon_nikodym_linear` | ✅ proved (2026-10-18; via `dominated_outer_sum_param`) |
| `choi_theorem_3_cptp_forward_complex` | ✅ proved (unconditional since 2026-10-18) |
| `choi_theorem_3_cptp`         | ✅ \<^bold>forward direction proved\<^bold>; reverse sorried with documented `extreme_CPTP` vacuity issue |
| `choi_theorem_3` (UCP form)   | ❌ `sorry` — documented convention mismatch (project uses CPTP-side products) |

\<^bold>Forward direction status (\<open>mat_lin_indep_complex \<Longrightarrow> extreme_CPTP_carrier\<close>):</br>
Skeleton fully assembled in `choi_theorem_3_cptp_forward_complex`, targeting
the new `extreme_CPTP_carrier` (carrier-point inequality, since the
original `extreme_CPTP` is vacuously false due to using raw function
inequality).

\<^bold>Internally proved\<^bold>:</br>
- `psi_cp` (Ψ is CP via `amplification_smult` + `psd_smult_nonneg`)
- `psi_range` (from `Phi1_range`)
- `diff_cp` (Φ - Ψ CP, via `completely_positive_cong` from `halfPhi2_cp`)
- Step C (Φ\<^sub>1 = kraus_quad_map d Vs T\<^sub>1 on carrier)
- Step D (ps_T1 via trace pairing duality)
- Step E (assembly: S nonzero, build complex c, contradict lin_indep)

\<^bold>Remaining sorries\<^bold> (historical; none remain as of 2026-10-18):</br>
- `cp_radon_nikodym` (axiom): substantial classical result. — CLOSED 2026-10-18.
- `Phi1_range`, `Phi2_range`: CPTP maps map carrier to carrier.
  Should be added as side hypotheses to `extreme_CPTP_carrier` (the
  project's CPTP definition doesn't enforce range, but it should).

\<^bold>What's left for full closure:</br>
- The three sorries above.
- UCP-side restatement (`choi_theorem_3` with products in \<open>M\<^sub>d\<close>).
- Glue: combine forward + reverse into the iff `choi_theorem_3_cptp_complex`
  (the original real-coefficient version is asymmetric).

\<^bold>Interactive workflow\<^bold>:</br>
Load the theory in jEdit from the project root:
\<open>/home/dusty/Desktop/Isabelle/Isabelle2025-2/bin/isabelle jedit -d . -l Vern_Paulsen_QC_3_10 Day23_ChoiExtremeUCP.thy\<close>

The UCP version's products convention is **wrong** as stated
(should be `{V_i V_j†}` in `M_d`, not `{V_j† V_i}` in `M_n`).
Either restate it or derive from CPTP via HS-adjoint duality.

---

## Existing infrastructure to leverage

| Lemma                          | Location                                | What it gives |
|--------------------------------|------------------------------------------|---------------|
| `kraus_cp_no_tp`               | `Quantum_Computing11.thy:5635`           | Kraus list ⟹ CP (no TP needed) |
| `kraus_is_cp`                  | `Quantum_Computing11.thy:4983`           | CPTP-side CP from `kraus_operators` |
| `psd_kraus_decomp`             | `Quantum_Computing_3_10.thy:3580`        | `T psd ⟹ T = Σ |u_l⟩⟨u_l|` |
| `choi_psd_if_cp`               | `Quantum_Computing11.thy:5558`           | CP ⟹ Choi PSD |
| `kraus_rep_of_psd_choi`        | `Quantum_Computing11.thy:6223`           | PSD Choi ⟹ Kraus rep exists |
| `choi_kraus_cptp`              | `Quantum_Computing11.thy:6830`           | CPTP iff Kraus existence |
| `kraus_map_dim_psd`            | (search QC11 for psd-preservation)        | `kraus_map_dim` preserves PSD |
| `kraus_operators` predicate    | `Quantum_Computing11.thy:4230`           | `(∀W ∈ Vs. W ∈ M_{d,n}) ∧ Σ W† W = I_n` |
| `kraus_map_dim` function       | `Quantum_Computing11.thy:4223`           | `foldr (λW acc. W ρ W† + acc) Ws (0_m d d)` |

`Schur_Decomposition` is already imported into `Essential_Functional_Analysis.thy`.
It gives `H = U T U†` for hermitian H with T upper-triangular (in fact diagonal
for hermitian). If a spectral theorem variant for k×k hermitian matrices is
needed, search there first; otherwise fall back to `psd_kraus_decomp`.

---

## Build commands & timing

```bash
# Day 23 session itself (heap-resident, ~20-30s after first build):
/home/dusty/Desktop/Isabelle/Isabelle2025-2/bin/isabelle build -d . Vern_Paulsen_QC

# Full project rebuild from scratch (cold heap, ~4 min total):
/home/dusty/Desktop/Isabelle/Isabelle2025-2/bin/isabelle build -d . Vern_Paulsen_QC

# To rebuild just the EFA heap if you touch it (~1m25s):
/home/dusty/Desktop/Isabelle/Isabelle2025-2/bin/isabelle build -d . Vern_Paulsen_QC_3_10
```

Edits to `Day23_ChoiExtremeUCP.thy` only require rebuilding the
`Vern_Paulsen_QC` session **on top of the existing heap**. Expect
**~25s per iteration** — many tight cycles are feasible.

If you touch `Essential_Functional_Analysis.thy` or `Quantum_Computing_3_10.thy`,
the whole heap rebuilds (~1m25s baseline, ~7m CPU). Avoid this unless
necessary.

---

## Known build-time pitfalls (from prior sessions)

1. **`zero_vec_def`/`zero_mat_def`/`eq_vecI` in `metis` hints** —
   triggers Matrix.vec normalization blow-up (>5 min hang). Use
   explicit `rule eq_vecI` + per-index `index_zero_vec(1)`.
2. **New top-level `Matrix.vec n (λk. …)` definitions in EFA.thy** —
   same trigger. Keep matrix/vec definitions local to proofs via
   `define`.
3. **`Matrix_Legacy.row` / `Matrix_Legacy.col`** namespace clash —
   write `Matrix.row` / `Matrix.col` explicitly.
4. **`real vec`** is ambiguous — use `real Matrix.vec`.
5. **`linarith`** can't handle goals with un-substituted symbolic
   terms; use chained `also` steps and substitute first.
6. **`index_unit_vec`** has clauses `(1)` (general if-form) and `(2)`
   (i=i = 1); use `(1)[of j L i]` with `j_lt, i_lt` for the off-diagonal
   case.

See `memory/efa_build_timing.md` for full details.

---

## Auxiliary CLI tools available

```
desorry     — bulk sledgehammer on sorries (see memory/isabelle_cli_tools.md)
eval_at     — proof-state queries (see same)
```

Project base: `/home/dusty/Desktop/Isabelle/Vern_Paulsen_QC/`
Isabelle binary: `/home/dusty/Desktop/Isabelle/Isabelle2025-2/bin/isabelle`
**Always use the explicit binary path** — the system `isabelle` is 2025
without the heaps.

---

## Estimated effort

| Sub-task                                    | Lines | Build cycles |
|---------------------------------------------|-------|--------------|
| Define `kraus_quad_map` + basic API         | ~40   | 3-5          |
| `kraus_perturbation_cp` (Lemma A)           | ~120  | 15-25        |
| Symmetric/antisym split + `kraus_quad_zero` | ~50   | 5-10         |
| `small_eps_psd` (ε bound)                   | ~60   | 8-12         |
| Distinctness via Choi-block (Lemma B)       | ~80   | 10-15        |
| Assembling `choi_theorem_3_cptp` reverse    | ~80   | 10-15        |
| **Total (reverse direction)**               | **~430** | **~50-80** |

Each build cycle ~25s ⟹ **~20-35 minutes of build wait** plus thinking time.
Plan for a 2-4 hour focused session.

The forward direction (CP Radon–Nikodym) is comparable in scope and
needs a separate session.

---

## Suggested entry prompt for the dedicated session

> Open the project at `/home/dusty/Desktop/Isabelle/Vern_Paulsen_QC/`,
> read `DAY23_HANDOFF.md` and `Day23_ChoiExtremeUCP.thy`. Close
> the **reverse direction** of `choi_theorem_3_cptp` following the
> mathematical roadmap in the handoff. Build with
> `isabelle build -d . Vern_Paulsen_QC` (use the
> `/home/dusty/Desktop/Isabelle/Isabelle2025-2/bin/isabelle` binary).
> Commit per coherent sub-lemma; push after each verified state. Honor
> the EFA build-time pitfalls.

Good luck.

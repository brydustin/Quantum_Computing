# Day23 CP Radon–Nikodym — CLOSED (2026-10-18)

**File:** `Day23_ChoiExtremeUCP.thy`   **Branch:** main

Both remaining `sorry`s are gone:

| Lemma | How it was closed |
|---|---|
| `A_Aplus_B_eq_B` | Operator-level proof (≈80 lines) replacing the eigenvector/index computation that timed out. With `Q = A⁺A`: `A Q = A` (from `A_Aplus_A_eq`), so `x − Qx ∈ ker A ⊆ ker B` by `loewner_ker_subset`; hence `B = B Q` (new helper `mat_eq_of_mult_vec_eq`), and taking adjoints gives `B = A A⁺ B`. No entry-wise sums. |
| `dominated_outer_sum_param` | `A = V V† = U D U†` (new `psd_spectral_decomp_nonneg`, extracted from the `psd_kraus_decomp` argument), `A⁺ = U D⁺ U†`, `T := V† A⁺ B A⁺ V`; `psd T` by `psd_conjugate`, and `V T V† = A A⁺ B A⁺ A = B` by `A_Aplus_B_eq_B` and its adjoint. |

Consequences: `cp_radon_nikodym_choi`, `cp_radon_nikodym_linear`,
`choi_theorem_3_cptp*` are now unconditional.

## Verification

* `isabelle build -d <afp>/thys -d . Vern_Paulsen_QC` passes with
  `quick_and_dirty = false` in all three sessions of `ROOT` (changed from
  `true`; timeout restored to 3600).
* Oracle audit via `Thm_Deps.all_oracles` on the key theorems: none.
  (With `quick_and_dirty = true` the audit reports `Pure.skip_proof` for
  everything downstream of a `fun`/`record`, because `Goal.prove_sorry`
  cheats on package-internal proofs in that mode — a false alarm, now
  eliminated at the source.)

## Environment notes

* The AFP is no longer registered as an Isabelle component; pass
  `-d /home/dusty/Desktop/Isabelle/afp-2026-04-09/thys` to every build /
  jedit invocation (or re-register it in
  `~/.isabelle/Isabelle2025-2/etc/components`).
* The parent heaps (JNF, Isabelle_Marries_Dirac, …) were stale and were
  rebuilt on 2026-10-18; a cold rebuild of the whole chain takes ≈15 min.
* `.Day23_pre_bisect_backup.thy` (untracked) holds the abandoned
  eigenvector-based proof attempt; it is no longer needed.
* See `AFP_FUNCTIONAL_ANALYSIS_SURVEY.md` for the AFP survey.

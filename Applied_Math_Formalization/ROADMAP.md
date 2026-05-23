# Nonemptiness Formalization Roadmap

This is the sorry-first plan for formalizing
`Applied Math/nonemptiness_unified_singlefile_complete.tex`.

## Current scaffold

- Session: `Applied_Math_Nonemptiness`
- Theory: [Nonemptiness_Scaffold.thy](/home/dusty/Desktop/Isabelle/Vern_Paulsen_QC/Applied_Math_Formalization/Nonemptiness_Scaffold.thy)
- Goal of the scaffold:
  - isolate the work in a clean session,
  - record the top-level theorem inventory,
  - define missing topological notions (`nowhere_dense`, `meager`),
  - centralize the future `sorry` targets.

## Vendored topology resource

A local vendored copy of the Munkres-style topology development is now available at:

- [Imported_Munkres_Topology/ROOT](/home/dusty/Desktop/Isabelle/Vern_Paulsen_QC/Imported_Munkres_Topology/ROOT:1)
- [Imported_Munkres_Topology/Munkres_Topology.thy](/home/dusty/Desktop/Isabelle/Vern_Paulsen_QC/Imported_Munkres_Topology/Munkres_Topology.thy:1)
- [Imported_Munkres_Topology/README.md](/home/dusty/Desktop/Isabelle/Vern_Paulsen_QC/Imported_Munkres_Topology/README.md:1)

Key fact:

- the vendored session builds locally as `Munkres_Topology_Local`
- `Theorem_48_2` in `Top1_Ch5_8.thy` gives the Baire-category theorem

Integration constraint:

- this development uses its own `top1_*` topology language
- the current nonemptiness scaffold uses `HOL-Analysis` / Euclidean-space language
- therefore we should add a bridge layer before importing the Munkres session into the nonemptiness session directly

## Why a separate session

- The existing project session still imports theories with active `sorry`s.
- This proof is primarily finite-dimensional analysis, topology, and explicit algebra.
- A clean session reduces proof noise and prevents us from building new results on unfinished quantum-computing dependencies.

## File strategy

The current scaffold keeps everything in one theory. The next split should be:

1. `Nonemptiness_Topology.thy`
   - `nowhere_dense`, `meager`
   - closure properties
   - nonempty open subsets of Euclidean space are not meager
   - lower-dimensional smooth image is meager

2. `Nonemptiness_Array_Factor.thy`
   - raw array-factor and power-pattern definitions
   - root-of-unity witness configuration
   - odd-`N` zero-geometry lemma for the array factor

3. `Nonemptiness_Fold_And_Regular.thy`
   - regular-stratum zero branch
   - fold-curve branch
   - finite exceptional-set argument on the fold

4. `Nonemptiness_Moment_Map.thy`
   - moment variables
   - block-triangular Jacobian lemma
   - rank-3 minor lemma
   - explicit six-point / 12x12 determinant witness

5. `Nonemptiness_H0_Residual.thy`
   - residual Hessian-zero closure
   - restricted minors
   - all residual codimension estimates

6. `Nonemptiness_CaseB.thy`
   - direct configuration-space closure of Case B

7. `Nonemptiness_Final.thy`
   - bad-set union
   - Baire closeout
   - final nonemptiness theorem

## Main sorry buckets

These are the major proof families, in dependency order.

### 1. Basic topological infrastructure

- `meager_Un`
- `meager_Union_nat`
- `open_nonempty_not_meager`
- `final_nonemptiness_from_bad_union`

Notes:
- Isabelle/HOL has Baire-category results, but not a ready-made `meager` API in the style used by the TeX note.
- This is a stand-alone infrastructure block and should be solved early.

### 2. Smooth-image meagerness

Target theorem from the TeX:
- smooth image of a lower-dimensional Euclidean chart is meager.

Planned route:
- prove a compact-cube Lipschitz lemma for `C1` maps,
- show compact images have empty interior by volume scaling,
- conclude meagerness by countable cube exhaustion.

This is a stand-alone result worth keeping independent from the nonemptiness project.

### 3. Regular-stratum zero branch

Target TeX components:
- `lem:Azero-surj`
- `prop:regzero`

Missing infrastructure:
- a specialized finite-dimensional parametric transversality theorem,
  or a direct substitute sufficient for `A(x, ω)` hitting `0 ∈ C`.

Recommendation:
- do not attempt full general transversality first.
- formalize the smallest theorem needed for maps `X × Y → R^2` with surjective `x`-partial at zeros.

### 4. Fold branch

Target TeX components:
- `lem:foldfields`
- `prop:foldzero`
- `lem:Efinite`
- `prop:foldnonzero`

Work items:
- formalize the explicit fold computation for `cvec`,
- define the exceptional finite set,
- prove the nontrivial real-analytic function argument used to get nowhere-dense zero sets.

Potential stand-alone infrastructure:
- nontrivial real-analytic functions on connected open sets have zero sets with empty interior.

### 5. Moment-map and surjective regular piece

Target TeX components:
- `lem:block`
- `lem:3x3`
- `lem:Msurj`
- `prop:dimZ`

This is the algebraic center of the proof.

Recommended order:
1. formalize the moment variables and the formulas for `Phi`, `H`, and `det H`;
2. prove the block-triangular Jacobian lemma;
3. prove the rank-3 minor lemma;
4. encode the six-point witness and verify the explicit determinant.

For the 12x12 determinant:
- treat it as a self-contained symbolic computation,
- use a fixed concrete matrix,
- let Isabelle normalize the arithmetic once the matrix is stated exactly.

### 6. Residual `H = 0` closure

Target TeX components:
- everything summarized by `prop:h0res-meager`

This should be handled as its own module. The appendix is long, but structurally it is a finite tree of codimension closures.

Recommended tactic:
- do not reproduce the appendix linearly.
- refactor it into named branch predicates and prove:
  - branch inclusion,
  - codimension estimate,
  - meager projection,
  - finite union closeout.

### 7. Direct Case B closure

Target TeX components:
- everything summarized by `cor:caseBmeager`

This is another independent module after the moment-map layer.

Recommendation:
- keep the direct `v`-block and common-parameter arguments separate,
- avoid mixing them into the regular-stratum file.

## Immediate next proof order

1. Finish the topological infrastructure in the scaffold.
2. Split the scaffold into the theory modules listed above.
3. Prove the constructive feasibility part.
4. Prove the smooth-image-meager lemma.
5. Build the specialized transversality lemma for the regular-zero branch.
6. Formalize the moment-map algebra and determinant witness.
7. Attack the residual `H = 0` and Case B appendix closures.
8. Remove the closeout `sorry`.

## Naming policy

Keep theorem names close to the paper labels, but not identical to LaTeX labels. Suggested Isabelle names:

- `open_feasible_family`
- `two_triple_cover`
- `regular_stratum_zero_meagerness`
- `fold_zero_meagerness`
- `fold_nonzero_meagerness`
- `regular_stratum_nonzero_meagerness`
- `bad_union_meagerness`
- `odd_N_nonemptiness`

## Verification policy

- Short-term: `quick_and_dirty = true` is acceptable in this session.
- Mid-term: eliminate `sorry`s from the topological layer first.
- Long-term: switch this session to `quick_and_dirty = false` only after the appendix modules are in place.

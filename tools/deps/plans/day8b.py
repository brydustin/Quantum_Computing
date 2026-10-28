"""Audit tick 22 (2026-10-28): Day 8's theorem on linearly independent states through three general
facts - outer_prod_mult (Day 2), psd_scale_below_one (Day 4), foldr_add_mat_smult (Matrix_Lemmas) -
from wip/d23/D08b.thy; outer_prod_idempotent becomes a corollary of outer_prod_mult."""
import os, sys
sys.path.insert(0, os.path.dirname(__file__))
from planlib import *

S = scratch_blocks("wip/d23/D08b.thy")
edit("Essential_Functional_Analysis/Matrix_Lemmas.thy",
     insert_after=[("foldr_add_mat_smult_pull", [S["foldr_add_mat_smult"]])])
edit("Day02_Trace_Projections.thy",
     remove=["outer_prod_idempotent"],
     insert_after=[("outer_prod_dagger", [txt(r"$(ab^*)(cd^*)=\braket bc\,ad^*$."), S["outer_prod_mult"]]),
                   ("outer_prod_idempotent", [S["outer_prod_idempotent"]])])
edit("Day04_Hermitian_Matrices.thy",
     insert_after=[("psd_spectral_decomp_nonneg",
                    [txt(r"A positive matrix is dominated by a multiple of $I$: $I-cA\ge0$ for some $c>0$."),
                     S["psd_scale_below_one"]])])
edit("Day08_Measurements.thy",
     remove=["lin_indep_states_unambiguous"],
     insert_after=[("lin_indep_states_unambiguous", [S["lin_indep_states_unambiguous"]])])
print("installed")

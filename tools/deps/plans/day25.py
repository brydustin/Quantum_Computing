"""Audit tick 37 (2026-10-28): Day 25's smult_mat_vec was Day 3's smult_mat_mult_vec with a
dim_vec premise; the duplicate goes and its five uses take the Day 3 fact."""
import os, sys
sys.path.insert(0, os.path.dirname(__file__))
from planlib import *

reps = [
    ("smult_mat_vec[OF A v] cpx_vec_length_smult", "smult_mat_mult_vec[OF A carrier_vecI[OF v]] cpx_vec_length_smult"),
    ("index_one_mat(2) index_smult_mat(2,3) one_mult_mat_vec smult_mat_vec x xc",
     "index_one_mat(2) index_smult_mat(2,3) one_mult_mat_vec smult_mat_mult_vec x xc"),
    ("smult_mat_vec[OF Ac x] cpx_vec_length_smult", "smult_mat_mult_vec[OF Ac carrier_vecI[OF x]] cpx_vec_length_smult"),
    ("smult_mat_vec[OF Yc x] smult_mat_vec[OF Ydc x]", "smult_mat_mult_vec[OF Yc xc] smult_mat_mult_vec[OF Ydc xc]"),
    ("smult_mat_vec[OF Pc x] smult_mat_vec[OF one_carrier_mat x] xc",
     "smult_mat_mult_vec[OF Pc xc] smult_mat_mult_vec[OF one_carrier_mat xc] xc")]
edit("Day25_Unital_Functional_Norm.thy", remove=["smult_mat_vec"], replace=reps)
print("installed")

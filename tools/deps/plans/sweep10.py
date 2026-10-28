"""Audit tick 50 (2026-10-28): psd_add_psd moves from Day 13 to Day 4 next to psd_smult_nonneg (the
positive matrices are a cone) with the same two-line quadratic-form proof (65 lines -> 13); Day 28's
hermitian_add_mat was Day 4's hermitian_plus with the premises permuted and goes.
`python3 sweep10.py --scratch` writes wip/d23/D50_NN.thy; without the flag it installs."""
import os, re, sys
sys.path.insert(0, os.path.dirname(__file__))
from planlib import *

D4, D13, D28 = "Day04_Hermitian_Matrices.thy", "Day13_Density_Matrices.thy", "Day28_Entanglement_Witnesses.thy"
SRC = {f: head(f) for f in (D4, D13, D28)}
BL = {f: {b["name"]: "\n".join(b["lines"]).rstrip("\n") for b in B.split(SRC[f]) if b["name"]} for f in SRC}

ADD = r'''lemma psd_add_psd:
  assumes A: "psd A" and B: "psd B"
      and Ac: "A \<in> carrier_mat n n" and Bc: "B \<in> carrier_mat n n"
  shows "psd (A + B)"
  unfolding psd_iff_quad_form_nonneg[OF add_carrier_mat[OF Bc]]
proof (intro allI impI)
  fix x :: "complex Matrix.vec" assume x: "dim_vec x = n"
  have "\<langle>x | (A + B) *\<^sub>v x\<rangle> = \<langle>x | A *\<^sub>v x\<rangle> + \<langle>x | B *\<^sub>v x\<rangle>"
    unfolding add_mult_distrib_mat_vec[OF Ac Bc carrier_vecI[OF x]]
    by (rule inner_prod_right_add') (use Ac Bc in simp)
  thus "\<langle>x | (A + B) *\<^sub>v x\<rangle> \<in> \<real> \<and> 0 \<le> Re \<langle>x | (A + B) *\<^sub>v x\<rangle>"
    using A[unfolded psd_iff_quad_form_nonneg[OF Ac], rule_format, OF x]
          B[unfolded psd_iff_quad_form_nonneg[OF Bc], rule_format, OF x] by (auto intro: Reals_add)
qed'''
USE_OLD = "hermitian_add_mat [OF Mcar Ncar Mherm Nherm]"
USE_NEW = "hermitian_plus[OF Mherm Nherm Mcar Ncar]"

if "--scratch" in sys.argv:
    out = ["theory D50", "  imports Quantum_Computing_by_VP.Day04_Hermitian_Matrices", "begin", "", ADD.replace("lemma psd_add_psd:", "lemma psd_add_psd':"), "", "end\n"]
    open(os.path.join(P, "wip/d23/D50.thy"), "w").write("\n".join(out))
    blk = None
    for b in B.split(SRC[D28]):
        if b["name"] and USE_OLD in "\n".join(b["lines"]): blk = "\n".join(b["lines"]).rstrip("\n")
    out = ["theory D50_28", "  imports Quantum_Computing_by_VP.Day28_Entanglement_Witnesses", "begin", "",
           re.sub(r"^(lemma|theorem|corollary) (\S+?):", r"\1 \2':", blk.replace(USE_OLD, USE_NEW), count=1), "", "end\n"]
    open(os.path.join(P, "wip/d23/D50_28.thy"), "w").write("\n".join(out))
    root = os.path.join(P, "wip/d23/ROOT"); r = open(root).read()
    open(root, "w").write(r[:r.index("  theories")] + "  theories\n    D50\n    D50_28\n")
    print("scratch written: D50 D50_28")
else:
    edit(D4, insert_after=[("psd_smult_nonneg", [ADD])])
    edit(D13, remove=["psd_add_psd"])
    assert SRC[D28].count(USE_OLD) == 1
    edit(D28, src=SRC[D28].replace(USE_OLD, USE_NEW), remove=["hermitian_add_mat"])
    print("installed")

"""Audit tick 48 (2026-10-28): Day 22's |Q_ab|^2 <= Q_aa Q_bb for a positive Q is Cauchy–Schwarz for
the columns of a square root W (Q = W*W, Q_ab = <w_a|w_b>); the bundle's diagonal Gram-entry lemma
becomes the full dagger_mult_inner (with the one-line proof of HHL_Approximate's
dagger_mult_entry, which it replaces there).  Installs on top of sweep7.  `python3 sweep8.py --scratch` writes wip/d23/D48_*.thy;
without the flag it installs."""
import os, re, sys
sys.path.insert(0, os.path.dirname(__file__))
from planlib import *

ML, D21, D22 = "Essential_Functional_Analysis/Matrix_Lemmas.thy", "Day21_Unitary_Freedom.thy", "Day22_UCP_Compact.thy"
FILES = [ML, D21, D22]
SRC = {f: head(f) for f in FILES}
BL = {f: {b["name"]: "\n".join(b["lines"]).rstrip("\n") for b in B.split(SRC[f]) if b["name"]} for f in FILES}
def seg(f, t): assert SRC[f].count(t) == 1, (f, t[:50]); return t

GRAM = r'''lemma dagger_mult_inner:
  fixes Y :: "complex Matrix.mat"
  assumes Yc: "Y \<in> carrier_mat p q" and i: "i < q" and j: "j < q"
  shows "((Y\<^sup>\<dagger>) * Y) $$ (i,j) = \<langle>Matrix.col Y i | Matrix.col Y j\<rangle>"
  using Yc i j by (simp add: dagger_def scalar_prod_def inner_prod_def atLeast0LessThan)'''
BOUND = r'''lemma psd_entry_bound_by_diag:
  fixes M :: "complex Matrix.mat"
  assumes Mcar: "M \<in> carrier_mat n n"
      and Mpsd: "psd M"
      and i: "i < n" and j: "j < n"
  shows "(norm (M $$ (i, j)))\<^sup>2 \<le> Re (M $$ (i, i)) * Re (M $$ (j, j))"
proof -
  obtain W where Wc: "W \<in> carrier_mat n n" and Wpsd: "psd W" and WW: "W * W = M"
    using psd_sqrt_exists[OF Mcar Mpsd] by blast
  have M: "M $$ (a, b) = \<langle>Matrix.col W a | Matrix.col W b\<rangle>" if "a < n" "b < n" for a b
    using dagger_mult_inner[OF Wc that] psd_hermitian[OF Wpsd] WW unfolding hermitian_def by simp
  show ?thesis
    using cauchy_schwarz_ineq[of "Matrix.col W i" "Matrix.col W j"] Wc
    unfolding M[OF i j] M[OF i i] M[OF j j] times_complex.sel(1) inner_prod_with_itself_Im by simp
qed'''
REPS = {ML: [(BL[ML]["dagger_mult_diag_inner"], GRAM)],
        D21: [(seg(D21, "dagger_mult_diag_inner[OF Yc j, symmetric]"), "dagger_mult_inner[OF Yc j j, symmetric]")],
        D22: [(BL[D22]["psd_entry_bound_by_diag"], BOUND)]}

def prime(t): return re.sub(r"^(lemma|theorem|corollary) (\S+?):", r"\1 \2':", t, count=1)

if "--scratch" in sys.argv:
    out = ["theory D48", "  imports Quantum_Computing_by_VP.Day22_UCP_Compact Quantum_Computing_by_VP.Day21_Unitary_Freedom", "begin", "",
           prime(GRAM), "", prime(BOUND).replace("dagger_mult_inner[", "dagger_mult_inner'["), "",
           prime(BL[D21]["dagger_mult_zero_imp_zero"].replace(REPS[D21][0][0], REPS[D21][0][1])).replace("dagger_mult_inner[", "dagger_mult_inner'["), "", "end\n"]
    open(os.path.join(P, "wip/d23/D48.thy"), "w").write("\n".join(out))
    print("scratch written: D48")
else:
    for f in FILES:                       # on top of sweep7, which also edits Matrix_Lemmas
        s = open(os.path.join(P, f)).read()
        for old, new in REPS[f]: assert s.count(old) == 1, (f, old[:40]); s = s.replace(old, new)
        edit(f, src=s)
    print("installed")

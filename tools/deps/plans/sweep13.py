"""Audit tick 53 (2026-10-28): Day 22's topology through HOL-Analysis: each closed set is
closed_Collect_eq / closed_Collect_le of continuous maps (continuous_intros + the bundle's
continuous_on_unwrap_lm_index), the quadratic form is a double sum of entries, the trace is linear
by unfolding.  Statements unchanged.  `python3 sweep13.py --scratch` writes wip/d23/D53.thy;
without the flag it installs."""
import os, re, sys
sys.path.insert(0, os.path.dirname(__file__))
from planlib import *

D22 = "Day22_UCP_Compact.thy"
SRC = head(D22)
BL = {b["name"]: "\n".join(b["lines"]).rstrip("\n") for b in B.split(SRC) if b["name"]}

NEW = {
"closed_entry_hermitian_eq": r'''lemma closed_entry_hermitian_eq:
  fixes i j :: nat
  assumes ij: "i < CARD('k :: finite)" "j < CARD('k)"
  shows "closed {M :: (complex, 'k, 'k) lmat.
                  unwrap_lm M $$ (i, j) = cnj (unwrap_lm M $$ (j, i))}"
  by (intro closed_Collect_eq continuous_on_cnj continuous_on_unwrap_lm_index ij)''',
"closed_hermitian_unwrap_lmat": r'''lemma closed_hermitian_unwrap_lmat:
  "closed {M :: (complex, 'k :: finite, 'k) lmat. hermitian (unwrap_lm M)}"
proof -
  have "hermitian (unwrap_lm M) \<longleftrightarrow>
        (\<forall>i < CARD('k). \<forall>j < CARD('k). unwrap_lm M $$ (i, j) = cnj (unwrap_lm M $$ (j, i)))"
    for M :: "(complex, 'k, 'k) lmat"
  proof
    assume "hermitian (unwrap_lm M)"
    thus "\<forall>i < CARD('k). \<forall>j < CARD('k). unwrap_lm M $$ (i, j) = cnj (unwrap_lm M $$ (j, i))"
      by (auto intro: hermitian_index)
  next
    assume e: "\<forall>i < CARD('k). \<forall>j < CARD('k). unwrap_lm M $$ (i, j) = cnj (unwrap_lm M $$ (j, i))"
    show "hermitian (unwrap_lm M)" unfolding hermitian_def
    proof (rule eq_matI)
      fix i j assume "i < dim_row (unwrap_lm M)" "j < dim_col (unwrap_lm M)"
      thus "(unwrap_lm M)\<^sup>\<dagger> $$ (i, j) = unwrap_lm M $$ (i, j)"
        using e[rule_format, of j i] by (simp add: dagger_def)
    qed simp_all
  qed
  hence "{M :: (complex, 'k, 'k) lmat. hermitian (unwrap_lm M)} =
         (\<Inter>i < CARD('k). \<Inter>j < CARD('k). {M. unwrap_lm M $$ (i, j) = cnj (unwrap_lm M $$ (j, i))})"
    by blast
  thus ?thesis by (auto intro!: closed_INT closed_entry_hermitian_eq)
qed''',
"closed_nonneg_quad_form_lmat": r'''lemma closed_nonneg_quad_form_lmat:
  fixes x :: "complex Matrix.vec"
  assumes xdim: "dim_vec x = CARD('k :: finite)"
  shows "closed {M :: (complex, 'k, 'k) lmat.
                  Re (\<langle>x | unwrap_lm M *\<^sub>v x\<rangle>) \<ge> 0}"
proof -
  have "\<langle>x | unwrap_lm M *\<^sub>v x\<rangle> =
        (\<Sum>i<CARD('k). \<Sum>j<CARD('k). cnj (x $ i) * (unwrap_lm M $$ (i, j) * x $ j))"
    for M :: "(complex, 'k, 'k) lmat"
    using xdim by (simp add: inner_prod_def scalar_prod_def sum_distrib_left atLeast0LessThan)
  moreover have "closed {M :: (complex, 'k, 'k) lmat.
      0 \<le> Re (\<Sum>i<CARD('k). \<Sum>j<CARD('k). cnj (x $ i) * (unwrap_lm M $$ (i, j) * x $ j))}"
    by (intro closed_Collect_le continuous_intros continuous_on_unwrap_lm_index) auto
  ultimately show ?thesis by simp
qed''',
"continuous_on_Tr_lmat": r'''lemma continuous_on_Tr_lmat:
  fixes S :: "(complex, 'k :: finite, 'k) lmat set"
  shows "continuous_on S Tr_lmat"
  unfolding Tr_lmat_def by (intro continuous_on_sum continuous_on_unwrap_lm_index) auto''',
"Tr_lmat_add": r'''lemma Tr_lmat_add:
  fixes M N :: "(complex, 'k :: finite, 'k) lmat"
  shows "Tr_lmat (M + N) = Tr_lmat M + Tr_lmat N"
  unfolding Tr_lmat_def by (simp add: sum.distrib)''',
"Tr_lmat_scaleR": r'''lemma Tr_lmat_scaleR:
  fixes M :: "(complex, 'k :: finite, 'k) lmat" and a :: real
  shows "Tr_lmat (a *\<^sub>R M) = a *\<^sub>R Tr_lmat M"
  unfolding Tr_lmat_def by (simp add: scaleR_sum_right)''',
"Tr_lmat_sum_scaleR": r'''lemma Tr_lmat_sum_scaleR:
  fixes T :: "'a set" and u :: "'a \<Rightarrow> real"
    and f :: "'a \<Rightarrow> (complex, 'k :: finite, 'k) lmat"
  assumes "finite T"
  shows "Tr_lmat (\<Sum>t \<in> T. u t *\<^sub>R f t) = (\<Sum>t \<in> T. u t *\<^sub>R Tr_lmat (f t))"
  using assms by induction (simp_all add: Tr_lmat_add Tr_lmat_scaleR)''',
"closed_unit_trace_lmat": r'''lemma closed_unit_trace_lmat:
  "closed {M :: (complex, 'k :: finite, 'k) lmat. Tr_lmat M = 1}"
  by (intro closed_Collect_eq continuous_on_Tr_lmat continuous_on_const)'''}

def prime(t): return re.sub(r"^(lemma|theorem|corollary) (\S+?):", r"\1 \2':", t, count=1)

if "--scratch" in sys.argv:
    out = ["theory D53", "  imports Quantum_Computing_by_VP.Day22_UCP_Compact", "begin", ""]
    for n, t in NEW.items():
        for m in NEW: t = re.sub(r"(?<=[ \[(])(%s)(?=[ \[)\]])" % m, m + "'", t) if m != n else t
        out += [prime(t), ""]
    out.append("end\n")
    open(os.path.join(P, "wip/d23/D53.thy"), "w").write("\n".join(out))
    root = os.path.join(P, "wip/d23/ROOT"); r = open(root).read()
    open(root, "w").write(r[:r.index("  theories")] + "  theories\n    D53\n")
    print("scratch written: D53")
else:
    s = SRC
    for n, t in NEW.items(): assert s.count(BL[n]) == 1, n; s = s.replace(BL[n], t)
    edit(D22, src=s)
    print("installed")

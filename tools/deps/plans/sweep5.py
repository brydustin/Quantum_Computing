"""Audit tick 45 (2026-10-28): the metis/smt calls of Days 5, 6, 8, 9 and 13.  Day 5's block form
T(v ⊕ w) is JNF's four_block_mat_mult_vec; Day 7 gains ‖h ⊗ k‖ = ‖h‖‖k‖, which settles the tensor
norms of Day 9; unit norms go through cpx_vec_length_one_iff.  `python3 sweep5.py --scratch` writes
one check theory per day (wip/d23/D45_NN.thy, listed in wip/d23/ROOT); without the flag it installs."""
import os, re, sys
sys.path.insert(0, os.path.dirname(__file__))
from planlib import *

D5, D6, D7, D8 = "Day05_Positivity_Tests.thy", "Day06_Tensor_Products.thy", "Day07_Postulates.thy", "Day08_Measurements.thy"
D9P, D9B, D13 = "Day09_POVMs_Entanglement.thy", "Day09_Bell_Measurement.thy", "Day13_Density_Matrices.thy"
FILES = [D5, D6, D7, D8, D9P, D9B, D13]
SRC = {f: head(f) for f in FILES}
EXP = {}
def L(f, a, b, need=True):
    t = "\n".join(SRC[f].split("\n")[a - 1:b]); assert not need or "metis" in t or "smt" in t, (f, a, b)
    EXP[t] = SRC[f].count(t); return t
def blocks(f): return {b["name"]: "\n".join(b["lines"]).rstrip("\n") for b in B.split(SRC[f]) if b["name"]}

TENSOR_NORM = [txt(r"Hence $\|h\otimes k\|=\|h\|\,\|k\|$."), r'''lemma tensor_vec_norm: "\<parallel>tensor_vec h k\<parallel> = \<parallel>h\<parallel> * \<parallel>k\<parallel>"
proof (rule power2_eq_imp_eq)
  have "\<langle>tensor_vec h k | tensor_vec h k\<rangle> = \<langle>h | h\<rangle> * \<langle>k | k\<rangle>"
    by (rule tensor_inner_prod[OF refl refl refl refl])
  thus "\<parallel>tensor_vec h k\<parallel>\<^sup>2 = (\<parallel>h\<parallel> * \<parallel>k\<parallel>)\<^sup>2"
    unfolding cpx_vec_length_inner_prod[symmetric] of_real_power[symmetric] of_real_mult[symmetric]
      of_real_eq_iff power_mult_distrib .
qed (simp_all add: cpx_vec_length_nonneg mult_nonneg_nonneg)''']

REPS = {
 D5: [(L(D5, 391, 394, False), r'''Formally the direct sum of vectors is JNF's concatenation \<open>@\<^sub>v\<close>, written
\<open>v \<oplus>\<^sub>v w\<close>, and block matrices are the library's \<open>four_block_mat\<close>.\<close>'''),
      (L(D5, 451, 521), r'''  by (rule four_block_mat_mult_vec[OF assms(3-6) carrier_vecI[OF assms(1)] carrier_vecI[OF assms(2)]])''')],
 D6: [(L(D6, 59, 61), r'''  have lw_nonempty: "list_of_vec w \<noteq> []"
    using assms(2) m_pos by (simp flip: length_greater_0_conv)''')],
 D8: [(L(D8, 442, 442, False), r'''  have uu: "\<langle>u|u\<rangle> = 1" using u unfolding cpx_vec_length_one_iff .'''),
      (L(D8, 449, 449), r'''  finally show ?thesis unfolding of_real_diff[symmetric] of_real_eq_iff .'''),
      (L(D8, 503, 504), r'''  by (rule less_le_trans[OF _ nonorthogonal_outcome_prob[OF ms q1 q2 i p1]]) (simp add: no)''')],
 D9P: [(L(D9P, 154, 166), r'''proof -
  have d1: "dim_vec \<psi>1 = n" and n1: "\<parallel>\<psi>1\<parallel> = 1" and d2: "dim_vec \<psi>2 = m" and n2: "\<parallel>\<psi>2\<parallel> = 1"
    using assms unfolding quantum_state_def by auto
  show ?thesis
    unfolding quantum_state_def tensor_vec_dim[OF d1 d2] tensor_vec_norm n1 n2 by simp
qed'''),
       (L(D9P, 230, 235), r'''  show ?thesis
    unfolding meas_prob_def mix tensor_vec_norm phi_norm by simp''')],
 D9B: [(L(D9B, 70, 87), r'''  using e_inner(1,4) unfolding tensor_vec_norm cpx_vec_length_one_iff[symmetric] by simp_all''')],
 D13: [(L(D13, 270, 277), r'''  have Tr_os: "Tr (outer_sum n [\<psi>]) = 1"
    using quantum_state_norm1[OF q] unfolding Tr_outer_sum_single[OF d\<psi>] cpx_vec_length_one_iff .'''),
       (L(D13, 534, 534), r'''    unfolding complex_norm_square[symmetric] c by simp''')]}
AFFECTED = {D5: ["block_mat_apply"], D6: ["tensor_vec_index"],
            D8: ["norm_sq_minus_component", "nonorthogonal_not_distinguishable"],
            D9P: ["tensor_of_states_is_state", "composite_measurement_prob"], D9B: ["tensor_e_norm"],
            D13: ["ensemble_density_Tr", "pure_density_smult_unit"]}

def prime(t): return re.sub(r"^(lemma|theorem|corollary) (\S+?):", r"\1 \2':", t, count=1)

if "--scratch" in sys.argv:
    outside = {REPS[D5][0][0]}             # the Day 5 text block is not inside a lemma
    used = {old: 0 for f in AFFECTED for old, _ in REPS[f] if old not in outside}
    names = []
    for f, lemmas in AFFECTED.items():
        bl, th = blocks(f), "D45_" + f[3:5] + ("B" if f == D9B else "")
        out = ["theory " + th, "  imports Quantum_Computing_by_VP." + f[:-4], "begin", ""]
        if f in (D9P, D9B):                   # the new Day 7 fact, ahead of its users
            out += [re.sub(r"lemma tensor_vec_norm:", "lemma tensor_vec_norm':", TENSOR_NORM[1]), ""]
        for n in lemmas:
            t = bl[n]
            for old, new in REPS[f]:
                if old in t and old in used: used[old] += t.count(old); t = t.replace(old, new)
            out += [prime(t).replace("tensor_vec_norm ", "tensor_vec_norm' "), ""]
        out.append("end\n"); names.append(th)
        open(os.path.join(P, "wip/d23", th + ".thy"), "w").write("\n".join(out))
    assert all(v == EXP[k] for k, v in used.items()), [k[:40] for k, v in used.items() if v != EXP[k]]
    root = os.path.join(P, "wip/d23/ROOT"); r = open(root).read()
    open(root, "w").write(r[:r.index("  theories")] + "  theories\n" + "".join("    %s\n" % n for n in names))
    print("scratch written:", *names)
else:
    for f in FILES:
        s = SRC[f]
        for old, new in dict(REPS.get(f, [])).items(): assert s.count(old) == EXP[old], (f, old[:40]); s = s.replace(old, new)
        if f == D7: edit(f, src=s, insert_after=[("tensor_inner_prod", TENSOR_NORM)])
        else: edit(f, src=s)
    print("installed")

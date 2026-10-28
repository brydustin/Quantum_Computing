"""Audit tick 43 (2026-10-28): the scattered one-line metis calls of Days 1, 11, 32, 33 and 34.
Day 1 gains cpx_vec_length_nonneg (Day 25's vnorm_nonneg, moved), cpx_vec_length_one_iff
(‖v‖ = 1 ⟷ ⟨v|v⟩ = 1) and the two cmod_sq_sum lemmas (moved up from Day 21); every unit-norm
conversion is then one unfolding, the in_set_conv_nth obtains are auto, the hs_inner_prod facts
are three-line unfoldings.  `python3 sweep3.py --scratch` writes wip/d23/D43.thy (primed copies of
every touched lemma) for tools/chk.sh; without the flag it installs."""
import os, re, sys
sys.path.insert(0, os.path.dirname(__file__))
from planlib import *

D1, D11, D21, D25 = "Day01_Inner_Product.thy", "Day11_Gates_No_Cloning.thy", "Day21_Average_Conjecture.thy", "Day25_Unital_Functional_Norm.thy"
D32, D33, D34 = "Day32_Phase_Flip_Code.thy", "Day33_Shor_Code.thy", "Day34_Knill_Laflamme.thy"
SRC = {f: head(f) for f in [D1, D11, D21, D25, D32, D33, D34]}
EXP = {}
def L(f, a, b):
    t = "\n".join(SRC[f].split("\n")[a - 1:b]); assert "metis" in t, (f, a, b); EXP[t] = SRC[f].count(t); return t
def blocks(f): return {b["name"]: "\n".join(b["lines"]).rstrip("\n") for b in B.split(SRC[f]) if b["name"]}

NEW1 = r'''lemma cpx_vec_length_nonneg: "\<parallel>v\<parallel> \<ge> 0"
  unfolding cpx_vec_length_def by (simp add: sum_nonneg)'''
NEW2 = r'''lemma cpx_vec_length_one_iff: "\<parallel>v\<parallel> = 1 \<longleftrightarrow> \<langle>v|v\<rangle> = 1"
  using cpx_vec_length_nonneg[of v]
  unfolding cpx_vec_length_inner_prod[symmetric] of_real_power[symmetric] of_real_eq_1_iff
  by (auto simp: power2_eq_1_iff)'''
HS_REAL = r'''lemma hs_inner_prod_self_real:
  shows "\<langle>\<langle> x | x \<rangle>\<rangle> \<in> \<real>"
  unfolding hs_inner_prod_def cmod_sq_sum'[symmetric] of_real_sum[symmetric] by simp'''
HS_NONNEG = r'''lemma hs_inner_prod_self_nonneg:
  shows "Re (\<langle>\<langle> x | x \<rangle>\<rangle>) \<ge> 0"
  unfolding hs_inner_prod_def cmod_sq_sum'[symmetric] of_real_sum[symmetric] by (simp add: sum_nonneg)'''

REPS = {
 D1: [(L(D1, 72, 73), r'''  have index_zero: "v $ i = 0" if "i < dim_vec v" for i
    using arg_cong[OF v_zero, of "\<lambda>w. w $ i"] that by simp'''),
      (L(D1, 272, 272), r'''    unfolding hs_inner_prod_cnj[OF assms(1,2)] hs_inner_prod_cnj[OF assms(3,4)] ..''')],
 D11: [(L(D11, 60, 62), r'''  have r_sq: "r * r = 1 / 2"
    unfolding r_def of_real_mult[symmetric] r_sq_real by simp'''),
       (L(D11, 106, 113), r'''  have \<psi>\<^sub>2_norm: "\<parallel>\<psi>\<^sub>2\<parallel> = 1"
    unfolding cpx_vec_length_one_iff using inner_\<psi>\<^sub>2_self by simp'''),
       (L(D11, 169, 171), r'''  have inner_self_\<psi>\<^sub>1: "\<langle>\<psi>\<^sub>1 | \<psi>\<^sub>1\<rangle> = 1"
    using quantum_state_norm1[OF \<psi>\<^sub>1_qs] unfolding cpx_vec_length_one_iff .''')],
 D32: [(L(D32, 82, 88), r'''  thus ?thesis unfolding cpx_vec_length_one_iff .'''),
       (L(D32, 105, 109), r'''  thus ?thesis unfolding cpx_vec_length_one_iff .'''),
       (L(D32, 149, 150), r'''  also have "\<dots> = (Pauli_Z * Pauli_Z) *\<^sub>v ket_plus"
    by (rule assoc_mult_mat_vec[OF Pauli_Z_carrier Pauli_Z_carrier ket_plus_carrier, symmetric])''')],
 D33: [(L(D33, 36, 36), r'''  hence "(2::nat) ^ Suc i * 2 ^ (8 - i) = 2 ^ 9" by (simp only: power_add[symmetric])'''),
       (L(D33, 759, 759), r'''  hence "(2::nat) ^ Suc i * 2 ^ (8 - i) = 2 ^ 9" by (simp only: power_add[symmetric])'''),
       (L(D33, 299, 300), r'''  have mem: "\<And>k. k < 3 \<Longrightarrow> snd (l ! k) \<in> {0,1,2,4} \<and> snd (l' ! k) \<in> {0,1,2,4}"
    using l l' len unfolding valid_label_def by auto'''),
       (L(D33, 319, 321), r'''    assume "l ! 0 = l' ! 0 \<and> l ! 1 = l' ! 1 \<and> l ! 2 = l' ! 2"
    thus "l = l'" using len by (auto simp: list_eq_iff_nth_eq less_Suc_eq numeral_eq_Suc)'''),
       (L(D33, 588, 588), r'''  then obtain j where j: "j < 22" and U: "U = shor_errors ! j" using shor_lengths(1) by (auto simp: in_set_conv_nth)''')],
 D34: [(L(D34, 69, 69), r'''    then obtain l where l: "l < length vs" and vl: "v = vs ! l" by (auto simp: in_set_conv_nth)'''),
       (L(D34, 888, 890), r'''    moreover have "complex_of_real (Re (Tr P)) = Tr P"
      by (rule Tr_hermitian_real[OF Pc, symmetric]) (simp add: hermitian_def Ph)
    ultimately have "Re (Tr P) \<noteq> 0" unfolding of_real_eq_0_iff[where 'a = complex, symmetric] by simp'''),
       (L(D34, 928, 928), r'''    then obtain a where a: "a < length ks" and "U = Us ! a" unfolding Us_len[symmetric] by (auto simp: in_set_conv_nth)'''),
       (L(D34, 972, 972), r'''      then obtain a where a: "a < length ks" and ka: "ks ! a = k" by (auto simp: in_set_conv_nth)''')]}
AFFECTED = {D1: ["cpx_vec_length_zero_iff", "hs_inner_prod_left_add"], D11: ["two_states_nontrivial_inner_prod", "no_cloning"],
            D32: ["ket_plus_unit", "ket_minus_unit", "Pauli_Z_ket_minus"],
            D33: ["qubit_op_carrier", "label_vec_inner", "shor_errors_unitary", "qubit_op_one"],
            D34: ["psd_PXP_decomp_in_range", "knill_laflamme_sufficiency"]}
assert "\\<psi>\\<^sub>2_norm_sq" not in SRC[D11].replace(L(D11, 106, 113), "")

def prime(t): return re.sub(r"^(lemma|theorem|corollary) (\S+?):", r"\1 \2':", t, count=1)

if "--scratch" in sys.argv:
    used = {old: 0 for reps in REPS.values() for old, _ in reps}
    out = ["theory D43", "  imports Quantum_Computing_by_VP.Day11_Gates_No_Cloning Quantum_Computing_by_VP.Day21_Average_Conjecture",
           "    Quantum_Computing_by_VP.Day32_Phase_Flip_Code Quantum_Computing_by_VP.Day33_Shor_Code",
           "    Quantum_Computing_by_VP.Day34_Knill_Laflamme", "begin", "", NEW1, "", NEW2, "", prime(HS_REAL), "", prime(HS_NONNEG), ""]
    for f, names in AFFECTED.items():
        bl = blocks(f)
        for n in names:
            t = bl[n]
            for old, new in REPS[f]:
                if old in t: used[old] += t.count(old); t = t.replace(old, new)
            out += [prime(t), ""]
    assert all(v == EXP[k] for k, v in used.items()), [k[:40] for k, v in used.items() if v != EXP[k]]
    out.append("end\n")
    open(os.path.join(P, "wip/d23/D43.thy"), "w").write("\n".join(out)); print("scratch written")
else:
    def applied(f):
        s = SRC[f]
        for old, new in dict(REPS[f]).items(): assert s.count(old) == EXP[old], (f, old[:40]); s = s.replace(old, new)
        return s
    b21 = blocks(D21)
    edit(D1, src=applied(D1), remove=["hs_inner_prod_self_real", "hs_inner_prod_self_nonneg"],
         insert_after=[("cpx_vec_length_pos", [NEW1, txt(r"$\|v\|=1$ iff $\braket vv=1$."), NEW2, b21["cmod_sq_sum"], b21["cmod_sq_sum'"]]),
                       ("hs_inner_prod_self_real", [HS_REAL]), ("hs_inner_prod_self_nonneg", [HS_NONNEG])])
    edit(D21, remove=["cmod_sq_sum", "cmod_sq_sum'"])
    edit(D25, src=SRC[D25].replace("vnorm_nonneg", "cpx_vec_length_nonneg"), remove=["cpx_vec_length_nonneg"])
    for f in [D11, D32, D33, D34]: edit(f, src=applied(f))
    print("installed")

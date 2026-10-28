"""Audit tick 46 (2026-10-28): the metis/smt calls of Days 22_MK, 23, 25_HB and 26: |z|^2 through
the bundle's cnj_mult_self_cmod, real parts through of_real_Re, the double adjoint through fun_cong,
the Kraus count through lin_indep_mats_length_le; and the bundle gains nat_eq_iff_div_mod (a number is
determined by quotient and remainder), which replaces the four local proofs of that fact (Days 15,
23_EE, 26, Unitary_Tensor_Algebra).  `python3 sweep6.py --scratch` writes one check theory per file
(wip/d23/D46_*.thy, listed in wip/d23/ROOT); without the flag it installs."""
import os, re, sys
sys.path.insert(0, os.path.dirname(__file__))
from planlib import *

ML, UTA = "Essential_Functional_Analysis/Matrix_Lemmas.thy", "Essential_Functional_Analysis/Unitary_Tensor_Algebra.thy"
D15, D22, D23C = "Day15_Partial_Traces.thy", "Day22_Minimal_Kraus.thy", "Day23_Choi_Extreme_Points.thy"
D23E, D25, D26 = "Day23_Extremality_Examples.thy", "Day25_Hahn_Banach.thy", "Day26_Arveson_Extension.thy"
FILES = [ML, UTA, D15, D22, D23C, D23E, D25, D26]
SRC = {f: head(f) for f in FILES}
EXP = {}
def L(f, a, b, need=True):
    t = "\n".join(SRC[f].split("\n")[a - 1:b]); assert not need or "metis" in t or "smt" in t, (f, a, b)
    EXP[t] = SRC[f].count(t); return t

DIVMOD = [txt(r"A number is determined by its quotient and remainder."), r'''lemma nat_eq_iff_div_mod:
  fixes x y k :: nat
  shows "x = y \<longleftrightarrow> x div k = y div k \<and> x mod k = y mod k"
proof
  assume "x div k = y div k \<and> x mod k = y mod k"
  hence "x div k * k + x mod k = y div k * k + y mod k" by simp
  thus "x = y" by (simp only: div_mult_mod_eq)
qed simp''']

REPS = {
 UTA: [(L(UTA, 187, 198, False), r'''    also have "\<dots> = (if i = j then 1 else 0)"
      unfolding nat_eq_iff_div_mod[symmetric] ..''')],
 D15: [(L(D15, 487, 496, False), r'''  show "unit_mat (m * m) (p * p) a b $$ (i, j) = op_elem m p (unit_mat m m (a div m) (a mod m)) (unit_mat p p (b div p) (b mod p)) $$ (i, j)"
    using ij m0 p0 a b
    by (auto simp: unit_mat_def op_elem_def less_mult_imp_div_less nat_eq_iff_div_mod[of i a m] nat_eq_iff_div_mod[of j b p])''')],
 D22: [(L(D22, 467, 467), r'''  have xnz: "x \<noteq> 0\<^sub>v ?m" using xi i by auto'''),
       (L(D22, 741, 741), r'''    then obtain l where l: "l < length As" and wl: "w = ?ws ! l" by (auto simp: in_set_conv_nth)''')],
 D23C: [(L(D23C, 1266, 1266), r'''    from fun_cong[OF this, of X1] have "\<Phi>\<^sub>1 X1 = \<Phi> X1"
      unfolding map_adjoint_adjoint[OF L1 X1] map_adjoint_adjoint[OF L X1] .'''),
        (L(D23C, 1360, 1362), r'''  hence "length (kraus_products Vs) \<le> n * n" by (rule lin_indep_mats_length_le)
  thus ?thesis using power2_le_imp_le[of "length Vs" n] by (simp add: power2_eq_square length_kraus_products)''')],
 D23E: [(L(D23E, 225, 225), r'''  have ll: "cnj z * z = 1" unfolding cnj_mult_self_cmod lam by simp'''),
        (L(D23E, 289, 290), r'''  hence "complex_of_real (1 / sqrt (real d)) * complex_of_real (1 / sqrt (real d)) = 1 / of_nat d"
    by (simp only: of_real_mult[symmetric]) simp'''),
        (L(D23E, 436, 436), r'''    have "k' div n = k div n \<and> k' mod n = k mod n \<longleftrightarrow> k' = k" by (rule nat_eq_iff_div_mod[symmetric])''')],
 D25: [(L(D25, 297, 299), r'''  have "0 \<le> C * hs_norm_lmat x" by (rule order_trans[OF abs_ge_zero F_C])'''),
       (L(D25, 315, 315), r'''      unfolding complex_norm_square by (simp only: mult.commute)'''),
       (L(D25, 535, 537), r'''      have h_pos: "0 < hs_norm_lmat x"
        using \<open>x \<noteq> 0\<close> hs_norm_lmat_nonneg[of x] by (simp add: hs_norm_lmat_zero_iff order_le_less)''')],
 D26: [(L(D26, 277, 277), r'''    using fherm by (auto simp: complex_eq_iff)'''),
       (L(D26, 537, 537), r'''      thus "Tr (W * Hm) = complex_of_real (ga Hm)" using of_real_Re[OF r] by simp'''),
       (L(D26, 689, 689), r'''  show ?thesis by (intro exI[of _ Ws] conjI Wc) (use Wk ext operator_systemD(1)[OF OS] in auto)'''),
       (L(D26, 760, 768, False), r'''    also have "\<dots> = 1\<^sub>m (k * n) $$ (x, y)"
      using x y nat_eq_iff_div_mod[of x y n] by auto''')]}

def blocks(f): return [(b["name"], "\n".join(b["lines"]).rstrip("\n")) for b in B.split(SRC[f]) if b["name"]]
def prime(t): return re.sub(r"^(lemma|theorem|corollary) (\S+?):", r"\1 \2':", t, count=1)
SESSION = {ML: "Essential_Functional_Analysis", UTA: "Essential_Functional_Analysis"}

if "--scratch" in sys.argv:
    used, names = {old: 0 for f in REPS for old, _ in REPS[f]}, []
    for f in REPS:
        th = "D46_" + (os.path.basename(f)[:-4].split("_")[0] if f in SESSION else f[3:5] + ("C" if f == D23C else "E" if f == D23E else ""))
        out = ["theory " + th, "  imports %s.%s" % (SESSION.get(f, "Quantum_Computing_by_VP"), os.path.basename(f)[:-4]), "begin", ""]
        needs = any("nat_eq_iff_div_mod" in new for _, new in REPS[f])
        if needs: out += [DIVMOD[1].replace("lemma nat_eq_iff_div_mod:", "lemma nat_eq_iff_div_mod':"), ""]
        for n, t in blocks(f):
            if not any(old in t for old, _ in REPS[f]): continue
            for old, new in REPS[f]:
                if old in t: used[old] += t.count(old); t = t.replace(old, new)
            t = prime(t)
            out += [t.replace("nat_eq_iff_div_mod", "nat_eq_iff_div_mod'") if needs else t, ""]
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
        if f == ML: edit(f, src=s, insert_after=[("Re_of_real_eq", DIVMOD)])
        else: edit(f, src=s)
    print("installed")

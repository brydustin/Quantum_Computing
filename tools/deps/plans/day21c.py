"""Audit tick 42 (2026-10-28): Day 21_AC's nine metis calls.  `cmod_sq_sum` moves to the top of the
theory with its companion `cmod_sq_sum'` (cnj f * f), so the four sum-of-squares sites are one
`unfolding` each; the eigenvalue sign and the cosine step are `Re_of_real_eq`/`cis.sel`; the split
congruence is `simp`; the idempotent-eigenvalue step is `auto`.  `python3 day21c.py --scratch`
writes wip/d23/D21c.thy (primed copies of every touched lemma) for tools/chk.sh; without the
flag it installs."""
import os, re, sys
sys.path.insert(0, os.path.dirname(__file__))
from planlib import *

F = "Day21_Average_Conjecture.thy"
NEW = r'''lemma cmod_sq_sum': "complex_of_real (\<Sum>k\<in>A. (cmod (f k))\<^sup>2) = (\<Sum>k\<in>A. cnj (f k) * f k)"
  unfolding cmod_sq_sum by (simp add: mult.commute)'''

REPS = [
 (r'''    hence "cos (2 * pi * (real m - real m') / real n) = 1" by (metis cis.sel(1) one_complex.sel(1))''',
  r'''    hence "cos (2 * pi * (real m - real m') / real n) = 1"
      using cis.sel(1)[of "2 * pi * (real m - real m') / real n"] by simp'''),
 (r'''    finally have "complex_of_real (D ! k) = \<langle>?u | Q *\<^sub>v ?u\<rangle>" .
    moreover have "Re \<langle>?u | Q *\<^sub>v ?u\<rangle> \<ge> 0" using Q du unfolding psd_def by auto
    ultimately show ?thesis by (metis Re_complex_of_real)''',
  r'''    finally have "D ! k = Re \<langle>?u | Q *\<^sub>v ?u\<rangle>" by (rule Re_of_real_eq)
    thus ?thesis using Q du unfolding psd_def by auto'''),
 (r'''  unfolding ucp_average_split_def by metis''',
  r'''  unfolding ucp_average_split_def by simp'''),
 (r'''    have "complex_of_real (\<Sum>a<n. (cmod (\<phi> l $ a))\<^sup>2) = (\<Sum>a<n. \<phi> l $ a * cnj (\<phi> l $ a))"
      by (simp add: complex_mult_cnj cmod_power2 del: of_real_power)
    hence "(\<Sum>a<n. (cmod (\<phi> l $ a))\<^sup>2) = 1" using e by (metis of_real_eq_1_iff)''',
  r'''    have "(\<Sum>a<n. (cmod (\<phi> l $ a))\<^sup>2) = 1" using e unfolding cmod_sq_sum[symmetric] of_real_eq_1_iff .'''),
 (r'''    have "complex_of_real (\<Sum>p<n. (cmod (\<phi> a l $ p))\<^sup>2) = (\<Sum>p<n. cnj (\<phi> a l $ p) * \<phi> a l $ p)"
      by (simp add: complex_mult_cnj cmod_power2 Groups.mult.commute[of "cnj _"] del: of_real_power)
    moreover have "(\<Sum>p<n. (cmod (\<phi> a l $ p))\<^sup>2) = 1"
      using \<phi>n[OF a l] unfolding cpx_vec_length_def by (metis (no_types, lifting) real_sqrt_eq_1_iff)
    ultimately show ?thesis by simp''',
  r'''    have "(\<Sum>p<n. (cmod (\<phi> a l $ p))\<^sup>2) = 1"
      using \<phi>n[OF a l] unfolding cpx_vec_length_def by (auto simp: real_sqrt_eq_1_iff)
    thus ?thesis unfolding cmod_sq_sum'[symmetric] of_real_eq_1_iff .'''),
 (r'''    have "complex_of_real (\<Sum>c<d. (cmod ((Km * V) $$ (c, k)))\<^sup>2) = (\<Sum>c<d. cnj ((Km * V) $$ (c, k)) * (Km * V) $$ (c, k))"
      by (simp add: complex_mult_cnj cmod_power2 Groups.mult.commute[of "cnj _"] del: of_real_power)
    hence "(\<Sum>c<d. (cmod ((Km * V) $$ (c, k)))\<^sup>2) = D ! k" using gram_e[OF k k] by (metis of_real_eq_iff)''',
  r'''    have "(\<Sum>c<d. (cmod ((Km * V) $$ (c, k)))\<^sup>2) = D ! k"
      using gram_e[OF k k] unfolding cmod_sq_sum'[symmetric] if_P[OF refl] of_real_eq_iff .'''),
 (r'''      hence "(\<Sum>a<d. cnj (V $$ (a, k)) * V $$ (a, k)) = 1" using VV k by simp
      moreover have "complex_of_real (\<Sum>a<d. (cmod (V $$ (a, k)))\<^sup>2) = (\<Sum>a<d. cnj (V $$ (a, k)) * V $$ (a, k))"
        by (simp add: complex_mult_cnj cmod_power2 Groups.mult.commute[of "cnj _"] del: of_real_power)
      ultimately have "(\<Sum>a<d. (cmod (V $$ (a, k)))\<^sup>2) = 1" by (metis of_real_eq_1_iff)''',
  r'''      hence "(\<Sum>a<d. cnj (V $$ (a, k)) * V $$ (a, k)) = 1" using VV k by simp
      hence "(\<Sum>a<d. (cmod (V $$ (a, k)))\<^sup>2) = 1" unfolding cmod_sq_sum'[symmetric] of_real_eq_1_iff .'''),
 (r'''      have rc: "cnj (\<Sum>j<d. c j * cnj (c j)) = (\<Sum>j<d. c j * cnj (c j))"
        using cmod_sq_sum[of c "{..<d}"] by (metis complex_cnj_complex_of_real)''',
  r'''      have rc: "cnj (\<Sum>j<d. c j * cnj (c j)) = (\<Sum>j<d. c j * cnj (c j))"
        unfolding cmod_sq_sum[symmetric] by simp'''),
 (r'''    thus ?thesis by (metis mult_cancel_right1 mult_eq_0_iff)''',
  r'''    thus ?thesis by auto''')]

AFFECTED = ["omega_pow_orth", "psd_eig", "ucp_average_split_cong", "horn_lemma", "ra_cq", "onb_complete",
            "svd_square", "contraction_avg", "bessel_rows"]

def prime(t): return re.sub(r"^(lemma|theorem|corollary) (\S+?):", r"\1 \2':", t, count=1)

blocks = {b["name"]: "\n".join(b["lines"]).rstrip("\n") for b in B.split(head(F)) if b["name"]}
if "--scratch" in sys.argv:
    used = {old: 0 for old, _ in REPS}
    def fix(t):
        for old, new in REPS:
            if old in t:
                assert t.count(old) == 1; t = t.replace(old, new); used[old] += 1
        return t
    out = ["theory D21c", "  imports Quantum_Computing_by_VP.Day21_Average_Conjecture", "begin", "", NEW, ""]
    out += [prime(fix(blocks[n])) + "\n" for n in AFFECTED] + ["end", ""]
    assert all(v == 1 for v in used.values()), {k[:50]: v for k, v in used.items()}
    open(os.path.join(P, "wip/d23/D21c.thy"), "w").write("\n".join(out)); print("scratch written")
else:
    edit(F, remove=["cmod_sq_sum"], insert_after=[("omega_pow_orth", [blocks["cmod_sq_sum"], NEW])], replace=REPS)
    print("installed")

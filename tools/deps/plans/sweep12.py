"""Audit tick 52 (2026-10-28): Day 22's |M| <= 1 for a positive unit-trace M as one chain,
|M|^2 = sum |M_ij|^2 <= sum Re M_ii Re M_jj = (Re Tr M)^2 = 1 (90 lines -> 17).
`python3 sweep12.py --scratch` writes wip/d23/D52.thy; without the flag it installs."""
import os, re, sys
sys.path.insert(0, os.path.dirname(__file__))
from planlib import *

D22 = "Day22_UCP_Compact.thy"
SRC = head(D22)
BL = {b["name"]: "\n".join(b["lines"]).rstrip("\n") for b in B.split(SRC) if b["name"]}

NEW = r'''lemma norm_lmat_le_of_psd_unit_trace:
  fixes M :: "(complex, 'k :: finite, 'k) lmat"
  assumes psd: "psd_lmat M" and tr: "Tr_lmat M = 1"
  shows "norm M \<le> 1"
proof (rule power2_le_imp_le)
  let ?M = "unwrap_lm M" and ?I = "{0..<CARD('k)}"
  have "?M \<in> carrier_mat CARD('k) CARD('k)" "psd ?M" using psd by simp_all
  note bound = psd_entry_bound_by_diag[OF this]
  have "(norm M)\<^sup>2 = inner M M" by (simp add: power2_norm_eq_inner)
  also have "\<dots> = (\<Sum>(i, j) \<in> ?I \<times> ?I. (norm (?M $$ (i, j)))\<^sup>2)"
    unfolding inner_lmat_def
    by (intro sum.cong refl) (auto simp: power2_norm_eq_inner [symmetric] split: prod.split)
  also have "\<dots> \<le> (\<Sum>(i, j) \<in> ?I \<times> ?I. Re (?M $$ (i, i)) * Re (?M $$ (j, j)))"
    using bound by (intro sum_mono) (auto split: prod.split)
  also have "\<dots> = (\<Sum>i \<in> ?I. Re (?M $$ (i, i))) * (\<Sum>j \<in> ?I. Re (?M $$ (j, j)))"
    unfolding sum_product sum.cartesian_product ..
  also have "\<dots> = 1"
    using tr unfolding Tr_lmat_def Re_sum[symmetric] by simp
  finally show "(norm M)\<^sup>2 \<le> 1\<^sup>2" by simp
qed simp'''

if "--scratch" in sys.argv:
    out = ["theory D52", "  imports Quantum_Computing_by_VP.Day22_UCP_Compact", "begin", "",
           NEW.replace("lemma norm_lmat_le_of_psd_unit_trace:", "lemma norm_lmat_le_of_psd_unit_trace':"), "", "end\n"]
    open(os.path.join(P, "wip/d23/D52.thy"), "w").write("\n".join(out))
    root = os.path.join(P, "wip/d23/ROOT"); r = open(root).read()
    open(root, "w").write(r[:r.index("  theories")] + "  theories\n    D52\n")
    print("scratch written: D52")
else:
    old = BL["norm_lmat_le_of_psd_unit_trace"]
    assert SRC.count(old) == 1
    edit(D22, src=SRC.replace(old, NEW))
    print("installed")

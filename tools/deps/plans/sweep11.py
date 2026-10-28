"""Audit tick 51 (2026-10-28): Day 13's trace positivity.  Re Tr P >= 0 for P >= 0 because each
P_ii = <e_i|P e_i> (Day 4 inner_unit_T_unit) has non-negative real part (59 lines -> 8);
Re Tr(M*M rho) >= 0 because Tr(M*M rho) = Tr(M rho M*) and M rho M* >= 0 (Day 2 Tr_cyclic,
Day 4 psd_conjugate; 73 -> 13, no square root needed).  `python3 sweep11.py --scratch` writes
wip/d23/D51.thy; without the flag it installs."""
import os, re, sys
sys.path.insert(0, os.path.dirname(__file__))
from planlib import *

D13 = "Day13_Density_Matrices.thy"
SRC = head(D13)
BL = {b["name"]: "\n".join(b["lines"]).rstrip("\n") for b in B.split(SRC) if b["name"]}

TRP = r'''lemma Tr_psd_Re_nonneg:
  assumes P: "psd P" and Pc: "P \<in> carrier_mat n n"
  shows "0 \<le> Re (Tr P)"
proof -
  have Pii: "0 \<le> Re (P $$ (i, i))" if "i < n" for i
    using P[unfolded psd_iff_quad_form_nonneg[OF Pc], rule_format, of "unit_vec n i"]
    unfolding inner_unit_T_unit[OF Pc that that] by simp
  show ?thesis unfolding Tr_carrier[OF Pc] Re_sum by (rule sum_nonneg) (simp add: Pii)
qed'''
EPT = r'''lemma ensemble_prob_trace:
  fixes Ms :: "complex Matrix.mat list"
  assumes ms: "measurement_system n Ms"
      and dm: "density_matrix n \<rho>"
      and Min: "M \<in> set Ms"
  shows "Re (Tr ((M\<^sup>\<dagger>) * M * \<rho>)) \<ge> 0"
proof -
  have M: "M \<in> carrier_mat n n" using ms Min by (auto simp: measurement_system_def)
  have \<rho>: "\<rho> \<in> carrier_mat n n" "psd \<rho>" using dm by (auto simp: density_matrix_def)
  have Md: "M\<^sup>\<dagger> \<in> carrier_mat n n" by (rule dagger_carrier[OF M])
  have "Tr ((M\<^sup>\<dagger>) * M * \<rho>) = Tr ((M * \<rho>) * (M\<^sup>\<dagger>))"
    unfolding assoc_mult_mat[OF Md M \<rho>(1)] by (rule Tr_cyclic) (use M \<rho>(1) in simp_all)
  moreover have "psd (M * \<rho> * (M\<^sup>\<dagger>))"
    using psd_conjugate[OF \<rho> Md] by (simp add: dagger_of_dagger_is_id)
  ultimately show ?thesis
    using Tr_psd_Re_nonneg[OF _ mult_carrier_mat[OF mult_carrier_mat[OF M \<rho>(1)] Md]] by simp
qed'''
REPS = [(BL["Tr_psd_Re_nonneg"], TRP), (BL["ensemble_prob_trace"], EPT)]

if "--scratch" in sys.argv:
    out = ["theory D51", "  imports Quantum_Computing_by_VP.Day13_Density_Matrices", "begin", "",
           TRP.replace("lemma Tr_psd_Re_nonneg:", "lemma Tr_psd_Re_nonneg':"), "",
           EPT.replace("lemma ensemble_prob_trace:", "lemma ensemble_prob_trace':").replace("Tr_psd_Re_nonneg[", "Tr_psd_Re_nonneg'["), "", "end\n"]
    open(os.path.join(P, "wip/d23/D51.thy"), "w").write("\n".join(out))
    root = os.path.join(P, "wip/d23/ROOT"); r = open(root).read()
    open(root, "w").write(r[:r.index("  theories")] + "  theories\n    D51\n")
    print("scratch written: D51")
else:
    s = SRC
    for old, new in REPS: assert s.count(old) == 1, old[:40]; s = s.replace(old, new)
    edit(D13, src=s)
    print("installed")

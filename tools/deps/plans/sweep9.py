"""Audit tick 49 (2026-10-28): Day 14's quadratic form of an ensemble density,
<g|rho g> = sum_i p_i |<psi_i|g>|^2, by induction with one vector identity per step:
rho_{(p,psi)#E} g = (p <psi|g>) psi + rho_E g (Day 4 outer_sum_singleton_eq + Day 2
outer_prod_mult_vec + Day 3 smult_mat_mult_vec).  `python3 sweep9.py --scratch` writes
wip/d23/D49.thy; without the flag it installs."""
import os, re, sys
sys.path.insert(0, os.path.dirname(__file__))
from planlib import *

D14 = "Day14_Pure_States.thy"
SRC = head(D14)
BL = {b["name"]: "\n".join(b["lines"]).rstrip("\n") for b in B.split(SRC) if b["name"]}

SINGLE = r'''lemma outer_sum_singleton_mult_vec:
  assumes \<psi>_dim: "dim_vec \<psi> = n" and \<gamma>_dim: "dim_vec \<gamma> = n"
  shows "outer_sum n [\<psi>] *\<^sub>v \<gamma> = \<langle>\<psi>|\<gamma>\<rangle> \<cdot>\<^sub>v \<psi>"
  unfolding outer_sum_singleton_eq[OF \<psi>_dim] by (rule outer_prod_mult_vec) (simp add: \<psi>_dim \<gamma>_dim)'''
QUAD = r'''lemma ensemble_density_quad_form:
  assumes E_dim: "\<forall>(p, \<psi>) \<in> set E. dim_vec \<psi> = n"
      and \<gamma>_dim: "dim_vec \<gamma> = n"
  shows "\<langle>\<gamma> | ensemble_density n E *\<^sub>v \<gamma>\<rangle> =
         (\<Sum>(p, \<psi>) \<leftarrow> E. complex_of_real p * \<langle>\<psi>|\<gamma>\<rangle> * cnj \<langle>\<psi>|\<gamma>\<rangle>)"
  using E_dim
proof (induction E)
  case Nil
  show ?case using \<gamma>_dim by (simp add: ensemble_density_def inner_prod_def scalar_prod_def)
next
  case (Cons a E)
  obtain p \<psi> where a: "a = (p, \<psi>)" by (cases a) auto
  have \<psi>: "dim_vec \<psi> = n" and E: "\<forall>(p, \<psi>) \<in> set E. dim_vec \<psi> = n" using Cons.prems a by auto
  have \<gamma>: "\<gamma> \<in> carrier_vec n" using \<gamma>_dim by auto
  have P: "outer_sum n [\<psi>] \<in> carrier_mat n n" by auto
  let ?c = "complex_of_real p * \<langle>\<psi>|\<gamma>\<rangle>" and ?r = "ensemble_density n E *\<^sub>v \<gamma>"
  have "ensemble_density n ((p, \<psi>) # E) *\<^sub>v \<gamma> = ?c \<cdot>\<^sub>v \<psi> + ?r"
    unfolding ensemble_density_Cons add_mult_distrib_mat_vec[OF smult_carrier_mat[OF P] ensemble_density_carrier_dim \<gamma>]
      smult_mat_mult_vec[OF P \<gamma>] outer_sum_singleton_mult_vec[OF \<psi> \<gamma>_dim] smult_smult_assoc ..
  moreover have "dim_vec (?c \<cdot>\<^sub>v \<psi>) = dim_vec ?r" using \<psi> ensemble_density_carrier_dim[of n E] by simp
  ultimately have "\<langle>\<gamma> | ensemble_density n ((p, \<psi>) # E) *\<^sub>v \<gamma>\<rangle> = ?c * \<langle>\<gamma>|\<psi>\<rangle> + \<langle>\<gamma>|?r\<rangle>"
    by (simp only: inner_prod_right_add' inner_prod_right_smult')
  thus ?case using Cons.IH[OF E] inner_prod_cnj[of \<psi> \<gamma>] \<psi> \<gamma>_dim a by (simp add: mult.assoc)
qed'''
REPS = [(BL["outer_sum_singleton_mult_vec"], SINGLE), (BL["ensemble_density_quad_form"], QUAD)]

def prime(t): return re.sub(r"^(lemma|theorem|corollary) (\S+?):", r"\1 \2':", t, count=1)

if "--scratch" in sys.argv:
    out = ["theory D49", "  imports Quantum_Computing_by_VP.Day14_Pure_States", "begin", "",
           prime(SINGLE), "", prime(QUAD).replace("outer_sum_singleton_mult_vec[", "outer_sum_singleton_mult_vec'["), "", "end\n"]
    open(os.path.join(P, "wip/d23/D49.thy"), "w").write("\n".join(out))
    root = os.path.join(P, "wip/d23/ROOT"); r = open(root).read()
    open(root, "w").write(r[:r.index("  theories")] + "  theories\n    D49\n")
    print("scratch written: D49")
else:
    s = SRC
    for old, new in REPS: assert s.count(old) == 1, old[:40]; s = s.replace(old, new)
    edit(D14, src=s)
    print("installed")

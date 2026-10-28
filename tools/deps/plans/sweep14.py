"""Audit tick 54 (2026-10-28): the last hand-built topology.  The bundle gains
continuous_on_lmat_entries (a map into lmat is continuous when its entries are) and the composable
continuous_on_unwrap_lm_index_comp; Day 28's continuity of (sigma, tau) |-> sigma (x) tau is then one
entry formula (122 lines -> 13), and Day 22's block-sum set is closed_Collect_eq (26 -> 5).
`python3 sweep14.py --scratch` writes wip/d23/D54*.thy; without the flag it installs."""
import os, re, sys
sys.path.insert(0, os.path.dirname(__file__))
from planlib import *

LE, D22, D28 = "Essential_Functional_Analysis/Lmat_Euclidean.thy", "Day22_UCP_Compact.thy", "Day28_Entanglement_Witnesses.thy"
SRC = {f: head(f) for f in (LE, D22, D28)}
BL = {f: {b["name"]: "\n".join(b["lines"]).rstrip("\n") for b in B.split(SRC[f]) if b["name"]} for f in SRC}

COMP = r'''lemma continuous_on_unwrap_lm_index_comp [continuous_intros]:
  fixes f :: "'b :: topological_space \<Rightarrow> ('a :: real_normed_vector, 'm :: finite, 'n :: finite) lmat"
  assumes "continuous_on S f" and "i < CARD('m)" and "j < CARD('n)"
  shows "continuous_on S (\<lambda>x. unwrap_lm (f x) $$ (i, j))"
  by (rule continuous_on_compose2[OF continuous_on_unwrap_lm_index[where S = UNIV, OF assms(2,3)] assms(1)]) simp'''
ENTRIES = r'''lemma continuous_on_lmat_entries:
  fixes f :: "'b :: t2_space \<Rightarrow> ('a :: euclidean_space, 'm :: finite, 'n :: finite) lmat"
  assumes "\<And>i j. i < CARD('m) \<Longrightarrow> j < CARD('n) \<Longrightarrow> continuous_on S (\<lambda>x. unwrap_lm (f x) $$ (i, j))"
  shows "continuous_on S f"
proof (subst continuous_on_componentwise, intro ballI)
  fix b :: "('a, 'm, 'n) lmat" assume "b \<in> Basis"
  then obtain i j u where b: "b = lmat_axis i j u" and ij: "i < CARD('m)" "j < CARD('n)"
    unfolding Basis_lmat_def Basis_lmat_set_def by auto
  show "continuous_on S (\<lambda>x. inner (f x) b)"
    unfolding b inner_lmat_axis[OF ij] by (intro continuous_intros assms ij)
qed'''
TENSOR = r'''lemma continuous_on_tensor_lmat:
  fixes T :: "((complex, 'm :: finite, 'm) lmat
              \<times> (complex, 'p :: finite, 'p) lmat) set"
  shows "continuous_on T (\<lambda>(\<sigma>, \<tau>). tensor_lmat \<sigma> \<tau>
                                    :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat)"
proof (rule continuous_on_lmat_entries)
  fix I J assume "I < CARD('m \<times> 'p)" "J < CARD('m \<times> 'p)"
  hence I: "I < CARD('m) * CARD('p)" and J: "J < CARD('m) * CARD('p)" by simp_all
  have e: "unwrap_lm ((\<lambda>(\<sigma>, \<tau>). tensor_lmat \<sigma> \<tau> :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat) x) $$ (I, J) =
           unwrap_lm (fst x) $$ (I div CARD('p), J div CARD('p)) * unwrap_lm (snd x) $$ (I mod CARD('p), J mod CARD('p))" for x
    using I J by (cases x) simp
  show "continuous_on T (\<lambda>x. unwrap_lm ((\<lambda>(\<sigma>, \<tau>). tensor_lmat \<sigma> \<tau> :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat) x) $$ (I, J))"
    unfolding e using I J by (intro continuous_intros) (auto simp: less_mult_imp_div_less)
qed'''
BLOCK = r'''lemma closed_block_sum_eq:
  assumes a: "a < CARD('d :: finite)" and b: "b < CARD('d)"
  shows "closed {M :: (complex, 'n :: finite \<times> 'd, 'n \<times> 'd) lmat.
                  (\<Sum>i<CARD('n). unwrap_lm M $$ (i * CARD('d) + a, i * CARD('d) + b)) = c}"
  by (intro closed_Collect_eq continuous_on_const continuous_on_sum continuous_on_unwrap_lm_index)
     (use mult_index_lt[OF _ a] mult_index_lt[OF _ b] in auto)'''

def prime(t, names):
    t = re.sub(r"^(lemma|theorem|corollary) (\S+?)( \[continuous_intros\])?:", r"\1 \2'\3:", t, count=1)
    for m in names: t = re.sub(r"(?<=[ \[(])(%s)(?=[ \[)\]])" % m, m + "'", t)
    return t

if "--scratch" in sys.argv:
    out = ["theory D54", "  imports Quantum_Computing_by_VP.Day28_Entanglement_Witnesses", "begin", "",
           prime(COMP, []), "", prime(ENTRIES, []), "",
           prime(TENSOR, ["continuous_on_lmat_entries"]).replace("(intro continuous_intros)", "(intro continuous_intros continuous_on_unwrap_lm_index_comp')"),
           "", "end\n"]
    open(os.path.join(P, "wip/d23/D54.thy"), "w").write("\n".join(out))
    out = ["theory D54_22", "  imports Quantum_Computing_by_VP.Day22_UCP_Compact", "begin", "", prime(BLOCK, []), "", "end\n"]
    open(os.path.join(P, "wip/d23/D54_22.thy"), "w").write("\n".join(out))
    root = os.path.join(P, "wip/d23/ROOT"); r = open(root).read()
    open(root, "w").write(r[:r.index("  theories")] + "  theories\n    D54\n    D54_22\n")
    print("scratch written: D54 D54_22")
else:
    edit(LE, insert_after=[("continuous_on_unwrap_lm_index", [COMP, txt("Conversely, a map into lmat is continuous when all its entries are."), ENTRIES])])
    edit(D22, src=SRC[D22].replace(BL[D22]["closed_block_sum_eq"], BLOCK))
    edit(D28, src=SRC[D28].replace(BL[D28]["continuous_on_tensor_lmat"], TENSOR))
    print("installed")

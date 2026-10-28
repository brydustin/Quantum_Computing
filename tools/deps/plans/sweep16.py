"""Audit tick 56 (2026-10-28): Day 15's operator-tensor isomorphism without the eight hand-stated
index identities per direction: given the bounds, simp recombines div/mod itself (126 lines -> ~60).
`python3 sweep16.py --scratch` writes wip/d23/D56.thy; without the flag it installs."""
import os, re, sys
sys.path.insert(0, os.path.dirname(__file__))
from planlib import *

D15 = "Day15_Partial_Traces.thy"
SRC = head(D15)
OLD = SRC[SRC.index("proposition operator_tensor_space_isomorphism:"):SRC.index("corollary operator_tensor_space_isomorphic:")].rstrip("\n")
NEW = r'''proposition operator_tensor_space_isomorphism:
  assumes m_pos: "0 < m"
      and p_pos: "0 < p"
  shows "is_isomorphism_between
           (operator_tensor_coordinate_space m p)
           (bipartite_operator_space m p)
           (operator_tensor_iso_map m p)"
proof -
  let ?V = "operator_tensor_coordinate_space m p"
  let ?W = "bipartite_operator_space m p"
  let ?F = "operator_tensor_iso_map m p"
  let ?G = "operator_tensor_iso_inv m p"
  have F_linear: "linear_structure_map ?V ?W ?F"
    unfolding linear_structure_map_def operator_tensor_coordinate_space_def
      bipartite_operator_space_def mat_linear_structure_def
    by (auto intro: operator_tensor_iso_map_zero[OF p_pos]
               operator_tensor_iso_map_add[OF p_pos]
               operator_tensor_iso_map_smult[OF p_pos])
  have G_linear: "linear_structure_map ?W ?V ?G"
    unfolding linear_structure_map_def operator_tensor_coordinate_space_def
      bipartite_operator_space_def mat_linear_structure_def
    by (auto intro: operator_tensor_iso_inv_zero[OF m_pos p_pos]
               operator_tensor_iso_inv_add[OF m_pos p_pos]
               operator_tensor_iso_inv_smult[OF m_pos p_pos])
  have GF: "?G (?F x) = x" if "x \<in> ls_carrier ?V" for x
  proof -
    have xc: "x \<in> carrier_mat (m*m) (p*p)"
      using that by (simp add: operator_tensor_coordinate_space_def mat_linear_structure_def)
    show ?thesis
    proof (rule eq_matI)
      fix a b assume "a < dim_row x" "b < dim_col x"
      hence a: "a < m*m" and b: "b < p*p" using xc by auto
      have "b div p < p" using b p_pos by (simp add: div_less_iff_less_mult)
      thus "?G (?F x) $$ (a,b) = x $$ (a,b)"
        using a b p_pos operator_tensor_iso_inv_row_bound[OF m_pos p_pos a b]
              operator_tensor_iso_inv_col_bound[OF m_pos p_pos, of a b]
        by (simp add: operator_tensor_iso_inv_def operator_tensor_iso_map_def)
    qed (use xc in \<open>simp_all add: operator_tensor_iso_inv_def\<close>)
  qed
  have FG: "?F (?G y) = y" if "y \<in> ls_carrier ?W" for y
  proof -
    have yc: "y \<in> carrier_mat (m*p) (m*p)"
      using that by (simp add: bipartite_operator_space_def mat_linear_structure_def)
    show ?thesis
    proof (rule eq_matI)
      fix r s assume "r < dim_row y" "s < dim_col y"
      hence r: "r < m*p" and s: "s < m*p" using yc by auto
      have "s div p < m" using s p_pos by (simp add: div_less_iff_less_mult)
      thus "?F (?G y) $$ (r,s) = y $$ (r,s)"
        using r s p_pos operator_tensor_iso_map_row_bound[OF p_pos r s]
              operator_tensor_iso_map_col_bound[OF p_pos, of r s]
        by (simp add: operator_tensor_iso_inv_def operator_tensor_iso_map_def)
    qed (use yc in \<open>simp_all add: operator_tensor_iso_map_def\<close>)
  qed
  show ?thesis
    unfolding is_isomorphism_between_def
    using F_linear G_linear GF FG by blast
qed'''

if "--scratch" in sys.argv:
    out = ["theory D56", "  imports Quantum_Computing_by_VP.Day15_Partial_Traces", "begin", "",
           NEW.replace("proposition operator_tensor_space_isomorphism:", "proposition operator_tensor_space_isomorphism':"), "", "end\n"]
    open(os.path.join(P, "wip/d23/D56.thy"), "w").write("\n".join(out))
    root = os.path.join(P, "wip/d23/ROOT"); r = open(root).read()
    open(root, "w").write(r[:r.index("  theories")] + "  theories\n    D56\n")
    print("scratch written: D56")
else:
    assert SRC.count(OLD) == 1
    edit(D15, src=SRC.replace(OLD, NEW))
    print("installed")

"""Audit tick 55 (2026-10-28): DIM of lmat is the card of the injective image
((i, j), u) |-> lmat_axis i j u of {..<m} x {..<n} x Basis (109 lines -> 14); injectivity is
inner_lmat_axis_axis against the orthonormal Basis.  `python3 sweep15.py --scratch` writes
wip/d23/D55.thy; without the flag it installs."""
import os, re, sys
sys.path.insert(0, os.path.dirname(__file__))
from planlib import *

LE = "Matrix_Analysis_Prerequisites/Lmat_Euclidean.thy"
SRC = head(LE)
BL = {b["name"]: "\n".join(b["lines"]).rstrip("\n") for b in B.split(SRC) if b["name"]}
NEW = r'''lemma DIM_lmat:
  "DIM(('a :: euclidean_space, 'm :: finite, 'n :: finite) lmat)
     = CARD('m) * CARD('n) * DIM('a)"
proof -
  let ?f = "\<lambda>((i, j), u). lmat_axis i j u :: ('a, 'm, 'n) lmat"
  let ?A = "({0..<CARD('m)} \<times> {0..<CARD('n)}) \<times> (Basis :: 'a set)"
  have inj: "inj_on ?f ?A"
  proof (rule inj_onI)
    fix x y assume x: "x \<in> ?A" and y: "y \<in> ?A" and eq: "?f x = ?f y"
    obtain i j u i' j' u' where xy: "x = ((i, j), u)" "y = ((i', j'), u')" by (cases x, cases y) auto
    from x y have ij: "i < CARD('m)" "j < CARD('n)" "i' < CARD('m)" "j' < CARD('n)"
      and u: "u \<in> Basis" "u' \<in> Basis" unfolding xy by auto
    have "lmat_axis i j u = (lmat_axis i' j' u' :: ('a, 'm, 'n) lmat)" using eq unfolding xy by simp
    hence "1 = inner (lmat_axis i j u :: ('a, 'm, 'n) lmat) (lmat_axis i' j' u')"
      using u(2) by (simp add: inner_lmat_axis_axis[OF ij(3,4) ij(3,4)] inner_Basis)
    thus "x = y"
      unfolding xy inner_lmat_axis_axis[OF ij] using u by (auto simp: inner_Basis split: if_splits)
  qed
  have "lmat_axis i j u \<in> ?f ` ?A" if "i < CARD('m)" "j < CARD('n)" "u \<in> Basis" for i j u
    by (rule rev_image_eqI[of "((i, j), u)"]) (use that in simp_all)
  hence "Basis = ?f ` ?A" unfolding Basis_lmat_def Basis_lmat_set_def by auto
  thus ?thesis using card_image[OF inj] by (simp add: card_cartesian_product)
qed'''

if "--scratch" in sys.argv:
    out = ["theory D55", "  imports Matrix_Analysis_Prerequisites.Lmat_Euclidean", "begin", "",
           NEW.replace("lemma DIM_lmat:", "lemma DIM_lmat':"), "", "end\n"]
    open(os.path.join(P, "wip/d23/D55.thy"), "w").write("\n".join(out))
    root = os.path.join(P, "wip/d23/ROOT"); r = open(root).read()
    open(root, "w").write(r[:r.index("  theories")] + "  theories\n    D55\n")
    print("scratch written: D55")
else:
    assert SRC.count(BL["DIM_lmat"]) == 1
    edit(LE, src=SRC.replace(BL["DIM_lmat"], NEW))
    print("installed")

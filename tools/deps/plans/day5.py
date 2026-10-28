"""Audit tick 8 (2026-10-27): Day 5's Cholesky reduction by completing the square on block vectors
(wip/d23/D05.thy): x = vCons z y, P x = vCons (a z + <b|y>) (z b + C y), S = C - (1/a) b b*, and
<x|Px> = a |z + <b|y>/a|^2 + <y|Sy>; inner_prod_vCons goes to Day 1."""
import os, sys
sys.path.insert(0, os.path.dirname(__file__))
from planlib import *

S = scratch_blocks("wip/d23/D05.thy")
edit("Day01_Inner_Product.thy", insert_after=[("inner_prod_sum",
     [txt(r"The inner product of two vectors with a prepended coordinate."), S["inner_prod_vCons"]])])
F = "Day05_Positivity_Tests.thy"
O = {b["name"]: "\n".join(b["lines"]).rstrip("\n") for b in B.split(head(F)) if b["name"]}
edit(F, remove=["hermitian_entry"],
     replace=[('    have "P $$ (0, j + 1) = cnj (P $$ (j + 1, 0))" by (rule hermitian_entry[OF h P n j])',
               '    have "P $$ (0, j + 1) = cnj (P $$ (j + 1, 0))" using hermitian_index[OF h, of 0 "j + 1"] P n j by simp'),
              (O["cholesky_reduction"],
     txt(r"""Completing the square: for $P=\begin{pmatrix}a&b^*\\b&C\end{pmatrix}$ with $a>0$ and
$S=C-\frac1a\,bb^*$, $\braket{(z,y)}{P(z,y)}=a\,|z+\braket{b}{y}/a|^2+\braket{y}{Sy}$; so $P\ge0$
iff $S\ge0$ (take $z=-\braket{b}{y}/a$ for the direction $\Rightarrow$).""") + "\n\n" + S["cholesky_reduction"])])
print("installed")

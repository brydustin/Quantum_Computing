"""Audit tick 14 (2026-10-27): Day 28's Hermitian witness theorem as a corollary of Day 26's
hermitian_witness_from_lmat, and that lemma by trace algebra (wip/d23/D28.thy)."""
import os, sys
sys.path.insert(0, os.path.dirname(__file__))
from planlib import *

S = scratch_blocks("wip/d23/D28.thy")
old26 = r"""text \<open>The inner-product-to-Re-trace bridge for hermitian arguments,
extracted as a separate lemma so we can reuse it for the strict
separation theorem.  This is the same hermitisation construction
that drives \<open>entanglement_witness_hermitian\<close>.\<close>"""
new26 = txt(r"""The Hermitian part $W=\tfrac12(A+A^*)$ of $A$ has $\mathrm{Re}\Tr(WM)=\langle a,M\rangle$ for every
Hermitian $M$: $\Tr(A^*M)=\overline{\Tr(M^*A)}=\overline{\Tr(AM)}$, and
$\langle a,M\rangle=\mathrm{Re}\,\langle\!\langle A|M\rangle\!\rangle=\mathrm{Re}\Tr(A^*M)$.  Day 28 uses it for the
Hermitian entanglement witness.""")
edit("Day26_Arveson_Extension.thy", remove=["hermitian_witness_from_lmat"],
     insert_after=[("hermitian_witness_from_lmat", [S["hermitian_witness_from_lmat"]])],
     replace=[(old26, new26)])
edit("Day28_Entanglement_Witnesses.thy", remove=["entanglement_witness_hermitian"],
     insert_after=[("entanglement_witness_hermitian", [S["entanglement_witness_hermitian"]])])
print("installed")

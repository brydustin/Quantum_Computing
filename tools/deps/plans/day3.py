"""Audit tick 6 (2026-10-27): Householder unitaries through the projection P = |w><w| (wip/d23/D03.thy),
and the "Step k" process comments of Days 11, 12, 21 removed."""
import os, sys
sys.path.insert(0, os.path.dirname(__file__))
from planlib import *

S = scratch_blocks("wip/d23/D03.thy")
edit("Day02_Trace_Projections.thy", insert_after=[("outer_prod_carrier",
     [txt(r"$\ketbra ww$ is idempotent for a unit vector $w$: $(ww^*)(ww^*)=w(w^*w)w^*$."), S["outer_prod_idempotent"]])])
edit("Day03_Unitary_Matrices.thy",
     remove=["householder_hermitian", "householder_unitary", "householder_mult_vec_index", "householder_mult_vec"],
     insert_after=[("householder_outer_prod",
                    [S["householder_hermitian"],
                     txt(r"$U_w^2=(I-2P)^2=I-4P+4P^2=I$ for the projection $P=\ketbra ww$, and $U_w$ is Hermitian."),
                     S["householder_unitary"],
                     txt(r"$U_wx=x-2\braket wx\,w$: the reflection of $x$ in the hyperplane $w^\perp$."),
                     S["householder_mult_vec"], S["householder_mult_vec_index"]])])
for f, drop in [("Day21_Unitary_Freedom.thy", lambda b: b.startswith("Step ")),
                ("Day12_Quantum_Parallelism.thy", lambda b: b.startswith(("Compute ", "Decompose ", "We also cannot", "Show equality"))),
                ("Day11_Gates_No_Cloning.thy", lambda b: b.startswith(("Step ", "Pick two", "Compute ")))]:
    open(os.path.join(P, f), "w").write(strip_comments(head(f), drop))
edit("Day11_Gates_No_Cloning.thy", src=open(os.path.join(P, "Day11_Gates_No_Cloning.thy")).read(),
     replace=[("theorem no_cloning:", txt(r"""The notes' argument: a cloner $U$ with ancilla $\varphi$ makes $\varphi$ a unit vector, and
$\braket{\psi_1}{\psi_2}=\braket{U(\psi_1\otimes\varphi)}{U(\psi_2\otimes\varphi)}=\braket{\psi_1}{\psi_2}^2$ for
unit $\psi_1,\psi_2$, so $\braket{\psi_1}{\psi_2}\in\{0,1\}$; two states with inner product strictly between
exist once $n\ge2$.""") + "\n\ntheorem no_cloning:")])
print("installed")

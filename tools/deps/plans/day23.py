"""Reorganise Day 23 (2026-10-27): the theory follows the notes' proof of Choi's Theorem 3,
general lemmas move to Matrix_Lemmas or to the lecture that has their tools, the direction
theorems get names that match the statement, and the examples follow the notes' order.
Reads the files at git HEAD and writes the working tree; rerun from a clean HEAD only."""
import os, re, subprocess, sys
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))
import blocks as B

P = os.path.abspath(os.path.join(os.path.dirname(__file__), "../../.."))

def head(path):
    return subprocess.run(["git", "-C", P, "show", "HEAD:" + path], capture_output=True,
                          text=True, check=True).stdout

def body(b):
    return "\n".join(b["lines"]).rstrip("\n")

class Src:
    def __init__(self, path):
        self.path, self.blocks, self.used = path, B.split(head(path)), set()
    def idx(self, key):
        if isinstance(key, int): return key
        hits = [i for i, b in enumerate(self.blocks) if b["name"] == key]
        assert len(hits) == 1, (self.path, key, hits)
        return hits[0]
    def take(self, *keys):
        out = []
        for k in keys:
            i = self.idx(k)
            assert i not in self.used, (self.path, k)
            self.used.add(i)
            out.append(body(self.blocks[i]))
        return out
    def drop(self, *keys):
        for k in keys:
            i = self.idx(k)
            assert i not in self.used, (self.path, k)
            self.used.add(i)
    def check_all_used(self):
        left = [(i, b["kind"], b["name"] or b["lines"][0][:50]) for i, b in enumerate(self.blocks)
                if i not in self.used and any(l.strip() for l in b["lines"])]
        assert not left, (self.path, left)

def sub(s, old, new, count=1):
    assert s.count(old) == count, (old[:60], s.count(old))
    return s.replace(old, new)

def txt(s):
    return "text \\<open>" + s.strip() + "\\<close>"

def heading(kind, title):
    return f"{kind} \\<open>{title}\\<close>"

def write(path, parts):
    open(os.path.join(P, path), "w").write("\n\n".join(parts) + "\n")

M = Src("Day23_Choi_Extreme_Points.thy")
E = Src("Day23_Extremality_Examples.thy")

# ---- lemmas that leave Day 23 ------------------------------------------------------------

to_ML_products = M.take("mat_mult_index_sum", "mat_eq_of_mult_vec_eq") + E.take("nonzero_entry")
M.drop(38, 134)   # their one-line texts
to_ML_folds = M.take("foldr_upt_add_carrier", "foldr_upt_add_acc_index", "foldr_upt_add_index",
                     "foldr_upt_add_acc_index_dn", "foldr_smult_nth_index") + E.take("foldr_smult_index")
M.drop(21, 25, 35, 86)
to_ML_sums = M.take("concat_uniform_length", "concat_uniform_nth", "sum_split_prod_atLeastLessThan")
M.drop(80, 88)
to_D2_units = E.take("unit_mult_left_entry", "unit_mult_right_entry")
to_D2_trace = M.take("Tr_mat_unit_mult", "mat_trace_pairing_unique")
M.drop(162, 163)
to_D4 = M.take("psd_conjugate"); M.drop(122)
to_D17 = M.take("kraus_map_dim_one"); M.drop(9, 10)
to_D21 = M.take("lin_indep_complex_mat_dagger"); M.drop(186)
# Day 1 already has these as inner_prod_right_add' and inner_prod_right_smult'
M.drop("inner_prod_add_right", "inner_prod_smult_right", 57, 60)

# ---- Day 23, main theory -----------------------------------------------------------------

pre, thy, sec = M.take(0, 1, 2)
intro = M.take(3)[0]
intro = intro[:intro.index("What is formalised here")] + r"""The formalisation proves the corollary first, for maps $\Phi(X)=\sum_iV_iXV_i^*$ with a
fixed linearly independent Kraus list (what $r=\crk(\Phi)$ gives, Day 22), and then the
theorem by duality.  The direction ($\Rightarrow$) is the notes' perturbation argument, written
with the maps $\psi_T(X)=\sum_{i,j}T_{ij}V_iXV_j^*$; for ($\Leftarrow$) a CP Radon--Nikodym
theorem takes the place of Choi 2.  The examples are in the next theory.\<close>"""

def reverse_theorem():
    s = M.take("choi_theorem_3_cptp_reverse")[0]
    s = sub(s, "theorem choi_theorem_3_cptp_reverse:", "theorem extreme_CPTP_imp_products_indep:")
    s = sub(s, '''      and dep: "\\<not> lin_indep_complex_mat n n (kraus_products Vs)"
  shows "\\<not> extreme_CPTP n d \\<Phi>"
proof -''', '''      and ext: "extreme_CPTP n d \\<Phi>"
  shows "lin_indep_complex_mat n n (kraus_products Vs)"
proof (rule ccontr)
  assume dep: "\\<not> lin_indep_complex_mat n n (kraus_products Vs)"''')
    s = sub(s, '''  show ?thesis
    by (rule not_extreme_CPTP_of_herm_witness[OF npos dpos \\<Phi>_in rep minimal H])''',
            '''  have "\\<not> extreme_CPTP n d \\<Phi>"
    by (rule not_extreme_CPTP_of_herm_witness[OF npos dpos \\<Phi>_in rep minimal H])
  thus False using ext by simp''')
    return s

def forward_theorem():
    s = M.take("choi_theorem_3_cptp_forward_complex")[0]
    return sub(s, "theorem choi_theorem_3_cptp_forward_complex:", "theorem products_indep_imp_extreme_CPTP:")

def iff_theorem():
    s = M.take("choi_theorem_3_cptp_iff")[0]
    return sub(s, '''  using choi_theorem_3_cptp_reverse[OF npos dpos \\<Phi>_in rep minimal]
        choi_theorem_3_cptp_forward_complex[OF npos dpos \\<Phi>_in rep]''',
               '''  using extreme_CPTP_imp_products_indep[OF npos dpos \\<Phi>_in rep minimal]
        products_indep_imp_extreme_CPTP[OF npos dpos \\<Phi>_in rep]''')

def small_eps():
    s = M.take("small_eps_psd")[0]
    s = sub(s, "          using inner_prod_add_right[OF x_d x_d dAx_dimv] .",
            "          by (rule inner_prod_right_add') (simp only: x_d dAx_dimv)")
    s = sub(s, "          using inner_prod_smult_right[OF x_d Ax_dim] by simp",
            "          using inner_prod_right_smult' by simp")
    return s

main = [pre, thy, sec, intro]

main += [heading("subsection", "Extreme points of CPTP and the products of a Kraus list"),
         txt(r"""Extremality compares maps on $M_n$: maps that agree on $M_n$ are the same point of
$\mathrm{CPTP}(M_n,M_d)$.  So a midpoint decomposition $\Phi=\tfrac12(\Phi_1+\Phi_2)$ that
witnesses non-extremality consists of maps that are CPTP and linear on $M_n$ and differ from
$\Phi$ at some matrix (\<open>cptp_pair_mid\<close>).""")]
M.drop(150, 151, 152)
main += M.take("lin_on_carrier", "lin_on_carrier_add", "lin_on_carrier_smult", "lin_on_carrierI",
               "cptp_pair_mid", "extreme_CPTP")
main += [txt(r"""A Kraus representation of $\Phi$, and the products $V_j^*V_i\in M_n$ of its operators for
all pairs $(i,j)$: there are $k^2$ of them, the one at position $ik+j$ being $V_j^*V_i$.""")]
M.drop(110, 111, 7, 15, 83)
main += M.take("cptp_kraus_rep", "kraus_products", "kraus_products_carrier", "length_kraus_products",
               "kraus_products_nth")

main += [heading("subsection", "Quadratic Kraus maps"),
         txt(r"""The quadratic Kraus map of a list $V_1,\dots,V_k$ and a matrix $T\in M_k$ is
\[ \psi_T(X)=\sum_{i,j}T_{ij}\,V_iXV_j^*. \]
It is linear in $T$ and in $X$, and $\psi_I$ is the Kraus map of the list.  For $T\ge0$ it is
completely positive (Lemma A); it is trace preserving when $\sum_{i,j}T_{ij}V_j^*V_i=I_n$; and
if the $V_i$ are linearly independent, different $T$ give different maps (Lemma B).""")]
M.drop(17, 18)
main += [heading("subsubsection", "Definition and entries")]
main += M.take("kraus_quad_row", "kraus_quad_map", "kraus_quad_row_carrier", "kraus_quad_map_carrier",
               28, "kraus_quad_row_index", 30, "kraus_quad_map_index")
main += [heading("subsubsection", "Linearity, and $T=I$"), txt("Linearity in the coefficient matrix.")]
M.drop(44, 94)
main += M.take("kraus_quad_map_add_Tm", "kraus_quad_map_smult_Tm", 48, "kraus_quad_map_zero_Tm",
               142, "kraus_quad_map_add_rho", "kraus_quad_map_smult_rho",
               96, "kraus_quad_map_one_eq_kraus_map_dim")
M.drop(141)
main += [heading("subsubsection", "Positive coefficients give completely positive maps (Lemma A)")]
main += M.take(53, 32, "kraus_combo", "kraus_combo_carrier")
main += [txt(r"Entries of $W_u$, of $W_u\rho$, and of $W_u\rho W_u^*$.")]
main += M.take("kraus_combo_index", "kraus_combo_times_rho_index", 42, "kraus_combo_quad_index")
M.drop(40)
main += M.take(46, "kraus_quad_map_outer_singleton")
main += [txt(r"""Hence for $T=\sum_lu_lu_l^*$ the map $\psi_T$ is the Kraus map of the
$W_{u_l}$.""")]
M.drop(50, 52)
main += M.take("kraus_quad_map_outer_sum_eq_kraus_map_dim", "kraus_perturbation_cp")

main += [heading("subsubsection", "The pair sum and the trace")]
main += M.take(66, "kraus_pair_row", "kraus_pair_sum", "kraus_pair_row_carrier", "kraus_pair_sum_carrier")
main += [txt("Entries of the pair sum.")]
M.drop(71, 65)
main += M.take("kraus_pair_row_index", "kraus_pair_sum_index", 74, "kraus_pair_sum_add_A",
               "kraus_pair_sum_smult_A", 77, "kraus_pair_sum_dagger", 98,
               "kraus_pair_sum_one_eq_sum_wdag_w", 107, "Tr_kraus_quad_map_eq", "kraus_quad_map_is_TP")
M.drop(93)

main += [heading("subsubsection", "Independent Kraus operators give different maps (Lemma B)")]
M.drop(100)
main += M.take(101, "lin_indep_zero_combo", 103, "kraus_quad_map_mat_unit_index", 105,
               "kraus_quad_map_nonzero_witness")

main += [heading("subsubsection", "The Choi matrix"),
         txt(r"""The Choi matrix of $\psi_T$ is $VTV^*$, where the columns of $V$ are the vectorised
$V_i$: the bridge from factorisations of Choi matrices back to quadratic Kraus maps.""")]
M.drop(113, 114, 119)
main += M.take("kraus_vec_mat", "kraus_vec_mat_carrier", "kraus_vec_mat_index",
               "kraus_vec_mat_dagger_index", "choi_matrix_kraus_quad_eq")

main += [heading("subsection", "Extreme maps have independent products"),
         txt(r"""The notes' direction ($\Rightarrow$), by contraposition.  A dependence among the products
gives a non-zero Hermitian $H$ with $\sum_{i,j}H_{ij}V_j^*V_i=0$.  For small $\epsilon>0$ the maps
\[ \Phi_\pm(X)=\sum_{i,j}(\delta_{ij}\pm\epsilon H_{ij})\,V_iXV_j^* \]
are completely positive (Lemma A, as $I\pm\epsilon H\ge0$) and trace preserving, differ from
$\Phi$ (Lemma B), and $\Phi=\tfrac12(\Phi_++\Phi_-)$.  So $\Phi$ is not extreme.""")]
main += [heading("subsubsection", "A Hermitian dependence")]
M.drop(79)
main += M.take(90, "mat_lin_indep_complex_neg_witness", "herm_witness_of_complex")
main += [heading("subsubsection", "Small perturbations of the identity")]
M.drop(55)
main += M.take(56, 61, "quad_form_bound_by_entry_sum", 63) + [small_eps()]
main += [heading("subsubsection", "The perturbed maps")]
M.drop(159)
main += M.take("not_extreme_CPTP_of_herm_witness") + [reverse_theorem()]

main += [heading("subsection", "A CP Radon--Nikodym theorem"),
         txt(r"""The notes prove ($\Leftarrow$) with Choi 2.  Here a CP Radon--Nikodym theorem takes its
place: if $0\le_{cp}\Psi\le_{cp}\Phi$ and $\Phi$ has the Kraus operators $V_i$, then
$\Psi=\psi_T$ for some $T\ge0$.  For Choi matrices this says that $0\le B\le VV^*$ implies
$B=VTV^*$ with $T\ge0$, which is proved with the Moore--Penrose pseudoinverse.""")]
main += [heading("subsubsection", "Dominated positive matrices")]
M.drop(121, 124, 138)
main += M.take(125, "pinv_list", "pinv_list_length", "pinv_list_index", "pinv_list_nonneg", 130,
               "diag_pinv_diag_eq", 132, "A_Aplus_A_eq", 136, "A_Aplus_B_eq_B", 139,
               "dominated_outer_sum_param")
main += [heading("subsubsection", "Completely positive maps below a Kraus map")]
M.drop(145)
main += M.take(146, "cp_radon_nikodym_choi", 148, "cp_radon_nikodym_linear")

main += [heading("subsection", "Independent products give extreme maps"),
         txt(r"""The notes' direction ($\Leftarrow$).  If $\Phi=\tfrac12(\Phi_1+\Phi_2)$, then
$\tfrac12\Phi_1\le_{cp}\Phi$, and the CP Radon--Nikodym theorem writes
$\Phi_1(X)=\sum_{i,j}T_{ij}V_iXV_j^*$ with $T\ge0$; trace preservation and the independence of
the products force $T=I$, i.e.\ $\Phi_1=\Phi$.""")]
M.drop(166, 167)
main += [forward_theorem()]

main += [heading("subsection", "Choi's Theorem 3")]
M.drop(169, 173)
main += M.take(170, 171) + [iff_theorem()]
main += [heading("subsubsection", "Unital maps (D23-1)")]
M.drop(174)
main += M.take(175, 176, "ucp_pair_mid", "extreme_UCP", "lin_on_from_carrier", "lin_on_carrier_from_lin_on",
               "map_adjoint_half", 182, "ucp_mid_imp_cptp_mid", "cptp_mid_imp_ucp_mid",
               "extreme_UCP_iff_adjoint")
main += [txt(r"""A unital Kraus representation of $\Phi:M_n\to M_d$ is a list of $d\times n$ matrices with
\[ \Phi(X)=\sum_iV_iXV_i^*\quad(X\in M_n),\qquad \sum_iV_iV_i^*=I_d; \]
every linear UCP map has one with $nd$ operators.  The adjoints of its operators are Kraus
operators of $\Phi^*$.""")]
M.drop(4, 5, 12, 13)
main += M.take("ucp_kraus_rep", "ucp_has_kraus_rep", "kraus_operators_dagger_of_unital", 189,
               "choi_theorem_3_ucp")
main += [heading("subsubsection", "An extreme channel has Choi rank at most $n$ (D22-6)")]
M.drop(191)
main += M.take(192, "extreme_CPTP_kraus_length_le", "extreme_CPTP_choi_rank_le", 195)
M.check_all_used()
write("Day23_Choi_Extreme_Points.thy", main)

# ---- Day 23, examples ----------------------------------------------------------------------

ex = E.take(0, 1, 2, 3, 4, "not_indep_of_dup", "not_indep_of_zero", "single_lin_indep",
            "single_mat_lin_indep", 11, "unitary_conjugation_extreme")
ex += E.take(*range(13, 26))
ex += E.take(*range(36, 47))
ex += [heading("subsubsection", "Example 4: the diagonal map")]
E.drop(26)
ex += E.take(*range(29, 36)) + E.take(47)
E.check_all_used()
write("Day23_Extremality_Examples.thy", ex)

# ---- receiving theories --------------------------------------------------------------------

def splice(text, inserts):
    """Insert blocks after the named blocks of a theory, leaving every other line as it is."""
    src = B.split(text)
    lines = text.split("\n")
    at = {}
    for after, new in inserts:
        k = [k for k, b in enumerate(src) if b["name"] == after]
        assert len(k) == 1, after
        at[src[k[0] + 1]["line"] - 1] = new
    out = []
    for n, l in enumerate(lines):
        if n in at:
            out += "\n\n".join(at[n]).split("\n") + [""]
        out.append(l)
    return "\n".join(out)

def splice_file(path, inserts):
    open(os.path.join(P, path), "w").write(splice(head(path), inserts))

splice_file("Essential_Functional_Analysis/Matrix_Lemmas.thy", [
    ("mat_mult_entry", [txt(r"""The same with the sum over $\{0..<q\}$; square matrices that agree on
every vector are equal; a non-zero matrix has a non-zero entry.""")] + to_ML_products),
    ("foldr_add_mat_cong", [txt(r"Sums over $[0..<N]$, and their entries.")] + to_ML_folds),
    ("sum_delta2", [txt(r"""Concatenating rows of equal length, and the reindexing
$\kappa=ik+j$.""")] + to_ML_sums)])
splice_file("Day02_Trace_Projections.thy", [
    ("mat_unit_mult_entry", [txt("Multiplying by a matrix unit selects a row or a column.")] + to_D2_units),
    ("hs_inner_prod_self_as_trace", [txt(r"""The trace pairing is non-degenerate: $\Tr(ME_{sr})=m_{rs}$, so if
$\Tr(M\rho)=\Tr(N\rho)$ for every $\rho\in M_n$ then $M=N$.""")] + to_D2_trace)])
splice_file("Day04_Hermitian_Matrices.thy", [("psd_MdagM", [txt(r"""Congruence preserves positivity: $P\ge0$ implies $M^*PM\ge0$, since
$\braket x{M^*PMx}=\braket{Mx}{P\,Mx}$.""")] + to_D4)])
splice_file("Day17_Quantum_Noise.thy", [("kraus_map_dim_carrier", [txt(r"""At the identity a Kraus map gives $\sum_iW_iW_i^*$; so it is unital iff
$\sum_iW_iW_i^*=I_d$.""")] + to_D17)])
splice_file("Day21_Unitary_Freedom.thy", [("lin_indep_complex_mat", [txt(r"""Linear independence passes to the adjoints: $\sum_kc_kW_k^*=0$ gives
$\sum_k\bar c_kW_k=0$.""")] + to_D21)])

# ---- imports (tools/deps/imports.py with plans/day23_moves.json) ---------------------------

s = head("Day25_Arveson_Correspondence.thy")
s = sub(s, "imports Day23_Choi_Extreme_Points Day24_Operator_Systems", "imports Day24_Operator_Systems")
open(os.path.join(P, "Day25_Arveson_Correspondence.thy"), "w").write(s)
s = head("Day26_Arveson_Extension.thy")
s = sub(s, "    Essential_Functional_Analysis.Lmat_Euclidean\n    Day25_Arveson_Correspondence\n",
        "    Essential_Functional_Analysis.Lmat_Euclidean\n    Day22_Minimal_Kraus\n    Day25_Arveson_Correspondence\n")
open(os.path.join(P, "Day26_Arveson_Extension.thy"), "w").write(s)
print("written")

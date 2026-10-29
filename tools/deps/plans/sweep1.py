"""Dead-code sweep (2026-10-27, audit tick 1): remove lemmas no proof or text uses, prove the
bit-flip channel CPTP through its Kraus operators, replace an smt proof in Day 2.
Reads the files at git HEAD and writes the working tree; rerun from a clean HEAD only."""
import os, re, subprocess, sys
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))
import blocks as B

P = os.path.abspath(os.path.join(os.path.dirname(__file__), "../../.."))

def head(path):
    return subprocess.run(["git", "-C", P, "show", "HEAD:" + path], capture_output=True,
                          text=True, check=True).stdout

def body(b): return "\n".join(b["lines"]).rstrip("\n")
def txt(s): return "text \\<open>" + s.strip() + "\\<close>"

def edit(path, remove=(), remove_with_text=(), insert_after=(), replace=()):
    """remove: block names; remove_with_text: also the text block before them;
    insert_after: [(name, [blocks])]; replace: [(old, new)] on the final text."""
    text = head(path)
    bl = B.split(text)
    lines = text.split("\n")
    drop, ins = set(), {}
    for n in list(remove) + list(remove_with_text):
        k = [i for i, b in enumerate(bl) if b["name"] == n]
        assert len(k) == 1, (path, n, k)
        drop.add(k[0])
        if n in remove_with_text:
            assert bl[k[0] - 1]["kind"] == "text", (path, n)
            drop.add(k[0] - 1)
    for n, new in insert_after:
        k = [i for i, b in enumerate(bl) if b["name"] == n]
        assert len(k) == 1, (path, n, k)
        ins[k[0]] = new
    out = []
    for i, b in enumerate(bl):
        if i not in drop:
            out += b["lines"]
        if i in ins:
            out += ("\n\n".join(ins[i]) + "\n").split("\n")
    s = "\n".join(out)
    s = re.sub(r"\n{3,}", "\n\n", s)
    for old, new in replace:
        assert s.count(old) == 1, (path, old[:60], s.count(old))
        s = s.replace(old, new)
    open(os.path.join(P, path), "w").write(s)

ML = "Matrix_Analysis_Prerequisites/"
edit(ML + "Matrix_Lemmas.thy", remove=["Re_cnj_mult_self", "foldr_upt_add_carrier", "foldr_upt_add_acc_index_dn",
                                       "foldr_smult_nth_index"])
edit(ML + "Unitary_Tensor_Algebra.thy", remove=["unitary_inv_l_dimrow", "unitary_inv_r_dimcol", "unitary_mult2"])
edit(ML + "Matrix_Typed.thy", remove=["cmult_lmat_one", "hs_norm_lmat_cmult_i"])
edit(ML + "Lmat_Euclidean.thy", remove=["unwrap_lm_plus_index", "unwrap_lm_minus_index", "unwrap_lm_zero_index",
                                        "lmat_axis_index", "LIMSEQ_unwrap_lm_index"])

# Day 2: the matrix-unit product entry from unit_mult_left_entry (was an smt proof before that lemma existed)
unit_entry = r'''lemma mat_unit_mult_entry:
  assumes r_lt: "r < m" and c_lt: "c < p" and j_lt: "j < n"
  shows "(E\<lbrakk>i,j ; m,n\<rbrakk> * E\<lbrakk>k,l ; n,p\<rbrakk>) $$ (r,c) = (if j = k \<and> r = i \<and> c = l then 1 else 0)"
  using unit_mult_left_entry[OF mat_unit_carrier r_lt c_lt j_lt, of i k l] j_lt c_lt by simp'''
edit("Day02_Trace_Projections.thy", remove=["mat_unit_mult_entry"],
     insert_after=[("unit_mult_right_entry", [unit_entry])])

# Day 3: scaling a Kraus operator
smult = [txt(r"Scaling an operator by $c$ scales $ABA^*$ and $A^*A$ by $|c|^2$."), r'''lemma smult_sandwich:
  fixes A :: "complex Matrix.mat"
  assumes A: "A \<in> carrier_mat d n" and B: "B \<in> carrier_mat n n"
  shows "(c \<cdot>\<^sub>m A) * B * ((c \<cdot>\<^sub>m A)\<^sup>\<dagger>) = (c * cnj c) \<cdot>\<^sub>m (A * B * (A\<^sup>\<dagger>))"
proof -
  have AB: "A * B \<in> carrier_mat d n" using A B by simp
  have Ad: "A\<^sup>\<dagger> \<in> carrier_mat n d" by (rule dagger_carrier[OF A])
  show ?thesis
    by (simp only: dagger_of_smult mult_smult_assoc_mat[OF A B] mult_smult_assoc_mat[OF AB smult_carrier_mat[OF Ad]]
                   mult_smult_distrib[OF AB Ad] smult_smult_mat)
qed''', r'''lemma smult_dagger_mult:
  fixes A :: "complex Matrix.mat"
  assumes A: "A \<in> carrier_mat d n"
  shows "((c \<cdot>\<^sub>m A)\<^sup>\<dagger>) * (c \<cdot>\<^sub>m A) = (cnj c * c) \<cdot>\<^sub>m ((A\<^sup>\<dagger>) * A)"
  by (simp only: dagger_of_smult mult_smult_assoc_mat[OF dagger_carrier[OF A] smult_carrier_mat[OF A]]
                 mult_smult_distrib[OF dagger_carrier[OF A] A] smult_smult_mat)''']
edit("Day03_Unitary_Matrices.thy", remove=["cpx_mat_cnj_four_block"], insert_after=[("dagger_of_smult", smult)])

edit("Day04_Hermitian_Matrices.thy", remove=["projection_zero"])
edit("Day05_Positivity_Tests.thy", remove=["chol_R_carrier", "direct_sum_vec_left"])
edit("Day07_Postulates.thy", remove=["quantum_state_dim"])
edit("Day08_Measurements.thy", remove=["outer_proj_cross_zero"])
edit("Day09_Bell_Measurement.thy", remove=["tensor_zero_right"])
edit("Day12_Quantum_Parallelism.thy", remove=["half_sqrt2_sq"])
edit("Day15_Partial_Traces.thy", remove=["operator_tensor_iso_map_entry", "operator_tensor_iso_inv_entry",
                                         "op_elem_carrier", "partial_trace_A_carrier"])

two = [r'''lemma kraus_map_dim_two:
  assumes V: "V \<in> carrier_mat d n" and W: "W \<in> carrier_mat d n" and \<rho>: "\<rho> \<in> carrier_mat n n"
  shows "kraus_map_dim d [V, W] \<rho> = V * \<rho> * (V\<^sup>\<dagger>) + W * \<rho> * (W\<^sup>\<dagger>)"
  using mult_carrier_mat[OF mult_carrier_mat[OF W \<rho>] dagger_carrier[OF W]] by simp''']
wtwo = [r'''lemma sum_wdag_w_two:
  assumes V: "V \<in> carrier_mat d n" and W: "W \<in> carrier_mat d n"
  shows "sum_wdag_w n [V, W] = (V\<^sup>\<dagger>) * V + (W\<^sup>\<dagger>) * W"
  using mult_carrier_mat[OF dagger_carrier[OF W] W] by (simp add: sum_wdag_w_Cons)''']
edit("Day17_Quantum_Noise.thy", remove=["amplification_one"],
     insert_after=[("kraus_map_dim_Cons", two), ("sum_wdag_w_Cons", wtwo)])
edit("Day19_Choi_Theorem.thy", remove=["choi_matrix_diff", "unit_blocks_carrier"])
edit("Day20_Positive_Functionals.thy", remove=["hs_inner_prod_left_zero"])
edit("Day21_Unitary_Freedom.thy", remove_with_text=["adjoint_image_in_dom"])
edit("Day23_Choi_Extreme_Points.thy", remove=["pinv_list_nonneg", "ucp_kraus_rep", "ucp_has_kraus_rep"],
     replace=[(r"""text \<open>A unital Kraus representation of $\Phi:M_n\to M_d$ is a list of $d\times n$ matrices with
\[ \Phi(X)=\sum_iV_iXV_i^*\quad(X\in M_n),\qquad \sum_iV_iV_i^*=I_d; \]
every linear UCP map has one with $nd$ operators.  The adjoints of its operators are Kraus
operators of $\Phi^*$.\<close>""",
               txt(r"The adjoints of the Kraus operators of a unital map are Kraus operators of its adjoint."))])
edit("Day24_Operator_Systems.thy", remove=["cp_on_mono"])
edit("Day28_Entanglement_Witnesses.thy", remove=["zero_not_in_Sprime", "bounded_convex_hull_Sprime"])
edit("Day29_Error_Correction.thy", remove=["length_repetition_encode", "repetition_encode_binary",
                                           "hamming_weight_zero_word", "xor_word_bits"])
edit("Day30_Bit_Flip_Code.thy", remove=["syndrome_proj_as_outer"])

# Day 31: the bit-flip channel is the Kraus map of sqrt(1-p) I and sqrt p X, hence CPTP and UCP
bf = [txt(r"""The error map is the Kraus map of $\sqrt{1-p}\,I$ and $\sqrt p\,X$, so it is completely positive
and trace preserving (Day 22); as $XX^*=I$ it is unital too."""), r'''definition bit_flip_kraus :: "real \<Rightarrow> complex Matrix.mat list" where
  "bit_flip_kraus p = [complex_of_real (sqrt (1 - p)) \<cdot>\<^sub>m 1\<^sub>m 2, complex_of_real (sqrt p) \<cdot>\<^sub>m Pauli_X]"''',
r'''lemma bit_flip_channel_kraus:
  assumes p: "0 \<le> p" "p \<le> 1" and \<rho>: "\<rho> \<in> carrier_mat 2 2"
  shows "bit_flip_channel p \<rho> = kraus_map_dim 2 (bit_flip_kraus p) \<rho>"
proof -
  have s: "complex_of_real (sqrt (1 - p)) * cnj (complex_of_real (sqrt (1 - p))) = complex_of_real (1 - p)"
    "complex_of_real (sqrt p) * cnj (complex_of_real (sqrt p)) = complex_of_real p"
    using p by (simp_all flip: of_real_mult)
  show ?thesis
    unfolding bit_flip_kraus_def bit_flip_channel_def
    by (simp only: kraus_map_dim_two[OF smult_carrier_mat[OF one_carrier_mat] smult_carrier_mat[OF Pauli_X_carrier] \<rho>]
                   smult_sandwich[OF one_carrier_mat \<rho>] smult_sandwich[OF Pauli_X_carrier \<rho>] s
                   dagger_of_id_is_id left_mult_one_mat[OF \<rho>] right_mult_one_mat[OF \<rho>])
qed''', r'''lemma bit_flip_kraus_operators:
  assumes p: "0 \<le> p" "p \<le> 1"
  shows "kraus_operators 2 2 (bit_flip_kraus p)"
proof -
  have s: "cnj (complex_of_real (sqrt (1 - p))) * complex_of_real (sqrt (1 - p)) = complex_of_real (1 - p)"
    "cnj (complex_of_real (sqrt p)) * complex_of_real (sqrt p) = complex_of_real p"
    using p by (simp_all flip: of_real_mult)
  have "sum_wdag_w 2 (bit_flip_kraus p) = complex_of_real (1 - p) \<cdot>\<^sub>m 1\<^sub>m 2 + complex_of_real p \<cdot>\<^sub>m 1\<^sub>m 2"
    unfolding bit_flip_kraus_def
    by (simp only: sum_wdag_w_two[OF smult_carrier_mat[OF one_carrier_mat] smult_carrier_mat[OF Pauli_X_carrier]]
                   smult_dagger_mult[OF one_carrier_mat] smult_dagger_mult[OF Pauli_X_carrier] s
                   dagger_of_id_is_id Pauli_X_dagger Pauli_X_squared right_mult_one_mat[OF one_carrier_mat])
  also have "\<dots> = 1\<^sub>m 2" by (rule eq_matI) (auto simp: algebra_simps)
  finally show ?thesis
    unfolding kraus_operators_altdef bit_flip_kraus_def[symmetric] by (simp add: bit_flip_kraus_def)
qed''', r'''lemma bit_flip_channel_CPTP:
  assumes p: "0 \<le> p" "p \<le> 1"
  shows "bit_flip_channel p \<in> CPTP 2 2"
  using kraus_is_cptp[OF bit_flip_kraus_operators[OF p]] bit_flip_channel_kraus[OF p]
        completely_positive_cong[of 2 "bit_flip_channel p" "kraus_map_dim 2 (bit_flip_kraus p)" 2]
        trace_preserving_cong[of 2 "bit_flip_channel p" "kraus_map_dim 2 (bit_flip_kraus p)"]
  by (simp add: CPTP_def)''', r'''lemma bit_flip_channel_UCP:
  assumes p: "0 \<le> p" "p \<le> 1"
  shows "bit_flip_channel p \<in> UCP 2 2"
proof -
  have XX: "Pauli_X * 1\<^sub>m 2 * (Pauli_X\<^sup>\<dagger>) = 1\<^sub>m 2"
    by (simp add: Pauli_X_dagger carrier_matD[OF Pauli_X_carrier] Pauli_X_squared)
  have "bit_flip_channel p (1\<^sub>m 2) = 1\<^sub>m 2"
    unfolding bit_flip_channel_def XX by (intro eq_matI) (auto simp: algebra_simps)
  thus ?thesis
    using kraus_is_cptp[OF bit_flip_kraus_operators[OF p]] bit_flip_channel_kraus[OF p]
          completely_positive_cong[of 2 "bit_flip_channel p" "kraus_map_dim 2 (bit_flip_kraus p)" 2]
    by (simp add: CPTP_def UCP_def unital_map_def)
qed''']
edit("Day31_Bit_Flip_Channel.thy",
     remove=["bit_flip_channel_carrier", "bit_flip_channel_trace_preserving", "bit_flip_channel_psd"],
     insert_after=[("bit_flip_channel", bf)])
edit("Day32_Phase_Flip_Code.thy", remove=["ket_minus_carrier", "ket_minus_index_0", "ket_minus_index_1",
     "phase_code_zero_dim", "phase_code_one_dim", "phase_code_zero_carrier", "phase_code_one_carrier",
     "orthogonal_projections_symm", "orthogonal_projections_sum", "orthogonal_projections_decomp_id"])
edit("Quantum_Channels.thy", remove=["bit_flip_channel_UCP", "bit_flip_channel_CPTP"])
print("swept")

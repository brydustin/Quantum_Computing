theory HHL_Termination
  imports HHL_Gates
begin

section \<open>Termination of the repeat-until-success loop\<close>

text \<open>The HHL repeat-until-success program was verified for partial correctness only.  Its loop
body re-initialises the registers, so every round is an independent trial with success probability
$p = C^2\norm{A^{-1}b}^2$.  We prove: the loop terminates with probability one (total correctness,
\<open>hhl_rus_prog_total\<close>); it exits after exactly $m$ failed rounds with probability $(1-p)^m p$, in the
target state (\<open>hhl_rus_prog_rounds\<close>); and the expected number of rounds is $1/p$
(\<open>hhl_rus_expected_rounds\<close>).  QHLProver has no total-correctness rule for loops, so the bound is
derived from the semantics: a loop whose body resets the state (\<open>while_reset_total\<close>).\<close>

lemma proj_basis_outer: "proj_basis K 0 = outer_prod (unit_vec K 0) (unit_vec K 0)"
proof (rule eq_matI)
  fix i j assume "i < dim_row (outer_prod (unit_vec K 0) (unit_vec K 0))" "j < dim_col (outer_prod (unit_vec K 0) (unit_vec K 0))"
  hence ij: "i < K" "j < K" by (simp_all add: carrier_matD[OF outer_prod_dim[OF unit_vec_carrier unit_vec_carrier]])
  show "proj_basis K 0 $$ (i, j) = outer_prod (unit_vec K 0) (unit_vec K 0) $$ (i, j)"
    unfolding index_outer_prod[OF unit_vec_carrier unit_vec_carrier ij] using ij by (simp add: proj_set_index)
qed (simp_all add: proj_set_index carrier_matD[OF outer_prod_dim[OF unit_vec_carrier unit_vec_carrier]])

lemma swap0_proj:
  assumes k: "k < K"
  shows "swap0 K k * proj_basis K k * adjoint (swap0 K k) = proj_basis K 0"
  unfolding swap0_adjoint swap0_conj[OF proj_set_carrier k]
  by (rule eq_matI) (use k in \<open>auto simp: proj_set_index\<close>)

context state_sig
begin

text \<open>Initialisation sends every state to $\mathrm{tr}(\rho)\,\ket0\bra0$.\<close>

lemma denote_init:
  assumes d0: "0 < d" and r: "\<rho> \<in> carrier_mat d d"
  shows "denote (init_com d) \<rho> = trace \<rho> \<cdot>\<^sub>m proj_basis d 0"
proof -
  have wc: "well_com (init_com d)" by (rule well_com_init[OF d0])
  have "denote (init_com d) \<rho> = matrix_sum d (\<lambda>k. denote (map (\<lambda>k. Utrans (swap0 d k)) [0..<d] ! k)
                                      (proj_basis d k * \<rho> * adjoint (proj_basis d k))) d"
    unfolding init_com_def by (rule denote_measure_expand[OF le_refl wc[unfolded init_com_def]])
  also have "\<dots> = matrix_sum d (\<lambda>k. \<rho> $$ (k, k) \<cdot>\<^sub>m proj_basis d 0) d"
  proof (rule matrix_sum_cong)
    fix k assume k: "k < d"
    have "denote (map (\<lambda>k. Utrans (swap0 d k)) [0..<d] ! k) (proj_basis d k * \<rho> * adjoint (proj_basis d k))
          = swap0 d k * (\<rho> $$ (k, k) \<cdot>\<^sub>m proj_basis d k) * adjoint (swap0 d k)"
      using k by (simp add: proj_set_adjoint proj_basis_sandwich[OF r k])
    also have "\<dots> = \<rho> $$ (k, k) \<cdot>\<^sub>m (swap0 d k * proj_basis d k * adjoint (swap0 d k))"
      by (simp only: mult_smult_distrib[OF swaprows_mat_carrier proj_set_carrier]
            mult_smult_assoc_mat[OF mult_carrier_mat[OF swaprows_mat_carrier proj_set_carrier] adjoint_dim[OF swaprows_mat_carrier]])
    finally show "denote (map (\<lambda>k. Utrans (swap0 d k)) [0..<d] ! k) (proj_basis d k * \<rho> * adjoint (proj_basis d k))
                  = \<rho> $$ (k, k) \<cdot>\<^sub>m proj_basis d 0" by (simp add: swap0_proj[OF k])
  qed
  also have "\<dots> = trace \<rho> \<cdot>\<^sub>m proj_basis d 0"
    unfolding matrix_sum_scalar[OF proj_set_carrier] trace_def using r by (simp add: atLeast0LessThan)
  finally show ?thesis .
qed

lemma denote_utrans_seq_pure:
  assumes Us: "\<And>U. U \<in> set Us \<Longrightarrow> U \<in> carrier_mat d d \<and> Complex_Matrix.unitary U" and \<phi>: "\<phi> \<in> carrier_vec d"
  shows "denote (utrans_seq Us) (c \<cdot>\<^sub>m outer_prod \<phi> \<phi>)
         = c \<cdot>\<^sub>m outer_prod (circuit_mat d Us *\<^sub>v \<phi>) (circuit_mat d Us *\<^sub>v \<phi>)"
  using assms
proof (induction Us arbitrary: \<phi>)
  case Nil thus ?case by simp
next
  case (Cons U Us)
  have U: "U \<in> carrier_mat d d" "Complex_Matrix.unitary U" using Cons.prems(1) by auto
  have R: "circuit_mat d Us \<in> carrier_mat d d" by (rule circuit_mat_carrier) (use Cons.prems(1) in auto)
  have "denote (utrans_seq (U # Us)) (c \<cdot>\<^sub>m outer_prod \<phi> \<phi>) = denote (utrans_seq Us) (U * (c \<cdot>\<^sub>m outer_prod \<phi> \<phi>) * adjoint U)"
    by simp
  also have "U * (c \<cdot>\<^sub>m outer_prod \<phi> \<phi>) * adjoint U = c \<cdot>\<^sub>m outer_prod (U *\<^sub>v \<phi>) (U *\<^sub>v \<phi>)"
    by (simp only: mult_smult_distrib[OF U(1) outer_prod_dim[OF Cons.prems(2) Cons.prems(2)]]
          mult_smult_assoc_mat[OF mult_carrier_mat[OF U(1) outer_prod_dim[OF Cons.prems(2) Cons.prems(2)]] adjoint_dim[OF U(1)]]
          outer_prod_left_right_mat[OF Cons.prems(2) Cons.prems(2) U(1) adjoint_dim[OF U(1)]] adjoint_adjoint)
  also have "denote (utrans_seq Us) \<dots> = c \<cdot>\<^sub>m outer_prod (circuit_mat d Us *\<^sub>v (U *\<^sub>v \<phi>)) (circuit_mat d Us *\<^sub>v (U *\<^sub>v \<phi>))"
    by (rule Cons.IH) (use Cons.prems mult_mat_vec_carrier[OF U(1) Cons.prems(2)] in auto)
  also have "circuit_mat d Us *\<^sub>v (U *\<^sub>v \<phi>) = circuit_mat d (U # Us) *\<^sub>v \<phi>"
    using assoc_mult_mat_vec[OF R U(1) Cons.prems(2)] by simp
  finally show ?case .
qed

text \<open>Initialisation followed by a circuit resets any state to the circuit's output.\<close>

lemma denote_init_circuit:
  assumes d0: "0 < d" and Us: "\<And>U. U \<in> set Us \<Longrightarrow> U \<in> carrier_mat d d \<and> Complex_Matrix.unitary U" and r: "\<rho> \<in> carrier_mat d d"
  shows "denote (init_com d ;; utrans_seq Us) \<rho>
         = trace \<rho> \<cdot>\<^sub>m outer_prod (circuit_mat d Us *\<^sub>v unit_vec d 0) (circuit_mat d Us *\<^sub>v unit_vec d 0)"
  by (simp only: denote.simps denote_init[OF d0 r] proj_basis_outer denote_utrans_seq_pure[OF Us unit_vec_carrier])

text \<open>A loop whose body resets the state to $\sigma$: after $m$ failed rounds the state inside the
loop is $(1-p)^m\sigma$, where $1-p$ is the probability of staying in the loop.\<close>

lemma while_reset_iter:
  assumes M: "measurement d 2 M" and Sc: "well_com Sc"
    and \<sigma>: "\<sigma> \<in> carrier_mat d d" "partial_density_operator \<sigma>" "trace \<sigma> = 1"
    and reset: "\<And>\<rho>. \<rho> \<in> carrier_mat d d \<Longrightarrow> partial_density_operator \<rho> \<Longrightarrow> denote Sc \<rho> = trace \<rho> \<cdot>\<^sub>m \<sigma>"
    and p: "trace (M 1 * \<sigma> * adjoint (M 1)) = complex_of_real (1 - p)" "0 \<le> p" "p \<le> 1"
    and c: "0 \<le> c" "c \<le> 1"
  shows "denote_while_n_iter (M 0) (M 1) (denote Sc) m (complex_of_real c \<cdot>\<^sub>m \<sigma>) = complex_of_real (c * (1 - p) ^ m) \<cdot>\<^sub>m \<sigma>"
  using c
proof (induction m arbitrary: c)
  case 0 thus ?case by simp
next
  case (Suc m)
  have M1: "M 1 \<in> carrier_mat d d" by (rule measurement_dim[OF M]) simp
  have pdo: "partial_density_operator (complex_of_real c \<cdot>\<^sub>m \<sigma>)"
    using \<sigma> Suc.prems positive_smult[OF \<sigma>(1)] unfolding partial_density_operator_def by (simp add: trace_smult less_eq_complex_def)
  have R: "M 1 * (complex_of_real c \<cdot>\<^sub>m \<sigma>) * adjoint (M 1) \<in> carrier_mat d d"
    using M1 \<sigma>(1) by (auto intro: mult_carrier_mat adjoint_dim)
  have Rp: "partial_density_operator (M 1 * (complex_of_real c \<cdot>\<^sub>m \<sigma>) * adjoint (M 1))"
    by (rule pdo_close_under_measurement[OF M1 _ pdo measurement_le_one_mat[OF M]]) (use \<sigma>(1) in auto)
  have tr: "trace (M 1 * (complex_of_real c \<cdot>\<^sub>m \<sigma>) * adjoint (M 1)) = complex_of_real (c * (1 - p))"
    unfolding mult_smult_distrib[OF M1 \<sigma>(1)] mult_smult_assoc_mat[OF mult_carrier_mat[OF M1 \<sigma>(1)] adjoint_dim[OF M1]]
      trace_smult[OF mult_carrier_mat[OF mult_carrier_mat[OF M1 \<sigma>(1)] adjoint_dim[OF M1]]] p(1) by simp
  have "denote_while_n_iter (M 0) (M 1) (denote Sc) (Suc m) (complex_of_real c \<cdot>\<^sub>m \<sigma>)
        = denote_while_n_iter (M 0) (M 1) (denote Sc) m (complex_of_real (c * (1 - p)) \<cdot>\<^sub>m \<sigma>)"
    by (simp only: denote_while_n_iter.simps reset[OF R Rp] tr)
  also have "\<dots> = complex_of_real (c * (1 - p) * (1 - p) ^ m) \<cdot>\<^sub>m \<sigma>"
    by (rule Suc.IH) (use Suc.prems p(2,3) mult_le_one[of c "1 - p"] in auto)
  also have "\<dots> = complex_of_real (c * (1 - p) ^ Suc m) \<cdot>\<^sub>m \<sigma>" by (simp only: power_Suc Groups.mult.assoc)
  finally show ?case .
qed

lemma while_reset_exit:
  assumes M: "measurement d 2 M" and Sc: "well_com Sc"
    and \<sigma>: "\<sigma> \<in> carrier_mat d d" "partial_density_operator \<sigma>" "trace \<sigma> = 1"
    and reset: "\<And>\<rho>. \<rho> \<in> carrier_mat d d \<Longrightarrow> partial_density_operator \<rho> \<Longrightarrow> denote Sc \<rho> = trace \<rho> \<cdot>\<^sub>m \<sigma>"
    and p: "trace (M 1 * \<sigma> * adjoint (M 1)) = complex_of_real (1 - p)" "0 \<le> p" "p \<le> 1"
    and c: "0 \<le> c" "c \<le> 1"
  shows "denote_while_n (M 0) (M 1) (denote Sc) m (complex_of_real c \<cdot>\<^sub>m \<sigma>)
         = complex_of_real (c * (1 - p) ^ m) \<cdot>\<^sub>m (M 0 * \<sigma> * adjoint (M 0))"
proof -
  have M0: "M 0 \<in> carrier_mat d d" by (rule measurement_dim[OF M]) simp
  have it: "denote_while_n_iter (M 0) (M 1) (denote Sc) m (complex_of_real c \<cdot>\<^sub>m \<sigma>) = complex_of_real (c * (1 - p) ^ m) \<cdot>\<^sub>m \<sigma>"
    by (rule while_reset_iter[OF assms])
  have "denote_while_n (M 0) (M 1) (denote Sc) m (complex_of_real c \<cdot>\<^sub>m \<sigma>) = M 0 * (complex_of_real (c * (1 - p) ^ m) \<cdot>\<^sub>m \<sigma>) * adjoint (M 0)"
    unfolding denote_while_n.simps it ..
  also have "\<dots> = complex_of_real (c * (1 - p) ^ m) \<cdot>\<^sub>m (M 0 * \<sigma> * adjoint (M 0))"
    by (simp only: mult_smult_distrib[OF M0 \<sigma>(1)] mult_smult_assoc_mat[OF mult_carrier_mat[OF M0 \<sigma>(1)] adjoint_dim[OF M0]])
  finally show ?thesis .
qed

text \<open>The value of a predicate $Q$ on the loop's output, bounded below by $m$ rounds.\<close>

lemma while_reset_bound:
  assumes M: "measurement d 2 M" and Sc: "well_com Sc"
    and \<sigma>: "\<sigma> \<in> carrier_mat d d" "partial_density_operator \<sigma>" "trace \<sigma> = 1"
    and reset: "\<And>\<rho>. \<rho> \<in> carrier_mat d d \<Longrightarrow> partial_density_operator \<rho> \<Longrightarrow> denote Sc \<rho> = trace \<rho> \<cdot>\<^sub>m \<sigma>"
    and p: "trace (M 1 * \<sigma> * adjoint (M 1)) = complex_of_real (1 - p)" "0 \<le> p" "p \<le> 1"
    and Q: "is_quantum_predicate Q" and v: "trace (Q * (M 0 * \<sigma> * adjoint (M 0))) = complex_of_real v"
    and c: "0 \<le> c" "c \<le> 1"
  shows "complex_of_real (c * v * (\<Sum>i<m. (1 - p) ^ i)) \<le> trace (Q * denote (While M Sc) (complex_of_real c \<cdot>\<^sub>m \<sigma>))"
  using c
proof (induction m arbitrary: c)
  case 0
  have wc: "well_com (While M Sc)" using M Sc by simp
  have Qc: "Q \<in> carrier_mat d d" and Qp: "positive Q" using Q unfolding is_quantum_predicate_def by auto
  have pdo: "partial_density_operator (complex_of_real c \<cdot>\<^sub>m \<sigma>)"
    using \<sigma> 0 positive_smult[OF \<sigma>(1)] unfolding partial_density_operator_def by (simp add: trace_smult less_eq_complex_def)
  have X: "denote (While M Sc) (complex_of_real c \<cdot>\<^sub>m \<sigma>) \<in> density_states"
    by (rule denote_density_states[OF _ wc]) (use \<sigma>(1) pdo in \<open>simp add: density_states_def\<close>)
  hence Xc: "denote (While M Sc) (complex_of_real c \<cdot>\<^sub>m \<sigma>) \<in> carrier_mat d d"
    and Xp: "partial_density_operator (denote (While M Sc) (complex_of_real c \<cdot>\<^sub>m \<sigma>))" by (auto simp: density_states_def)
  have "trace (0\<^sub>m d d * denote (While M Sc) (complex_of_real c \<cdot>\<^sub>m \<sigma>)) \<le> trace (Q * denote (While M Sc) (complex_of_real c \<cdot>\<^sub>m \<sigma>))"
    by (rule lowner_le_traceD[OF zero_carrier_mat Qc Xc zero_lowner_le_positiveI[OF Qc Qp] Xp])
  thus ?case using left_mult_zero_mat[OF Xc] by simp
next
  case (Suc m)
  have wc: "well_com (While M Sc)" using M Sc by simp
  have M0: "M 0 \<in> carrier_mat d d" and M1: "M 1 \<in> carrier_mat d d" by (rule measurement_dim[OF M], simp)+
  have Qc: "Q \<in> carrier_mat d d" using Q unfolding is_quantum_predicate_def by auto
  have pdo: "partial_density_operator (complex_of_real c \<cdot>\<^sub>m \<sigma>)"
    using \<sigma> Suc.prems positive_smult[OF \<sigma>(1)] unfolding partial_density_operator_def by (simp add: trace_smult less_eq_complex_def)
  have R: "M 1 * (complex_of_real c \<cdot>\<^sub>m \<sigma>) * adjoint (M 1) \<in> carrier_mat d d"
    using M1 \<sigma>(1) by (auto intro: mult_carrier_mat adjoint_dim)
  have Rp: "partial_density_operator (M 1 * (complex_of_real c \<cdot>\<^sub>m \<sigma>) * adjoint (M 1))"
    by (rule pdo_close_under_measurement[OF M1 _ pdo measurement_le_one_mat[OF M]]) (use \<sigma>(1) in auto)
  have tr: "trace (M 1 * (complex_of_real c \<cdot>\<^sub>m \<sigma>) * adjoint (M 1)) = complex_of_real (c * (1 - p))"
    unfolding mult_smult_distrib[OF M1 \<sigma>(1)] mult_smult_assoc_mat[OF mult_carrier_mat[OF M1 \<sigma>(1)] adjoint_dim[OF M1]]
      trace_smult[OF mult_carrier_mat[OF mult_carrier_mat[OF M1 \<sigma>(1)] adjoint_dim[OF M1]]] p(1) by simp
  let ?E = "M 0 * \<sigma> * adjoint (M 0)" and ?B = "denote (While M Sc) (complex_of_real (c * (1 - p)) \<cdot>\<^sub>m \<sigma>)"
  have Ec: "?E \<in> carrier_mat d d" using M0 \<sigma>(1) by (auto intro: mult_carrier_mat adjoint_dim)
  have Bc: "?B \<in> carrier_mat d d"
  proof -
    have "partial_density_operator (complex_of_real (c * (1 - p)) \<cdot>\<^sub>m \<sigma>)"
      using \<sigma> Suc.prems p(2,3) positive_smult[OF \<sigma>(1)] mult_le_one[of c "1 - p"] unfolding partial_density_operator_def by (simp add: trace_smult less_eq_complex_def)
    thus ?thesis using denote_density_states[OF _ wc, of "complex_of_real (c * (1 - p)) \<cdot>\<^sub>m \<sigma>"] \<sigma>(1)
      by (auto simp: density_states_def)
  qed
  have split: "denote (While M Sc) (complex_of_real c \<cdot>\<^sub>m \<sigma>) = complex_of_real c \<cdot>\<^sub>m ?E + ?B"
    using denote_while_split[OF wc, of "complex_of_real c \<cdot>\<^sub>m \<sigma>"] \<sigma>(1) pdo
    unfolding density_states_def reset[OF R Rp] tr
      mult_smult_distrib[OF M0 \<sigma>(1)] mult_smult_assoc_mat[OF mult_carrier_mat[OF M0 \<sigma>(1)] adjoint_dim[OF M0]] by simp
  have eq: "trace (Q * denote (While M Sc) (complex_of_real c \<cdot>\<^sub>m \<sigma>)) = complex_of_real (c * v) + trace (Q * ?B)"
    unfolding split mult_add_distrib_mat[OF Qc smult_carrier_mat[OF Ec] Bc] mult_smult_distrib[OF Qc Ec]
      trace_add_linear[OF smult_carrier_mat[OF mult_carrier_mat[OF Qc Ec]] mult_carrier_mat[OF Qc Bc]]
      trace_smult[OF mult_carrier_mat[OF Qc Ec]] v by simp
  have IH: "complex_of_real (c * (1 - p) * v * (\<Sum>i<m. (1 - p) ^ i)) \<le> trace (Q * ?B)"
    by (rule Suc.IH) (use Suc.prems p(2,3) mult_le_one[of c "1 - p"] in auto)
  have s: "(\<Sum>i<Suc m. (1 - p) ^ i) = 1 + (1 - p) * (\<Sum>i<m. (1 - p) ^ i)"
    unfolding sum.lessThan_Suc_shift by (simp add: sum_distrib_left del: sum.lessThan_Suc)
  have "c * v * (\<Sum>i<Suc m. (1 - p) ^ i) = c * v + c * (1 - p) * v * (\<Sum>i<m. (1 - p) ^ i)"
    unfolding s by (simp add: algebra_simps)
  thus ?case unfolding eq using IH by (simp add: add_left_mono)
qed

text \<open>Letting $m\to\infty$: the loop's output carries at least $c\,v/p$ of the predicate $Q$.\<close>

lemma while_reset_total:
  assumes M: "measurement d 2 M" and Sc: "well_com Sc"
    and \<sigma>: "\<sigma> \<in> carrier_mat d d" "partial_density_operator \<sigma>" "trace \<sigma> = 1"
    and reset: "\<And>\<rho>. \<rho> \<in> carrier_mat d d \<Longrightarrow> partial_density_operator \<rho> \<Longrightarrow> denote Sc \<rho> = trace \<rho> \<cdot>\<^sub>m \<sigma>"
    and p: "trace (M 1 * \<sigma> * adjoint (M 1)) = complex_of_real (1 - p)" "0 < p" "p \<le> 1"
    and Q: "is_quantum_predicate Q" and v: "trace (Q * (M 0 * \<sigma> * adjoint (M 0))) = complex_of_real v"
    and c: "0 \<le> c" "c \<le> 1"
  shows "complex_of_real (c * v / p) \<le> trace (Q * denote (While M Sc) (complex_of_real c \<cdot>\<^sub>m \<sigma>))"
proof -
  let ?t = "trace (Q * denote (While M Sc) (complex_of_real c \<cdot>\<^sub>m \<sigma>))"
  have b: "complex_of_real (c * v * (\<Sum>i<m. (1 - p) ^ i)) \<le> ?t" for m
    by (rule while_reset_bound[OF M Sc \<sigma> reset p(1) less_imp_le[OF p(2)] p(3) Q v c])
  have le: "c * v * (\<Sum>i<m. (1 - p) ^ i) \<le> Re ?t" and im: "Im ?t = 0" for m
    using b[of m] unfolding less_eq_complex_def by simp_all
  have "(\<lambda>i. (1 - p) ^ i) sums (1 / (1 - (1 - p)))" by (rule geometric_sums) (use p in simp)
  hence "(\<lambda>m. c * v * (\<Sum>i<m. (1 - p) ^ i)) \<longlonglongrightarrow> c * v * (1 / p)"
    unfolding sums_def by (intro tendsto_mult_left) simp
  hence "c * v * (1 / p) \<le> Re ?t" by (rule LIMSEQ_le_const2) (use le in blast)
  hence "c * v / p \<le> Re ?t" by simp
  thus ?thesis unfolding less_eq_complex_def using im by simp
qed

end

text \<open>The expected number of rounds of such a loop is $\sum_{m\ge0}(1-p)^m=1/p$, equivalently
$\sum_{m\ge0}(m+1)\,p\,(1-p)^m = 1/p$.\<close>

lemma rounds_expectation:
  assumes p: "0 < p" "p \<le> 1"
  shows "(\<lambda>m. (1 - p) ^ m) sums (1 / p)" and "(\<lambda>m. real (Suc m) * (p * (1 - p) ^ m)) sums (1 / p)"
proof -
  show "(\<lambda>m. (1 - p) ^ m) sums (1 / p)" using geometric_sums[of "1 - p"] p by simp
  have "(\<lambda>m. p * (real (Suc m) * (1 - p) ^ m)) sums (p * (1 / (1 - (1 - p))\<^sup>2))"
    by (rule sums_mult[OF geometric_deriv_sums]) (use p in simp)
  thus "(\<lambda>m. real (Suc m) * (p * (1 - p) ^ m)) sums (1 / p)"
    using p by (simp add: power2_eq_square field_simps)
qed

subsection \<open>The HHL repeat-until-success loop terminates with probability one\<close>

context
  fixes A Ub :: "complex Matrix.mat" and b :: "complex Matrix.vec" and n k :: nat and t0 C :: real
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and n0: "0 < n" and k: "1 \<le> k" and t0: "0 < t0"
    and spec: "\<And>l. l \<in> herm_spectrum A \<Longrightarrow> \<exists>j. 0 < j \<and> j < 2 ^ k \<and> l = reg_eig t0 (2 ^ k) j"
    and Ub: "Ub \<in> carrier_mat n n" "Quantum.unitary Ub" "Ub *\<^sub>v unit_vec n 0 = b"
    and Cb: "\<And>j. j < 2 ^ k \<Longrightarrow> \<bar>C / reg_eig t0 (2 ^ k) j\<bar> \<le> 1"
begin

text \<open>The state after one run of the circuit, its two measurement branches and the success
probability $p = C^2\norm{A^{-1}b}^2$.\<close>

lemma rus_state:
  defines "Dm \<equiv> 2 ^ k * (n * 2)" and "\<psi> \<equiv> tensor_vec (unit_vec (2 ^ k) 0) (hhl_out A C b)"
    and "p \<equiv> C\<^sup>2 * \<parallel>herm_inv A *\<^sub>v b\<parallel>\<^sup>2"
    and "w1 \<equiv> tensor_vec (unit_vec (2 ^ k) 0) (tensor_vec ((complex_of_real C \<cdot>\<^sub>m herm_inv A) *\<^sub>v b) (unit_vec 2 1))"
  shows "\<psi> \<in> carrier_vec Dm" "outer_prod \<psi> \<psi> \<in> carrier_mat Dm Dm"
    and "partial_density_operator (outer_prod \<psi> \<psi>)" "trace (outer_prod \<psi> \<psi>) = 1"
    and "trace (anc_proj Dm 0 * outer_prod \<psi> \<psi> * adjoint (anc_proj Dm 0)) = complex_of_real (1 - p)"
    and "anc_proj Dm 1 * outer_prod \<psi> \<psi> * adjoint (anc_proj Dm 1) = outer_prod w1 w1"
    and "trace (outer_prod (hhl_target A k b) (hhl_target A k b) * outer_prod w1 w1) = complex_of_real p"
    and "0 \<le> p" "p \<le> 1"
proof -
  interpret state_sig "[2 ^ k, n, 2]" .
  have dd: "d = Dm" by (simp add: d_def Dm_def)
  let ?w0 = "tensor_vec (unit_vec (2 ^ k) 0) (tensor_vec (mat_fun (\<lambda>x. complex_of_real (sqrt (1 - (C / x)\<^sup>2))) A *\<^sub>v b) (unit_vec 2 0))"
  let ?t = "hhl_target A k b"
  note dims = prog_branch(3,4)[OF A n0 k t0 spec Ub Cb]
  have cc: "circuit_mat Dm (hhl_gates A Ub t0 k C) \<in> carrier_mat Dm Dm"
    unfolding Dm_def by (rule circuit_mat_carrier) (use prog_gates[OF A n0 k t0 spec Ub Cb] in auto)
  have dd': "d = 2 ^ k * (n * 2)" by (simp add: d_def)
  have cu: "Complex_Matrix.unitary (circuit_mat d (hhl_gates A Ub t0 k C))"
    by (rule circuit_mat_unitary) (use prog_gates[OF A n0 k t0 spec Ub Cb] dd' in auto)
  have \<psi>e: "\<psi> = circuit_mat Dm (hhl_gates A Ub t0 k C) *\<^sub>v unit_vec Dm 0"
    unfolding \<psi>_def Dm_def by (rule prog_out[OF A n0 k t0 spec Ub Cb, symmetric])
  show \<psi>c: "\<psi> \<in> carrier_vec Dm" unfolding \<psi>e by (rule mult_mat_vec_carrier[OF cc unit_vec_carrier])
  have e1: "inner_prod (unit_vec Dm 0 :: complex Matrix.vec) (unit_vec Dm 0) = 1"
  proof -
    have "inner_prod (unit_vec Dm 0) (unit_vec Dm 0) = \<langle>unit_vec Dm 0|unit_vec Dm 0\<rangle>" by (rule inner_bridge) simp
    also have "\<dots> = complex_of_real (\<parallel>unit_vec Dm 0\<parallel>\<^sup>2)" by (rule cpx_vec_length_inner_prod[symmetric])
    also have "\<dots> = 1" using n0 by (simp add: Dm_def)
    finally show ?thesis .
  qed
  have \<psi>1: "inner_prod \<psi> \<psi> = 1"
    unfolding \<psi>e using unitary_inner_keep[OF cc[unfolded dd[symmetric]] cu, of "unit_vec Dm 0"] dd e1 by simp
  show \<sigma>c: "outer_prod \<psi> \<psi> \<in> carrier_mat Dm Dm" by (rule outer_prod_dim[OF \<psi>c \<psi>c])
  show tr1: "trace (outer_prod \<psi> \<psi>) = 1" unfolding trace_outer_prod[OF \<psi>c \<psi>c] \<psi>1 ..
  show "partial_density_operator (outer_prod \<psi> \<psi>)"
    unfolding partial_density_operator_def tr1 using positive_same_outer_prod[OF \<psi>c] by simp
  have br: "anc_proj Dm j * outer_prod \<psi> \<psi> * adjoint (anc_proj Dm j) = outer_prod (anc_proj Dm j *\<^sub>v \<psi>) (anc_proj Dm j *\<^sub>v \<psi>)" for j
    unfolding outer_prod_left_right_mat[OF \<psi>c \<psi>c proj_set_carrier adjoint_dim[OF proj_set_carrier]] adjoint_adjoint ..
  have b0: "anc_proj Dm 0 *\<^sub>v \<psi> = ?w0" unfolding \<psi>_def Dm_def by (rule prog_branch(1)[OF A n0 k t0 spec Ub Cb])
  have b1: "anc_proj Dm 1 *\<^sub>v \<psi> = w1" unfolding \<psi>_def w1_def Dm_def by (rule prog_branch(2)[OF A n0 k t0 spec Ub Cb])
  note dA = carrier_matD[OF mat_fun_carrier[OF A]]
  have w0c: "?w0 \<in> carrier_vec Dm" unfolding Dm_def by (rule carrier_vecI) (simp add: tensor_vec_dim dA)
  have w1c: "w1 \<in> carrier_vec Dm" unfolding Dm_def w1_def by (rule carrier_vecI) (simp add: tensor_vec_dim dA herm_inv_def)
  have sum1: "\<parallel>mat_fun (\<lambda>x. complex_of_real (sqrt (1 - (C / x)\<^sup>2))) A *\<^sub>v b\<parallel>\<^sup>2 + p = 1"
    unfolding p_def by (rule hhl_out_branches[OF A n0 k t0 spec Ub Cb])
  hence g0: "\<parallel>mat_fun (\<lambda>x. complex_of_real (sqrt (1 - (C / x)\<^sup>2))) A *\<^sub>v b\<parallel>\<^sup>2 = 1 - p" by linarith
  have "trace (anc_proj Dm 0 * outer_prod \<psi> \<psi> * adjoint (anc_proj Dm 0)) = inner_prod ?w0 ?w0"
    unfolding br b0 by (rule trace_outer_prod[OF w0c w0c])
  also have "\<dots> = complex_of_real (\<parallel>mat_fun (\<lambda>x. complex_of_real (sqrt (1 - (C / x)\<^sup>2))) A *\<^sub>v b\<parallel>\<^sup>2)"
    by (rule branch_overlaps(5)[OF A n0 k t0 spec Ub Cb])
  finally show "trace (anc_proj Dm 0 * outer_prod \<psi> \<psi> * adjoint (anc_proj Dm 0)) = complex_of_real (1 - p)" unfolding g0 .
  show "anc_proj Dm 1 * outer_prod \<psi> \<psi> * adjoint (anc_proj Dm 1) = outer_prod w1 w1" unfolding br b1 ..
  have tc: "?t \<in> carrier_vec Dm" unfolding Dm_def by (rule carrier_vecI[OF target_dim[OF A n0 k t0 spec Ub Cb]])
  have "trace (outer_prod ?t ?t * outer_prod w1 w1) = inner_prod ?t w1 * trace (outer_prod ?t w1)"
    unfolding outer_prod_mult_outer_prod[OF tc tc w1c w1c] by (rule trace_smult[OF outer_prod_dim[OF tc w1c]])
  also have "\<dots> = inner_prod ?t w1 * inner_prod w1 ?t" unfolding trace_outer_prod[OF tc w1c] ..
  also have "\<dots> = complex_of_real (C * \<parallel>herm_inv A *\<^sub>v b\<parallel>) * complex_of_real (C * \<parallel>herm_inv A *\<^sub>v b\<parallel>)"
    unfolding w1_def
    by (rule arg_cong2[where f = "(*)", OF branch_overlaps(3)[OF A n0 k t0 spec Ub Cb] branch_overlaps(4)[OF A n0 k t0 spec Ub Cb]])
  also have "\<dots> = complex_of_real p" unfolding p_def by (simp add: power2_eq_square)
  finally show "trace (outer_prod ?t ?t * outer_prod w1 w1) = complex_of_real p" .
  show "0 \<le> p" unfolding p_def by simp
  have "0 \<le> \<parallel>mat_fun (\<lambda>x. complex_of_real (sqrt (1 - (C / x)\<^sup>2))) A *\<^sub>v b\<parallel>\<^sup>2" by simp
  thus "p \<le> 1" using sum1 by linarith
qed

text \<open>The success probability is positive as soon as $C\neq0$.\<close>

lemma rus_p_pos: "C \<noteq> 0 \<Longrightarrow> 0 < C\<^sup>2 * \<parallel>herm_inv A *\<^sub>v b\<parallel>\<^sup>2"
  using sol_nonzero[OF A n0 k t0 spec Ub Cb] by (simp add: zero_less_mult_iff)

text \<open>The loop body resets the register to the circuit's output.\<close>

lemma rus_reset:
  assumes Us: "\<And>U. U \<in> set Us \<Longrightarrow> U \<in> carrier_mat (2 ^ k * (n * 2)) (2 ^ k * (n * 2)) \<and> Complex_Matrix.unitary U"
      and circ: "circuit_mat (2 ^ k * (n * 2)) Us = circuit_mat (2 ^ k * (n * 2)) (hhl_gates A Ub t0 k C)"
      and r: "\<rho> \<in> carrier_mat (2 ^ k * (n * 2)) (2 ^ k * (n * 2))"
  shows "state_sig.denote [2 ^ k, n, 2] (init_com (2 ^ k * (n * 2)) ;; utrans_seq Us) \<rho>
         = trace \<rho> \<cdot>\<^sub>m outer_prod (tensor_vec (unit_vec (2 ^ k) 0) (hhl_out A C b)) (tensor_vec (unit_vec (2 ^ k) 0) (hhl_out A C b))"
proof -
  interpret state_sig "[2 ^ k, n, 2]" .
  have dd: "d = 2 ^ k * (n * 2)" by (simp add: d_def)
  have "denote (init_com d ;; utrans_seq Us) \<rho> = trace \<rho> \<cdot>\<^sub>m outer_prod (circuit_mat d Us *\<^sub>v unit_vec d 0) (circuit_mat d Us *\<^sub>v unit_vec d 0)"
    by (rule denote_init_circuit) (use n0 Us dd r in auto)
  also have "circuit_mat d Us *\<^sub>v unit_vec d 0 = tensor_vec (unit_vec (2 ^ k) 0) (hhl_out A C b)"
    unfolding dd circ by (rule prog_out[OF A n0 k t0 spec Ub Cb])
  finally show ?thesis unfolding dd .
qed

theorem hhl_rus_prog_total:
  assumes Us: "\<And>U. U \<in> set Us \<Longrightarrow> U \<in> carrier_mat (2 ^ k * (n * 2)) (2 ^ k * (n * 2)) \<and> Complex_Matrix.unitary U"
      and circ: "circuit_mat (2 ^ k * (n * 2)) Us = circuit_mat (2 ^ k * (n * 2)) (hhl_gates A Ub t0 k C)"
      and C0: "C \<noteq> 0"
  shows "state_sig.hoare_total_correct [2 ^ k, n, 2] (1\<^sub>m (2 ^ k * (n * 2))) (hhl_rus_prog (2 ^ k * (n * 2)) Us)
     (outer_prod (hhl_target A k b) (hhl_target A k b))"
proof -
  interpret state_sig "[2 ^ k, n, 2]" .
  let ?D = "2 ^ k * (n * 2)" and ?\<psi> = "tensor_vec (unit_vec (2 ^ k) 0) (hhl_out A C b)" and ?p = "C\<^sup>2 * \<parallel>herm_inv A *\<^sub>v b\<parallel>\<^sup>2"
  let ?\<sigma> = "outer_prod ?\<psi> ?\<psi>" and ?T = "outer_prod (hhl_target A k b) (hhl_target A k b)"
  let ?M = "\<lambda>j. anc_proj ?D (1 - j)" and ?Sc = "init_com ?D ;; utrans_seq Us"
  have dd: "d = ?D" by (simp add: d_def)
  have wc: "well_com (hhl_rus_prog ?D Us)" by (rule hhl_rus_prog_well_com[OF A n0 k t0 spec Ub Cb Us])
  hence M: "measurement d 2 ?M" and Sc: "well_com ?Sc" unfolding rus_meas_def by simp_all
  note st = rus_state
  have p0: "0 < ?p" by (rule rus_p_pos[OF C0])
  have reset: "\<rho> \<in> carrier_mat d d \<Longrightarrow> partial_density_operator \<rho> \<Longrightarrow> denote ?Sc \<rho> = trace \<rho> \<cdot>\<^sub>m ?\<sigma>" for \<rho>
    unfolding dd by (rule rus_reset[OF Us circ])
  show ?thesis unfolding hoare_total_correct_def
  proof
    fix \<rho> assume r: "\<rho> \<in> density_states"
    have rc: "\<rho> \<in> carrier_mat d d" and pd: "partial_density_operator \<rho>" using r by (auto simp: density_states_def)
    have tr0: "0 \<le> trace \<rho>" using positive_trace[OF rc] pd unfolding partial_density_operator_def by simp
    have tr1: "trace \<rho> \<le> 1" using pd unfolding partial_density_operator_def by simp
    define c where "c = Re (trace \<rho>)"
    have tr: "trace \<rho> = complex_of_real c" using tr0 unfolding c_def less_eq_complex_def by (simp add: complex_eq_iff)
    have c: "0 \<le> c" "c \<le> 1" using tr0 tr1 unfolding c_def less_eq_complex_def by simp_all
    have "denote (hhl_rus_prog ?D Us) \<rho> = denote (While ?M ?Sc) (denote ?Sc \<rho>)" unfolding rus_meas_def by (rule denote.simps(3))
    also have "\<dots> = denote (While ?M ?Sc) (complex_of_real c \<cdot>\<^sub>m ?\<sigma>)" unfolding reset[OF rc pd] tr ..
    finally have e: "denote (hhl_rus_prog ?D Us) \<rho> = denote (While ?M ?Sc) (complex_of_real c \<cdot>\<^sub>m ?\<sigma>)" .
    have p1: "trace (?M 1 * ?\<sigma> * adjoint (?M 1)) = complex_of_real (1 - ?p)" by (simp only: diff_self_eq_0 st(5))
    have v: "trace (?T * (?M 0 * ?\<sigma> * adjoint (?M 0))) = complex_of_real ?p" by (simp only: diff_zero st(6) st(7))
    have "complex_of_real (c * ?p / ?p) \<le> trace (?T * denote (While ?M ?Sc) (complex_of_real c \<cdot>\<^sub>m ?\<sigma>))"
      by (rule while_reset_total[OF M Sc st(2)[folded dd] st(3) st(4) reset p1 p0 st(9) post_facts(5)[OF A n0 k t0 spec Ub Cb] v c])
    moreover have "c * ?p / ?p = c" by (rule nonzero_mult_div_cancel_right[OF not_sym[OF less_imp_neq[OF p0]]])
    ultimately have "complex_of_real c \<le> trace (?T * denote (While ?M ?Sc) (complex_of_real c \<cdot>\<^sub>m ?\<sigma>))" by simp
    thus "trace (1\<^sub>m ?D * \<rho>) \<le> trace (?T * denote (hhl_rus_prog ?D Us) \<rho>)"
      unfolding e left_mult_one_mat[OF rc[unfolded dd]] tr .
  qed
qed

text \<open>The loop exits after exactly $m$ failed rounds with probability $(1-p)^m p$, in the target state;
after $m$ rounds it is still running with probability $(1-p)^m$.\<close>

theorem hhl_rus_prog_rounds:
  assumes Us: "\<And>U. U \<in> set Us \<Longrightarrow> U \<in> carrier_mat (2 ^ k * (n * 2)) (2 ^ k * (n * 2)) \<and> Complex_Matrix.unitary U"
      and circ: "circuit_mat (2 ^ k * (n * 2)) Us = circuit_mat (2 ^ k * (n * 2)) (hhl_gates A Ub t0 k C)"
      and r: "\<rho> \<in> state_sig.density_states [2 ^ k, n, 2]"
  defines "Dm \<equiv> 2 ^ k * (n * 2)" and "p \<equiv> C\<^sup>2 * \<parallel>herm_inv A *\<^sub>v b\<parallel>\<^sup>2"
    and "Sc \<equiv> init_com (2 ^ k * (n * 2)) ;; utrans_seq Us"
    and "w1 \<equiv> tensor_vec (unit_vec (2 ^ k) 0) (tensor_vec ((complex_of_real C \<cdot>\<^sub>m herm_inv A) *\<^sub>v b) (unit_vec 2 1))"
  shows "state_sig.denote_while_n (anc_proj Dm 1) (anc_proj Dm 0) (state_sig.denote [2 ^ k, n, 2] Sc) m (state_sig.denote [2 ^ k, n, 2] Sc \<rho>)
           = (trace \<rho> * complex_of_real ((1 - p) ^ m)) \<cdot>\<^sub>m outer_prod w1 w1"
    and "trace (state_sig.denote_while_n (anc_proj Dm 1) (anc_proj Dm 0) (state_sig.denote [2 ^ k, n, 2] Sc) m
                 (state_sig.denote [2 ^ k, n, 2] Sc \<rho>)) = trace \<rho> * complex_of_real ((1 - p) ^ m * p)"
    and "trace (state_sig.denote_while_n_iter (anc_proj Dm 1) (anc_proj Dm 0) (state_sig.denote [2 ^ k, n, 2] Sc) m
                 (state_sig.denote [2 ^ k, n, 2] Sc \<rho>)) = trace \<rho> * complex_of_real ((1 - p) ^ m)"
proof -
  interpret state_sig "[2 ^ k, n, 2]" .
  let ?\<psi> = "tensor_vec (unit_vec (2 ^ k) 0) (hhl_out A C b)"
  let ?\<sigma> = "outer_prod ?\<psi> ?\<psi>" and ?M = "\<lambda>j. anc_proj Dm (1 - j)"
  have dd: "d = Dm" by (simp add: d_def Dm_def)
  have dd': "d = 2 ^ k * (n * 2)" by (simp add: d_def)
  have wc: "well_com (hhl_rus_prog Dm Us)" unfolding Dm_def by (rule hhl_rus_prog_well_com[OF A n0 k t0 spec Ub Cb Us])
  hence M: "measurement d 2 ?M" and Sc: "well_com Sc" unfolding rus_meas_def Sc_def Dm_def by simp_all
  note st = rus_state
  have reset: "\<rho> \<in> carrier_mat d d \<Longrightarrow> partial_density_operator \<rho> \<Longrightarrow> denote Sc \<rho> = trace \<rho> \<cdot>\<^sub>m ?\<sigma>" for \<rho>
    unfolding dd Sc_def Dm_def by (rule rus_reset[OF Us circ])
  have rc: "\<rho> \<in> carrier_mat d d" and pd: "partial_density_operator \<rho>" using r by (auto simp: density_states_def)
  have tr0: "0 \<le> trace \<rho>" using positive_trace[OF rc] pd unfolding partial_density_operator_def by simp
  have tr1: "trace \<rho> \<le> 1" using pd unfolding partial_density_operator_def by simp
  define c where "c = Re (trace \<rho>)"
  have tr: "trace \<rho> = complex_of_real c" using tr0 unfolding c_def less_eq_complex_def by (simp add: complex_eq_iff)
  have c: "0 \<le> c" "c \<le> 1" using tr0 tr1 unfolding c_def less_eq_complex_def by simp_all
  have p1: "trace (?M 1 * ?\<sigma> * adjoint (?M 1)) = complex_of_real (1 - p)"
    unfolding p_def Dm_def by (simp only: diff_self_eq_0 st(5))
  have ex0: "denote_while_n (?M 0) (?M 1) (denote Sc) m (complex_of_real c \<cdot>\<^sub>m ?\<sigma>)
             = complex_of_real (c * (1 - p) ^ m) \<cdot>\<^sub>m (?M 0 * ?\<sigma> * adjoint (?M 0))"
    unfolding p_def by (rule while_reset_exit[OF M Sc st(2)[folded dd'] st(3) st(4) reset p1[unfolded p_def] st(8) st(9) c])
  have it0: "denote_while_n_iter (?M 0) (?M 1) (denote Sc) m (complex_of_real c \<cdot>\<^sub>m ?\<sigma>) = complex_of_real (c * (1 - p) ^ m) \<cdot>\<^sub>m ?\<sigma>"
    unfolding p_def by (rule while_reset_iter[OF M Sc st(2)[folded dd'] st(3) st(4) reset p1[unfolded p_def] st(8) st(9) c])
  have M0: "?M 0 = anc_proj Dm 1" and M1: "?M 1 = anc_proj Dm 0" by simp_all
  note ex = ex0[unfolded M0 M1 st(6)[folded w1_def Dm_def]] and it = it0[unfolded M0 M1]
  have w1c: "w1 \<in> carrier_vec Dm" unfolding w1_def Dm_def
    by (rule carrier_vecI) (simp add: tensor_vec_dim carrier_matD[OF mat_fun_carrier[OF A]] herm_inv_def)
  show 1: "denote_while_n (anc_proj Dm 1) (anc_proj Dm 0) (denote Sc) m (denote Sc \<rho>) = (trace \<rho> * complex_of_real ((1 - p) ^ m)) \<cdot>\<^sub>m outer_prod w1 w1"
    unfolding reset[OF rc pd] tr ex by simp
  have "trace (outer_prod w1 w1) = complex_of_real p"
  proof -
    have Hc: "herm_inv A \<in> carrier_mat n n" unfolding herm_inv_def by (rule mat_fun_carrier[OF A])
    have "(complex_of_real C \<cdot>\<^sub>m herm_inv A) *\<^sub>v b = complex_of_real C \<cdot>\<^sub>v (herm_inv A *\<^sub>v b)"
      using Ub by (intro smult_mat_mult_vec[OF Hc]) auto
    hence "\<parallel>w1\<parallel> = \<bar>C\<bar> * \<parallel>herm_inv A *\<^sub>v b\<parallel>" unfolding w1_def using Ub
      by (simp add: vnorm_tensor tensor_vec_dim cpx_vec_length_smult carrier_matD[OF mat_fun_carrier[OF A]] herm_inv_def)
    hence "\<langle>w1|w1\<rangle> = complex_of_real p" unfolding cpx_vec_length_inner_prod[symmetric] p_def by (simp add: power_mult_distrib)
    thus ?thesis unfolding trace_outer_prod[OF w1c w1c] using inner_bridge[of w1 w1] by simp
  qed
  thus "trace (denote_while_n (anc_proj Dm 1) (anc_proj Dm 0) (denote Sc) m (denote Sc \<rho>)) = trace \<rho> * complex_of_real ((1 - p) ^ m * p)"
    unfolding 1 trace_smult[OF outer_prod_dim[OF w1c w1c]] by simp
  show "trace (denote_while_n_iter (anc_proj Dm 1) (anc_proj Dm 0) (denote Sc) m (denote Sc \<rho>)) = trace \<rho> * complex_of_real ((1 - p) ^ m)"
    unfolding reset[OF rc pd] tr it trace_smult[OF st(2)] st(4) by simp
qed

text \<open>Expected number of rounds: $1/p = 1/(C^2\norm{A^{-1}b}^2)$.\<close>

theorem hhl_rus_expected_rounds:
  assumes C0: "C \<noteq> 0"
  defines "p \<equiv> C\<^sup>2 * \<parallel>herm_inv A *\<^sub>v b\<parallel>\<^sup>2"
  shows "(\<lambda>m. real (Suc m) * (p * (1 - p) ^ m)) sums (1 / p)" and "(\<lambda>m. (1 - p) ^ m) sums (1 / p)"
  using rounds_expectation[OF rus_p_pos[OF C0] rus_state(9)]
  unfolding p_def by simp_all

theorem hhl_rus_total:
  assumes "C \<noteq> 0"
  shows "state_sig.hoare_total_correct [2 ^ k, n, 2] (1\<^sub>m (2 ^ k * (n * 2))) (hhl_rus A Ub t0 k C)
     (outer_prod (hhl_target A k b) (hhl_target A k b))"
  unfolding hhl_rus_def carrier_matD(1)[OF A(1)]
  by (rule hhl_rus_prog_total[OF prog_gates[OF A n0 k t0 spec Ub Cb] refl assms])

theorem hhl_elem_rus_total:
  assumes "C \<noteq> 0"
  shows "state_sig.hoare_total_correct [2 ^ k, n, 2] (1\<^sub>m (2 ^ k * (n * 2))) (hhl_elem_rus A Ub t0 k C)
     (outer_prod (hhl_target A k b) (hhl_target A k b))"
  unfolding hhl_elem_rus_def carrier_matD(1)[OF A(1)]
  by (rule hhl_rus_prog_total[OF elem_gates_ok[OF A n0 k t0 spec Ub Cb] hhl_elem_circuit[OF A n0 k t0 spec Ub Cb] assms])

end

end

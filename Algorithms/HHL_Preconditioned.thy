theory HHL_Preconditioned
  imports HHL_Gates
begin

section \<open>HHL on a preconditioned system\<close>

text \<open>Preconditioning replaces $Ax=b$ by $BAx=Bb$ (\<open>precond_left\<close>).  $BA$ need not be
Hermitian, so the program runs on its Hermitian dilation $\tilde M=\begin{pmatrix}0&BA\\(BA)^*&0\end{pmatrix}$
(\<open>herm_embed\<close>) with right-hand side $\ket{Bb}\oplus0$, $\ket{Bb}=Bb/\norm{Bb}$.  On success the
system register holds $0\oplus\hat x$, $\hat x=x/\norm x$ for the solution of the original
system, and the success probability is $C^2\norm x^2/\norm{Bb}^2\ge C^2/\norm{BA}^2$.\<close>

definition pc_rhs :: "complex Matrix.mat \<Rightarrow> complex Matrix.vec \<Rightarrow> complex Matrix.vec" where
  "pc_rhs B b = (complex_of_real (1 / \<parallel>B *\<^sub>v b\<parallel>) \<cdot>\<^sub>v (B *\<^sub>v b)) @\<^sub>v 0\<^sub>v (dim_row B)"

definition pc_target :: "nat \<Rightarrow> complex Matrix.vec \<Rightarrow> complex Matrix.vec" where
  "pc_target k x = tensor_vec (unit_vec (2 ^ k) 0) (tensor_vec (0\<^sub>v (dim_vec x) @\<^sub>v (complex_of_real (1 / \<parallel>x\<parallel>) \<cdot>\<^sub>v x)) (unit_vec 2 1))"

lemma vnorm_append: "\<parallel>a @\<^sub>v c\<parallel> = sqrt (\<parallel>a\<parallel>\<^sup>2 + \<parallel>c\<parallel>\<^sup>2)"
proof -
  have "(\<Sum>i<dim_vec a + dim_vec c. (cmod ((a @\<^sub>v c) $ i))\<^sup>2)
        = (\<Sum>i<dim_vec a. (cmod (a $ i))\<^sup>2) + (\<Sum>j<dim_vec c. (cmod (c $ j))\<^sup>2)"
    unfolding sum_split_add by (simp add: index_append_vec)
  thus ?thesis by (simp add: cpx_vec_length_def sum_nonneg)
qed

context state_sig
begin

text \<open>Weakening a scalar precondition.\<close>

lemma total_scalar_weaken:
  assumes h: "\<Turnstile>\<^sub>t {complex_of_real c \<cdot>\<^sub>m 1\<^sub>m d} Sc {Q}" and c: "c' \<le> c"
  shows "\<Turnstile>\<^sub>t {complex_of_real c' \<cdot>\<^sub>m 1\<^sub>m d} Sc {Q}"
  unfolding hoare_total_correct_def
proof
  fix \<rho> assume r: "\<rho> \<in> density_states"
  have rc: "\<rho> \<in> carrier_mat d d" and p: "positive \<rho>" using r by (auto simp: density_states_def partial_density_operator_def)
  have tr: "trace ((complex_of_real e \<cdot>\<^sub>m 1\<^sub>m d) * \<rho>) = complex_of_real e * trace \<rho>" for e
    using rc by (simp add: mult_smult_assoc_mat[OF one_carrier_mat rc] trace_smult[OF rc])
  have t0: "trace \<rho> \<ge> 0" by (rule positive_trace[OF rc p])
  have "complex_of_real c' * trace \<rho> \<le> complex_of_real c * trace \<rho>"
    using t0 c by (auto simp: less_eq_complex_def intro: mult_right_mono)
  also have "\<dots> \<le> trace (Q * denote Sc \<rho>)"
    using h r unfolding hoare_total_correct_def tr[symmetric] by blast
  finally show "trace ((complex_of_real c' \<cdot>\<^sub>m 1\<^sub>m d) * \<rho>) \<le> trace (Q * denote Sc \<rho>)" unfolding tr .
qed

end

context
  fixes A B Ub :: "complex Matrix.mat" and b x :: "complex Matrix.vec" and n k :: nat and t0 C :: real
  assumes A: "A \<in> carrier_mat n n" and B: "B \<in> carrier_mat n n" and n0: "0 < n" and k: "1 \<le> k" and t0: "0 < t0"
    and x: "dim_vec x = n" "A *\<^sub>v x = b"
    and spec: "\<And>l. l \<in> herm_spectrum (herm_embed (B * A)) \<Longrightarrow> \<exists>j. 0 < j \<and> j < 2 ^ k \<and> l = reg_eig t0 (2 ^ k) j"
    and Ub: "Ub \<in> carrier_mat (n + n) (n + n)" "Quantum.unitary Ub" "Ub *\<^sub>v unit_vec (n + n) 0 = pc_rhs B b"
    and Cb: "\<And>j. j < 2 ^ k \<Longrightarrow> \<bar>C / reg_eig t0 (2 ^ k) j\<bar> \<le> 1"
begin

lemma pc_M: "B * A \<in> carrier_mat n n" using A B by simp

lemma pc_H: "herm_embed (B * A) \<in> carrier_mat (n + n) (n + n)" "hermitian (herm_embed (B * A))"
  using herm_embed_carrier[OF pc_M] herm_embed_hermitian[OF pc_M] by auto

lemma pc_n: "0 < n + n" using n0 by simp

lemma pc_Bx: "B *\<^sub>v b = (B * A) *\<^sub>v x"
  using assoc_mult_mat_vec[OF B A carrier_vecI[OF x(1)]] x(2) by simp

lemma pc_Bb: "0 < \<parallel>B *\<^sub>v b\<parallel>"
proof (rule ccontr)
  assume "\<not> 0 < \<parallel>B *\<^sub>v b\<parallel>"
  hence z: "\<parallel>B *\<^sub>v b\<parallel> = 0" using vnorm_ge0[of "B *\<^sub>v b"] by linarith
  have "\<parallel>pc_rhs B b\<parallel> = 0" unfolding pc_rhs_def vnorm_append cpx_vec_length_smult z vnorm_zero_vec by simp
  moreover have "\<parallel>pc_rhs B b\<parallel> = 1"
  proof -
    have "\<parallel>pc_rhs B b\<parallel> = \<parallel>unit_vec (n + n) 0\<parallel>" using unitary_vnorm[OF Ub(1,2), of "unit_vec (n + n) 0"] Ub(3) by simp
    thus ?thesis using n0 by (simp add: cpx_vec_length_def lessThan_atLeast0 sum.atLeast_Suc_lessThan unit_vec_def)
  qed
  ultimately show False by simp
qed

lemma pc_x: "0 < \<parallel>x\<parallel>"
proof (rule vnorm_pos[OF x(1)])
  show "x \<noteq> 0\<^sub>v n"
  proof
    assume "x = 0\<^sub>v n"
    hence "B *\<^sub>v b = 0\<^sub>v n" unfolding pc_Bx using mult_zero_vec_right[OF pc_M] by simp
    thus False using pc_Bb vnorm_zero_vec by simp
  qed
qed

lemma pc_solve:
  "herm_inv (herm_embed (B * A)) *\<^sub>v pc_rhs B b = 0\<^sub>v n @\<^sub>v (complex_of_real (1 / \<parallel>B *\<^sub>v b\<parallel>) \<cdot>\<^sub>v x)"
proof -
  let ?c = "complex_of_real (1 / \<parallel>B *\<^sub>v b\<parallel>)"
  have z: "0 \<notin> herm_spectrum (herm_embed (B * A))"
  proof
    assume "0 \<in> herm_spectrum (herm_embed (B * A))"
    then obtain j where "0 < j" "j < 2 ^ k" "0 = reg_eig t0 (2 ^ k) j" using spec by blast
    thus False using reg_eig_nonzero[OF t0] by metis
  qed
  have My: "(B * A) *\<^sub>v (?c \<cdot>\<^sub>v x) = ?c \<cdot>\<^sub>v (B *\<^sub>v b)"
    unfolding pc_Bx by (rule mult_mat_vec[OF pc_M carrier_vecI[OF x(1)]])
  have "herm_inv (herm_embed (B * A)) *\<^sub>v ((?c \<cdot>\<^sub>v (B *\<^sub>v b)) @\<^sub>v 0\<^sub>v n) = 0\<^sub>v n @\<^sub>v (?c \<cdot>\<^sub>v x)"
    by (rule herm_embed_inverse[OF pc_M _ My z]) (simp add: x(1))
  thus ?thesis unfolding pc_rhs_def using B by simp
qed

lemma pc_norm: "\<parallel>herm_inv (herm_embed (B * A)) *\<^sub>v pc_rhs B b\<parallel> = \<parallel>x\<parallel> / \<parallel>B *\<^sub>v b\<parallel>"
  unfolding pc_solve vnorm_append vnorm_zero_vec cpx_vec_length_smult using pc_Bb vnorm_ge0[of x] by (simp add: norm_divide)

lemma pc_target_eq: "hhl_target (herm_embed (B * A)) k (pc_rhs B b) = pc_target k x"
proof -
  let ?y = "0\<^sub>v n @\<^sub>v (complex_of_real (1 / \<parallel>B *\<^sub>v b\<parallel>) \<cdot>\<^sub>v x)"
  have "complex_of_real (1 / \<parallel>herm_inv (herm_embed (B * A)) *\<^sub>v pc_rhs B b\<parallel>) \<cdot>\<^sub>v ?y
        = 0\<^sub>v (dim_vec x) @\<^sub>v (complex_of_real (1 / \<parallel>x\<parallel>) \<cdot>\<^sub>v x)"
    unfolding pc_norm using pc_Bb pc_x x(1) by (intro eq_vecI) (auto simp: index_append_vec)
  thus ?thesis unfolding hhl_target_def pc_target_def pc_solve by simp
qed

text \<open>The two programs on the preconditioned system: success probability and the output state.\<close>

theorem hhl_precond_success:
  "state_sig.hoare_total_correct [2 ^ k, n + n, 2] (complex_of_real (C\<^sup>2 * (\<parallel>x\<parallel> / \<parallel>B *\<^sub>v b\<parallel>)\<^sup>2) \<cdot>\<^sub>m 1\<^sub>m (2 ^ k * ((n + n) * 2)))
     (hhl_program (herm_embed (B * A)) Ub t0 k C) (anc_proj (2 ^ k * ((n + n) * 2)) 1)"
  using hhl_success_total[OF pc_H pc_n k t0 spec Ub Cb] unfolding pc_norm .

theorem hhl_precond_correct:
  "state_sig.hoare_total_correct [2 ^ k, n + n, 2] (1\<^sub>m (2 ^ k * ((n + n) * 2))) (hhl_program (herm_embed (B * A)) Ub t0 k C)
     (anc_proj (2 ^ k * ((n + n) * 2)) 0 + outer_prod (pc_target k x) (pc_target k x))"
  using hhl_correct_total[OF pc_H pc_n k t0 spec Ub Cb] unfolding pc_target_eq .

theorem hhl_precond_rus:
  "state_sig.hoare_partial_correct [2 ^ k, n + n, 2] (1\<^sub>m (2 ^ k * ((n + n) * 2))) (hhl_rus (herm_embed (B * A)) Ub t0 k C)
     (outer_prod (pc_target k x) (pc_target k x))"
  using hhl_rus_partial[OF pc_H pc_n k t0 spec Ub Cb] unfolding pc_target_eq .

theorem hhl_elem_precond_success:
  "state_sig.hoare_total_correct [2 ^ k, n + n, 2] (complex_of_real (C\<^sup>2 * (\<parallel>x\<parallel> / \<parallel>B *\<^sub>v b\<parallel>)\<^sup>2) \<cdot>\<^sub>m 1\<^sub>m (2 ^ k * ((n + n) * 2)))
     (hhl_elem_program (herm_embed (B * A)) Ub t0 k C) (anc_proj (2 ^ k * ((n + n) * 2)) 1)"
  using hhl_elem_success_total[OF pc_H pc_n k t0 spec Ub Cb] unfolding pc_norm .

theorem hhl_elem_precond_correct:
  "state_sig.hoare_total_correct [2 ^ k, n + n, 2] (1\<^sub>m (2 ^ k * ((n + n) * 2))) (hhl_elem_program (herm_embed (B * A)) Ub t0 k C)
     (anc_proj (2 ^ k * ((n + n) * 2)) 0 + outer_prod (pc_target k x) (pc_target k x))"
  using hhl_elem_correct_total[OF pc_H pc_n k t0 spec Ub Cb] unfolding pc_target_eq .

theorem hhl_elem_precond_rus:
  "state_sig.hoare_partial_correct [2 ^ k, n + n, 2] (1\<^sub>m (2 ^ k * ((n + n) * 2))) (hhl_elem_rus (herm_embed (B * A)) Ub t0 k C)
     (outer_prod (pc_target k x) (pc_target k x))"
  using hhl_elem_rus_partial[OF pc_H pc_n k t0 spec Ub Cb] unfolding pc_target_eq .

text \<open>With $\norm{BAv}\le s\norm v$ the success probability is at least $(C/s)^2$: a good
preconditioner (small $s$, eigenvalues of $\tilde M$ away from $0$ so that $C$ is large) raises it.\<close>

theorem hhl_elem_precond_bound:
  assumes s: "0 < s" and Ms: "\<And>v. dim_vec v = n \<Longrightarrow> \<parallel>(B * A) *\<^sub>v v\<parallel> \<le> s * \<parallel>v\<parallel>"
  shows "state_sig.hoare_total_correct [2 ^ k, n + n, 2] (complex_of_real ((C / s)\<^sup>2) \<cdot>\<^sub>m 1\<^sub>m (2 ^ k * ((n + n) * 2)))
     (hhl_elem_program (herm_embed (B * A)) Ub t0 k C) (anc_proj (2 ^ k * ((n + n) * 2)) 1)"
proof -
  interpret state_sig "[2 ^ k, n + n, 2]" .
  have dd: "d = 2 ^ k * ((n + n) * 2)" by (simp add: d_def)
  have "\<parallel>B *\<^sub>v b\<parallel> \<le> s * \<parallel>x\<parallel>" unfolding pc_Bx by (rule Ms[OF x(1)])
  hence "1 / s \<le> \<parallel>x\<parallel> / \<parallel>B *\<^sub>v b\<parallel>" using s pc_Bb pc_x by (simp add: field_simps)
  hence "(1 / s)\<^sup>2 \<le> (\<parallel>x\<parallel> / \<parallel>B *\<^sub>v b\<parallel>)\<^sup>2" using s by (intro power_mono) simp_all
  hence le: "(C / s)\<^sup>2 \<le> C\<^sup>2 * (\<parallel>x\<parallel> / \<parallel>B *\<^sub>v b\<parallel>)\<^sup>2"
    using mult_left_mono[of "(1 / s)\<^sup>2" "(\<parallel>x\<parallel> / \<parallel>B *\<^sub>v b\<parallel>)\<^sup>2" "C\<^sup>2"] by (simp add: power_divide)
  show ?thesis using total_scalar_weaken[OF hhl_elem_precond_success[unfolded dd[symmetric]] le] unfolding dd .
qed

end

end

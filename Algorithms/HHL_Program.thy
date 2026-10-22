theory HHL_Program
  imports HHL_Trajectory QHLProver.Quantum_Hoare
begin

text \<open>The HHL algorithm as a program of the quantum while-language of the AFP entry
\<open>QHLProver\<close> (quantum Hoare logic, with soundness and completeness), verified with its proof
rules.  The program initialises all registers, prepares $\ket b$, runs the eight gates of
\<open>HHL_Trajectory\<close> and measures the ancilla; a second program repeats the circuit until the
ancilla reads $1$.  Predicates are matrices $0\le P\le I$ and $\{P\}\,S\,\{Q\}$ means
$\mathrm{tr}(P\rho)\le\mathrm{tr}(Q\,[\![S]\!]\rho)$ (plus the non-termination mass, for partial
correctness).  QHLProver has no initialisation statement; it is built from a measurement in
the computational basis followed by a swap of the outcome to $\ket0$.  Names that QHLProver
shares with the notes' library (\<open>unitary\<close>, \<open>inner_prod\<close>, \<open>hermitian\<close>) carry their
theory prefix where both are meant.\<close>

section \<open>Programs of gates\<close>

primrec utrans_seq :: "complex Matrix.mat list \<Rightarrow> com" where
  "utrans_seq [] = SKIP"
| "utrans_seq (U # Us) = Utrans U ;; utrans_seq Us"

primrec circuit_mat :: "nat \<Rightarrow> complex Matrix.mat list \<Rightarrow> complex Matrix.mat" where
  "circuit_mat K [] = 1\<^sub>m K"
| "circuit_mat K (U # Us) = circuit_mat K Us * U"

lemma circuit_mat_carrier:
  "(\<And>U. U \<in> set Us \<Longrightarrow> U \<in> carrier_mat K K) \<Longrightarrow> circuit_mat K Us \<in> carrier_mat K K"
  by (induction Us) auto

context state_sig
begin

lemma circuit_mat_unitary:
  "(\<And>U. U \<in> set Us \<Longrightarrow> U \<in> carrier_mat d d \<and> Complex_Matrix.unitary U) \<Longrightarrow> Complex_Matrix.unitary (circuit_mat d Us)"
proof (induction Us)
  case Nil
  show ?case by (simp add: unitary_one)
next
  case (Cons U Us)
  have c: "circuit_mat d Us \<in> carrier_mat d d" using Cons.prems by (intro circuit_mat_carrier) auto
  show ?case using unitary_times_unitary[OF c _ Cons.IH] Cons.prems by auto
qed

lemma well_com_utrans_seq:
  "(\<And>U. U \<in> set Us \<Longrightarrow> U \<in> carrier_mat d d \<and> Complex_Matrix.unitary U) \<Longrightarrow> well_com (utrans_seq Us)"
  by (induction Us) auto

text \<open>The weakest precondition of a gate sequence: conjugation by the circuit matrix.\<close>

lemma hoare_utrans_seq:
  assumes "\<And>U. U \<in> set Us \<Longrightarrow> U \<in> carrier_mat d d \<and> Complex_Matrix.unitary U" and Q: "is_quantum_predicate Q"
  shows "\<turnstile>\<^sub>p {adjoint (circuit_mat d Us) * Q * circuit_mat d Us} utrans_seq Us {Q}"
  using assms(1)
proof (induction Us)
  case Nil
  have Qd: "Q \<in> carrier_mat d d" using Q unfolding is_quantum_predicate_def by simp
  have "adjoint (1\<^sub>m d) * Q * 1\<^sub>m d = Q" using Qd by (simp add: adjoint_one)
  thus ?case using hoare_partial.intros(1)[OF Q] by simp
next
  case (Cons U Us)
  let ?R = "circuit_mat d Us"
  have U: "U \<in> carrier_mat d d" "Complex_Matrix.unitary U" using Cons.prems by auto
  have R: "?R \<in> carrier_mat d d" using Cons.prems by (intro circuit_mat_carrier) auto
  have Ru: "Complex_Matrix.unitary ?R" using Cons.prems by (intro circuit_mat_unitary) auto
  have Qd: "Q \<in> carrier_mat d d" using Q unfolding is_quantum_predicate_def by simp
  have q1: "is_quantum_predicate (adjoint ?R * Q * ?R)" by (rule qp_close_under_unitary_operator[OF R Ru Q])
  have q2: "is_quantum_predicate (adjoint U * (adjoint ?R * Q * ?R) * U)" by (rule qp_close_under_unitary_operator[OF U q1])
  have h1: "\<turnstile>\<^sub>p {adjoint U * (adjoint ?R * Q * ?R) * U} Utrans U {adjoint ?R * Q * ?R}" by (rule hoare_partial.intros(2)[OF q1])
  have h2: "\<turnstile>\<^sub>p {adjoint ?R * Q * ?R} utrans_seq Us {Q}" using Cons by auto
  have e: "adjoint U * (adjoint ?R * Q * ?R) * U = adjoint (circuit_mat d (U # Us)) * Q * circuit_mat d (U # Us)"
    using U(1) R Qd by (simp add: adjoint_mult[OF R U(1)]) (mat_assoc d)
  show ?case using hoare_partial.intros(3)[OF q2 q1 Q h1 h2] unfolding utrans_seq.simps e .
qed

text \<open>Pure states as predicates: $\ket\psi\bra\psi$ for a unit vector $\psi$.\<close>

lemma qp_pure:
  assumes "dim_vec \<psi> = d" and "inner_prod \<psi> \<psi> = 1"
  shows "is_quantum_predicate (outer_prod \<psi> \<psi>)"
proof -
  have c: "\<psi> \<in> carrier_vec d" using assms(1) by (rule carrier_vecI)
  have "outer_prod \<psi> \<psi> \<in> carrier_mat d d" using outer_prod_dim[OF c c] .
  moreover have "positive (outer_prod \<psi> \<psi>)" by (rule positive_same_outer_prod[OF c])
  moreover have "outer_prod \<psi> \<psi> \<le>\<^sub>L 1\<^sub>m d" by (rule outer_prod_le_one[OF c]) (use assms(2) in simp)
  ultimately show ?thesis unfolding is_quantum_predicate_def by simp
qed

lemma unitary_inner_keep:
  assumes U: "U \<in> carrier_mat d d" "Complex_Matrix.unitary U" and \<psi>: "dim_vec \<psi> = d"
  shows "inner_prod (U *\<^sub>v \<psi>) (U *\<^sub>v \<psi>) = inner_prod \<psi> \<psi>"
proof -
  have \<psi>c: "\<psi> \<in> carrier_vec d" using \<psi> by (rule carrier_vecI)
  have Uc: "U *\<^sub>v \<psi> \<in> carrier_vec d" using U(1) \<psi>c by simp
  have "inner_prod (U *\<^sub>v \<psi>) (U *\<^sub>v \<psi>) = inner_prod (adjoint U *\<^sub>v (U *\<^sub>v \<psi>)) \<psi>"
    by (rule adjoint_def_alter[OF Uc \<psi>c U(1)])
  also have "adjoint U *\<^sub>v (U *\<^sub>v \<psi>) = (adjoint U * U) *\<^sub>v \<psi>" by (rule assoc_mult_mat_vec[symmetric, OF adjoint_dim[OF U(1)] U(1) \<psi>c])
  also have "adjoint U * U = 1\<^sub>m d" using U by (simp add: unitary_simps)
  finally show ?thesis using \<psi>c by simp
qed

text \<open>A gate maps the pure state $\psi$ to $U\psi$.\<close>

lemma hoare_utrans_pure:
  assumes U: "U \<in> carrier_mat d d" "Complex_Matrix.unitary U" and \<psi>: "dim_vec \<psi> = d" "inner_prod \<psi> \<psi> = 1"
  shows "\<turnstile>\<^sub>p {outer_prod \<psi> \<psi>} Utrans U {outer_prod (U *\<^sub>v \<psi>) (U *\<^sub>v \<psi>)}"
proof -
  have \<psi>c: "\<psi> \<in> carrier_vec d" using \<psi>(1) by (rule carrier_vecI)
  have Uc: "U *\<^sub>v \<psi> \<in> carrier_vec d" using U(1) \<psi>c by simp
  have q: "is_quantum_predicate (outer_prod (U *\<^sub>v \<psi>) (U *\<^sub>v \<psi>))"
    by (rule qp_pure) (use U \<psi> unitary_inner_keep[OF U \<psi>(1)] in simp_all)
  have "adjoint U * outer_prod (U *\<^sub>v \<psi>) (U *\<^sub>v \<psi>) * U = outer_prod (adjoint U *\<^sub>v (U *\<^sub>v \<psi>)) (adjoint U *\<^sub>v (U *\<^sub>v \<psi>))"
    by (rule outer_prod_left_right_mat[OF Uc Uc adjoint_dim[OF U(1)] U(1)])
  also have "adjoint U *\<^sub>v (U *\<^sub>v \<psi>) = \<psi>"
  proof -
    have "adjoint U *\<^sub>v (U *\<^sub>v \<psi>) = (adjoint U * U) *\<^sub>v \<psi>" by (rule assoc_mult_mat_vec[symmetric, OF adjoint_dim[OF U(1)] U(1) \<psi>c])
    also have "adjoint U * U = 1\<^sub>m d" using U by (simp add: unitary_simps)
    finally show ?thesis using \<psi>c by simp
  qed
  finally show ?thesis using hoare_partial.intros(2)[OF q, of U] by simp
qed

end

lemma matrix_sum_index:
  assumes f: "\<And>k. k < n \<Longrightarrow> f k \<in> carrier_mat K K" and ij: "i < K" "j < K"
  shows "matrix_sum K f n $$ (i, j) = (\<Sum>k<n. f k $$ (i, j))"
  using f
proof (induction n)
  case (Suc n)
  have c: "matrix_sum K f n \<in> carrier_mat K K" by (rule matrix_sum_dim) (use Suc.prems in auto)
  have "matrix_sum K f (Suc n) $$ (i, j) = f n $$ (i, j) + matrix_sum K f n $$ (i, j)"
    using c Suc.prems[of n] ij by simp
  thus ?case using Suc by (simp add: add_ac)
qed (use ij in simp)

definition swap_idx :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "swap_idx k i = (if i = 0 then k else if i = k then 0 else i)"

lemma swap_idx_inv [simp]: "swap_idx k (swap_idx k i) = i" by (simp add: swap_idx_def)
lemma swap_idx_lt: "k < K \<Longrightarrow> i < K \<Longrightarrow> swap_idx k i < K" by (simp add: swap_idx_def)
lemma swap_idx_eq: "swap_idx k i = j \<longleftrightarrow> i = swap_idx k j" by (auto simp: swap_idx_def)

definition swap0 :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
  "swap0 K k = Matrix.mat K K (\<lambda>(i, j). if j = swap_idx k i then 1 else 0)"

definition proj_basis :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
  "proj_basis K k = Matrix.mat K K (\<lambda>(i, j). if i = k \<and> j = k then 1 else 0)"

text \<open>Initialisation of the whole state to $\ket0$: measure in the computational basis, then
swap the outcome $\ket k$ to $\ket0$.\<close>

definition init_com :: "nat \<Rightarrow> com" where
  "init_com K = Measure K (proj_basis K) (map (\<lambda>k. Utrans (swap0 K k)) [0..<K])"

lemma swap0_carrier [simp]: "swap0 K k \<in> carrier_mat K K" by (simp add: swap0_def)
lemma proj_basis_carrier [simp]: "proj_basis K k \<in> carrier_mat K K" by (simp add: proj_basis_def)

lemma swap0_adjoint: "k < K \<Longrightarrow> adjoint (swap0 K k) = swap0 K k"
  by (rule eq_matI) (auto simp: swap0_def adjoint_eval swap_idx_eq)

lemma swap0_square: "k < K \<Longrightarrow> swap0 K k * swap0 K k = 1\<^sub>m K"
proof (rule eq_matI)
  fix i j assume "k < K" "i < dim_row (1\<^sub>m K)" "j < dim_col (1\<^sub>m K)"
  hence kij: "k < K" "i < K" "j < K" by simp_all
  have "(swap0 K k * swap0 K k) $$ (i, j) = (\<Sum>l<K. (if l = swap_idx k i then 1 else 0) * (if j = swap_idx k l then 1 else 0))"
    using kij by (simp add: swap0_def scalar_prod_def atLeast0LessThan)
  also have "\<dots> = (\<Sum>l\<in>{swap_idx k i}. (if j = swap_idx k l then 1 else 0))"
    using kij swap_idx_lt[of k K i] by (intro sum.mono_neutral_cong_right) auto
  also have "\<dots> = 1\<^sub>m K $$ (i, j)" using kij by auto
  finally show "(swap0 K k * swap0 K k) $$ (i, j) = 1\<^sub>m K $$ (i, j)" .
qed (simp_all add: swap0_def)

lemma swap0_unitary: "k < K \<Longrightarrow> Complex_Matrix.unitary (swap0 K k)"
  unfolding Complex_Matrix.unitary_def inverts_mat_def using swap0_adjoint swap0_square by (simp add: swap0_def)

lemma proj_basis_adjoint: "adjoint (proj_basis K k) = proj_basis K k"
  by (rule eq_matI) (auto simp: proj_basis_def adjoint_eval)

lemma proj_basis_square: "k < K \<Longrightarrow> proj_basis K k * proj_basis K k = proj_basis K k"
proof (rule eq_matI)
  fix i j assume "k < K" "i < dim_row (proj_basis K k)" "j < dim_col (proj_basis K k)"
  hence kij: "k < K" "i < K" "j < K" by (simp_all add: proj_basis_def)
  have "(proj_basis K k * proj_basis K k) $$ (i, j) = (\<Sum>l<K. (if i = k \<and> l = k then 1 else 0) * (if l = k \<and> j = k then 1 else 0))"
    using kij by (simp add: proj_basis_def scalar_prod_def atLeast0LessThan)
  also have "\<dots> = (\<Sum>l\<in>{k}. (if i = k \<and> l = k then 1 else 0) * (if l = k \<and> j = k then 1 else 0))"
    using kij by (intro sum.mono_neutral_cong_right) auto
  finally show "(proj_basis K k * proj_basis K k) $$ (i, j) = proj_basis K k $$ (i, j)" using kij by (simp add: proj_basis_def)
qed (simp_all add: proj_basis_def)

lemma proj_basis_sum: "matrix_sum K (\<lambda>k. adjoint (proj_basis K k) * proj_basis K k) K = 1\<^sub>m K"
proof (rule eq_matI)
  fix i j assume "i < dim_row (1\<^sub>m K)" "j < dim_col (1\<^sub>m K)"
  hence ij: "i < K" "j < K" by simp_all
  have "matrix_sum K (\<lambda>k. adjoint (proj_basis K k) * proj_basis K k) K $$ (i, j) = (\<Sum>k<K. proj_basis K k $$ (i, j))"
    by (subst matrix_sum_index) (use ij in \<open>simp_all add: proj_basis_adjoint proj_basis_square\<close>)
  also have "\<dots> = (\<Sum>k\<in>{i}. proj_basis K k $$ (i, j))" using ij by (intro sum.mono_neutral_cong_right) (auto simp: proj_basis_def)
  finally show "matrix_sum K (\<lambda>k. adjoint (proj_basis K k) * proj_basis K k) K $$ (i, j) = 1\<^sub>m K $$ (i, j)"
    using ij by (simp add: proj_basis_def)
next
  have "matrix_sum K (\<lambda>k. adjoint (proj_basis K k) * proj_basis K k) K \<in> carrier_mat K K"
    by (rule matrix_sum_dim) (simp add: proj_basis_adjoint proj_basis_square)
  thus "dim_row (matrix_sum K (\<lambda>k. adjoint (proj_basis K k) * proj_basis K k) K) = dim_row (1\<^sub>m K)"
    "dim_col (matrix_sum K (\<lambda>k. adjoint (proj_basis K k) * proj_basis K k) K) = dim_col (1\<^sub>m K)" by auto
qed

lemma swap0_left: "Q \<in> carrier_mat K K \<Longrightarrow> k < K \<Longrightarrow> i < K \<Longrightarrow> j < K \<Longrightarrow> (swap0 K k * Q) $$ (i, j) = Q $$ (swap_idx k i, j)"
proof -
  assume Q: "Q \<in> carrier_mat K K" and kij: "k < K" "i < K" "j < K"
  have "(swap0 K k * Q) $$ (i, j) = (\<Sum>l<K. (if l = swap_idx k i then 1 else 0) * Q $$ (l, j))"
    using Q kij by (simp add: swap0_def scalar_prod_def atLeast0LessThan)
  also have "\<dots> = (\<Sum>l\<in>{swap_idx k i}. (if l = swap_idx k i then 1 else 0) * Q $$ (l, j))"
    using kij swap_idx_lt[of k K i] by (intro sum.mono_neutral_cong_right) auto
  finally show ?thesis by simp
qed

lemma swap0_right: "Q \<in> carrier_mat K K \<Longrightarrow> k < K \<Longrightarrow> i < K \<Longrightarrow> j < K \<Longrightarrow> (Q * swap0 K k) $$ (i, j) = Q $$ (i, swap_idx k j)"
proof -
  assume Q: "Q \<in> carrier_mat K K" and kij: "k < K" "i < K" "j < K"
  have "(Q * swap0 K k) $$ (i, j) = (\<Sum>l<K. Q $$ (i, l) * (if j = swap_idx k l then 1 else 0))"
    using Q kij by (simp add: swap0_def scalar_prod_def atLeast0LessThan)
  also have "\<dots> = (\<Sum>l\<in>{swap_idx k j}. Q $$ (i, l) * (if j = swap_idx k l then 1 else 0))"
    using kij swap_idx_lt[of k K j] by (intro sum.mono_neutral_cong_right) (auto simp: swap_idx_eq)
  finally show ?thesis by (simp add: swap_idx_eq)
qed

lemma proj_basis_sandwich:
  assumes P: "P \<in> carrier_mat K K" and k: "k < K"
  shows "proj_basis K k * P * proj_basis K k = P $$ (k, k) \<cdot>\<^sub>m proj_basis K k"
proof (rule eq_matI)
  fix i j assume "i < dim_row (P $$ (k, k) \<cdot>\<^sub>m proj_basis K k)" "j < dim_col (P $$ (k, k) \<cdot>\<^sub>m proj_basis K k)"
  hence ij: "i < K" "j < K" by (simp_all add: proj_basis_def)
  have l: "(proj_basis K k * P) $$ (i, l) = (if i = k then P $$ (k, l) else 0)" if l: "l < K" for l
  proof -
    have "(proj_basis K k * P) $$ (i, l) = (\<Sum>a<K. (if i = k \<and> a = k then 1 else 0) * P $$ (a, l))"
      using P ij l by (simp add: proj_basis_def scalar_prod_def atLeast0LessThan)
    also have "\<dots> = (\<Sum>a\<in>{k}. (if i = k \<and> a = k then 1 else 0) * P $$ (a, l))"
      using k by (intro sum.mono_neutral_cong_right) auto
    finally show ?thesis by simp
  qed
  have "(proj_basis K k * P * proj_basis K k) $$ (i, j) = (\<Sum>l<K. (proj_basis K k * P) $$ (i, l) * (if l = k \<and> j = k then 1 else 0))"
    using P ij by (simp add: proj_basis_def scalar_prod_def atLeast0LessThan)
  also have "\<dots> = (\<Sum>l\<in>{k}. (proj_basis K k * P) $$ (i, l) * (if l = k \<and> j = k then 1 else 0))"
    using k by (intro sum.mono_neutral_cong_right) auto
  also have "\<dots> = (P $$ (k, k) \<cdot>\<^sub>m proj_basis K k) $$ (i, j)" using l[OF k] ij by (simp add: proj_basis_def)
  finally show "(proj_basis K k * P * proj_basis K k) $$ (i, j) = (P $$ (k, k) \<cdot>\<^sub>m proj_basis K k) $$ (i, j)" .
qed (use P in \<open>simp_all add: proj_basis_def\<close>)

lemma mult_unit_vec_index: "(A :: complex Matrix.mat) \<in> carrier_mat K K \<Longrightarrow> i < K \<Longrightarrow> l < K \<Longrightarrow> (A *\<^sub>v unit_vec K i) $ l = A $$ (l, i)"
proof -
  assume A: "A \<in> carrier_mat K K" and il: "i < K" "l < K"
  have "(A *\<^sub>v unit_vec K i) $ l = (\<Sum>a<K. A $$ (l, a) * unit_vec K i $ a)"
    using A il by (simp add: scalar_prod_def atLeast0LessThan)
  also have "\<dots> = (\<Sum>a\<in>{i}. A $$ (l, a) * unit_vec K i $ a)" using il by (intro sum.mono_neutral_cong_right) auto
  finally show ?thesis using il by simp
qed

context state_sig
begin

lemma qp_diag:
  assumes Q: "is_quantum_predicate Q" and i: "i < d"
  shows "Q $$ (i, i) \<in> \<real>" "0 \<le> Re (Q $$ (i, i))" "Re (Q $$ (i, i)) \<le> 1"
proof -
  have Qd: "Q \<in> carrier_mat d d" and pQ: "positive Q" and le: "Q \<le>\<^sub>L 1\<^sub>m d" using Q unfolding is_quantum_predicate_def by auto
  let ?e = "unit_vec d i"
  have qe: "inner_prod ?e (Q *\<^sub>v ?e) = Q $$ (i, i)" by (rule unit_vec_bracket[OF Qd i])
  have "inner_prod ?e (Q *\<^sub>v ?e) \<ge> 0" using pQ Qd i unfolding positive_def by auto
  hence g: "Q $$ (i, i) \<ge> 0" using qe by simp
  thus "Q $$ (i, i) \<in> \<real>" "0 \<le> Re (Q $$ (i, i))" by (auto simp: less_eq_complex_def complex_is_Real_iff)
  have p1: "positive (1\<^sub>m d - Q)" using le unfolding lowner_le_def by simp
  have "inner_prod ?e ((1\<^sub>m d - Q) *\<^sub>v ?e) \<ge> 0" using p1 Qd i unfolding positive_def by auto
  moreover have "inner_prod ?e ((1\<^sub>m d - Q) *\<^sub>v ?e) = 1 - Q $$ (i, i)"
    using unit_vec_bracket[OF minus_carrier_mat[OF Qd] i] Qd i by simp
  ultimately show "Re (Q $$ (i, i)) \<le> 1" by (simp add: less_eq_complex_def)
qed

lemma qp_scalar:
  fixes q :: complex
  assumes "q \<in> \<real>" "0 \<le> Re q" "Re q \<le> 1"
  shows "is_quantum_predicate (q \<cdot>\<^sub>m 1\<^sub>m d)"
proof -
  have q0: "q \<ge> 0" and q1: "1 - q \<ge> 0" using assms by (auto simp: less_eq_complex_def complex_is_Real_iff)
  have "positive (q \<cdot>\<^sub>m 1\<^sub>m d)" by (rule positive_smult[OF one_carrier_mat positive_one q0])
  moreover have "1\<^sub>m d - q \<cdot>\<^sub>m 1\<^sub>m d = (1 - q) \<cdot>\<^sub>m 1\<^sub>m d" by (rule eq_matI) auto
  moreover have "positive ((1 - q) \<cdot>\<^sub>m 1\<^sub>m d)" by (rule positive_smult[OF one_carrier_mat positive_one q1])
  ultimately show ?thesis unfolding is_quantum_predicate_def lowner_le_def by auto
qed

lemma well_com_init: "0 < d \<Longrightarrow> well_com (init_com d)"
  unfolding init_com_def using proj_basis_sum swap0_unitary
  by (auto simp: measurement_def list_all_length)

text \<open>Initialisation: $\{\langle0|Q|0\rangle\,I\}\ \mathit{init}\ \{Q\}$.\<close>

theorem hoare_init:
  assumes Q: "is_quantum_predicate Q" and d0: "0 < d"
  shows "\<turnstile>\<^sub>p {Q $$ (0, 0) \<cdot>\<^sub>m 1\<^sub>m d} init_com d {Q}"
proof -
  have Qd: "Q \<in> carrier_mat d d" using Q unfolding is_quantum_predicate_def by simp
  let ?P = "\<lambda>k. adjoint (swap0 d k) * Q * swap0 d k"
  have qP: "is_quantum_predicate (?P k)" if "k < d" for k
    by (rule qp_close_under_unitary_operator[OF swap0_carrier swap0_unitary[OF that] Q])
  have br: "\<turnstile>\<^sub>p {?P k} map (\<lambda>k. Utrans (swap0 d k)) [0..<d] ! k {Q}" if "k < d" for k
    using hoare_partial.intros(2)[OF Q, of "swap0 d k"] that by simp
  have h: "\<turnstile>\<^sub>p {matrix_sum d (\<lambda>k. adjoint (proj_basis d k) * ?P k * proj_basis d k) d} init_com d {Q}"
    unfolding init_com_def by (rule hoare_partial.intros(4)[OF qP Q br])
  have Pkk: "?P k $$ (k, k) = Q $$ (0, 0)" if k: "k < d" for k
  proof -
    have XQ: "swap0 d k * Q \<in> carrier_mat d d" by (rule mult_carrier_mat[OF swap0_carrier Qd])
    have "?P k $$ (k, k) = (swap0 d k * Q * swap0 d k) $$ (k, k)" using swap0_adjoint[OF k] by simp
    also have "\<dots> = (swap0 d k * Q) $$ (k, swap_idx k k)" by (rule swap0_right[OF XQ k k k])
    also have "\<dots> = Q $$ (swap_idx k k, swap_idx k k)" using swap_idx_lt[OF k k] by (intro swap0_left[OF Qd k k])
    finally show ?thesis using d0 by (simp add: swap_idx_def)
  qed
  have "matrix_sum d (\<lambda>k. adjoint (proj_basis d k) * ?P k * proj_basis d k) d = Q $$ (0, 0) \<cdot>\<^sub>m 1\<^sub>m d"
  proof (rule eq_matI)
    fix i j assume "i < dim_row (Q $$ (0, 0) \<cdot>\<^sub>m 1\<^sub>m d)" "j < dim_col (Q $$ (0, 0) \<cdot>\<^sub>m 1\<^sub>m d)"
    hence ij: "i < d" "j < d" by simp_all
    have Pc: "?P k \<in> carrier_mat d d" for k
      by (rule mult_carrier_mat[OF mult_carrier_mat[OF adjoint_dim[OF swap0_carrier] Qd] swap0_carrier])
    have PKc: "adjoint (proj_basis d k) * ?P k * proj_basis d k \<in> carrier_mat d d" for k
      by (rule mult_carrier_mat[OF mult_carrier_mat[OF adjoint_dim[OF proj_basis_carrier] Pc] proj_basis_carrier])
    have "matrix_sum d (\<lambda>k. adjoint (proj_basis d k) * ?P k * proj_basis d k) d $$ (i, j)
          = (\<Sum>k<d. (Q $$ (0, 0) \<cdot>\<^sub>m proj_basis d k) $$ (i, j))"
    proof -
      have "matrix_sum d (\<lambda>k. adjoint (proj_basis d k) * ?P k * proj_basis d k) d $$ (i, j)
            = (\<Sum>k<d. (adjoint (proj_basis d k) * ?P k * proj_basis d k) $$ (i, j))"
        by (rule matrix_sum_index[OF PKc ij])
      also have "\<dots> = (\<Sum>k<d. (Q $$ (0, 0) \<cdot>\<^sub>m proj_basis d k) $$ (i, j))"
        by (rule sum.cong[OF refl]) (simp add: proj_basis_adjoint proj_basis_sandwich[OF Pc] Pkk)
      finally show ?thesis .
    qed
    also have "\<dots> = (\<Sum>k\<in>{i}. (Q $$ (0, 0) \<cdot>\<^sub>m proj_basis d k) $$ (i, j))"
      using ij by (intro sum.mono_neutral_cong_right) (auto simp: proj_basis_def)
    also have "\<dots> = (Q $$ (0, 0) \<cdot>\<^sub>m 1\<^sub>m d) $$ (i, j)" using ij by (simp add: proj_basis_def)
    finally show "matrix_sum d (\<lambda>k. adjoint (proj_basis d k) * ?P k * proj_basis d k) d $$ (i, j) = (Q $$ (0, 0) \<cdot>\<^sub>m 1\<^sub>m d) $$ (i, j)" .
  next
    have "matrix_sum d (\<lambda>k. adjoint (proj_basis d k) * ?P k * proj_basis d k) d \<in> carrier_mat d d"
      by (rule matrix_sum_dim) (rule mult_carrier_mat[OF mult_carrier_mat[OF adjoint_dim[OF proj_basis_carrier]
          mult_carrier_mat[OF mult_carrier_mat[OF adjoint_dim[OF swap0_carrier] Qd] swap0_carrier]] proj_basis_carrier])
    thus "dim_row (matrix_sum d (\<lambda>k. adjoint (proj_basis d k) * ?P k * proj_basis d k) d) = dim_row (Q $$ (0, 0) \<cdot>\<^sub>m 1\<^sub>m d)"
      "dim_col (matrix_sum d (\<lambda>k. adjoint (proj_basis d k) * ?P k * proj_basis d k) d) = dim_col (Q $$ (0, 0) \<cdot>\<^sub>m 1\<^sub>m d)" by auto
  qed
  thus ?thesis using h by simp
qed

end

section \<open>Bridges to the library of the notes\<close>

lemma dagger_eq_adjoint: "Quantum.dagger A = mat_adjoint A"
  by (simp add: Quantum.dagger_def Complex_Matrix.adjoint_def conjugate_complex_def)

lemma unitary_bridge:
  assumes U: "U \<in> carrier_mat K K" and u: "Quantum.unitary U"
  shows "Complex_Matrix.unitary U"
  using U u unfolding Complex_Matrix.unitary_def Quantum.unitary_def inverts_mat_def dagger_eq_adjoint by auto

lemma inner_bridge: "dim_vec v = dim_vec w \<Longrightarrow> Complex_Matrix.inner_prod v w = Quantum.inner_prod v w"
  by (simp add: Quantum.inner_prod_def scalar_prod_def conjugate_vec_def mult.commute)

lemma circuit_mat_run:
  "(\<And>U. U \<in> set Us \<Longrightarrow> U \<in> carrier_mat K K) \<Longrightarrow> dim_vec v = K \<Longrightarrow> circuit_mat K Us *\<^sub>v v = run_gates v Us"
proof (induction Us arbitrary: v)
  case Nil
  thus ?case using carrier_vecI[of v K] by simp
next
  case (Cons U Us)
  have U: "U \<in> carrier_mat K K" using Cons.prems by simp
  have R: "circuit_mat K Us \<in> carrier_mat K K" by (rule circuit_mat_carrier) (use Cons.prems in auto)
  have "circuit_mat K (U # Us) *\<^sub>v v = circuit_mat K Us *\<^sub>v (U *\<^sub>v v)"
    using assoc_mult_mat_vec[OF R U carrier_vecI[OF Cons.prems(2)]] by simp
  also have "\<dots> = run_gates (U *\<^sub>v v) Us" by (rule Cons.IH) (use Cons.prems U in auto)
  finally show ?case by simp
qed

lemma assoc3_mult_vec:
  fixes A B E :: "complex Matrix.mat" and v :: "complex Matrix.vec" and n1 n2 n3 n4 :: nat
  assumes "A \<in> carrier_mat n1 n2" "B \<in> carrier_mat n2 n3" "E \<in> carrier_mat n3 n4" "v \<in> carrier_vec n4"
  shows "(A * B * E) *\<^sub>v v = A *\<^sub>v (B *\<^sub>v (E *\<^sub>v v))"
proof -
  have "(A * B * E) *\<^sub>v v = (A * B) *\<^sub>v (E *\<^sub>v v)" using assms by (intro assoc_mult_mat_vec) auto
  also have "\<dots> = A *\<^sub>v (B *\<^sub>v (E *\<^sub>v v))" using assms by (intro assoc_mult_mat_vec) auto
  finally show ?thesis .
qed

context state_sig
begin

text \<open>A gate sequence moves a pure state along its trajectory.\<close>

lemma hoare_run:
  assumes "\<And>U. U \<in> set Us \<Longrightarrow> U \<in> carrier_mat d d \<and> Complex_Matrix.unitary U"
    and "dim_vec \<psi> = d" "inner_prod \<psi> \<psi> = 1"
  shows "\<turnstile>\<^sub>p {outer_prod \<psi> \<psi>} utrans_seq Us {outer_prod (run_gates \<psi> Us) (run_gates \<psi> Us)}"
  using assms
proof (induction Us arbitrary: \<psi>)
  case Nil
  show ?case using hoare_partial.intros(1)[OF qp_pure[OF Nil.prems(2,3)]] by simp
next
  case (Cons U Us)
  have U: "U \<in> carrier_mat d d" "Complex_Matrix.unitary U" using Cons.prems by auto
  have d1: "dim_vec (U *\<^sub>v \<psi>) = d" using U(1) by simp
  have n1: "inner_prod (U *\<^sub>v \<psi>) (U *\<^sub>v \<psi>) = 1" using unitary_inner_keep[OF U Cons.prems(2)] Cons.prems(3) by simp
  have h1: "\<turnstile>\<^sub>p {outer_prod \<psi> \<psi>} Utrans U {outer_prod (U *\<^sub>v \<psi>) (U *\<^sub>v \<psi>)}" by (rule hoare_utrans_pure[OF U Cons.prems(2,3)])
  have h2: "\<turnstile>\<^sub>p {outer_prod (U *\<^sub>v \<psi>) (U *\<^sub>v \<psi>)} utrans_seq Us {outer_prod (run_gates (U *\<^sub>v \<psi>) Us) (run_gates (U *\<^sub>v \<psi>) Us)}"
    by (rule Cons.IH) (use Cons.prems d1 n1 in auto)
  have dr: "dim_vec (run_gates (U *\<^sub>v \<psi>) Us) = d" and nr: "inner_prod (run_gates (U *\<^sub>v \<psi>) Us) (run_gates (U *\<^sub>v \<psi>) Us) = 1"
  proof -
    have c: "circuit_mat d Us \<in> carrier_mat d d" by (rule circuit_mat_carrier) (use Cons.prems in auto)
    have cu: "Complex_Matrix.unitary (circuit_mat d Us)" by (rule circuit_mat_unitary) (use Cons.prems in auto)
    have e: "run_gates (U *\<^sub>v \<psi>) Us = circuit_mat d Us *\<^sub>v (U *\<^sub>v \<psi>)" by (rule circuit_mat_run[symmetric]) (use Cons.prems d1 in auto)
    show "dim_vec (run_gates (U *\<^sub>v \<psi>) Us) = d" unfolding e using c by simp
    show "inner_prod (run_gates (U *\<^sub>v \<psi>) Us) (run_gates (U *\<^sub>v \<psi>) Us) = 1" unfolding e unitary_inner_keep[OF c cu d1] by (rule n1)
  qed
  show ?case unfolding utrans_seq.simps run_gates.simps
    by (rule hoare_partial.intros(3)[OF qp_pure[OF Cons.prems(2,3)] qp_pure[OF d1 n1] qp_pure[OF dr nr] h1 h2])
qed

lemma inner_matrix_sum:
  fixes M :: "nat \<Rightarrow> complex Matrix.mat" and Q :: "complex Matrix.mat" and \<psi> :: "complex Matrix.vec"
  assumes M: "\<And>j. j < m \<Longrightarrow> M j \<in> carrier_mat d d" and Q: "Q \<in> carrier_mat d d" and \<psi>: "dim_vec \<psi> = d"
  shows "inner_prod \<psi> (matrix_sum d (\<lambda>j. adjoint (M j) * Q * M j) m *\<^sub>v \<psi>) = (\<Sum>j<m. inner_prod (M j *\<^sub>v \<psi>) (Q *\<^sub>v (M j *\<^sub>v \<psi>)))"
  using M
proof (induction m)
  case 0
  have "0\<^sub>m d d *\<^sub>v \<psi> = 0\<^sub>v d" using \<psi> by (intro eq_vecI) (simp_all add: scalar_prod_def)
  thus ?case using \<psi> by (simp add: scalar_prod_def)
next
  case (Suc m)
  have \<psi>c: "\<psi> \<in> carrier_vec d" using \<psi> by (rule carrier_vecI)
  have Mm: "M m \<in> carrier_mat d d" using Suc.prems by simp
  have Xj: "adjoint (M j) * Q * M j \<in> carrier_mat d d" if "j < Suc m" for j
    using Suc.prems[OF that] by (intro mult_carrier_mat[OF mult_carrier_mat[OF adjoint_dim Q]]) auto
  have X: "adjoint (M m) * Q * M m \<in> carrier_mat d d" by (rule Xj) simp
  have S: "matrix_sum d (\<lambda>j. adjoint (M j) * Q * M j) m \<in> carrier_mat d d"
    by (rule matrix_sum_dim) (rule Xj, simp)
  have "inner_prod \<psi> (matrix_sum d (\<lambda>j. adjoint (M j) * Q * M j) (Suc m) *\<^sub>v \<psi>)
        = inner_prod \<psi> ((adjoint (M m) * Q * M m) *\<^sub>v \<psi>) + inner_prod \<psi> (matrix_sum d (\<lambda>j. adjoint (M j) * Q * M j) m *\<^sub>v \<psi>)"
    using X S \<psi>c by (simp add: add_mult_distrib_mat_vec[OF X S \<psi>c] add_scalar_prod_distrib[of _ d])
  also have "inner_prod \<psi> ((adjoint (M m) * Q * M m) *\<^sub>v \<psi>) = inner_prod (M m *\<^sub>v \<psi>) (Q *\<^sub>v (M m *\<^sub>v \<psi>))"
  proof -
    have "(adjoint (M m) * Q * M m) *\<^sub>v \<psi> = adjoint (M m) *\<^sub>v (Q *\<^sub>v (M m *\<^sub>v \<psi>))"
      by (rule assoc3_mult_vec[OF adjoint_dim[OF Mm] Q Mm \<psi>c])
    moreover have "inner_prod \<psi> (adjoint (M m) *\<^sub>v (Q *\<^sub>v (M m *\<^sub>v \<psi>))) = inner_prod (adjoint (adjoint (M m)) *\<^sub>v \<psi>) (Q *\<^sub>v (M m *\<^sub>v \<psi>))"
      by (rule adjoint_def_alter[OF \<psi>c _ adjoint_dim[OF Mm]]) (use Mm Q \<psi>c in simp)
    ultimately show ?thesis by (simp add: adjoint_adjoint)
  qed
  finally show ?case using Suc by (simp add: add_ac)
qed

text \<open>A program that initialises, runs a circuit and measures: its precondition for $Q$ is
the probability-weighted value $\sum_j\langle\psi|M_j^*QM_j|\psi\rangle$ on the circuit output
$\psi=U\ket0$, times $I$.\<close>

theorem hoare_init_circuit_measure:
  assumes Q: "is_quantum_predicate Q" and d0: "0 < d"
    and Us: "\<And>U. U \<in> set Us \<Longrightarrow> U \<in> carrier_mat d d \<and> Complex_Matrix.unitary U"
    and M: "measurement d 2 M"
  defines "\<psi> \<equiv> circuit_mat d Us *\<^sub>v unit_vec d 0"
  shows "\<turnstile>\<^sub>p { (\<Sum>j<2. inner_prod (M j *\<^sub>v \<psi>) (Q *\<^sub>v (M j *\<^sub>v \<psi>))) \<cdot>\<^sub>m 1\<^sub>m d}
           init_com d ;; utrans_seq Us ;; Measure 2 M [SKIP, SKIP] {Q}"
proof -
  let ?PM = "matrix_sum d (\<lambda>j. adjoint (M j) * Q * M j) 2" and ?C = "circuit_mat d Us"
  have Qd: "Q \<in> carrier_mat d d" using Q unfolding is_quantum_predicate_def by simp
  have Mj: "M j \<in> carrier_mat d d" if "j < 2" for j using M that unfolding measurement_def by simp
  have C: "?C \<in> carrier_mat d d" by (rule circuit_mat_carrier) (use Us in auto)
  have Cu: "Complex_Matrix.unitary ?C" by (rule circuit_mat_unitary[OF Us])
  have qPM: "is_quantum_predicate ?PM" by (rule qps_after_measure_is_qp[OF M]) (use Q in simp)
  have hm: "\<turnstile>\<^sub>p {?PM} Measure 2 M [SKIP, SKIP] {Q}"
  proof -
    have "\<turnstile>\<^sub>p {Q} [SKIP, SKIP] ! j {Q}" if "j < 2" for j
      using that hoare_partial.intros(1)[OF Q] by (cases j) auto
    thus ?thesis using hoare_partial.intros(4)[of 2 "\<lambda>_. Q" Q "[SKIP, SKIP]" M] Q by auto
  qed
  have qR: "is_quantum_predicate (adjoint ?C * ?PM * ?C)" by (rule qp_close_under_unitary_operator[OF C Cu qPM])
  have hc: "\<turnstile>\<^sub>p {adjoint ?C * ?PM * ?C} utrans_seq Us {?PM}" by (rule hoare_utrans_seq[OF Us qPM])
  have hi: "\<turnstile>\<^sub>p {(adjoint ?C * ?PM * ?C) $$ (0, 0) \<cdot>\<^sub>m 1\<^sub>m d} init_com d {adjoint ?C * ?PM * ?C}"
    by (rule hoare_init[OF qR d0])
  have q0: "is_quantum_predicate ((adjoint ?C * ?PM * ?C) $$ (0, 0) \<cdot>\<^sub>m 1\<^sub>m d)"
    using qp_diag[OF qR d0] by (intro qp_scalar) auto
  have val: "(adjoint ?C * ?PM * ?C) $$ (0, 0) = (\<Sum>j<2. inner_prod (M j *\<^sub>v \<psi>) (Q *\<^sub>v (M j *\<^sub>v \<psi>)))"
  proof -
    have PMc: "?PM \<in> carrier_mat d d" using qPM unfolding is_quantum_predicate_def by simp
    have e0: "unit_vec d 0 \<in> carrier_vec d" by simp
    have \<psi>c: "\<psi> \<in> carrier_vec d" unfolding \<psi>_def using C by simp
    have "(adjoint ?C * ?PM * ?C) $$ (0, 0) = inner_prod (unit_vec d 0) ((adjoint ?C * ?PM * ?C) *\<^sub>v unit_vec d 0)"
      by (rule unit_vec_bracket[symmetric]) (use C PMc d0 in \<open>auto intro: mult_carrier_mat adjoint_dim\<close>)
    also have "(adjoint ?C * ?PM * ?C) *\<^sub>v unit_vec d 0 = adjoint ?C *\<^sub>v (?PM *\<^sub>v \<psi>)"
      unfolding \<psi>_def by (rule assoc3_mult_vec[OF adjoint_dim[OF C] PMc C e0])
    also have "inner_prod (unit_vec d 0) (adjoint ?C *\<^sub>v (?PM *\<^sub>v \<psi>)) = inner_prod (adjoint (adjoint ?C) *\<^sub>v unit_vec d 0) (?PM *\<^sub>v \<psi>)"
      by (rule adjoint_def_alter[OF e0 _ adjoint_dim[OF C]]) (use PMc \<psi>c in simp)
    also have "adjoint (adjoint ?C) *\<^sub>v unit_vec d 0 = \<psi>" unfolding \<psi>_def by (simp add: adjoint_adjoint)
    also have "inner_prod \<psi> (?PM *\<^sub>v \<psi>) = (\<Sum>j<2. inner_prod (M j *\<^sub>v \<psi>) (Q *\<^sub>v (M j *\<^sub>v \<psi>)))"
      by (rule inner_matrix_sum[OF Mj Qd carrier_vecD[OF \<psi>c]])
    finally show ?thesis .
  qed
  have "\<turnstile>\<^sub>p {(adjoint ?C * ?PM * ?C) $$ (0, 0) \<cdot>\<^sub>m 1\<^sub>m d} init_com d ;; utrans_seq Us {?PM}"
    by (rule hoare_partial.intros(3)[OF q0 qR qPM hi hc])
  hence "\<turnstile>\<^sub>p {(adjoint ?C * ?PM * ?C) $$ (0, 0) \<cdot>\<^sub>m 1\<^sub>m d} init_com d ;; utrans_seq Us ;; Measure 2 M [SKIP, SKIP] {Q}"
    by (rule hoare_partial.intros(3)[OF q0 qPM Q _ hm])
  thus ?thesis unfolding val .
qed

text \<open>Without the final measurement: $\{\langle\psi|R|\psi\rangle\,I\}\ \mathit{init};U\ \{R\}$.\<close>

theorem hoare_init_circuit:
  assumes Rp: "is_quantum_predicate Rp" and d0: "0 < d"
    and Us: "\<And>U. U \<in> set Us \<Longrightarrow> U \<in> carrier_mat d d \<and> Complex_Matrix.unitary U"
  defines "\<psi> \<equiv> circuit_mat d Us *\<^sub>v unit_vec d 0"
  shows "\<turnstile>\<^sub>p {inner_prod \<psi> (Rp *\<^sub>v \<psi>) \<cdot>\<^sub>m 1\<^sub>m d} init_com d ;; utrans_seq Us {Rp}"
proof -
  let ?C = "circuit_mat d Us"
  have Rd: "Rp \<in> carrier_mat d d" using Rp unfolding is_quantum_predicate_def by simp
  have C: "?C \<in> carrier_mat d d" by (rule circuit_mat_carrier) (use Us in auto)
  have Cu: "Complex_Matrix.unitary ?C" by (rule circuit_mat_unitary[OF Us])
  have qR: "is_quantum_predicate (adjoint ?C * Rp * ?C)" by (rule qp_close_under_unitary_operator[OF C Cu Rp])
  have hc: "\<turnstile>\<^sub>p {adjoint ?C * Rp * ?C} utrans_seq Us {Rp}" by (rule hoare_utrans_seq[OF Us Rp])
  have hi: "\<turnstile>\<^sub>p {(adjoint ?C * Rp * ?C) $$ (0, 0) \<cdot>\<^sub>m 1\<^sub>m d} init_com d {adjoint ?C * Rp * ?C}" by (rule hoare_init[OF qR d0])
  have q0: "is_quantum_predicate ((adjoint ?C * Rp * ?C) $$ (0, 0) \<cdot>\<^sub>m 1\<^sub>m d)"
    using qp_diag[OF qR d0] by (intro qp_scalar) auto
  have val: "(adjoint ?C * Rp * ?C) $$ (0, 0) = inner_prod \<psi> (Rp *\<^sub>v \<psi>)"
  proof -
    have e0: "unit_vec d 0 \<in> carrier_vec d" by simp
    have \<psi>c: "\<psi> \<in> carrier_vec d" unfolding \<psi>_def using C by simp
    have "(adjoint ?C * Rp * ?C) $$ (0, 0) = inner_prod (unit_vec d 0) ((adjoint ?C * Rp * ?C) *\<^sub>v unit_vec d 0)"
      by (rule unit_vec_bracket[symmetric]) (use C Rd d0 in \<open>auto intro: mult_carrier_mat adjoint_dim\<close>)
    also have "(adjoint ?C * Rp * ?C) *\<^sub>v unit_vec d 0 = adjoint ?C *\<^sub>v (Rp *\<^sub>v \<psi>)"
      unfolding \<psi>_def by (rule assoc3_mult_vec[OF adjoint_dim[OF C] Rd C e0])
    also have "inner_prod (unit_vec d 0) (adjoint ?C *\<^sub>v (Rp *\<^sub>v \<psi>)) = inner_prod (adjoint (adjoint ?C) *\<^sub>v unit_vec d 0) (Rp *\<^sub>v \<psi>)"
      by (rule adjoint_def_alter[OF e0 _ adjoint_dim[OF C]]) (use Rd \<psi>c in simp)
    also have "adjoint (adjoint ?C) *\<^sub>v unit_vec d 0 = \<psi>" unfolding \<psi>_def by (simp add: adjoint_adjoint)
    finally show ?thesis .
  qed
  show ?thesis using hoare_partial.intros(3)[OF q0 qR Rp hi hc] unfolding val .
qed

end

section \<open>The HHL program\<close>

text \<open>Measuring the ancilla (the lowest qubit): $P_j$ projects onto ancilla value $j$.\<close>

definition anc_proj :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
  "anc_proj K j = Matrix.mat K K (\<lambda>(r, s). if r = s \<and> r mod 2 = j then 1 else 0)"

lemma anc_proj_carrier [simp]: "anc_proj K j \<in> carrier_mat K K" by (simp add: anc_proj_def)

lemma anc_proj_adjoint: "adjoint (anc_proj K j) = anc_proj K j"
  by (rule eq_matI) (auto simp: anc_proj_def adjoint_eval)

lemma anc_proj_mult_vec: "dim_vec v = K \<Longrightarrow> anc_proj K j *\<^sub>v v = Matrix.vec K (\<lambda>r. if r mod 2 = j then v $ r else 0)"
proof (rule eq_vecI)
  fix r assume v: "dim_vec v = K" and "r < dim_vec (Matrix.vec K (\<lambda>r. if r mod 2 = j then v $ r else 0))"
  hence r: "r < K" by simp
  have "(anc_proj K j *\<^sub>v v) $ r = (\<Sum>s<K. (if r = s \<and> r mod 2 = j then 1 else 0) * v $ s)"
    using r v by (simp add: anc_proj_def scalar_prod_def atLeast0LessThan)
  also have "\<dots> = (\<Sum>s\<in>{r}. (if r = s \<and> r mod 2 = j then 1 else 0) * v $ s)" using r by (intro sum.mono_neutral_cong_right) auto
  finally show "(anc_proj K j *\<^sub>v v) $ r = Matrix.vec K (\<lambda>r. if r mod 2 = j then v $ r else 0) $ r" using r by simp
qed (simp add: anc_proj_def)

lemma anc_proj_square: "anc_proj K j * anc_proj K j = anc_proj K j"
proof (rule eq_matI)
  fix r s assume "r < dim_row (anc_proj K j)" "s < dim_col (anc_proj K j)"
  hence rs: "r < K" "s < K" by (simp_all add: anc_proj_def)
  have "(anc_proj K j * anc_proj K j) $$ (r, s) = (\<Sum>l<K. (if r = l \<and> r mod 2 = j then 1 else 0) * (if l = s \<and> l mod 2 = j then 1 else 0))"
    using rs by (simp add: anc_proj_def scalar_prod_def atLeast0LessThan)
  also have "\<dots> = (\<Sum>l\<in>{r}. (if r = l \<and> r mod 2 = j then 1 else 0) * (if l = s \<and> l mod 2 = j then 1 else 0))"
    using rs by (intro sum.mono_neutral_cong_right) auto
  finally show "(anc_proj K j * anc_proj K j) $$ (r, s) = anc_proj K j $$ (r, s)" using rs by (simp add: anc_proj_def)
qed (simp_all add: anc_proj_def)

lemma anc_proj_sum: "anc_proj K 0 + anc_proj K 1 = 1\<^sub>m K"
  by (rule eq_matI) (auto simp: anc_proj_def)

lemma anc_proj_measurement: "measurement K 2 (anc_proj K)"
proof -
  have "matrix_sum K (\<lambda>j. adjoint (anc_proj K j) * anc_proj K j) 2 = anc_proj K 1 + (anc_proj K 0 + 0\<^sub>m K K)"
    by (simp add: numeral_2_eq_2 anc_proj_adjoint anc_proj_square)
  also have "\<dots> = 1\<^sub>m K" by (rule eq_matI) (auto simp: anc_proj_def)
  finally show ?thesis unfolding measurement_def by simp
qed

lemma anc_proj_swap_measurement: "measurement K 2 (\<lambda>j. anc_proj K (1 - j))"
proof -
  have "matrix_sum K (\<lambda>j. adjoint (anc_proj K (1 - j)) * anc_proj K (1 - j)) 2 = anc_proj K 0 + (anc_proj K 1 + 0\<^sub>m K K)"
    by (simp add: numeral_2_eq_2 anc_proj_adjoint anc_proj_square)
  also have "\<dots> = 1\<^sub>m K" by (rule eq_matI) (auto simp: anc_proj_def)
  finally show ?thesis unfolding measurement_def by simp
qed

text \<open>On $a\otimes g\otimes\ket i$ the projector $P_j$ keeps the vector iff $i=j$.\<close>

lemma anc_proj_tensor:
  assumes a: "dim_vec a = N" and g: "dim_vec g = n" and i: "i < 2"
  shows "anc_proj (N * (n * 2)) j *\<^sub>v tensor_vec a (tensor_vec g (unit_vec 2 i))
         = (if i = j then tensor_vec a (tensor_vec g (unit_vec 2 i)) else 0\<^sub>v (N * (n * 2)))"
proof -
  let ?v = "tensor_vec a (tensor_vec g (unit_vec 2 i))"
  have dg: "dim_vec (tensor_vec g (unit_vec 2 i)) = n * 2" by (simp add: tensor_vec_dim g)
  have dv: "dim_vec ?v = N * (n * 2)" by (simp add: tensor_vec_dim a dg)
  have entry: "?v $ r = 0" if r: "r < N * (n * 2)" "r mod 2 \<noteq> i" for r
  proof -
    have q: "r mod (n * 2) < n * 2" using r(1) by (cases "n * 2") auto
    have m: "r mod (n * 2) mod 2 = r mod 2" by (simp add: mod_mod_cancel)
    have "?v $ r = a $ (r div (n * 2)) * tensor_vec g (unit_vec 2 i) $ (r mod (n * 2))"
      by (rule tensor_vec_index[OF a dg r(1)])
    also have "tensor_vec g (unit_vec 2 i) $ (r mod (n * 2)) = g $ (r mod (n * 2) div 2) * unit_vec 2 i $ (r mod (n * 2) mod 2)"
      by (rule tensor_vec_index[OF g _ q]) simp
    also have "unit_vec 2 i $ (r mod (n * 2) mod 2) = 0" using r(2) m by (simp add: unit_vec_def)
    finally show ?thesis by simp
  qed
  show ?thesis
  proof (rule eq_vecI)
    fix r assume "r < dim_vec (if i = j then ?v else 0\<^sub>v (N * (n * 2)))"
    hence r: "r < N * (n * 2)" using dv by (cases "i = j") simp_all
    have "(anc_proj (N * (n * 2)) j *\<^sub>v ?v) $ r = (if r mod 2 = j then ?v $ r else 0)"
      using r by (simp add: anc_proj_mult_vec[OF dv])
    also have "\<dots> = (if i = j then ?v else 0\<^sub>v (N * (n * 2))) $ r"
      using r entry[OF r] by (cases "r mod 2 = i"; cases "i = j") auto
    finally show "(anc_proj (N * (n * 2)) j *\<^sub>v ?v) $ r = (if i = j then ?v else 0\<^sub>v (N * (n * 2))) $ r" .
  qed (use dv in \<open>auto simp: anc_proj_def\<close>)
qed

context state_sig
begin

lemma qp_anc_proj: "is_quantum_predicate (anc_proj d j)"
proof -
  have p: "positive (anc_proj d i)" for i
    by (rule positive_if_decomp[OF anc_proj_carrier]) (rule exI[of _ "anc_proj d i"], simp add: anc_proj_adjoint anc_proj_square)
  have "1\<^sub>m d - anc_proj d j = anc_proj d (1 - j)" if "j < 2"
  proof (cases "j = 0")
    case True
    thus ?thesis by (intro eq_matI) (auto simp: anc_proj_def)
  next
    case False
    hence "j = 1" using that by simp
    thus ?thesis by (intro eq_matI) (auto simp: anc_proj_def)
  qed
  moreover have "1\<^sub>m d - anc_proj d j = 1\<^sub>m d" if "\<not> j < 2"
    using that by (intro eq_matI) (auto simp: anc_proj_def)
  ultimately have "positive (1\<^sub>m d - anc_proj d j)" using p positive_one by (cases "j < 2") auto
  thus ?thesis using p unfolding is_quantum_predicate_def lowner_le_def by (simp add: anc_proj_def)
qed

end

lemma unit_vec_tensor: "tensor_vec (unit_vec N 0) (unit_vec m 0) = unit_vec (N * m) 0"
proof (rule eq_vecI)
  fix r assume "r < dim_vec (unit_vec (N * m) 0)"
  hence r: "r < N * m" by simp
  have m: "0 < m" using r by (cases m) auto
  have "tensor_vec (unit_vec N 0) (unit_vec m 0) $ r = unit_vec N 0 $ (r div m) * unit_vec m 0 $ (r mod m)"
    using tensor_vec_index[of "unit_vec N 0" N "unit_vec m 0" m r] r by simp
  also have "\<dots> = unit_vec (N * m) 0 $ r"
  proof -
    have "r div m = 0 \<and> r mod m = 0 \<longleftrightarrow> r = 0" by (metis div_mult_mod_eq mult_0_right add_0 div_0 mod_0)
    moreover have "r div m < N" using r by (simp add: less_mult_imp_div_less)
    ultimately show ?thesis using r m by (auto simp: unit_vec_def)
  qed
  finally show "tensor_vec (unit_vec N 0) (unit_vec m 0) $ r = unit_vec (N * m) 0 $ r" .
qed (simp add: tensor_vec_dim)

text \<open>The programs for any gate list \<open>Us\<close>: initialise, run \<open>Us\<close>, measure the ancilla; or repeat
while the ancilla reads $0$.\<close>

definition hhl_prog :: "nat \<Rightarrow> complex Matrix.mat list \<Rightarrow> com" where
  "hhl_prog K Us = init_com K ;; utrans_seq Us ;; Measure 2 (anc_proj K) [SKIP, SKIP]"

definition hhl_rus_prog :: "nat \<Rightarrow> complex Matrix.mat list \<Rightarrow> com" where
  "hhl_rus_prog K Us = init_com K ;; utrans_seq Us ;; While (\<lambda>j. anc_proj K (1 - j)) (init_com K ;; utrans_seq Us)"

definition hhl_program :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> com" where
  "hhl_program A Ub t0 k C = hhl_prog (2 ^ k * (dim_row A * 2)) (hhl_gates A Ub t0 k C)"

definition hhl_rus :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> com" where
  "hhl_rus A Ub t0 k C = hhl_rus_prog (2 ^ k * (dim_row A * 2)) (hhl_gates A Ub t0 k C)"

text \<open>The solution state $\ket0\otimes\hat x\otimes\ket1$, $\hat x=A^{-1}b/\norm{A^{-1}b}$.\<close>

definition hhl_target :: "complex Matrix.mat \<Rightarrow> nat \<Rightarrow> complex Matrix.vec \<Rightarrow> complex Matrix.vec" where
  "hhl_target A k b = tensor_vec (unit_vec (2 ^ k) 0)
     (tensor_vec (complex_of_real (1 / \<parallel>herm_inv A *\<^sub>v b\<parallel>) \<cdot>\<^sub>v (herm_inv A *\<^sub>v b)) (unit_vec 2 1))"

context
  fixes A Ub :: "complex Matrix.mat" and b :: "complex Matrix.vec" and n k :: nat and t0 C :: real
  assumes A: "A \<in> carrier_mat n n" "Quantum_Computing_3_10.hermitian A" and n0: "0 < n" and k: "1 \<le> k" and t0: "0 < t0"
    and spec: "\<And>l. l \<in> herm_spectrum A \<Longrightarrow> \<exists>j. 0 < j \<and> j < 2 ^ k \<and> l = reg_eig t0 (2 ^ k) j"
    and Ub: "Ub \<in> carrier_mat n n" "Quantum.unitary Ub" "Ub *\<^sub>v unit_vec n 0 = b"
    and Cb: "\<And>j. j < 2 ^ k \<Longrightarrow> \<bar>C / reg_eig t0 (2 ^ k) j\<bar> \<le> 1"
begin

lemma mat_fun_dims [simp]: "dim_row (mat_fun g A) = n" "dim_col (mat_fun g A) = n"
  using mat_fun_carrier[OF A] by auto

lemma herm_inv_dims [simp]: "dim_row (herm_inv A) = n" "dim_col (herm_inv A) = n"
  using mat_fun_carrier[OF A] unfolding herm_inv_def by auto

lemma prog_d: "state_sig.d [2 ^ k, n, 2] = 2 ^ k * (n * 2)" by (simp add: state_sig.d_def)

lemma prog_gates: "U \<in> set (hhl_gates A Ub t0 k C) \<Longrightarrow> U \<in> carrier_mat (2 ^ k * (n * 2)) (2 ^ k * (n * 2)) \<and> Complex_Matrix.unitary U"
  using hhl_gates_unitary[OF A n0 k t0 spec Ub Cb] unitary_bridge by blast

lemma prog_out: "circuit_mat (2 ^ k * (n * 2)) (hhl_gates A Ub t0 k C) *\<^sub>v unit_vec (2 ^ k * (n * 2)) 0
                 = tensor_vec (unit_vec (2 ^ k) 0) (hhl_out A C b)"
proof -
  have "circuit_mat (2 ^ k * (n * 2)) (hhl_gates A Ub t0 k C) *\<^sub>v unit_vec (2 ^ k * (n * 2)) 0
        = run_gates (unit_vec (2 ^ k * (n * 2)) 0) (hhl_gates A Ub t0 k C)"
    by (rule circuit_mat_run) (use prog_gates in auto)
  also have "\<dots> = tensor_vec (unit_vec (2 ^ k) 0) (hhl_out A C b)"
    unfolding unit_vec_tensor[symmetric] by (rule hhl_run[OF A n0 k t0 spec Ub])
  finally show ?thesis .
qed

lemma unit2_norm: "i < 2 \<Longrightarrow> \<parallel>unit_vec 2 i\<parallel> = 1"
  by (auto simp: cpx_vec_length_def numeral_2_eq_2 lessThan_Suc unit_vec_def)

lemma unitN_norm: "\<parallel>unit_vec (2 ^ k) 0\<parallel> = 1"
  by (simp add: cpx_vec_length_def lessThan_atLeast0 sum.atLeast_Suc_lessThan unit_vec_def)

text \<open>The two ancilla branches of the final state $\ket0\otimes\mathrm{out}$.\<close>

lemma prog_branch:
  defines "g0 \<equiv> mat_fun (\<lambda>x. complex_of_real (sqrt (1 - (C / x)\<^sup>2))) A *\<^sub>v b"
    and "g1 \<equiv> (complex_of_real C \<cdot>\<^sub>m herm_inv A) *\<^sub>v b"
  shows "anc_proj (2 ^ k * (n * 2)) 0 *\<^sub>v tensor_vec (unit_vec (2 ^ k) 0) (hhl_out A C b) = tensor_vec (unit_vec (2 ^ k) 0) (tensor_vec g0 (unit_vec 2 0))"
    and "anc_proj (2 ^ k * (n * 2)) 1 *\<^sub>v tensor_vec (unit_vec (2 ^ k) 0) (hhl_out A C b) = tensor_vec (unit_vec (2 ^ k) 0) (tensor_vec g1 (unit_vec 2 1))"
    and "dim_vec g0 = n" "dim_vec g1 = n"
proof -
  have Hc: "herm_inv A \<in> carrier_mat n n" unfolding herm_inv_def by (rule mat_fun_carrier[OF A])
  have Gc: "mat_fun (\<lambda>x. complex_of_real (sqrt (1 - (C / x)\<^sup>2))) A \<in> carrier_mat n n" by (rule mat_fun_carrier[OF A])
  have bd: "dim_vec b = n" using Ub by auto
  show d0: "dim_vec g0 = n" and d1: "dim_vec g1 = n" unfolding g0_def g1_def using Hc Gc bd by simp_all
  let ?a = "unit_vec (2 ^ k) 0"
  have sp: "tensor_vec ?a (hhl_out A C b) = tensor_vec ?a (tensor_vec g0 (unit_vec 2 0)) + tensor_vec ?a (tensor_vec g1 (unit_vec 2 1))"
    unfolding hhl_out_def g0_def[symmetric] g1_def[symmetric]
    by (rule tensor_vec_bilinear_right) (simp_all add: tensor_vec_dim d0 d1)
  have c0: "tensor_vec ?a (tensor_vec g0 (unit_vec 2 0)) \<in> carrier_vec (2 ^ k * (n * 2))"
    by (rule carrier_vecI) (simp add: tensor_vec_dim d0)
  have c1: "tensor_vec ?a (tensor_vec g1 (unit_vec 2 1)) \<in> carrier_vec (2 ^ k * (n * 2))"
    by (rule carrier_vecI) (simp add: tensor_vec_dim d1)
  have P: "anc_proj (2 ^ k * (n * 2)) j *\<^sub>v tensor_vec ?a (hhl_out A C b)
           = anc_proj (2 ^ k * (n * 2)) j *\<^sub>v tensor_vec ?a (tensor_vec g0 (unit_vec 2 0))
           + anc_proj (2 ^ k * (n * 2)) j *\<^sub>v tensor_vec ?a (tensor_vec g1 (unit_vec 2 1))" for j
    unfolding sp by (rule mult_add_distrib_mat_vec[OF anc_proj_carrier c0 c1])
  show "anc_proj (2 ^ k * (n * 2)) 0 *\<^sub>v tensor_vec ?a (hhl_out A C b) = tensor_vec ?a (tensor_vec g0 (unit_vec 2 0))"
    unfolding P using anc_proj_tensor[of ?a "2 ^ k" g0 n 0 0] anc_proj_tensor[of ?a "2 ^ k" g1 n 1 0] d0 d1 c0 by simp
  show "anc_proj (2 ^ k * (n * 2)) 1 *\<^sub>v tensor_vec ?a (hhl_out A C b) = tensor_vec ?a (tensor_vec g1 (unit_vec 2 1))"
    unfolding P using anc_proj_tensor[of ?a "2 ^ k" g0 n 0 1] anc_proj_tensor[of ?a "2 ^ k" g1 n 1 1] d0 d1 c1 by simp
qed

text \<open>Success probability: the ancilla reads $1$ with probability at least $C^2\norm{A^{-1}b}^2$.
The theorems hold for every gate list with the circuit of \<open>hhl_gates\<close>.\<close>

theorem hhl_prog_success:
  assumes Us: "\<And>U. U \<in> set Us \<Longrightarrow> U \<in> carrier_mat (2 ^ k * (n * 2)) (2 ^ k * (n * 2)) \<and> Complex_Matrix.unitary U"
      and circ: "circuit_mat (2 ^ k * (n * 2)) Us = circuit_mat (2 ^ k * (n * 2)) (hhl_gates A Ub t0 k C)"
  shows "state_sig.hoare_partial [2 ^ k, n, 2] (complex_of_real (C\<^sup>2 * \<parallel>herm_inv A *\<^sub>v b\<parallel>\<^sup>2) \<cdot>\<^sub>m 1\<^sub>m (2 ^ k * (n * 2)))
     (hhl_prog (2 ^ k * (n * 2)) Us) (anc_proj (2 ^ k * (n * 2)) 1)"
proof -
  interpret state_sig "[2 ^ k, n, 2]" .
  let ?D = "2 ^ k * (n * 2)" and ?a = "unit_vec (2 ^ k) 0"
  let ?g0 = "mat_fun (\<lambda>x. complex_of_real (sqrt (1 - (C / x)\<^sup>2))) A *\<^sub>v b" and ?g1 = "(complex_of_real C \<cdot>\<^sub>m herm_inv A) *\<^sub>v b"
  let ?\<psi> = "tensor_vec ?a (hhl_out A C b)"
  have dd: "d = ?D" by (simp add: d_def)
  have nA: "dim_row A = n" using A(1) by simp
  have h: "hoare_partial ((\<Sum>j<2. inner_prod (anc_proj d j *\<^sub>v (circuit_mat d Us *\<^sub>v unit_vec d 0))
                 (anc_proj d 1 *\<^sub>v (anc_proj d j *\<^sub>v (circuit_mat d Us *\<^sub>v unit_vec d 0)))) \<cdot>\<^sub>m 1\<^sub>m d)
             (init_com d ;; utrans_seq Us ;; Measure 2 (anc_proj d) [SKIP, SKIP]) (anc_proj d 1)"
    by (rule hoare_init_circuit_measure[OF qp_anc_proj _ _ anc_proj_measurement]) (use Us dd n0 in auto)
  have w1: "anc_proj ?D 1 *\<^sub>v tensor_vec ?a (tensor_vec ?g1 (unit_vec 2 1)) = tensor_vec ?a (tensor_vec ?g1 (unit_vec 2 1))"
    using anc_proj_tensor[of ?a "2 ^ k" ?g1 n 1 1] prog_branch(4) by simp
  have w0: "anc_proj ?D 1 *\<^sub>v tensor_vec ?a (tensor_vec ?g0 (unit_vec 2 0)) = 0\<^sub>v ?D"
    using anc_proj_tensor[of ?a "2 ^ k" ?g0 n 0 1] prog_branch(3) by simp
  have val: "(\<Sum>j<2. inner_prod (anc_proj ?D j *\<^sub>v ?\<psi>) (anc_proj ?D 1 *\<^sub>v (anc_proj ?D j *\<^sub>v ?\<psi>)))
             = complex_of_real (C\<^sup>2 * \<parallel>herm_inv A *\<^sub>v b\<parallel>\<^sup>2)"
  proof -
    let ?w = "tensor_vec ?a (tensor_vec ?g1 (unit_vec 2 1))"
    have dw: "dim_vec ?w = ?D" by (simp add: tensor_vec_dim prog_branch(4))
    have "inner_prod ?w ?w = \<langle>?w|?w\<rangle>" by (rule inner_bridge) simp
    also have "\<dots> = complex_of_real (\<parallel>?w\<parallel>\<^sup>2)" by (rule cpx_vec_length_inner_prod[symmetric])
    also have "\<parallel>?w\<parallel> = \<parallel>?g1\<parallel>"
      using unitN_norm unit2_norm[of 1] prog_branch(4) by (simp add: vnorm_tensor tensor_vec_dim)
    also have "\<parallel>?g1\<parallel> = \<bar>C\<bar> * \<parallel>herm_inv A *\<^sub>v b\<parallel>"
    proof -
      have Hc: "herm_inv A \<in> carrier_mat n n" unfolding herm_inv_def by (rule mat_fun_carrier[OF A])
      have "?g1 = complex_of_real C \<cdot>\<^sub>v (herm_inv A *\<^sub>v b)" using Ub by (intro smult_mat_mult_vec[OF Hc]) auto
      thus ?thesis by (simp add: cpx_vec_length_smult)
    qed
    finally have i1: "inner_prod ?w ?w = complex_of_real (C\<^sup>2 * \<parallel>herm_inv A *\<^sub>v b\<parallel>\<^sup>2)" by (simp add: power_mult_distrib)
    have dw0: "dim_vec (tensor_vec ?a (tensor_vec ?g0 (unit_vec 2 0))) = ?D" by (simp add: tensor_vec_dim prog_branch(3))
    have cc: "conjugate (tensor_vec ?a (tensor_vec ?g0 (unit_vec 2 0))) \<in> carrier_vec ?D" by (rule carrier_vecI) (simp add: dw0)
    have i0: "inner_prod (tensor_vec ?a (tensor_vec ?g0 (unit_vec 2 0))) (0\<^sub>v ?D) = 0"
      unfolding conjugate_scalar_prod by (rule scalar_prod_left_zero[OF cc])
    have s2: "(\<Sum>j<2. F j) = F 0 + F 1" for F :: "nat \<Rightarrow> complex" by (simp add: numeral_2_eq_2)
    show ?thesis unfolding s2 prog_branch(1) prog_branch(2) w0 w1 i0 i1 by simp
  qed
  show ?thesis using h unfolding dd circ prog_out val hhl_prog_def .
qed

theorem hhl_success:
  "state_sig.hoare_partial [2 ^ k, n, 2] (complex_of_real (C\<^sup>2 * \<parallel>herm_inv A *\<^sub>v b\<parallel>\<^sup>2) \<cdot>\<^sub>m 1\<^sub>m (2 ^ k * (n * 2)))
     (hhl_program A Ub t0 k C) (anc_proj (2 ^ k * (n * 2)) 1)"
  unfolding hhl_program_def carrier_matD(1)[OF A(1)]
  by (rule hhl_prog_success[where Us = "hhl_gates A Ub t0 k C", OF prog_gates refl])

lemma sol_nonzero: "0 < \<parallel>herm_inv A *\<^sub>v b\<parallel>"
proof -
  have bd: "dim_vec b = n" using Ub by auto
  have nb: "\<parallel>b\<parallel> = 1"
  proof -
    have "\<parallel>b\<parallel> = \<parallel>unit_vec n 0\<parallel>" using unitary_vnorm[OF Ub(1,2), of "unit_vec n 0"] Ub(3) by simp
    thus ?thesis using n0 by (simp add: cpx_vec_length_def lessThan_atLeast0 sum.atLeast_Suc_lessThan unit_vec_def)
  qed
  have Ax: "A *\<^sub>v (herm_inv A *\<^sub>v b) = b" by (rule hhl_solution(1)[OF A t0 _ spec bd]) simp
  have "herm_inv A *\<^sub>v b \<noteq> 0\<^sub>v n"
  proof
    assume "herm_inv A *\<^sub>v b = 0\<^sub>v n"
    hence "b = 0\<^sub>v n" using Ax A(1) by (metis mult_zero_vec_right)
    moreover have "\<parallel>0\<^sub>v n\<parallel> = 0" by (simp add: cpx_vec_length_def)
    ultimately show False using nb by simp
  qed
  moreover have "dim_vec (herm_inv A *\<^sub>v b) = n" by simp
  ultimately have "\<parallel>herm_inv A *\<^sub>v b\<parallel> \<noteq> 0" using cpx_vec_length_zero_iff[of "herm_inv A *\<^sub>v b"] by simp
  thus ?thesis using vnorm_ge0[of "herm_inv A *\<^sub>v b"] by linarith
qed

lemma target_dim: "dim_vec (hhl_target A k b) = 2 ^ k * (n * 2)"
  using Ub by (simp add: hhl_target_def tensor_vec_dim)

lemma target_unit: "inner_prod (hhl_target A k b) (hhl_target A k b) = 1"
proof -
  let ?x = "herm_inv A *\<^sub>v b"
  have dx: "dim_vec ?x = n" by simp
  have "\<parallel>hhl_target A k b\<parallel> = \<parallel>complex_of_real (1 / \<parallel>?x\<parallel>) \<cdot>\<^sub>v ?x\<parallel>"
    unfolding hhl_target_def using unitN_norm unit2_norm[of 1] by (simp add: vnorm_tensor tensor_vec_dim)
  also have "\<dots> = 1" using sol_nonzero by (simp add: cpx_vec_length_smult norm_divide)
  finally have "\<parallel>hhl_target A k b\<parallel> = 1" .
  hence "\<langle>hhl_target A k b|hhl_target A k b\<rangle> = 1" using cpx_vec_length_inner_prod[of "hhl_target A k b"] by simp
  thus ?thesis using inner_bridge[of "hhl_target A k b" "hhl_target A k b"] by simp
qed

lemma inner3:
  assumes "dim_vec a1 = 2 ^ k" "dim_vec a2 = 2 ^ k" "dim_vec u = n" "dim_vec v = n" "dim_vec e1 = 2" "dim_vec e2 = 2"
  shows "inner_prod (tensor_vec a1 (tensor_vec u e1)) (tensor_vec a2 (tensor_vec v e2)) = \<langle>a1|a2\<rangle> * (\<langle>u|v\<rangle> * \<langle>e1|e2\<rangle>)"
proof -
  have "inner_prod (tensor_vec a1 (tensor_vec u e1)) (tensor_vec a2 (tensor_vec v e2)) = \<langle>tensor_vec a1 (tensor_vec u e1)|tensor_vec a2 (tensor_vec v e2)\<rangle>"
    by (rule inner_bridge) (use assms in \<open>simp add: tensor_vec_dim\<close>)
  also have "\<dots> = \<langle>a1|a2\<rangle> * \<langle>tensor_vec u e1|tensor_vec v e2\<rangle>"
    by (rule tensor_inner_prod) (use assms in \<open>simp_all add: tensor_vec_dim\<close>)
  also have "\<langle>tensor_vec u e1|tensor_vec v e2\<rangle> = \<langle>u|v\<rangle> * \<langle>e1|e2\<rangle>" by (rule tensor_inner_prod) (use assms in simp_all)
  finally show ?thesis .
qed

lemma unit2_inner: "i < 2 \<Longrightarrow> j < 2 \<Longrightarrow> \<langle>unit_vec 2 i|unit_vec 2 j\<rangle> = (if i = j then 1 else 0)"
  by (auto simp: Quantum.inner_prod_def unit_vec_def numeral_2_eq_2 atLeast0LessThan lessThan_Suc)

lemma unitN_inner: "\<langle>unit_vec (2 ^ k) 0|unit_vec (2 ^ k) 0\<rangle> = 1"
  using cpx_vec_length_inner_prod[of "unit_vec (2 ^ k) 0"] unitN_norm by simp

text \<open>Overlaps of the two ancilla branches $w_0=\ket0\otimes G_0b\otimes\ket0$, $w_1=\ket0\otimes G_1b\otimes\ket1$
with the solution state $t$.\<close>

lemma branch_overlaps:
  defines "x \<equiv> herm_inv A *\<^sub>v b"
    and "w0 \<equiv> tensor_vec (unit_vec (2 ^ k) 0) (tensor_vec (mat_fun (\<lambda>x. complex_of_real (sqrt (1 - (C / x)\<^sup>2))) A *\<^sub>v b) (unit_vec 2 0))"
    and "w1 \<equiv> tensor_vec (unit_vec (2 ^ k) 0) (tensor_vec ((complex_of_real C \<cdot>\<^sub>m herm_inv A) *\<^sub>v b) (unit_vec 2 1))"
  shows "inner_prod (hhl_target A k b) w0 = 0" "inner_prod w0 (hhl_target A k b) = 0"
    and "inner_prod (hhl_target A k b) w1 = complex_of_real (C * \<parallel>x\<parallel>)" "inner_prod w1 (hhl_target A k b) = complex_of_real (C * \<parallel>x\<parallel>)"
    and "inner_prod w0 w0 = complex_of_real (\<parallel>mat_fun (\<lambda>x. complex_of_real (sqrt (1 - (C / x)\<^sup>2))) A *\<^sub>v b\<parallel>\<^sup>2)"
    and "inner_prod w1 w0 = 0"
proof -
  let ?a = "unit_vec (2 ^ k) 0" and ?g0 = "mat_fun (\<lambda>x. complex_of_real (sqrt (1 - (C / x)\<^sup>2))) A *\<^sub>v b"
  let ?g1 = "(complex_of_real C \<cdot>\<^sub>m herm_inv A) *\<^sub>v b" and ?xh = "complex_of_real (1 / \<parallel>x\<parallel>) \<cdot>\<^sub>v x"
  have bd: "dim_vec b = n" using Ub by auto
  have dx: "dim_vec x = n" unfolding x_def by simp
  have d: "dim_vec ?g0 = n" "dim_vec ?g1 = n" "dim_vec ?xh = n" "dim_vec ?a = 2 ^ k" using dx by simp_all
  have t: "hhl_target A k b = tensor_vec ?a (tensor_vec ?xh (unit_vec 2 1))" unfolding hhl_target_def x_def ..
  have g1: "?g1 = complex_of_real C \<cdot>\<^sub>v x"
    unfolding x_def by (rule smult_mat_mult_vec) (use bd in \<open>auto simp: herm_inv_def intro!: carrier_matI\<close>)
  have xx: "\<langle>x|x\<rangle> = complex_of_real (\<parallel>x\<parallel>\<^sup>2)" by (rule cpx_vec_length_inner_prod[symmetric])
  have xg: "\<langle>?xh|?g1\<rangle> = complex_of_real (C * \<parallel>x\<parallel>)"
  proof -
    have "\<langle>?xh|?g1\<rangle> = cnj (complex_of_real (1 / \<parallel>x\<parallel>)) * (complex_of_real C * \<langle>x|x\<rangle>)"
    proof -
      have l: "\<langle>complex_of_real (1 / \<parallel>x\<parallel>) \<cdot>\<^sub>v x|x\<rangle> = cnj (complex_of_real (1 / \<parallel>x\<parallel>)) * \<langle>x|x\<rangle>"
        by (rule inner_prod_left_smult') simp
      show ?thesis unfolding g1 inner_prod_right_smult' l by simp
    qed
    also have "\<dots> = complex_of_real (C * \<parallel>x\<parallel>)" unfolding xx using sol_nonzero
      by (simp add: x_def power2_eq_square field_simps)
    finally show ?thesis .
  qed
  show t0: "inner_prod (hhl_target A k b) w0 = 0"
    unfolding t w0_def by (subst inner3) (simp_all add: d dx unit2_inner)
  show "inner_prod w0 (hhl_target A k b) = 0"
    unfolding t w0_def by (subst inner3) (simp_all add: d dx unit2_inner)
  show "inner_prod (hhl_target A k b) w1 = complex_of_real (C * \<parallel>x\<parallel>)"
  proof -
    have "inner_prod (hhl_target A k b) w1 = \<langle>?a|?a\<rangle> * (\<langle>?xh|?g1\<rangle> * \<langle>unit_vec 2 1|unit_vec 2 1\<rangle>)"
      unfolding t w1_def by (rule inner3) (simp_all add: d dx)
    thus ?thesis unfolding xg unitN_inner unit2_inner[of 1 1, simplified] by simp
  qed
  show "inner_prod w1 (hhl_target A k b) = complex_of_real (C * \<parallel>x\<parallel>)"
  proof -
    have "\<langle>?g1|?xh\<rangle> = cnj \<langle>?xh|?g1\<rangle>" by (rule inner_prod_cnj) (simp add: d dx)
    hence gx: "\<langle>?g1|?xh\<rangle> = complex_of_real (C * \<parallel>x\<parallel>)" unfolding xg by simp
    have "inner_prod w1 (hhl_target A k b) = \<langle>?a|?a\<rangle> * (\<langle>?g1|?xh\<rangle> * \<langle>unit_vec 2 1|unit_vec 2 1\<rangle>)"
      unfolding t w1_def by (rule inner3) (simp_all add: d dx)
    thus ?thesis unfolding gx unitN_inner unit2_inner[of 1 1, simplified] by simp
  qed
  show "inner_prod w0 w0 = complex_of_real (\<parallel>?g0\<parallel>\<^sup>2)"
  proof -
    have "inner_prod w0 w0 = \<langle>?a|?a\<rangle> * (\<langle>?g0|?g0\<rangle> * \<langle>unit_vec 2 0|unit_vec 2 0\<rangle>)"
      unfolding w0_def by (rule inner3) (simp_all add: d dx)
    thus ?thesis unfolding unitN_inner unit2_inner[of 0 0, simplified] cpx_vec_length_inner_prod[symmetric] by simp
  qed
  show "inner_prod w1 w0 = 0"
    unfolding w0_def w1_def by (subst inner3) (simp_all add: d dx unit2_inner)
qed

text \<open>The postcondition ``ancilla $0$, or exactly the solution state'' is the predicate
$P_0+\ket t\bra t$; as $P_1^*\ket t\bra tP_1+P_0^*IP_0$ it is a quantum predicate.\<close>

lemma post_facts:
  defines "Dm \<equiv> 2 ^ k * (n * 2)" and "Tt \<equiv> outer_prod (hhl_target A k b) (hhl_target A k b)"
  shows "anc_proj Dm 1 *\<^sub>v hhl_target A k b = hhl_target A k b"
    and "adjoint (anc_proj Dm 1) * Tt * anc_proj Dm 1 + adjoint (anc_proj Dm 0) * 1\<^sub>m Dm * anc_proj Dm 0 = anc_proj Dm 0 + Tt"
    and "matrix_sum Dm (\<lambda>j. adjoint (anc_proj Dm (1 - j)) * (if j = 0 then Tt else 1\<^sub>m Dm) * anc_proj Dm (1 - j)) 2 = anc_proj Dm 0 + Tt"
    and "state_sig.is_quantum_predicate [2 ^ k, n, 2] (anc_proj Dm 0 + Tt)"
    and "state_sig.is_quantum_predicate [2 ^ k, n, 2] Tt"
proof -
  interpret state_sig "[2 ^ k, n, 2]" .
  have dd: "d = Dm" by (simp add: d_def Dm_def)
  let ?t = "hhl_target A k b"
  have tc: "?t \<in> carrier_vec Dm" unfolding Dm_def by (rule carrier_vecI[OF target_dim])
  show t1: "anc_proj Dm 1 *\<^sub>v ?t = ?t"
    unfolding Dm_def hhl_target_def using anc_proj_tensor[of "unit_vec (2 ^ k) 0" "2 ^ k" _ n 1 1] Ub by simp
  have Tc: "Tt \<in> carrier_mat Dm Dm" unfolding Tt_def using outer_prod_dim[OF tc tc] .
  have T1: "adjoint (anc_proj Dm 1) * Tt * anc_proj Dm 1 = Tt"
  proof -
    have "anc_proj Dm 1 * Tt * anc_proj Dm 1 = outer_prod (anc_proj Dm 1 *\<^sub>v ?t) (adjoint (anc_proj Dm 1) *\<^sub>v ?t)"
      unfolding Tt_def by (rule outer_prod_left_right_mat[OF tc tc anc_proj_carrier anc_proj_carrier])
    thus ?thesis unfolding anc_proj_adjoint t1 Tt_def .
  qed
  have A0: "adjoint (anc_proj Dm 0) * 1\<^sub>m Dm * anc_proj Dm 0 = anc_proj Dm 0"
  proof -
    have "anc_proj Dm 0 * 1\<^sub>m Dm = anc_proj Dm 0" by (rule right_mult_one_mat[OF anc_proj_carrier])
    thus ?thesis unfolding anc_proj_adjoint by (simp add: anc_proj_square)
  qed
  show e: "adjoint (anc_proj Dm 1) * Tt * anc_proj Dm 1 + adjoint (anc_proj Dm 0) * 1\<^sub>m Dm * anc_proj Dm 0 = anc_proj Dm 0 + Tt"
    unfolding T1 A0 by (rule comm_add_mat[OF Tc anc_proj_carrier])
  show m: "matrix_sum Dm (\<lambda>j. adjoint (anc_proj Dm (1 - j)) * (if j = 0 then Tt else 1\<^sub>m Dm) * anc_proj Dm (1 - j)) 2 = anc_proj Dm 0 + Tt"
    using A0 T1 Tc by (simp add: numeral_2_eq_2)
  show qT: "is_quantum_predicate Tt" unfolding Tt_def dd[symmetric] by (rule qp_pure) (simp_all add: target_dim target_unit dd Dm_def)
  have q1: "is_quantum_predicate (1\<^sub>m d)"
    unfolding is_quantum_predicate_def using positive_one lowner_le_refl[of "1\<^sub>m d" d] by simp
  have "is_quantum_predicate (matrix_sum d (\<lambda>j. adjoint (anc_proj d (1 - j)) * (if j = 0 then Tt else 1\<^sub>m d) * anc_proj d (1 - j)) 2)"
    by (rule qps_after_measure_is_qp[OF anc_proj_swap_measurement]) (use qT q1 dd in auto)
  thus "is_quantum_predicate (anc_proj Dm 0 + Tt)" unfolding dd m .
qed

text \<open>The branches under the postcondition $P_0+\ket t\bra t$.\<close>

lemma post_branches:
  defines "Dm \<equiv> 2 ^ k * (n * 2)" and "Tt \<equiv> outer_prod (hhl_target A k b) (hhl_target A k b)"
    and "w0 \<equiv> tensor_vec (unit_vec (2 ^ k) 0) (tensor_vec (mat_fun (\<lambda>x. complex_of_real (sqrt (1 - (C / x)\<^sup>2))) A *\<^sub>v b) (unit_vec 2 0))"
    and "w1 \<equiv> tensor_vec (unit_vec (2 ^ k) 0) (tensor_vec ((complex_of_real C \<cdot>\<^sub>m herm_inv A) *\<^sub>v b) (unit_vec 2 1))"
  shows "(anc_proj Dm 0 + Tt) *\<^sub>v w0 = w0"
    and "(anc_proj Dm 0 + Tt) *\<^sub>v w1 = complex_of_real (C * \<parallel>herm_inv A *\<^sub>v b\<parallel>) \<cdot>\<^sub>v hhl_target A k b"
proof -
  let ?t = "hhl_target A k b" and ?c = "complex_of_real (C * \<parallel>herm_inv A *\<^sub>v b\<parallel>)"
  have bd: "dim_vec b = n" using Ub by auto
  have tc: "?t \<in> carrier_vec Dm" unfolding Dm_def by (rule carrier_vecI[OF target_dim])
  have w0c: "w0 \<in> carrier_vec Dm" unfolding w0_def Dm_def by (rule carrier_vecI) (simp add: tensor_vec_dim bd)
  have w1c: "w1 \<in> carrier_vec Dm" unfolding w1_def Dm_def by (rule carrier_vecI) (simp add: tensor_vec_dim bd)
  have Tc: "Tt \<in> carrier_mat Dm Dm" unfolding Tt_def using outer_prod_dim[OF tc tc] .
  have T0: "Tt *\<^sub>v w0 = 0\<^sub>v Dm"
  proof -
    have "Tt *\<^sub>v w0 = inner_prod ?t w0 \<cdot>\<^sub>v ?t" unfolding Tt_def by (rule outer_prod_mult_vec[OF tc tc w0c])
    also have "inner_prod ?t w0 = 0" unfolding w0_def by (rule branch_overlaps(1))
    finally show ?thesis using tc by (intro eq_vecI) auto
  qed
  have T1: "Tt *\<^sub>v w1 = ?c \<cdot>\<^sub>v ?t"
  proof -
    have "Tt *\<^sub>v w1 = inner_prod ?t w1 \<cdot>\<^sub>v ?t" unfolding Tt_def by (rule outer_prod_mult_vec[OF tc tc w1c])
    also have "inner_prod ?t w1 = ?c" unfolding w1_def by (rule branch_overlaps(3))
    finally show ?thesis .
  qed
  have P00: "anc_proj Dm 0 *\<^sub>v w0 = w0"
    unfolding w0_def Dm_def using anc_proj_tensor[of "unit_vec (2 ^ k) 0" "2 ^ k" _ n 0 0] bd by simp
  have P01: "anc_proj Dm 0 *\<^sub>v w1 = 0\<^sub>v Dm"
    unfolding w1_def Dm_def using anc_proj_tensor[of "unit_vec (2 ^ k) 0" "2 ^ k" _ n 1 0] bd by simp
  show "(anc_proj Dm 0 + Tt) *\<^sub>v w0 = w0"
    unfolding add_mult_distrib_mat_vec[OF anc_proj_carrier Tc w0c] P00 T0 using w0c by simp
  show "(anc_proj Dm 0 + Tt) *\<^sub>v w1 = ?c \<cdot>\<^sub>v ?t"
    unfolding add_mult_distrib_mat_vec[OF anc_proj_carrier Tc w1c] P01 T1 using tc by simp
qed

lemma one_branch_sum:
  "complex_of_real (\<parallel>mat_fun (\<lambda>x. complex_of_real (sqrt (1 - (C / x)\<^sup>2))) A *\<^sub>v b\<parallel>\<^sup>2)
   + complex_of_real (C * \<parallel>herm_inv A *\<^sub>v b\<parallel>) * complex_of_real (C * \<parallel>herm_inv A *\<^sub>v b\<parallel>) = 1"
proof -
  have c: "complex_of_real (C * \<parallel>herm_inv A *\<^sub>v b\<parallel>) * complex_of_real (C * \<parallel>herm_inv A *\<^sub>v b\<parallel>)
           = complex_of_real (C\<^sup>2 * \<parallel>herm_inv A *\<^sub>v b\<parallel>\<^sup>2)" by (simp add: power2_eq_square)
  have e: "\<parallel>mat_fun (\<lambda>x. complex_of_real (sqrt (1 - (C / x)\<^sup>2))) A *\<^sub>v b\<parallel>\<^sup>2 + C\<^sup>2 * \<parallel>herm_inv A *\<^sub>v b\<parallel>\<^sup>2 = 1"
    by (rule hhl_out_branches[OF A n0 k t0 spec Ub Cb])
  show ?thesis unfolding c of_real_add[symmetric] e by simp
qed

text \<open>Correctness: whenever the ancilla reads $1$, the state is exactly $\ket0\otimes\hat x\otimes\ket1$.\<close>

theorem hhl_prog_correct:
  assumes Us: "\<And>U. U \<in> set Us \<Longrightarrow> U \<in> carrier_mat (2 ^ k * (n * 2)) (2 ^ k * (n * 2)) \<and> Complex_Matrix.unitary U"
      and circ: "circuit_mat (2 ^ k * (n * 2)) Us = circuit_mat (2 ^ k * (n * 2)) (hhl_gates A Ub t0 k C)"
  shows "state_sig.hoare_partial [2 ^ k, n, 2] (1\<^sub>m (2 ^ k * (n * 2))) (hhl_prog (2 ^ k * (n * 2)) Us)
     (anc_proj (2 ^ k * (n * 2)) 0 + outer_prod (hhl_target A k b) (hhl_target A k b))"
proof -
  interpret state_sig "[2 ^ k, n, 2]" .
  let ?D = "2 ^ k * (n * 2)" and ?a = "unit_vec (2 ^ k) 0" and ?t = "hhl_target A k b"
  let ?Q = "anc_proj ?D 0 + outer_prod ?t ?t" and ?x = "herm_inv A *\<^sub>v b"
  let ?g0 = "mat_fun (\<lambda>x. complex_of_real (sqrt (1 - (C / x)\<^sup>2))) A *\<^sub>v b" and ?g1 = "(complex_of_real C \<cdot>\<^sub>m herm_inv A) *\<^sub>v b"
  let ?w0 = "tensor_vec ?a (tensor_vec ?g0 (unit_vec 2 0))" and ?w1 = "tensor_vec ?a (tensor_vec ?g1 (unit_vec 2 1))"
  have dd: "d = ?D" by (simp add: d_def)
  have nA: "dim_row A = n" using A(1) by simp
  have qQ: "is_quantum_predicate ?Q" using post_facts(4) by simp
  have qQ': "is_quantum_predicate (anc_proj d 0 + outer_prod ?t ?t)" using qQ dd by simp
  have h: "hoare_partial ((\<Sum>j<2. inner_prod (anc_proj d j *\<^sub>v (circuit_mat d Us *\<^sub>v unit_vec d 0))
                 ((anc_proj d 0 + outer_prod ?t ?t) *\<^sub>v (anc_proj d j *\<^sub>v (circuit_mat d Us *\<^sub>v unit_vec d 0)))) \<cdot>\<^sub>m 1\<^sub>m d)
             (init_com d ;; utrans_seq Us ;; Measure 2 (anc_proj d) [SKIP, SKIP]) (anc_proj d 0 + outer_prod ?t ?t)"
    by (rule hoare_init_circuit_measure[OF qQ' _ _ anc_proj_measurement]) (use Us dd n0 in auto)
  have val: "(\<Sum>j<2. inner_prod (anc_proj ?D j *\<^sub>v tensor_vec ?a (hhl_out A C b)) (?Q *\<^sub>v (anc_proj ?D j *\<^sub>v tensor_vec ?a (hhl_out A C b)))) = 1"
  proof -
    have s2: "(\<Sum>j<2. F j) = F 0 + F 1" for F :: "nat \<Rightarrow> complex" by (simp add: numeral_2_eq_2)
    have i1: "inner_prod ?w1 (complex_of_real (C * \<parallel>?x\<parallel>) \<cdot>\<^sub>v ?t) = complex_of_real (C * \<parallel>?x\<parallel>) * complex_of_real (C * \<parallel>?x\<parallel>)"
    proof -
      have "inner_prod ?w1 (complex_of_real (C * \<parallel>?x\<parallel>) \<cdot>\<^sub>v ?t) = \<langle>?w1|complex_of_real (C * \<parallel>?x\<parallel>) \<cdot>\<^sub>v ?t\<rangle>"
        by (rule inner_bridge) (use Ub in \<open>simp add: tensor_vec_dim target_dim\<close>)
      also have "\<dots> = complex_of_real (C * \<parallel>?x\<parallel>) * \<langle>?w1|?t\<rangle>" by (rule inner_prod_right_smult')
      also have "\<langle>?w1|?t\<rangle> = inner_prod ?w1 ?t" by (rule inner_bridge[symmetric]) (use Ub in \<open>simp add: tensor_vec_dim target_dim\<close>)
      also have "\<dots> = complex_of_real (C * \<parallel>?x\<parallel>)" by (rule branch_overlaps(4))
      finally show ?thesis .
    qed
    have "complex_of_real (\<parallel>?g0\<parallel>\<^sup>2) + complex_of_real (C * \<parallel>?x\<parallel>) * complex_of_real (C * \<parallel>?x\<parallel>) = 1"
      by (rule one_branch_sum)
    thus ?thesis unfolding s2 prog_branch(1) prog_branch(2) post_branches i1 branch_overlaps(5) by simp
  qed
  have e1: "(1::complex) \<cdot>\<^sub>m 1\<^sub>m ?D = 1\<^sub>m ?D" by (rule eq_matI) auto
  show ?thesis using h unfolding dd circ prog_out val hhl_prog_def e1 .
qed

theorem hhl_correct:
  "state_sig.hoare_partial [2 ^ k, n, 2] (1\<^sub>m (2 ^ k * (n * 2))) (hhl_program A Ub t0 k C)
     (anc_proj (2 ^ k * (n * 2)) 0 + outer_prod (hhl_target A k b) (hhl_target A k b))"
  unfolding hhl_program_def carrier_matD(1)[OF A(1)]
  by (rule hhl_prog_correct[where Us = "hhl_gates A Ub t0 k C", OF prog_gates refl])

text \<open>Repeat until success: the loop re-runs the circuit while the ancilla reads $0$.  On
termination the state is exactly $\ket0\otimes\hat x\otimes\ket1$ (partial correctness).\<close>

theorem hhl_rus_prog_correct:
  assumes Us: "\<And>U. U \<in> set Us \<Longrightarrow> U \<in> carrier_mat (2 ^ k * (n * 2)) (2 ^ k * (n * 2)) \<and> Complex_Matrix.unitary U"
      and circ: "circuit_mat (2 ^ k * (n * 2)) Us = circuit_mat (2 ^ k * (n * 2)) (hhl_gates A Ub t0 k C)"
  shows "state_sig.hoare_partial [2 ^ k, n, 2] (1\<^sub>m (2 ^ k * (n * 2))) (hhl_rus_prog (2 ^ k * (n * 2)) Us)
     (outer_prod (hhl_target A k b) (hhl_target A k b))"
proof -
  interpret state_sig "[2 ^ k, n, 2]" .
  let ?D = "2 ^ k * (n * 2)" and ?a = "unit_vec (2 ^ k) 0" and ?t = "hhl_target A k b"
  let ?T = "outer_prod ?t ?t" and ?x = "herm_inv A *\<^sub>v b"
  let ?M = "\<lambda>j. anc_proj ?D (1 - j)"
  let ?S = "init_com ?D ;; utrans_seq Us"
  let ?R = "adjoint (?M 0) * ?T * ?M 0 + adjoint (?M 1) * 1\<^sub>m ?D * ?M 1"
  let ?g0 = "mat_fun (\<lambda>x. complex_of_real (sqrt (1 - (C / x)\<^sup>2))) A *\<^sub>v b" and ?g1 = "(complex_of_real C \<cdot>\<^sub>m herm_inv A) *\<^sub>v b"
  let ?w0 = "tensor_vec ?a (tensor_vec ?g0 (unit_vec 2 0))" and ?w1 = "tensor_vec ?a (tensor_vec ?g1 (unit_vec 2 1))"
  have dd: "d = ?D" by (simp add: d_def)
  have nA: "dim_row A = n" using A(1) by simp
  have R: "?R = anc_proj ?D 0 + ?T" using post_facts(2) by simp
  have qR: "is_quantum_predicate ?R" unfolding R using post_facts(4) by simp
  have qT: "is_quantum_predicate ?T" using post_facts(5) by simp
  have q1: "is_quantum_predicate (1\<^sub>m ?D)" unfolding is_quantum_predicate_def dd[symmetric]
    using positive_one lowner_le_refl[of "1\<^sub>m d" d] by simp
  have bd: "dim_vec b = n" using Ub by auto
  have sp: "tensor_vec ?a (hhl_out A C b) = ?w0 + ?w1"
    unfolding hhl_out_def by (rule tensor_vec_bilinear_right) (simp_all add: tensor_vec_dim bd)
  have w0c: "?w0 \<in> carrier_vec ?D" by (rule carrier_vecI) (simp add: tensor_vec_dim bd)
  have w1c: "?w1 \<in> carrier_vec ?D" by (rule carrier_vecI) (simp add: tensor_vec_dim bd)
  have Rc: "anc_proj ?D 0 + ?T \<in> carrier_mat ?D ?D" using post_facts(4) unfolding is_quantum_predicate_def d_def by simp
  have val: "inner_prod (tensor_vec ?a (hhl_out A C b)) ((anc_proj ?D 0 + ?T) *\<^sub>v tensor_vec ?a (hhl_out A C b)) = 1"
  proof -
    have "(anc_proj ?D 0 + ?T) *\<^sub>v (?w0 + ?w1) = ?w0 + complex_of_real (C * \<parallel>?x\<parallel>) \<cdot>\<^sub>v ?t"
      unfolding mult_add_distrib_mat_vec[OF Rc w0c w1c] post_branches ..
    hence "inner_prod (?w0 + ?w1) ((anc_proj ?D 0 + ?T) *\<^sub>v (?w0 + ?w1)) = \<langle>?w0 + ?w1|?w0 + complex_of_real (C * \<parallel>?x\<parallel>) \<cdot>\<^sub>v ?t\<rangle>"
      using inner_bridge[of "?w0 + ?w1" "?w0 + complex_of_real (C * \<parallel>?x\<parallel>) \<cdot>\<^sub>v ?t"] w0c w1c target_dim by simp
    also have "\<dots> = \<langle>?w0|?w0\<rangle> + \<langle>?w0|complex_of_real (C * \<parallel>?x\<parallel>) \<cdot>\<^sub>v ?t\<rangle> + \<langle>?w1|?w0\<rangle> + \<langle>?w1|complex_of_real (C * \<parallel>?x\<parallel>) \<cdot>\<^sub>v ?t\<rangle>"
      by (rule No_Cloning.inner_prod_expand) (use w0c w1c target_dim in simp_all)
    also have "\<dots> = complex_of_real (\<parallel>?g0\<parallel>\<^sup>2) + complex_of_real (C * \<parallel>?x\<parallel>) * complex_of_real (C * \<parallel>?x\<parallel>)"
    proof -
      have b: "\<langle>u|v\<rangle> = inner_prod u v" if "dim_vec u = ?D" "dim_vec v = ?D" for u v by (rule inner_bridge[symmetric]) (use that in simp)
      have d0: "dim_vec ?w0 = ?D" "dim_vec ?w1 = ?D" "dim_vec ?t = ?D" using w0c w1c target_dim by auto
      show ?thesis unfolding inner_prod_right_smult' b[OF d0(1) d0(1)] b[OF d0(1) d0(3)] b[OF d0(2) d0(1)] b[OF d0(2) d0(3)]
        branch_overlaps(2,4,5,6) by simp
    qed
    also have "\<dots> = 1" by (rule one_branch_sum)
    finally show ?thesis unfolding sp .
  qed
  have body: "hoare_partial (1\<^sub>m ?D) ?S ?R"
  proof -
    have "hoare_partial (inner_prod (circuit_mat d Us *\<^sub>v unit_vec d 0)
                 ((anc_proj ?D 0 + ?T) *\<^sub>v (circuit_mat d Us *\<^sub>v unit_vec d 0)) \<cdot>\<^sub>m 1\<^sub>m d)
            (init_com d ;; utrans_seq Us) (anc_proj ?D 0 + ?T)"
      by (rule hoare_init_circuit) (use post_facts(4) Us dd n0 in auto)
    moreover have "(1::complex) \<cdot>\<^sub>m 1\<^sub>m ?D = 1\<^sub>m ?D" by (rule eq_matI) auto
    ultimately show ?thesis unfolding dd circ prog_out val R by simp
  qed
  have loop: "hoare_partial ?R (While ?M ?S) ?T"
    by (rule hoare_partial.intros(5)[OF qT q1[folded dd, unfolded dd]]) (use body in simp)
  have "hoare_partial (1\<^sub>m ?D) (?S ;; While ?M ?S) ?T"
    by (rule hoare_partial.intros(3)[OF q1 qR qT body loop])
  thus ?thesis unfolding hhl_rus_prog_def .
qed

theorem hhl_rus_correct:
  "state_sig.hoare_partial [2 ^ k, n, 2] (1\<^sub>m (2 ^ k * (n * 2))) (hhl_rus A Ub t0 k C)
     (outer_prod (hhl_target A k b) (hhl_target A k b))"
  unfolding hhl_rus_def carrier_matD(1)[OF A(1)]
  by (rule hhl_rus_prog_correct[where Us = "hhl_gates A Ub t0 k C", OF prog_gates refl])

end

fun while_free :: "com \<Rightarrow> bool" where
  "while_free SKIP = True"
| "while_free (Utrans U) = True"
| "while_free (com.Seq Sa Sb) = (while_free Sa \<and> while_free Sb)"
| "while_free (Measure n M Sc) = list_all while_free Sc"
| "while_free (While M Sc) = False"

context state_sig
begin

text \<open>Programs without loops terminate: they preserve the trace.\<close>

lemma denote_trace_eq:
  "while_free Sc \<Longrightarrow> well_com Sc \<Longrightarrow> \<rho> \<in> carrier_mat d d \<Longrightarrow> partial_density_operator \<rho> \<Longrightarrow> trace (denote Sc \<rho>) = trace \<rho>"
proof (induction Sc arbitrary: \<rho>)
  case SKIP
  show ?case by simp
next
  case (Utrans U)
  have U: "U \<in> carrier_mat d d" "Complex_Matrix.unitary U" using Utrans by auto
  have "trace \<rho> = trace (adjoint (adjoint U) * \<rho> * adjoint U)"
    by (rule unitary_operator_keep_trace[OF adjoint_dim[OF U(1)] Utrans(3) unitary_adjoint[OF U]])
  thus ?case by (simp add: adjoint_adjoint)
next
  case (Seq Sa Sb)
  have p1: "denote Sa \<rho> \<in> carrier_mat d d" "partial_density_operator (denote Sa \<rho>)"
    using denote_dim_pdo[of Sa \<rho>] Seq.prems by auto
  show ?case using Seq.IH(1)[of \<rho>] Seq.IH(2)[OF _ _ p1] Seq.prems by simp
next
  case (Measure n M Sc)
  have m: "measurement d n M" and l: "length Sc = n" and w: "list_all well_com Sc" and f: "list_all while_free Sc"
    using Measure.prems by auto
  have Mk: "M k \<in> carrier_mat d d" if "k < n" for k using measurement_dim[OF m that] .
  have Rk: "M k * \<rho> * adjoint (M k) \<in> carrier_mat d d" if "k < n" for k
    using Mk[OF that] Measure.prems(3) by (auto intro: mult_carrier_mat adjoint_dim)
  have Pk: "partial_density_operator (M k * \<rho> * adjoint (M k))" if "k < n" for k
    by (rule pdo_close_under_measurement[OF Mk[OF that] Measure.prems(3,4) measurement_le_one_mat[OF m that]])
  have Sk: "Sc ! k \<in> set Sc" "well_com (Sc ! k)" "while_free (Sc ! k)" if "k < n" for k
    using that l w f by (auto simp: list_all_length)
  have Dk: "denote (Sc ! k) (M k * \<rho> * adjoint (M k)) \<in> carrier_mat d d" if "k < n" for k
    using denote_dim_pdo[OF Sk(2)[OF that] Rk[OF that] Pk[OF that]] by simp
  have "trace (denote (Measure n M Sc) \<rho>) = (\<Sum>k\<in>{0..<n}. trace (denote (Sc ! k) (M k * \<rho> * adjoint (M k))))"
  proof -
    have "denote (Measure n M Sc) \<rho> = matrix_sum d (\<lambda>k. denote (Sc ! k) (M k * \<rho> * adjoint (M k))) n"
      unfolding denote.simps denote_measure_def using l by (intro matrix_sum_cong) simp
    thus ?thesis using trace_matrix_sum_linear[of n "\<lambda>k. denote (Sc ! k) (M k * \<rho> * adjoint (M k))"] Dk by simp
  qed
  also have "\<dots> = (\<Sum>k\<in>{0..<n}. trace (adjoint (M k) * M k * \<rho>))"
  proof (rule sum.cong[OF refl])
    fix k assume "k \<in> {0..<n}"
    hence k: "k < n" by simp
    have "trace (denote (Sc ! k) (M k * \<rho> * adjoint (M k))) = trace (M k * \<rho> * adjoint (M k))"
      by (rule Measure.IH[OF Sk(1)[OF k] Sk(3)[OF k] Sk(2)[OF k] Rk[OF k] Pk[OF k]])
    also have "\<dots> = trace (adjoint (M k) * (M k * \<rho>))"
      by (rule trace_comm) (use Mk[OF k] Measure.prems(3) in \<open>auto intro: mult_carrier_mat adjoint_dim\<close>)
    also have "\<dots> = trace (adjoint (M k) * M k * \<rho>)"
      using Mk[OF k] Measure.prems(3) by (simp add: assoc_mult_mat[symmetric, of _ d d _ d _ d] adjoint_dim)
    finally show "trace (denote (Sc ! k) (M k * \<rho> * adjoint (M k))) = trace (adjoint (M k) * M k * \<rho>)" .
  qed
  also have "\<dots> = trace (matrix_sum d (\<lambda>k. adjoint (M k) * M k) n * \<rho>)"
  proof -
    have c: "adjoint (M k) * M k * \<rho> \<in> carrier_mat d d" if "k < n" for k
      using Mk[OF that] Measure.prems(3) by (auto intro: mult_carrier_mat adjoint_dim)
    have "matrix_sum d (\<lambda>k. adjoint (M k) * M k * \<rho>) n = matrix_sum d (\<lambda>k. adjoint (M k) * M k) n * \<rho>"
      by (rule matrix_sum_mult_right) (use Mk Measure.prems(3) in \<open>auto intro: mult_carrier_mat adjoint_dim\<close>)
    moreover have "trace (matrix_sum d (\<lambda>k. adjoint (M k) * M k * \<rho>) n) = (\<Sum>k\<in>{0..<n}. trace (adjoint (M k) * M k * \<rho>))"
      by (rule trace_matrix_sum_linear) (rule c)
    ultimately show ?thesis by simp
  qed
  also have "\<dots> = trace \<rho>" using m Measure.prems(3) unfolding measurement_def by simp
  finally show ?case .
next
  case (While M Sc)
  thus ?case by simp
qed

lemma partial_to_total:
  "\<Turnstile>\<^sub>p {P} Sc {Q} \<Longrightarrow> while_free Sc \<Longrightarrow> well_com Sc \<Longrightarrow> \<Turnstile>\<^sub>t {P} Sc {Q}"
  unfolding hoare_partial_correct_def hoare_total_correct_def density_states_def
  using denote_trace_eq by auto

end

context
  fixes A Ub :: "complex Matrix.mat" and b :: "complex Matrix.vec" and n k :: nat and t0 C :: real
  assumes A: "A \<in> carrier_mat n n" "Quantum_Computing_3_10.hermitian A" and n0: "0 < n" and k: "1 \<le> k" and t0: "0 < t0"
    and spec: "\<And>l. l \<in> herm_spectrum A \<Longrightarrow> \<exists>j. 0 < j \<and> j < 2 ^ k \<and> l = reg_eig t0 (2 ^ k) j"
    and Ub: "Ub \<in> carrier_mat n n" "Quantum.unitary Ub" "Ub *\<^sub>v unit_vec n 0 = b"
    and Cb: "\<And>j. j < 2 ^ k \<Longrightarrow> \<bar>C / reg_eig t0 (2 ^ k) j\<bar> \<le> 1"
begin

lemma hhl_prog_well_com:
  assumes Us: "\<And>U. U \<in> set Us \<Longrightarrow> U \<in> carrier_mat (2 ^ k * (n * 2)) (2 ^ k * (n * 2)) \<and> Complex_Matrix.unitary U"
  shows "state_sig.well_com [2 ^ k, n, 2] (hhl_prog (2 ^ k * (n * 2)) Us)"
proof -
  interpret state_sig "[2 ^ k, n, 2]" .
  have dd: "d = 2 ^ k * (n * 2)" by (simp add: d_def)
  show ?thesis unfolding hhl_prog_def dd[symmetric]
    using well_com_init well_com_utrans_seq[of Us] Us anc_proj_measurement[of d] n0 by (auto simp: dd)
qed

lemma hhl_rus_prog_well_com:
  assumes Us: "\<And>U. U \<in> set Us \<Longrightarrow> U \<in> carrier_mat (2 ^ k * (n * 2)) (2 ^ k * (n * 2)) \<and> Complex_Matrix.unitary U"
  shows "state_sig.well_com [2 ^ k, n, 2] (hhl_rus_prog (2 ^ k * (n * 2)) Us)"
proof -
  interpret state_sig "[2 ^ k, n, 2]" .
  have dd: "d = 2 ^ k * (n * 2)" by (simp add: d_def)
  show ?thesis unfolding hhl_rus_prog_def dd[symmetric]
    using well_com_init well_com_utrans_seq[of Us] Us anc_proj_swap_measurement[of d] n0 by (auto simp: dd)
qed

lemma hhl_program_well_com: "state_sig.well_com [2 ^ k, n, 2] (hhl_program A Ub t0 k C)"
  unfolding hhl_program_def carrier_matD(1)[OF A(1)] by (rule hhl_prog_well_com[OF prog_gates[OF A n0 k t0 spec Ub Cb]])

lemma hhl_rus_well_com: "state_sig.well_com [2 ^ k, n, 2] (hhl_rus A Ub t0 k C)"
  unfolding hhl_rus_def carrier_matD(1)[OF A(1)] by (rule hhl_rus_prog_well_com[OF prog_gates[OF A n0 k t0 spec Ub Cb]])

lemma hhl_prog_while_free: "while_free (hhl_prog K Us)"
proof -
  have "while_free (utrans_seq Us)" for Us by (induction Us) auto
  thus ?thesis by (simp add: hhl_prog_def init_com_def list_all_iff)
qed

lemma hhl_program_while_free: "while_free (hhl_program A Ub t0 k C)"
  unfolding hhl_program_def by (rule hhl_prog_while_free)

text \<open>The semantic statements, by soundness of the logic.  The program without the loop
terminates, so its triples hold for total correctness.\<close>

theorem hhl_prog_success_total:
  assumes Us: "\<And>U. U \<in> set Us \<Longrightarrow> U \<in> carrier_mat (2 ^ k * (n * 2)) (2 ^ k * (n * 2)) \<and> Complex_Matrix.unitary U"
      and circ: "circuit_mat (2 ^ k * (n * 2)) Us = circuit_mat (2 ^ k * (n * 2)) (hhl_gates A Ub t0 k C)"
  shows "state_sig.hoare_total_correct [2 ^ k, n, 2] (complex_of_real (C\<^sup>2 * \<parallel>herm_inv A *\<^sub>v b\<parallel>\<^sup>2) \<cdot>\<^sub>m 1\<^sub>m (2 ^ k * (n * 2)))
     (hhl_prog (2 ^ k * (n * 2)) Us) (anc_proj (2 ^ k * (n * 2)) 1)"
proof -
  interpret state_sig "[2 ^ k, n, 2]" .
  show ?thesis
    by (rule partial_to_total[OF hoare_partial_sound[OF hhl_prog_success[OF A n0 k t0 spec Ub Cb Us circ] hhl_prog_well_com[OF Us]]
          hhl_prog_while_free hhl_prog_well_com[OF Us]])
qed

theorem hhl_prog_correct_total:
  assumes Us: "\<And>U. U \<in> set Us \<Longrightarrow> U \<in> carrier_mat (2 ^ k * (n * 2)) (2 ^ k * (n * 2)) \<and> Complex_Matrix.unitary U"
      and circ: "circuit_mat (2 ^ k * (n * 2)) Us = circuit_mat (2 ^ k * (n * 2)) (hhl_gates A Ub t0 k C)"
  shows "state_sig.hoare_total_correct [2 ^ k, n, 2] (1\<^sub>m (2 ^ k * (n * 2))) (hhl_prog (2 ^ k * (n * 2)) Us)
     (anc_proj (2 ^ k * (n * 2)) 0 + outer_prod (hhl_target A k b) (hhl_target A k b))"
proof -
  interpret state_sig "[2 ^ k, n, 2]" .
  show ?thesis
    by (rule partial_to_total[OF hoare_partial_sound[OF hhl_prog_correct[OF A n0 k t0 spec Ub Cb Us circ] hhl_prog_well_com[OF Us]]
          hhl_prog_while_free hhl_prog_well_com[OF Us]])
qed

theorem hhl_rus_prog_partial:
  assumes Us: "\<And>U. U \<in> set Us \<Longrightarrow> U \<in> carrier_mat (2 ^ k * (n * 2)) (2 ^ k * (n * 2)) \<and> Complex_Matrix.unitary U"
      and circ: "circuit_mat (2 ^ k * (n * 2)) Us = circuit_mat (2 ^ k * (n * 2)) (hhl_gates A Ub t0 k C)"
  shows "state_sig.hoare_partial_correct [2 ^ k, n, 2] (1\<^sub>m (2 ^ k * (n * 2))) (hhl_rus_prog (2 ^ k * (n * 2)) Us)
     (outer_prod (hhl_target A k b) (hhl_target A k b))"
proof -
  interpret state_sig "[2 ^ k, n, 2]" .
  show ?thesis by (rule hoare_partial_sound[OF hhl_rus_prog_correct[OF A n0 k t0 spec Ub Cb Us circ] hhl_rus_prog_well_com[OF Us]])
qed

theorem hhl_success_total:
  "state_sig.hoare_total_correct [2 ^ k, n, 2] (complex_of_real (C\<^sup>2 * \<parallel>herm_inv A *\<^sub>v b\<parallel>\<^sup>2) \<cdot>\<^sub>m 1\<^sub>m (2 ^ k * (n * 2)))
     (hhl_program A Ub t0 k C) (anc_proj (2 ^ k * (n * 2)) 1)"
  unfolding hhl_program_def carrier_matD(1)[OF A(1)] by (rule hhl_prog_success_total[OF prog_gates[OF A n0 k t0 spec Ub Cb] refl])

theorem hhl_correct_total:
  "state_sig.hoare_total_correct [2 ^ k, n, 2] (1\<^sub>m (2 ^ k * (n * 2))) (hhl_program A Ub t0 k C)
     (anc_proj (2 ^ k * (n * 2)) 0 + outer_prod (hhl_target A k b) (hhl_target A k b))"
  unfolding hhl_program_def carrier_matD(1)[OF A(1)] by (rule hhl_prog_correct_total[OF prog_gates[OF A n0 k t0 spec Ub Cb] refl])

theorem hhl_rus_partial:
  "state_sig.hoare_partial_correct [2 ^ k, n, 2] (1\<^sub>m (2 ^ k * (n * 2))) (hhl_rus A Ub t0 k C)
     (outer_prod (hhl_target A k b) (hhl_target A k b))"
  unfolding hhl_rus_def carrier_matD(1)[OF A(1)] by (rule hhl_rus_prog_partial[OF prog_gates[OF A n0 k t0 spec Ub Cb] refl])

lemma states_ok:
  "i \<le> 8 \<Longrightarrow> dim_vec (hhl_states A b t0 k C ! i) = 2 ^ k * (n * 2)
     \<and> inner_prod (hhl_states A b t0 k C ! i) (hhl_states A b t0 k C ! i) = 1"
proof (induction i)
  case 0
  let ?\<psi> = "tensor_vec (unit_vec (2 ^ k) 0) (tensor_vec (unit_vec n 0) (unit_vec 2 0))"
  have nA: "dim_row A = n" using A(1) by simp
  have e: "\<parallel>unit_vec m 0\<parallel> = 1" if "0 < m" for m :: nat
    using that by (simp add: cpx_vec_length_def lessThan_atLeast0 sum.atLeast_Suc_lessThan unit_vec_def)
  have d: "dim_vec ?\<psi> = 2 ^ k * (n * 2)" by (simp add: tensor_vec_dim)
  have "\<parallel>?\<psi>\<parallel> = 1" using e[of "2 ^ k"] e[OF n0] e[of 2] by (simp add: vnorm_tensor tensor_vec_dim)
  hence "\<langle>?\<psi>|?\<psi>\<rangle> = 1" using cpx_vec_length_inner_prod[of ?\<psi>] by simp
  hence "inner_prod ?\<psi> ?\<psi> = 1" using inner_bridge[of ?\<psi> ?\<psi>] by simp
  thus ?case using d by (simp add: hhl_states_def Let_def nA)
next
  case (Suc i)
  interpret state_sig "[2 ^ k, n, 2]" .
  have dd: "d = 2 ^ k * (n * 2)" by (simp add: d_def)
  have i: "i < 8" using Suc.prems by simp
  have G: "hhl_gates A Ub t0 k C ! i \<in> carrier_mat d d" "Complex_Matrix.unitary (hhl_gates A Ub t0 k C ! i)"
  proof -
    have m: "hhl_gates A Ub t0 k C ! i \<in> set (hhl_gates A Ub t0 k C)" by (rule nth_mem) (use i in simp)
    show "hhl_gates A Ub t0 k C ! i \<in> carrier_mat d d" "Complex_Matrix.unitary (hhl_gates A Ub t0 k C ! i)"
      using prog_gates[OF A n0 k t0 spec Ub Cb m] dd by auto
  qed
  have IH: "dim_vec (hhl_states A b t0 k C ! i) = d" "inner_prod (hhl_states A b t0 k C ! i) (hhl_states A b t0 k C ! i) = 1"
    using Suc.IH i dd by auto
  have st: "hhl_states A b t0 k C ! Suc i = hhl_gates A Ub t0 k C ! i *\<^sub>v hhl_states A b t0 k C ! i"
    by (rule hhl_steps[OF A n0 k t0 spec Ub i, symmetric])
  show ?case unfolding st using G(1) unitary_inner_keep[OF G IH(1)] IH dd by simp
qed

text \<open>The Hoare-logic trajectory: each gate takes the pure state $\ket{\psi_i}\bra{\psi_i}$ to
$\ket{\psi_{i+1}}\bra{\psi_{i+1}}$ (\<open>hhl_states\<close>), and the whole circuit takes $\ket{000}$ to
$\ket0\otimes\mathrm{out}$.\<close>

theorem hhl_step_triples:
  assumes i: "i < 8"
  shows "state_sig.hoare_partial [2 ^ k, n, 2]
           (outer_prod (hhl_states A b t0 k C ! i) (hhl_states A b t0 k C ! i))
           (Utrans (hhl_gates A Ub t0 k C ! i))
           (outer_prod (hhl_states A b t0 k C ! Suc i) (hhl_states A b t0 k C ! Suc i))"
proof -
  interpret state_sig "[2 ^ k, n, 2]" .
  have dd: "d = 2 ^ k * (n * 2)" by (simp add: d_def)
  have G: "hhl_gates A Ub t0 k C ! i \<in> carrier_mat d d" "Complex_Matrix.unitary (hhl_gates A Ub t0 k C ! i)"
  proof -
    have m: "hhl_gates A Ub t0 k C ! i \<in> set (hhl_gates A Ub t0 k C)" by (rule nth_mem) (use i in simp)
    show "hhl_gates A Ub t0 k C ! i \<in> carrier_mat d d" "Complex_Matrix.unitary (hhl_gates A Ub t0 k C ! i)"
      using prog_gates[OF A n0 k t0 spec Ub Cb m] dd by auto
  qed
  have S: "dim_vec (hhl_states A b t0 k C ! i) = d" "inner_prod (hhl_states A b t0 k C ! i) (hhl_states A b t0 k C ! i) = 1"
    using states_ok[of i] i dd by auto
  show ?thesis using hoare_utrans_pure[OF G S] hhl_steps[OF A n0 k t0 spec Ub i] by simp
qed

theorem hhl_trajectory:
  "state_sig.hoare_partial [2 ^ k, n, 2]
     (outer_prod (hhl_states A b t0 k C ! 0) (hhl_states A b t0 k C ! 0))
     (utrans_seq (hhl_gates A Ub t0 k C))
     (outer_prod (hhl_states A b t0 k C ! 8) (hhl_states A b t0 k C ! 8))"
proof -
  interpret state_sig "[2 ^ k, n, 2]" .
  have dd: "d = 2 ^ k * (n * 2)" by (simp add: d_def)
  have nA: "dim_row A = n" using A(1) by simp
  have S: "dim_vec (hhl_states A b t0 k C ! 0) = d" "inner_prod (hhl_states A b t0 k C ! 0) (hhl_states A b t0 k C ! 0) = 1"
    using states_ok[of 0] dd by auto
  have r: "run_gates (hhl_states A b t0 k C ! 0) (hhl_gates A Ub t0 k C) = hhl_states A b t0 k C ! 8"
    using hhl_run[OF A n0 k t0 spec Ub] by (simp add: hhl_states_def Let_def nA)
  have g: "\<And>U. U \<in> set (hhl_gates A Ub t0 k C) \<Longrightarrow> U \<in> carrier_mat d d \<and> Complex_Matrix.unitary U"
    using prog_gates[OF A n0 k t0 spec Ub Cb] dd by auto
  show ?thesis using hoare_run[where Us = "hhl_gates A Ub t0 k C", OF g S] unfolding r .
qed

end

end

theory Program_Channels
  imports Vern_Paulsen_QC.Day32_Recovery_Proposition Vern_Paulsen_QC.Day23_ChoiExtremeUCP
    Vern_Paulsen_QC.Day22_Adjoint_Maps HHL_Algorithm.HHL_Program
begin

section \<open>Loop-free programs are channels\<close>

text \<open>The programs of \<open>HHL_Algorithm\<close> are commands of the quantum while-language of AFP \<open>QHLProver\<close>, whose
meaning is a map on density matrices.  For a program without loops this map is the Kraus map
$\rho\mapsto\sum_i K_i\rho K_i^*$ of the lectures (Lecture 19), with Kraus operators read off the
program: a gate $U$ gives $U$; a sequence gives the products $BA$ (\<^const>\<open>kraus_compose\<close> of
Days 32--33); a measurement $\{M_k\}$ gives $BM_k$ for every Kraus operator $B$ of branch $k$.
The operators satisfy $\sum_i K_i^*K_i=I$, so the meaning is completely positive and trace
preserving (Choi's theorem in the form \<open>kraus_is_cp\<close>).\<close>

text \<open>Kraus operators of a measurement $\{M_k\}_{k<n}$ whose branch $k$ has Kraus operators \<open>Ks ! k\<close>,
and of a program on $d$-dimensional states (none for a loop).\<close>

fun meas_kraus :: "nat \<Rightarrow> (nat \<Rightarrow> complex Matrix.mat) \<Rightarrow> complex Matrix.mat list list \<Rightarrow> complex Matrix.mat list" where
  "meas_kraus 0 M Ks = []"
| "meas_kraus (Suc k) M Ks = map (\<lambda>B. B * M k) (Ks ! k) @ meas_kraus k M Ks"

fun kraus_of :: "nat \<Rightarrow> com \<Rightarrow> complex Matrix.mat list" where
  "kraus_of d SKIP = [1\<^sub>m d]"
| "kraus_of d (Utrans U) = [U]"
| "kraus_of d (c1 ;; c2) = kraus_compose (kraus_of d c2) (kraus_of d c1)"
| "kraus_of d (Measure n M Ss) = meas_kraus n M (map (kraus_of d) Ss)"
| "kraus_of d (While M c) = []"

lemma set_meas_kraus: "w \<in> set (meas_kraus n M Ks) \<longleftrightarrow> (\<exists>k<n. \<exists>B \<in> set (Ks ! k). w = B * M k)"
  by (induction n) (auto simp: less_Suc_eq)

context state_sig
begin

lemma kraus_of_carrier:
  "well_com c \<Longrightarrow> while_free c \<Longrightarrow> \<forall>w \<in> set (kraus_of d c). w \<in> carrier_mat d d"
proof (induction c)
  case (Seq c1 c2)
  thus ?case by (auto intro: kraus_compose_carrier[rule_format])
next
  case (Measure n M Ss)
  have wc: "\<And>k. k < n \<Longrightarrow> well_com (Ss ! k)" "\<And>k. k < n \<Longrightarrow> while_free (Ss ! k)" "length Ss = n"
    "\<And>k. k < n \<Longrightarrow> M k \<in> carrier_mat d d"
    using Measure.prems by (auto simp: list_all_length measurement_def)
  show ?case
  proof
    fix w assume "w \<in> set (kraus_of d (Measure n M Ss))"
    hence "\<exists>k<n. \<exists>B \<in> set (map (kraus_of d) Ss ! k). w = B * M k" by (simp only: kraus_of.simps set_meas_kraus)
    then obtain k B where k: "k < n" and B0: "B \<in> set (map (kraus_of d) Ss ! k)" and w: "w = B * M k" by blast
    have B: "B \<in> set (kraus_of d (Ss ! k))" using B0 k wc(3) by simp
    have "B \<in> carrier_mat d d" using Measure.IH[OF nth_mem wc(1,2)] k B wc(3) by auto
    thus "w \<in> carrier_mat d d" unfolding w using wc(4)[OF k] by simp
  qed
qed auto

text \<open>The meaning of a loop-free program is its Kraus map.\<close>

lemma kraus_map_meas:
  assumes M: "\<And>k. k < n \<Longrightarrow> M k \<in> carrier_mat d d"
      and Ks: "\<And>k. k < n \<Longrightarrow> \<forall>B \<in> set (Ks ! k). B \<in> carrier_mat d d"
      and r: "r \<in> carrier_mat d d"
  shows "kraus_map_dim d (meas_kraus n M Ks) r = matrix_sum d (\<lambda>k. kraus_map_dim d (Ks ! k) (M k * r * adjoint (M k))) n"
  using M Ks
proof (induction n)
  case (Suc n)
  have c1: "\<forall>B \<in> set (map (\<lambda>B. B * M n) (Ks ! n)). B \<in> carrier_mat d d"
    using Suc.prems(1)[of n] Suc.prems(2)[of n] by (auto intro: mult_carrier_mat)
  have c2: "\<forall>B \<in> set (meas_kraus n M Ks). B \<in> carrier_mat d d"
  proof
    fix B assume "B \<in> set (meas_kraus n M Ks)"
    then obtain k E where k: "k < n" and E: "E \<in> set (Ks ! k)" and B: "B = E * M k" unfolding set_meas_kraus by blast
    have "E \<in> carrier_mat d d" using Suc.prems(2)[of k] k E by simp
    thus "B \<in> carrier_mat d d" unfolding B using Suc.prems(1)[of k] k by simp
  qed
  have "kraus_map_dim d (map (\<lambda>B. B * M n) (Ks ! n)) r = kraus_map_dim d (Ks ! n) (M n * r * adjoint (M n))"
    using kraus_map_dim_map_mult_right[of "Ks ! n" d d "M n" d r] Suc.prems(1)[of n] Suc.prems(2)[of n] r by (simp add: dagger_adjoint)
  moreover have "kraus_map_dim d (meas_kraus n M Ks) r = matrix_sum d (\<lambda>k. kraus_map_dim d (Ks ! k) (M k * r * adjoint (M k))) n"
    by (rule Suc.IH) (use Suc.prems less_SucI in blast)+
  ultimately show ?case by (simp add: kraus_map_dim_append[OF c1 c2 r])
qed simp

theorem denote_kraus:
  "well_com c \<Longrightarrow> while_free c \<Longrightarrow> r \<in> carrier_mat d d \<Longrightarrow> denote c r = kraus_map_dim d (kraus_of d c) r"
proof (induction c arbitrary: r)
  case SKIP
  thus ?case by simp
next
  case (Utrans U)
  hence "U * r * adjoint U \<in> carrier_mat d d" by auto
  thus ?case by (simp add: dagger_adjoint)
next
  case (Seq c1 c2)
  have k1: "\<forall>w \<in> set (kraus_of d c1). w \<in> carrier_mat d d" and k2: "\<forall>w \<in> set (kraus_of d c2). w \<in> carrier_mat d d"
    using kraus_of_carrier Seq.prems by auto
  have "denote c1 r \<in> carrier_mat d d" using Seq kraus_map_dim_carrier k1 by auto
  thus ?case using Seq kraus_map_dim_compose[OF k2 k1 Seq.prems(3)] by simp
next
  case (Measure n M Ss)
  have wc: "\<And>k. k < n \<Longrightarrow> well_com (Ss ! k)" "\<And>k. k < n \<Longrightarrow> while_free (Ss ! k)" "length Ss = n"
    "\<And>k. k < n \<Longrightarrow> M k \<in> carrier_mat d d"
    using Measure.prems by (auto simp: list_all_length measurement_def)
  have Ks: "\<forall>B \<in> set (map (kraus_of d) Ss ! k). B \<in> carrier_mat d d" if k: "k < n" for k
    using kraus_of_carrier[OF wc(1,2)[OF k]] k wc(3) by simp
  have "denote (Measure n M Ss) r = matrix_sum d (\<lambda>k. denote (Ss ! k) (M k * r * adjoint (M k))) n"
    unfolding denote.simps denote_measure_def by (rule matrix_sum_cong) (simp add: wc(3))
  also have "\<dots> = matrix_sum d (\<lambda>k. kraus_map_dim d (map (kraus_of d) Ss ! k) (M k * r * adjoint (M k))) n"
  proof (rule matrix_sum_cong)
    fix k assume k: "k < n"
    have "M k * r * adjoint (M k) \<in> carrier_mat d d" using wc(4)[OF k] Measure.prems(3) by (auto intro!: mult_carrier_mat adjoint_dim)
    thus "denote (Ss ! k) (M k * r * adjoint (M k)) = kraus_map_dim d (map (kraus_of d) Ss ! k) (M k * r * adjoint (M k))"
      using Measure.IH[OF nth_mem wc(1,2)] k wc(3) by simp
  qed
  also have "\<dots> = kraus_map_dim d (kraus_of d (Measure n M Ss)) r"
    using kraus_map_meas[OF wc(4) Ks Measure.prems(3)] by simp
  finally show ?case .
qed simp

text \<open>The Kraus operators are complete: $\sum_i K_i^*K_i=I$.\<close>

lemma sum_wdag_meas:
  assumes M: "\<And>k. k < n \<Longrightarrow> M k \<in> carrier_mat d d"
      and Ks: "\<And>k. k < n \<Longrightarrow> kraus_operators d d (Ks ! k)"
  shows "sum_wdag_w d (meas_kraus n M Ks) = matrix_sum d (\<lambda>j. adjoint (M j) * M j) n"
  using M Ks
proof (induction n)
  case (Suc n)
  have Kn: "\<forall>B \<in> set (Ks ! n). B \<in> carrier_mat d d" "sum_wdag_w d (Ks ! n) = 1\<^sub>m d"
    using Suc.prems(2)[of n] by (simp_all add: kraus_operators_altdef)
  have c1: "\<forall>B \<in> set (map (\<lambda>B. B * M n) (Ks ! n)). B \<in> carrier_mat d d"
    using Kn(1) Suc.prems(1)[of n] by (auto intro: mult_carrier_mat)
  have c2: "\<forall>B \<in> set (meas_kraus n M Ks). B \<in> carrier_mat d d"
  proof
    fix B assume "B \<in> set (meas_kraus n M Ks)"
    then obtain j E where j: "j < n" and E: "E \<in> set (Ks ! j)" and B: "B = E * M j" unfolding set_meas_kraus by blast
    have "E \<in> carrier_mat d d" using Suc.prems(2)[of j] j E by (simp add: kraus_operators_def)
    thus "B \<in> carrier_mat d d" unfolding B using Suc.prems(1)[of j] j by simp
  qed
  have "sum_wdag_w d (map (\<lambda>B. B * M n) (Ks ! n)) = adjoint (M n) * M n"
    using sum_wdag_w_map_mult_right[OF Kn(1) Suc.prems(1)[of n]] Kn(2) Suc.prems(1)[of n] by (simp add: dagger_adjoint)
  moreover have "sum_wdag_w d (meas_kraus n M Ks) = matrix_sum d (\<lambda>j. adjoint (M j) * M j) n"
    by (rule Suc.IH) (use Suc.prems less_SucI in blast)+
  ultimately show ?case by (simp add: sum_wdag_w_append[OF c1 c2])
qed simp

theorem kraus_of_operators: "well_com c \<Longrightarrow> while_free c \<Longrightarrow> kraus_operators d d (kraus_of d c)"
proof (induction c)
  case SKIP
  thus ?case by (simp add: kraus_operators_def)
next
  case (Utrans U)
  hence a: "Complex_Matrix.adjoint U * U = 1\<^sub>m d" using unitary_simps by auto
  show ?case using Utrans.prems a by (auto simp: kraus_operators_def dagger_adjoint)
next
  case (Seq c1 c2)
  thus ?case by (auto intro: kraus_operators_compose)
next
  case (Measure n M Ss)
  have wc: "\<And>k. k < n \<Longrightarrow> well_com (Ss ! k)" "\<And>k. k < n \<Longrightarrow> while_free (Ss ! k)" "length Ss = n"
    "\<And>k. k < n \<Longrightarrow> M k \<in> carrier_mat d d" "matrix_sum d (\<lambda>j. adjoint (M j) * M j) n = 1\<^sub>m d"
    using Measure.prems by (auto simp: list_all_length measurement_def)
  have Ks: "kraus_operators d d (map (kraus_of d) Ss ! k)" if k: "k < n" for k
    using Measure.IH[OF nth_mem wc(1,2)[OF k]] k wc(3) by simp
  show ?case
    unfolding kraus_operators_altdef
    using kraus_of_carrier[OF Measure.prems] sum_wdag_meas[OF wc(4) Ks] wc(5) by simp
qed simp

text \<open>A loop-free program denotes the channel with these Kraus operators (Lecture 19).\<close>

theorem program_channel:
  assumes "well_com c" "while_free c"
  shows "cptp_kraus_rep d d (denote c) (kraus_of d c)"
  unfolding cptp_kraus_rep_def using kraus_of_operators[OF assms] denote_kraus[OF assms] by simp

corollary program_cptp:
  assumes "well_com c" "while_free c" "0 < d"
  shows "completely_positive d d (denote c)" "trace_preserving d (denote c)"
proof -
  have e: "\<And>r. r \<in> carrier_mat d d \<Longrightarrow> denote c r = kraus_map_dim d (kraus_of d c) r"
    using denote_kraus[OF assms(1,2)] by simp
  show "completely_positive d d (denote c)"
    using completely_positive_cong[of d "denote c" "kraus_map_dim d (kraus_of d c)" d] e
          kraus_is_cp[OF kraus_of_operators[OF assms(1,2)] assms(3) assms(3)] by simp
  show "trace_preserving d (denote c)"
    using trace_preserving_cong[of d "denote c" "kraus_map_dim d (kraus_of d c)"] e
          kraus_is_trace_preserving[OF kraus_of_operators[OF assms(1,2)]] by simp
qed

end

text \<open>The HHL program is a channel on the clock, system and ancilla registers.\<close>

theorem hhl_program_channel:
  fixes A Ub :: "complex Matrix.mat" and b :: "complex Matrix.vec" and n k :: nat and t0 C :: real
  assumes A: "A \<in> carrier_mat n n" "Complex_Matrix.hermitian A" and n0: "0 < n" and k: "1 \<le> k" and t0: "0 < t0"
    and spec: "\<And>l. l \<in> herm_spectrum A \<Longrightarrow> \<exists>j. 0 < j \<and> j < 2 ^ k \<and> l = reg_eig t0 (2 ^ k) j"
    and Ub: "Ub \<in> carrier_mat n n" "Quantum.unitary Ub" "Ub *\<^sub>v unit_vec n 0 = b"
    and Cb: "\<And>j. j < 2 ^ k \<Longrightarrow> \<bar>C / reg_eig t0 (2 ^ k) j\<bar> \<le> 1"
  shows "cptp_kraus_rep (2 ^ k * (n * 2)) (2 ^ k * (n * 2)) (state_sig.denote [2 ^ k, n, 2] (hhl_program A Ub t0 k C))
           (kraus_of (2 ^ k * (n * 2)) (hhl_program A Ub t0 k C))"
  using state_sig.program_channel[OF hhl_program_well_com[OF A n0 k t0 spec Ub Cb]
          hhl_program_while_free[OF A n0 k t0 spec Ub Cb]]
  by (simp add: state_sig.d_def)

end

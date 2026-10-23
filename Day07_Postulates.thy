(*  Title:   Day07_Postulates.thy
    Author:  Dustin Bryant, after Vern Paulsen's lecture of 12 September 2011 (Day 7)
*)

theory Day07_Postulates
  imports Day06_Tensor_Products
begin

section \<open>Day 7 (12 September 2011): tensor products of Hilbert spaces; the postulates\<close>

text \<open>\begin{notesremark}
For Hilbert spaces $\Hil,\Kil$ set
$\langle h_1\otimes k_1|h_2\otimes k_2\rangle=\braket{h_1}{h_2}_{\Hil}\braket{k_1}{k_2}_{\Kil}$.
\end{notesremark}
\begin{notestheorem}
This extends to a sesquilinear form on $\Hil\otimes\Kil$ with $\langle u|u\rangle=0$ only
for $u=0$, hence to an inner product; in finite dimensions $\Hil\otimes\Kil$ with this inner
product is the Hilbert space tensor product (in infinite dimensions one completes).
\end{notestheorem}
\begin{notesprop}
If $\{h_i\}$ and $\{k_j\}$ are orthonormal bases of $\Hil$ and $\Kil$, then
$\{h_i\otimes k_j\}$ is an orthonormal basis of $\Hil\otimes\Kil$.
\end{notesprop}
In physics notation $e_i\otimes e_j=\ket{ij}$, and for $N$ qubits
$e_{i_1}\otimes\cdots\otimes e_{i_N}=\ket{i_1\cdots i_N}$ with the multi-index
$I=(i_1,\dots,i_N)\in\Z_2^N$.  In the concrete model positivity of the form is automatic;
the multiplicativity of the inner product and the orthonormal product basis are proved
below.\<close>

lemma tensor_inner_prod:
  assumes "dim_vec h1 = n" "dim_vec h2 = n"
          "dim_vec k1 = m" "dim_vec k2 = m"
  shows "\<langle>tensor_vec h1 k1 | tensor_vec h2 k2\<rangle> =
         \<langle>h1 | h2\<rangle> * \<langle>k1 | k2\<rangle>"
proof -
  let ?f = "\<lambda>i. cnj (tensor_vec h1 k1 $ i) * tensor_vec h2 k2 $ i"

  have step1:
    "\<langle>tensor_vec h1 k1 | tensor_vec h2 k2\<rangle> =
     (\<Sum>i = 0..<n*m. ?f i)"
    using assms
    by (simp add: inner_prod_def tensor_vec_dim)

  have step2:
    "(\<Sum>i = 0..<n*m. ?f i) =
     (\<Sum>a = 0..<n. \<Sum>b = 0..<m. ?f (a*m+b))"
  proof -
    have "(\<Sum>i = 0..<n*m. ?f i) = (\<Sum>a<n. sum ?f {a*m..<a*m+m})"
      using sum.nat_group[of ?f m n]
      by (simp add: atLeast0LessThan)
    also have "... = (\<Sum>a = 0..<n. \<Sum>b = 0..<m. ?f (a*m+b))"
    proof (rule sum.cong)
      show "{..<n} = {0..<n}" by auto
    next
      fix a
      assume a: "a \<in> {0..<n}"
      have "sum ?f {a*m..<a*m+m} = (\<Sum>b = 0..<m. ?f (a*m+b))"
      proof (rule sum.reindex_bij_witness[where i = "\<lambda>b. a*m+b" and j = "\<lambda>x. x - a*m"])
        show "\<And>b. b \<in> {0..<m} \<Longrightarrow> a*m + b \<in> {a*m..<a*m+m}"
          by simp
        show "\<And>x. x \<in> {a*m..<a*m+m} \<Longrightarrow> x - a*m \<in> {0..<m}"
          by fastforce
        show "\<And>x. x \<in> {a*m..<a*m+m} \<Longrightarrow> (\<lambda>b. a*m+b) (x - a*m) = x"
          by simp
        show "\<And>b. b \<in> {0..<m} \<Longrightarrow> (\<lambda>x. x - a*m) ((\<lambda>b. a*m+b) b) = b"
          by simp
        show "\<And>b. b \<in> {a * m..<a * m + m} \<Longrightarrow>
            (cnj ((tensor_vec h1 k1) $ (a * m + (b - a * m))) *
             ((tensor_vec h2 k2) $ (a * m + (b - a * m)))) =
            (cnj ((tensor_vec h1 k1) $ b) *
             ((tensor_vec h2 k2) $ b))"
            by force
      qed
      then show "(\<Sum>i = a * m..<a * m + m.
        (cnj ((tensor_vec h1 k1) $ i)) * ((tensor_vec h2 k2) $ i)) =
        (\<Sum>b = 0..<m.(cnj ((tensor_vec h1 k1) $ (a * m + b))) * ((tensor_vec h2 k2) $ (a*m + b)))".
    qed
    finally show ?thesis.
  qed

  have step3:
    "(\<Sum>a = 0..<n. \<Sum>b = 0..<m. ?f (a*m+b)) =
     (\<Sum>a = 0..<n. \<Sum>b = 0..<m.
        cnj (h1 $ a * k1 $ b) * (h2 $ a * k2 $ b))"
  proof (rule sum.cong)
    show "{0..<n} = {0..<n}" by simp
  next
    fix a
    assume a: "a \<in> {0..<n}"
    show "(\<Sum>b = 0..<m. ?f (a*m+b)) =
          (\<Sum>b = 0..<m. cnj (h1 $ a * k1 $ b) * (h2 $ a * k2 $ b))"
    proof (rule sum.cong)
      show "{0..<m} = {0..<m}" by simp
    next
      fix b
      assume b: "b \<in> {0..<m}"
      have alt: "a < n"
        using a by simp
      have blt: "b < m"
        using b by simp
      have ab_lt: "a * m + b < n * m"
      proof -
        have "a * m + b < a * m + m"
          using blt by simp
        also have "... \<le> n * m"
          by (metis Suc_leI add.commute alt mult_Suc mult_le_mono1)
        finally show ?thesis.
      qed
      have div_eq: "(a*m+b) div m = a" using blt by simp
      have mod_eq: "(a*m+b) mod m = b" using blt by simp
      have idx1: "tensor_vec h1 k1 $ (a*m+b) = h1 $ a * k1 $ b"
        using tensor_vec_index[OF assms(1) assms(3) ab_lt] div_eq mod_eq by simp

      have idx2: "tensor_vec h2 k2 $ (a*m+b) = h2 $ a * k2 $ b"
        using tensor_vec_index[OF assms(2) assms(4) ab_lt] div_eq mod_eq by simp

      show "?f (a*m+b) = cnj (h1 $ a * k1 $ b) * (h2 $ a * k2 $ b)"
        unfolding idx1 idx2 by simp
    qed
  qed

  have step4:
    "(\<Sum>a = 0..<n. \<Sum>b = 0..<m.
        cnj (h1 $ a * k1 $ b) * (h2 $ a * k2 $ b)) =
     (\<Sum>a = 0..<n. \<Sum>b = 0..<m.
        (cnj (h1 $ a) * h2 $ a) * (cnj (k1 $ b) * k2 $ b))"
    by (smt (verit, best) complex_cnj_mult mult.commute semigroup_mult_class.mult.assoc sum.cong)


  have step5:
  "(\<Sum>a = 0..<n. \<Sum>b = 0..<m.
      (cnj (h1 $ a) * h2 $ a) * (cnj (k1 $ b) * k2 $ b)) =
   (\<Sum>a = 0..<n. cnj (h1 $ a) * h2 $ a) *
   (\<Sum>b = 0..<m. cnj (k1 $ b) * k2 $ b)"
  proof -
    have "(\<Sum>a = 0..<n. \<Sum>b = 0..<m.
            (cnj (h1 $ a) * h2 $ a) * (cnj (k1 $ b) * k2 $ b))
        = (\<Sum>a = 0..<n. (cnj (h1 $ a) * h2 $ a) * (\<Sum>b = 0..<m. cnj (k1 $ b) * k2 $ b))"
      by (simp add: sum_distrib_left algebra_simps)
    also have "... =
        (\<Sum>a = 0..<n. cnj (h1 $ a) * h2 $ a) *
        (\<Sum>b = 0..<m. cnj (k1 $ b) * k2 $ b)"
      by (simp add: sum_distrib_right algebra_simps)
    finally show ?thesis .
  qed

  have step6:
    "(\<Sum>a = 0..<n. cnj (h1 $ a) * h2 $ a) *
     (\<Sum>b = 0..<m. cnj (k1 $ b) * k2 $ b)
     = \<langle>h1 | h2\<rangle> * \<langle>k1 | k2\<rangle>"
    using assms
    by (simp add: inner_prod_def)

  show ?thesis
    using step1 step2 step3 step4 step5 step6
    by argo
qed


lemma length_concat_map_upt:
  "length (concat (map (\<lambda>i. map (\<lambda>j. f i j) [0..<m]) [0..<n])) = n * m"
  by (simp add: length_concat o_def sum_list_triv)

lemma nth_concat_map_upt:
  assumes p_lt: "p < n * m"
  shows "concat (map (\<lambda>i. map (\<lambda>j. f i j) [0..<m]) [0..<n]) ! p =
         f (p div m) (p mod m)"
  using p_lt
proof (induction n arbitrary: p)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have m_pos: "0 < m"
    using Suc.prems by (cases m) auto
  have upt_Suc: "[0..<Suc n] = [0..<n] @ [n]"
    by (simp add: upt_Suc_append)
  show ?case
  proof (cases "p < n * m")
    case True
    have len_prev:
      "length (concat (map (\<lambda>i. map (\<lambda>j. f i j) [0..<m]) [0..<n])) = n * m"
      by (rule length_concat_map_upt)
    have "concat (map (\<lambda>i. map (\<lambda>j. f i j) [0..<m]) [0..<Suc n]) ! p =
          concat (map (\<lambda>i. map (\<lambda>j. f i j) [0..<m]) [0..<n]) ! p"
      using True len_prev
      by (simp add: upt_Suc nth_append)
    also have "... = f (p div m) (p mod m)"
      using Suc.IH[OF True] .
    finally show ?thesis .
  next
    case False
    have p_ge: "n * m \<le> p"
      using False by simp
    define r where "r = p - n * m"
    have p_eq: "p = n * m + r"
      using p_ge by (simp add: r_def)
    have r_lt: "r < m"
      using Suc.prems p_eq by simp
    have div_eq: "p div m = n"
      using p_eq r_lt m_pos by simp
    have mod_eq: "p mod m = r"
      using p_eq r_lt by simp
    have len_prev:
      "length (concat (map (\<lambda>i. map (\<lambda>j. f i j) [0..<m]) [0..<n])) = n * m"
      by (rule length_concat_map_upt)
    have "concat (map (\<lambda>i. map (\<lambda>j. f i j) [0..<m]) [0..<Suc n]) ! p =
          (map (\<lambda>j. f n j) [0..<m]) ! r"
      using p_eq len_prev
      by (simp add: upt_Suc nth_append)
    also have "... = f n r"
      using r_lt by simp
    also have "... = f (p div m) (p mod m)"
      using div_eq mod_eq by simp
    finally show ?thesis .
  qed
qed

lemma tensor_onb:
  assumes hs_onb: "orthonormal_list n hs"
      and hs_len: "length hs = n"
      and ks_onb: "orthonormal_list m ks"
      and ks_len: "length ks = m"
  shows "orthonormal_list (n*m)
         [tensor_vec (hs ! i) (ks ! j). i \<leftarrow> [0..<n], j \<leftarrow> [0..<m]]"
proof -
  let ?ts = "[tensor_vec (hs ! i) (ks ! j). i \<leftarrow> [0..<n], j \<leftarrow> [0..<m]]"

  have ts_len: "length ?ts = n * m"
    using length_concat_map_upt[of "\<lambda>i j. tensor_vec (hs ! i) (ks ! j)" m n]
    by simp

  have hs_dim:
    "\<And>i. i < n \<Longrightarrow> dim_vec (hs ! i) = n"
    using hs_onb hs_len
    unfolding orthonormal_list_def
    by auto

  have ks_dim:
    "\<And>j. j < m \<Longrightarrow> dim_vec (ks ! j) = m"
    using ks_onb ks_len
    unfolding orthonormal_list_def
    by auto

  have hs_ip:
    "\<And>i j. i < n \<Longrightarrow> j < n \<Longrightarrow> \<langle>hs ! i | hs ! j\<rangle> = (if i = j then 1 else 0)"
    using hs_onb hs_len
    unfolding orthonormal_list_def
    by auto

  have ks_ip:
    "\<And>i j. i < m \<Longrightarrow> j < m \<Longrightarrow> \<langle>ks ! i | ks ! j\<rangle> = (if i = j then 1 else 0)"
    using ks_onb ks_len
    unfolding orthonormal_list_def
    by auto

  have nth_ts: "\<And>p. p < n*m \<Longrightarrow> ?ts ! p = tensor_vec (hs ! (p div m)) (ks ! (p mod m))"
  proof -
    fix p
    assume p_lt: "p < n*m"
    then have div_lt: "p div m < n"
      using less_mult_imp_div_less by presburger

    have mod_lt: "p mod m < m"
      by (metis mod_by_0 mod_less_divisor mod_mult_self2_is_0 p_lt zero_less_iff_neq_zero)


    have "?ts = concat (map (\<lambda>i. map (\<lambda>j. tensor_vec (hs ! i) (ks ! j)) [0..<m]) [0..<n])"
      by simp
    moreover have
      "concat (map (\<lambda>i. map (\<lambda>j. tensor_vec (hs ! i) (ks ! j)) [0..<m]) [0..<n]) ! p
       = tensor_vec (hs ! (p div m)) (ks ! (p mod m))"
      using nth_concat_map_upt[OF p_lt, of "\<lambda>i j. tensor_vec (hs ! i) (ks ! j)"] .
    ultimately show "?ts ! p = tensor_vec (hs ! (p div m)) (ks ! (p mod m))"
      by simp
  qed

  have ts_dim:  "\<And>p. p < length ?ts \<Longrightarrow> dim_vec (?ts ! p) = n*m"
  proof -
    fix p
    assume p_lt: "p < length ?ts"
    then have p_lt': "p < n*m"
      using ts_len by simp
    have div_lt: "p div m < n"
      using less_mult_imp_div_less p_lt' by blast
    have mod_lt: "p mod m < m"
      using p_lt' ks_len
      by (cases m, auto)
    have "?ts ! p = tensor_vec (hs ! (p div m)) (ks ! (p mod m))"
      using nth_ts p_lt' by blast
    then show "dim_vec (?ts ! p) = n*m"
      using hs_dim[OF div_lt] ks_dim[OF mod_lt] tensor_vec_dim by presburger
  qed

  have ts_ip:
    "\<And>p q. p < length ?ts \<Longrightarrow> q < length ?ts
       \<Longrightarrow> \<langle>?ts ! p | ?ts ! q\<rangle> = (if p = q then 1 else 0)"
  proof -
    fix p q
    assume p_lt: "p < length ?ts"
       and q_lt: "q < length ?ts"

    have p_lt': "p < n*m" and q_lt': "q < n*m"
      using p_lt q_lt ts_len by simp_all

    have pd: "p div m < n"
      using less_mult_imp_div_less p_lt' by blast
    have pm: "p mod m < m"
      using p_lt' ks_len by (cases m, auto)
    have qd: "q div m < n"
      using less_mult_imp_div_less q_lt' by blast
    have qm: "q mod m < m"
      using q_lt' ks_len by (cases m, auto)
    have p_nth:
      "?ts ! p = tensor_vec (hs ! (p div m)) (ks ! (p mod m))"
      using nth_ts p_lt' by blast
    have q_nth:
      "?ts ! q = tensor_vec (hs ! (q div m)) (ks ! (q mod m))"
      using nth_ts q_lt' by blast

    have "\<langle>?ts ! p | ?ts ! q\<rangle>
        = \<langle>tensor_vec (hs ! (p div m)) (ks ! (p mod m))
           | tensor_vec (hs ! (q div m)) (ks ! (q mod m))\<rangle>"
      using p_nth q_nth by simp
    also have "... =
        \<langle>hs ! (p div m) | hs ! (q div m)\<rangle> *
        \<langle>ks ! (p mod m) | ks ! (q mod m)\<rangle>"
      using hs_dim[OF pd] hs_dim[OF qd] ks_dim[OF pm] ks_dim[OF qm]
      by (rule tensor_inner_prod)
    also have "... =
        (if p div m = q div m then 1 else 0) *
        (if p mod m = q mod m then 1 else 0)"
      using hs_ip[OF pd qd] ks_ip[OF pm qm] by simp
    also have "... = (if p = q then 1 else 0)"
      using p_lt' q_lt' ks_len
      by (simp, metis div_mod_decomp)
    finally show "\<langle>?ts ! p | ?ts ! q\<rangle> = (if p = q then 1 else 0)".
  qed

  show ?thesis
    unfolding orthonormal_list_def
    using ts_len ts_dim ts_ip
    by (metis (lifting) in_set_conv_nth)
qed

subsection \<open>Postulates of quantum mechanics\<close>

text \<open>\begin{notespost}[1]
To each isolated physical system corresponds a Hilbert space, the \emph{state space}; the
state of the system is completely described by a unit vector in it, the \emph{state vector}.
\end{notespost}
\begin{notespost}[2]
The time evolution of a closed system from $t_1$ to $t_2$ is described by a unitary
$U:\Hil\to\Hil$: a system in state $\psi$ at $t_1$ is in state $U\psi$ at $t_2$.
\end{notespost}
\begin{notespost}[3]
Quantum measurements are described by a collection $\{M_m\}$ of \emph{measurement
operators} on $\Hil$.  If the system is in state $\psi$, the probability of observing $m$ is
$p_m(\psi)=\braket{\psi}{M_m^*M_m\psi}=\norm{M_m\psi}^2$; since the probabilities sum to
one, $\sum_m M_m^*M_m=I$.  After observing $m$ the state is $M_m\psi/p_m(\psi)^{1/2}$.
\end{notespost}
Formally a state is \<open>quantum_state n \<psi>\<close> (a unit vector in $\C^n$), evolution is
\<open>evolve U \<psi>\<close>, a measurement system is a list \<open>Ms\<close> with
\<open>measurement_system n Ms\<close> (all $n\times n$ with $\sum_m M_m^\dagger M_m=I$), and
$p_m(\psi)$ is \<open>meas_prob M \<psi>\<close>.\<close>

definition quantum_state :: "nat \<Rightarrow> complex Matrix.vec \<Rightarrow> bool" where
  "quantum_state n \<psi> \<equiv> dim_vec \<psi> = n \<and> \<parallel>\<psi>\<parallel> = 1"

lemma quantum_state_norm1:
  assumes "quantum_state n \<psi>"
  shows "\<parallel>\<psi>\<parallel> = 1"
  using assms
  by (simp add: quantum_state_def)

lemma quantum_state_dim:
  assumes "quantum_state n \<psi>"
  shows "dim_vec \<psi> = n"
  using assms
  by (simp add: quantum_state_def)


definition evolve :: "complex Matrix.mat \<Rightarrow> complex Matrix.vec \<Rightarrow> complex Matrix.vec" where
  "evolve U \<psi> \<equiv> U *\<^sub>v \<psi>"

lemma unitary_preserves_state:
  assumes "unitary U" and "quantum_state n \<psi>" and "dim_col U = n"
  shows "quantum_state (dim_row U) (evolve U \<psi>)"
  unfolding quantum_state_def evolve_def
proof
  show "dim_vec (U *\<^sub>v \<psi>) = dim_row U" by simp
  have "\<parallel>U *\<^sub>v \<psi>\<parallel> = \<parallel>\<psi>\<parallel>"
    using unitary_isometry[OF assms(1)] assms(2,3)
    by (simp add: quantum_state_def)
  also have "\<parallel>\<psi>\<parallel> = 1"
    using assms(2) quantum_state_def by simp
  finally show "\<parallel>U *\<^sub>v \<psi>\<parallel> = 1".
qed


definition measurement_system :: "nat \<Rightarrow> complex Matrix.mat list \<Rightarrow> bool" where
  "measurement_system n Ms \<equiv>
     (\<forall>M \<in> set Ms. M \<in> carrier_mat n n) \<and>
     foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) Ms (0\<^sub>m n n) = 1\<^sub>m n"

definition meas_prob :: "complex Matrix.mat \<Rightarrow> complex Matrix.vec \<Rightarrow> real" where
  "meas_prob M \<psi> \<equiv> \<parallel>M *\<^sub>v \<psi>\<parallel>\<^sup>2"


lemma measurement_probs_sum_one:
  assumes ms: "measurement_system n Ms"
      and st: "quantum_state n \<psi>"
  shows "(\<Sum>M \<leftarrow> Ms. meas_prob M \<psi>) = 1"
proof -
  have psi_dim: "dim_vec \<psi> = n" using st by (auto simp: quantum_state_def)
  have psi_norm: "\<parallel>\<psi>\<parallel> = 1" using st by (auto simp: quantum_state_def)
  have psi_car: "\<psi> \<in> carrier_vec n" using psi_dim
    by fastforce 

  (* Step 1: \<parallel>M\<psi>\<parallel>² = \<langle>\<psi> | M\<dagger>M \<psi>\<rangle> for each M *)
  have step1: "\<And>M. M \<in> set Ms \<Longrightarrow> meas_prob M \<psi> = Re (\<langle>\<psi> | ((M\<^sup>\<dagger>) * M) *\<^sub>v \<psi>\<rangle>)"
    by (metis (lifting) Re_complex_of_real assoc_mult_mat_vec carrier_matD(2) carrier_mat_triv 
        cpx_vec_length_inner_prod dagger_of_dagger_is_id dim_mult_mat_vec dim_row_of_dagger 
        inner_prod_adjoint_swap meas_prob_def measurement_system_def ms psi_car psi_dim)

  have sum_eq: "(\<Sum>M \<leftarrow> Ms. meas_prob M \<psi>) =
              Re (\<langle>\<psi> | (foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) Ms (0\<^sub>m n n)) *\<^sub>v \<psi>\<rangle>)"
  proof -
    have all_car: "\<And>M. M \<in> set Ms \<Longrightarrow> M \<in> carrier_mat n n"
      using ms by (auto simp: measurement_system_def)
    have fold_car:
      "\<And>Ns. set Ns \<subseteq> set Ms \<Longrightarrow>
        foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) Ns (0\<^sub>m n n) \<in> carrier_mat n n"
    proof -
      fix Ns
      assume sub: "set Ns \<subseteq> set Ms"
      show "foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) Ns (0\<^sub>m n n) \<in> carrier_mat n n"
        using sub
      proof (induction Ns)
        case Nil
        show ?case by simp
      next
        case (Cons A As)
        have Acar: "A \<in> carrier_mat n n"
          using Cons.prems all_car by auto
        have sub_As: "set As \<subseteq> set Ms"
          using Cons.prems by auto
        show ?case
          using Cons.IH[OF sub_As] Acar by simp
      qed
    qed

    have sum_eq_aux:
      "\<And>Ns. set Ns \<subseteq> set Ms \<Longrightarrow>
        (\<Sum>M \<leftarrow> Ns. meas_prob M \<psi>) =
        Re (\<langle>\<psi> | (foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) Ns (0\<^sub>m n n)) *\<^sub>v \<psi>\<rangle>)"
    proof -
      fix Ns
      assume sub: "set Ns \<subseteq> set Ms"
      show "(\<Sum>M \<leftarrow> Ns. meas_prob M \<psi>) =
        Re (\<langle>\<psi> | (foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) Ns (0\<^sub>m n n)) *\<^sub>v \<psi>\<rangle>)"
        using sub
      proof (induction Ns)
        case Nil
        have "(\<Sum>M\<leftarrow>[]. meas_prob M \<psi>) = 0"
          by simp
        also have "... = Re (\<langle>\<psi> | (0\<^sub>m n n) *\<^sub>v \<psi>\<rangle>)"
          by (metis diff_self inner_prod_right_minus' minus_mult_distrib_mat_vec minus_r_inv_mat
              one_carrier_mat psi_car zero_complex.simps(1))
        finally show ?case
          by simp
      next
        case (Cons M Ns)
        have Mcar: "M \<in> carrier_mat n n"
          using Cons.prems all_car by auto
        have sub_Ns: "set Ns \<subseteq> set Ms"
          using Cons.prems by auto
        have IH:
          "(\<Sum>Ma\<leftarrow>Ns. meas_prob Ma \<psi>) =
           Re (\<langle>\<psi> | (foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) Ns (0\<^sub>m n n)) *\<^sub>v \<psi>\<rangle>)"
          using Cons.IH[OF sub_Ns] .
        have Mpsi_dim: "dim_vec (M *\<^sub>v \<psi>) = n"
          using Mcar psi_dim by simp
        have stepM: "meas_prob M \<psi> = Re (\<langle>\<psi> | ((M\<^sup>\<dagger>) * M) *\<^sub>v \<psi>\<rangle>)"
        proof -
          have adj_eq: "\<langle>\<psi> | ((M\<^sup>\<dagger>) * M) *\<^sub>v \<psi>\<rangle> = \<langle>M *\<^sub>v \<psi> | M *\<^sub>v \<psi>\<rangle>"
          proof -
            have "\<langle>\<psi> | ((M\<^sup>\<dagger>) * M) *\<^sub>v \<psi>\<rangle> = \<langle>\<psi> | (M\<^sup>\<dagger>) *\<^sub>v (M *\<^sub>v \<psi>)\<rangle>"
              using Mcar psi_car
              by (metis Mpsi_dim assoc_mult_mat_vec
                  carrier_mat_triv dim_col_of_dagger dim_mult_mat_vec)
            also have "... = \<langle>(M\<^sup>\<dagger>)\<^sup>\<dagger> *\<^sub>v \<psi> | M *\<^sub>v \<psi>\<rangle>"
              using inner_prod_adjoint_swap[of "M\<^sup>\<dagger>" n n \<psi> "M *\<^sub>v \<psi>"] Mcar psi_dim Mpsi_dim by force
            also have "... = \<langle>M *\<^sub>v \<psi> | M *\<^sub>v \<psi>\<rangle>"
              using dagger_of_dagger_is_id by presburger
            finally show ?thesis .
          qed
          have "meas_prob M \<psi> = \<parallel>M *\<^sub>v \<psi>\<parallel>\<^sup>2"
            by (simp add: meas_prob_def)
          also have "... = Re (\<langle>M *\<^sub>v \<psi> | M *\<^sub>v \<psi>\<rangle>)"
            by (metis Re_complex_of_real cpx_vec_length_inner_prod)
          also have "... = Re (\<langle>\<psi> | ((M\<^sup>\<dagger>) * M) *\<^sub>v \<psi>\<rangle>)"
            using adj_eq by simp
          finally show ?thesis .
        qed
        have carr_fold:
          "foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) Ns (0\<^sub>m n n) \<in> carrier_mat n n"
          using fold_car[OF sub_Ns] .
        have add_inside:
          "Re (\<langle>\<psi> | ((M\<^sup>\<dagger>) * M) *\<^sub>v \<psi>\<rangle>) +
           Re (\<langle>\<psi> | (foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) Ns (0\<^sub>m n n)) *\<^sub>v \<psi>\<rangle>)
           =
           Re (\<langle>\<psi> | (((M\<^sup>\<dagger>) * M) +
                     foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) Ns (0\<^sub>m n n)) *\<^sub>v \<psi>\<rangle>)"
        proof -
          have "\<langle>\<psi> | ((((M\<^sup>\<dagger>) * M) +
                     foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) Ns (0\<^sub>m n n)) *\<^sub>v \<psi>)\<rangle>
              = \<langle>\<psi> | ((M\<^sup>\<dagger>) * M) *\<^sub>v \<psi>\<rangle>
                + \<langle>\<psi> | (foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) Ns (0\<^sub>m n n)) *\<^sub>v \<psi>\<rangle>"
            using psi_dim Mcar carr_fold
            by (metis (lifting) add_mult_distrib_mat_vec carrier_matD(1,2) carrier_mat_triv
                dim_mult_mat_vec dim_row_of_dagger index_mult_mat(2,3) inner_prod_right_add' psi_car)
          then show ?thesis
            by simp
        qed
        have "(\<Sum>Ma\<leftarrow>M # Ns. meas_prob Ma \<psi>)
            = meas_prob M \<psi> + (\<Sum>Ma\<leftarrow>Ns. meas_prob Ma \<psi>)"
          by simp
        also have "... =
            Re (\<langle>\<psi> | ((M\<^sup>\<dagger>) * M) *\<^sub>v \<psi>\<rangle>) +
            Re (\<langle>\<psi> | (foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) Ns (0\<^sub>m n n)) *\<^sub>v \<psi>\<rangle>)"
          using stepM IH by simp
        also have "... =
            Re (\<langle>\<psi> | ((((M\<^sup>\<dagger>) * M) +
                     foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) Ns (0\<^sub>m n n)) *\<^sub>v \<psi>)\<rangle>)"
          using add_inside by simp
        also have "... =
            Re (\<langle>\<psi> | (foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) (M # Ns) (0\<^sub>m n n)) *\<^sub>v \<psi>\<rangle>)"
          by simp
        finally show ?case .
      qed
    qed
    show ?thesis
      using sum_eq_aux[of Ms] by simp
  qed
  (* Step 3: replace \<Sum>M\<dagger>M with I and use \<langle>\<psi>|\<psi>\<rangle> = \<parallel>\<psi>\<parallel>² = 1 *)
  have id_eq: "foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) Ms (0\<^sub>m n n) = 1\<^sub>m n"
    using ms by (simp add: measurement_system_def)
  have inner_one: "\<langle>\<psi> | (1\<^sub>m n) *\<^sub>v \<psi>\<rangle> = 1"
  proof -
    have "(1\<^sub>m n) *\<^sub>v \<psi> = \<psi>" using psi_car by simp
    hence "\<langle>\<psi> | (1\<^sub>m n) *\<^sub>v \<psi>\<rangle> = \<langle>\<psi>|\<psi>\<rangle>" by simp
    also have "\<dots> = (\<parallel>\<psi>\<parallel>)\<^sup>2"
      by (metis cpx_vec_length_inner_prod)
    also have "\<dots> = 1" using psi_norm by simp
    finally show ?thesis.
  qed
  show ?thesis
    using sum_eq id_eq inner_one by simp
qed

text \<open>$p_m(\psi)=\braket{\psi}{M_m^*M_m\psi}$, the form in which the notes state Postulate 3.\<close>

lemma meas_prob_quad_form:
  fixes M :: "complex Matrix.mat" and \<psi> :: "complex Matrix.vec"
  assumes M: "M \<in> carrier_mat n n" and \<psi>: "dim_vec \<psi> = n"
  shows "meas_prob M \<psi> = Re \<langle>\<psi> | (M\<^sup>\<dagger> * M) *\<^sub>v \<psi>\<rangle>"
proof -
  have \<psi>c: "\<psi> \<in> carrier_vec n" using \<psi> by auto
  have Md: "M\<^sup>\<dagger> \<in> carrier_mat n n" using M by auto
  have M\<psi>: "dim_vec (M *\<^sub>v \<psi>) = n" using M \<psi> by auto
  have "\<langle>\<psi> | (M\<^sup>\<dagger> * M) *\<^sub>v \<psi>\<rangle> = \<langle>\<psi> | M\<^sup>\<dagger> *\<^sub>v (M *\<^sub>v \<psi>)\<rangle>"
    using M Md \<psi>c by (simp add: assoc_mult_mat_vec)
  also have "\<dots> = \<langle>(M\<^sup>\<dagger>)\<^sup>\<dagger> *\<^sub>v \<psi> | M *\<^sub>v \<psi>\<rangle>"
    using inner_prod_adjoint_swap[OF Md \<psi> M\<psi>] .
  also have "\<dots> = \<langle>M *\<^sub>v \<psi> | M *\<^sub>v \<psi>\<rangle>" by (simp add: dagger_of_dagger_is_id)
  finally show ?thesis
    unfolding meas_prob_def by (simp add: cpx_vec_length_inner_prod[symmetric])
qed

text \<open>After outcome $m$ the state becomes $M_m\psi/\norm{M_m\psi}$:\<close>

definition post_meas_state :: "complex Matrix.mat \<Rightarrow> complex Matrix.vec \<Rightarrow> complex Matrix.vec" where
  "post_meas_state M \<psi> \<equiv> (1 / complex_of_real (\<parallel>M *\<^sub>v \<psi>\<parallel>)) \<cdot>\<^sub>v (M *\<^sub>v \<psi>)"

text \<open>\begin{notespost}[4, Day 9]
The state space of a composite system is the tensor product of the state spaces of its
components; if the $i$-th component is in state $\psi_i$, the system is in state
$\psi_1\otimes\cdots\otimes\psi_n$.
\end{notespost}\<close>

lemma tensor_of_states_is_state:
  assumes "quantum_state n \<psi>1" and "quantum_state m \<psi>2"
  shows "quantum_state (n*m) (tensor_vec \<psi>1 \<psi>2)"
proof -
  have d1: "dim_vec \<psi>1 = n" and d2: "dim_vec \<psi>2 = m"
    using assms by (auto simp: quantum_state_def)
  have norm1: "\<parallel>\<psi>1\<parallel> = 1" and norm2: "\<parallel>\<psi>2\<parallel> = 1"
    using assms by (auto simp: quantum_state_def)
  have dim: "dim_vec (tensor_vec \<psi>1 \<psi>2) = n * m"
    using d1 d2 by (rule tensor_vec_dim)
  (* From tensor_inner_prod: \<langle>\<psi>1\<otimes>\<psi>2 | \<psi>1\<otimes>\<psi>2\<rangle> = \<langle>\<psi>1|\<psi>1\<rangle>\<sqdot>\<langle>\<psi>2|\<psi>2\<rangle> = 1\<sqdot>1 = 1. *)
  have norm_tensor: "\<parallel>tensor_vec \<psi>1 \<psi>2\<parallel> = 1"
    by (smt (verit) cpx_vec_length_inner_prod inner_prod_csqrt norm1 norm2 of_real_eq_1_iff 
        one_power2 power2_eq_square tensor_inner_prod)
  show ?thesis
    unfolding quantum_state_def using dim norm_tensor by simp
qed

end

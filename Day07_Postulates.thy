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
  have "\<langle>tensor_vec h1 k1 | tensor_vec h2 k2\<rangle>
        = (\<Sum>r < n * m. cnj (h1 $ (r div m) * k1 $ (r mod m)) * (h2 $ (r div m) * k2 $ (r mod m)))"
    unfolding inner_prod_def tensor_vec_dim[OF assms(2,4)] atLeast0LessThan
    by (rule sum.cong[OF refl]) (simp add: tensor_vec_index[OF assms(1,3)] tensor_vec_index[OF assms(2,4)])
  also have "\<dots> = (\<Sum>i<n. \<Sum>j<m. (cnj (h1 $ i) * h2 $ i) * (cnj (k1 $ j) * k2 $ j))"
    unfolding sum_div_mod[where g = "\<lambda>i j. cnj (h1 $ i * k1 $ j) * (h2 $ i * k2 $ j)"]
    by (intro sum.cong refl) (simp add: mult_ac)
  also have "\<dots> = (\<Sum>i<n. cnj (h1 $ i) * h2 $ i) * (\<Sum>j<m. cnj (k1 $ j) * k2 $ j)"
    unfolding sum_product ..
  finally show ?thesis unfolding inner_prod_def assms atLeast0LessThan .
qed

text \<open>Position $p$ of the product list $[h_i\otimes k_j]_{i<n,\,j<m}$ holds $h_{p\div m}\otimes k_{p\bmod m}$.\<close>

lemma length_concat_map_upt:
  "length (concat (map (\<lambda>i. map (\<lambda>j. f i j) [0..<m]) [0..<n])) = n * m"
  by (simp add: length_concat o_def sum_list_triv)

lemma nth_concat_map_upt:
  assumes "p < n * m"
  shows "concat (map (\<lambda>i. map (\<lambda>j. f i j) [0..<m]) [0..<n]) ! p = f (p div m) (p mod m)"
  using assms
proof (induction n arbitrary: p)
  case (Suc n)
  show ?case
  proof (cases "p < n * m")
    case True
    thus ?thesis using Suc.IH[OF True] by (simp add: upt_Suc nth_append length_concat_map_upt)
  next
    case False
    have m: "0 < m" using Suc.prems by (cases m) simp_all
    define r where "r = p - n * m"
    have r: "p = n * m + r" "r < m" using False Suc.prems unfolding r_def by simp_all
    have "concat (map (\<lambda>i. map (\<lambda>j. f i j) [0..<m]) [0..<Suc n]) ! p = f n r"
      using r by (simp add: upt_Suc nth_append length_concat_map_upt)
    thus ?thesis using r m by simp
  qed
qed simp

lemma tensor_onb:
  assumes hs_onb: "orthonormal_list n hs"
      and hs_len: "length hs = n"
      and ks_onb: "orthonormal_list m ks"
      and ks_len: "length ks = m"
  shows "orthonormal_list (n*m)
         [tensor_vec (hs ! i) (ks ! j). i \<leftarrow> [0..<n], j \<leftarrow> [0..<m]]"
proof -
  let ?ts = "[tensor_vec (hs ! i) (ks ! j). i \<leftarrow> [0..<n], j \<leftarrow> [0..<m]]"
  have len: "length ?ts = n * m" by (simp add: length_concat o_def sum_list_triv)
  have nth: "?ts ! p = tensor_vec (hs ! (p div m)) (ks ! (p mod m))" if "p < n * m" for p
    by (rule nth_concat_map_upt[OF that])
  have hd: "dim_vec (hs ! i) = n" if "i < n" for i
    using hs_onb hs_len that unfolding orthonormal_list_def by auto
  have kd: "dim_vec (ks ! j) = m" if "j < m" for j
    using ks_onb ks_len that unfolding orthonormal_list_def by auto
  have hip: "\<langle>hs ! i | hs ! i'\<rangle> = (if i = i' then 1 else 0)" if "i < n" "i' < n" for i i'
    using hs_onb hs_len that unfolding orthonormal_list_def by auto
  have kip: "\<langle>ks ! j | ks ! j'\<rangle> = (if j = j' then 1 else 0)" if "j < m" "j' < m" for j j'
    using ks_onb ks_len that unfolding orthonormal_list_def by auto
  have dv: "p div m < n" if "p < n * m" for p using that less_mult_imp_div_less by blast
  have md: "p mod m < m" if "p < n * m" for p using that by (cases m) simp_all
  show ?thesis unfolding orthonormal_list_def
  proof (intro conjI ballI allI impI)
    fix v assume "v \<in> set ?ts"
    then obtain p where p: "p < n * m" and v: "v = ?ts ! p" unfolding in_set_conv_nth len by blast
    show "dim_vec v = n * m" unfolding v nth[OF p]
      by (rule tensor_vec_dim[OF hd[OF dv[OF p]] kd[OF md[OF p]]])
  next
    fix p q assume "p < length ?ts" "q < length ?ts"
    hence p: "p < n * m" and q: "q < n * m" unfolding len by simp_all
    have "\<langle>?ts ! p | ?ts ! q\<rangle> =
          (if p div m = q div m then 1 else 0) * (if p mod m = q mod m then 1 else 0)"
      unfolding nth[OF p] nth[OF q]
                tensor_inner_prod[OF hd[OF dv[OF p]] hd[OF dv[OF q]] kd[OF md[OF p]] kd[OF md[OF q]]]
                hip[OF dv[OF p] dv[OF q]] kip[OF md[OF p] md[OF q]] ..
    also have "\<dots> = (if p = q then 1 else 0)"
    proof -
      have "p = q" if "p div m = q div m" "p mod m = q mod m"
        using div_mult_mod_eq[of p m, unfolded that] by simp
      thus ?thesis by auto
    qed
    finally show "\<langle>?ts ! p | ?ts ! q\<rangle> = (if p = q then 1 else 0)" .
  qed
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

text \<open>A state is a unit vector, and evolution is $\psi\mapsto U\psi$ with $U$ unitary; it stays a state
since $\norm{U\psi}^2=\braket{\psi}{U^*U\psi}=\norm\psi^2=1$.\<close>

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

text \<open>A measurement is a list $M_1,\dots,M_k$ with $\sum_iM_i^*M_i=I$.  Outcome $i$ has probability
\[ p_i=\norm{M_i\psi}^2=\braket{\psi}{M_i^*M_i\,\psi}, \]
and these add up to $\braket{\psi}{(\sum_iM_i^*M_i)\psi}=\norm\psi^2=1$.\<close>

definition measurement_system :: "nat \<Rightarrow> complex Matrix.mat list \<Rightarrow> bool" where
  "measurement_system n Ms \<equiv>
     (\<forall>M \<in> set Ms. M \<in> carrier_mat n n) \<and>
     foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) Ms (0\<^sub>m n n) = 1\<^sub>m n"

definition meas_prob :: "complex Matrix.mat \<Rightarrow> complex Matrix.vec \<Rightarrow> real" where
  "meas_prob M \<psi> \<equiv> \<parallel>M *\<^sub>v \<psi>\<parallel>\<^sup>2"

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

lemma measurement_probs_sum_one:
  assumes ms: "measurement_system n Ms"
      and st: "quantum_state n \<psi>"
  shows "(\<Sum>M \<leftarrow> Ms. meas_prob M \<psi>) = 1"
proof -
  have \<psi>: "\<psi> \<in> carrier_vec n" "\<parallel>\<psi>\<parallel> = 1" using st by (auto simp: quantum_state_def)
  have "(\<Sum>M \<leftarrow> Ns. meas_prob M \<psi>) =
        Re \<langle>\<psi> | foldr (\<lambda>M acc. M\<^sup>\<dagger> * M + acc) Ns (0\<^sub>m n n) *\<^sub>v \<psi>\<rangle>"
    if "set Ns \<subseteq> set Ms" for Ns
    using that
  proof (induction Ns)
    case Nil
    show ?case using \<psi>(1) by (simp add: inner_prod_def scalar_prod_def)
  next
    case (Cons M Ns)
    have M: "M \<in> carrier_mat n n" and F: "foldr (\<lambda>M acc. M\<^sup>\<dagger> * M + acc) Ns (0\<^sub>m n n) \<in> carrier_mat n n"
      using ms Cons.prems
      by (auto simp: measurement_system_def intro!: foldr_add_mat_carrier mult_carrier_mat dagger_carrier)
    have "(\<Sum>M \<leftarrow> M # Ns. meas_prob M \<psi>) =
          Re (\<langle>\<psi> | (M\<^sup>\<dagger> * M) *\<^sub>v \<psi>\<rangle> + \<langle>\<psi> | foldr (\<lambda>M acc. M\<^sup>\<dagger> * M + acc) Ns (0\<^sub>m n n) *\<^sub>v \<psi>\<rangle>)"
      using Cons meas_prob_quad_form[OF M carrier_vecD[OF \<psi>(1)]] by simp
    also have "\<dots> = Re \<langle>\<psi> | (M\<^sup>\<dagger> * M + foldr (\<lambda>M acc. M\<^sup>\<dagger> * M + acc) Ns (0\<^sub>m n n)) *\<^sub>v \<psi>\<rangle>"
      unfolding add_mult_distrib_mat_vec[OF mult_carrier_mat[OF dagger_carrier[OF M] M] F \<psi>(1)]
      by (subst inner_prod_right_add') (simp_all add: carrier_matD[OF M] carrier_matD[OF F])
    finally show ?case by simp
  qed
  from this[OF subset_refl] ms \<psi>(1) have "(\<Sum>M \<leftarrow> Ms. meas_prob M \<psi>) = Re \<langle>\<psi>|\<psi>\<rangle>"
    by (simp add: measurement_system_def)
  thus ?thesis unfolding cpx_vec_length_inner_prod[of \<psi>, symmetric] \<psi>(2) by simp
qed

text \<open>After outcome $m$ the state becomes $M_m\psi/\norm{M_m\psi}$:\<close>

definition post_meas_state :: "complex Matrix.mat \<Rightarrow> complex Matrix.vec \<Rightarrow> complex Matrix.vec" where
  "post_meas_state M \<psi> \<equiv> (1 / complex_of_real (\<parallel>M *\<^sub>v \<psi>\<parallel>)) \<cdot>\<^sub>v (M *\<^sub>v \<psi>)"

end

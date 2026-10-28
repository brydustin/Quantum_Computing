(*  Title:   Day09_POVMs_Entanglement.thy
    Author:  Dustin Bryant, after Vern Paulsen's lecture of 16 September 2011 (Day 9)
*)

theory Day09_POVMs_Entanglement
  imports Day07_Postulates
begin

section \<open>Day 9 (16 September 2011): positive operator-valued measures; composite systems; entanglement\<close>

subsection \<open>Positive operator-valued measures\<close>

text \<open>If two measurement systems satisfy $M_m^*M_m=\tilde M_m^*\tilde M_m$ for all $m$ then
$p_m=\tilde p_m$: only the operators $M_m^*M_m$ matter, and $\sum_mM_m^*M_m=I$.  Conversely
if $P_m\ge 0$ with $\sum_mP_m=I$ then $M_m=P_m^{1/2}$ is a measurement system.
\begin{notesdef}
A \emph{positive operator-valued measure} (POVM) is a set $\{P_m\}$ of positive operators with
$\sum_mP_m=I$.
\end{notesdef}\<close>

definition povm :: "nat \<Rightarrow> complex Matrix.mat list \<Rightarrow> bool" where
  "povm n Ps \<equiv>
     (\<forall>P \<in> set Ps. P \<in> carrier_mat n n \<and> psd P) \<and>
     foldr (\<lambda>P acc. P + acc) Ps (0\<^sub>m n n) = 1\<^sub>m n"

text \<open>Every measurement gives a POVM: $P_i=M_i^*M_i$ is positive because
$\braket x{M_i^*M_ix}=\norm{M_ix}^2\ge0$, and $\sum_iP_i=I$.\<close>

lemma measurement_induces_povm:
  assumes ms: "measurement_system n Ms"
  shows "povm n (map (\<lambda>M. (M\<^sup>\<dagger>) * M) Ms)"
proof -
  have "foldr (\<lambda>P acc. P + acc) (map (\<lambda>M. M\<^sup>\<dagger> * M) Ms) (0\<^sub>m n n)
        = foldr (\<lambda>M acc. M\<^sup>\<dagger> * M + acc) Ms (0\<^sub>m n n)"
    by (simp add: foldr_map o_def)
  thus ?thesis using ms unfolding povm_def measurement_system_def
    by (auto intro!: mult_carrier_mat dagger_carrier MdagM_psd)
qed

text \<open>Conversely, every POVM comes from a measurement: $P_i\ge0$ has the positive square root
$M_i=P_i^{1/2}$, with $M_i^*M_i=P_i$, and $\sum_iP_i=I$ is the measurement condition.\<close>

lemma psd_sqrt_measurement_factor:
  assumes Pcar: "P \<in> carrier_mat n n"
      and Ppsd: "psd P"
  shows "\<exists>M. M \<in> carrier_mat n n \<and> M\<^sup>\<dagger> * M = P"
proof -
  obtain Q where Qcar: "Q \<in> carrier_mat n n"
    and Qpsd: "psd Q"
    and QQ: "Q * Q = P"
    using psd_sqrt_exists[OF Pcar Ppsd] by blast
  have Qdag: "Q\<^sup>\<dagger> = Q"
    using psd_hermitian[OF Qpsd]
    unfolding hermitian_def by simp
  have "Q\<^sup>\<dagger> * Q = P"
    using Qdag QQ by simp
  thus ?thesis
    using Qcar by blast
qed

lemma psd_sqrt_measurement_factors:
  assumes Ps: "\<forall>P \<in> set Ps. P \<in> carrier_mat n n \<and> psd P"
  shows "\<exists>Ms. (\<forall>M \<in> set Ms. M \<in> carrier_mat n n) \<and>
               map (\<lambda>M. M\<^sup>\<dagger> * M) Ms = Ps"
  using Ps
proof (induction Ps)
  case Nil
  show ?case by simp
next
  case (Cons P Ps)
  have Pcar: "P \<in> carrier_mat n n"
    using Cons.prems by simp
  have Ppsd: "psd P"
    using Cons.prems by simp
  obtain M where Mcar: "M \<in> carrier_mat n n"
    and M_factor: "M\<^sup>\<dagger> * M = P"
    using psd_sqrt_measurement_factor[OF Pcar Ppsd] by blast
  obtain Ms where Mscar: "\<forall>M \<in> set Ms. M \<in> carrier_mat n n"
    and Ms_factor: "map (\<lambda>M. M\<^sup>\<dagger> * M) Ms = Ps"
    using Cons.IH Cons.prems by simp blast
  have "(\<forall>N \<in> set (M # Ms). N \<in> carrier_mat n n) \<and>
        map (\<lambda>N. N\<^sup>\<dagger> * N) (M # Ms) = P # Ps"
    using Mcar M_factor Mscar Ms_factor by simp
  thus ?case
    by meson
qed

lemma povm_from_sqrt:
  assumes pv: "povm n Ps"
  shows "\<exists>Ms. measurement_system n Ms \<and>
              map (\<lambda>M. M\<^sup>\<dagger> * M) Ms = Ps"
proof -
  have psd_each: "\<forall>P \<in> set Ps. P \<in> carrier_mat n n \<and> psd P"
    using pv by (simp add: povm_def)
  have sum_id: "foldr (\<lambda>P acc. P + acc) Ps (0\<^sub>m n n) = 1\<^sub>m n"
    using pv by (simp add: povm_def)
  obtain Ms where Mcar: "\<forall>M \<in> set Ms. M \<in> carrier_mat n n"
    and Ms_factor: "map (\<lambda>M. M\<^sup>\<dagger> * M) Ms = Ps"
    using psd_sqrt_measurement_factors[OF psd_each] by blast
  have "foldr (\<lambda>M acc. M\<^sup>\<dagger> * M + acc) Ms (0\<^sub>m n n) =
        foldr (\<lambda>P acc. P + acc) Ps (0\<^sub>m n n)"
    using Ms_factor by (induction Ms arbitrary: Ps) auto
  also have "\<dots> = 1\<^sub>m n"
    using sum_id by simp
  finally have meas_sum:
    "foldr (\<lambda>M acc. M\<^sup>\<dagger> * M + acc) Ms (0\<^sub>m n n) = 1\<^sub>m n" .
  have "measurement_system n Ms"
    unfolding measurement_system_def
    using Mcar meas_sum by simp
  thus ?thesis
    using Ms_factor by blast
qed

lemma povm_prob:
  assumes pv: "povm n Ps" and st: "quantum_state n \<psi>"
      and Pin: "P \<in> set Ps"
  shows "Re (\<langle>\<psi> | P *\<^sub>v \<psi>\<rangle>) \<ge> 0"
proof -
  have Ppsd: "psd P" using pv Pin by (auto simp: povm_def)
  have Pcar: "P \<in> carrier_mat n n" using pv Pin by (auto simp: povm_def)
  have psi_dim: "dim_vec \<psi> = n" using st by (auto simp: quantum_state_def)
  show ?thesis
    using Ppsd Pcar psi_dim unfolding psd_def by simp
qed

subsection \<open>Composite systems\<close>

text \<open>The notes' example: photons in states
$\tfrac1{\sqrt2}(\ket0+\ket1)$ and $\tfrac1{\sqrt2}(\ket0+i\ket1)$ form the pair
$\tfrac12(\ket{00}+i\ket{01}+\ket{10}+i\ket{11})\in\C^2\otimes\C^2$, a vector of Schmidt
rank $1$.  Two photons described by a unit vector $\psi\in\C^2\otimes\C^2$ can be regarded
as two separate subsystems iff $\psi=\psi_1\otimes\psi_2$ iff the Schmidt rank of $\psi$ is
$1$; otherwise $\psi$ is \emph{entangled}, which does happen in nature.

Tensor products of operators: for $R:\Hil\to\Hil$ and $T:\Kil\to\Kil$ there is a unique
$R\otimes T$ with $(R\otimes T)(\sum_l h_l\otimes k_l)=\sum_l Rh_l\otimes Tk_l$, and
(1) $(R_1\otimes T_1)(R_2\otimes T_2)=R_1R_2\otimes T_1T_2$, (2) $(R\otimes T)^*=R^*\otimes T^*$
(both proved in Unitary\_Tensor\_Algebra for the Kronecker product).
\begin{notesremark}
If lab A has the measurement system $\{M_m\}$ on $\Hil$ and lab B has state space $\Kil$,
the measurement system of the composite is $\{M_m\otimes I_{\Kil}\}$ and
$p_m^{AB}(\psi\otimes\phi)=\norm{(M_m\otimes I)(\psi\otimes\phi)}^2=p_m^A(\psi)$.
\end{notesremark}\<close>

text \<open>\begin{notespost}[4]
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
  have norm_tensor: "\<parallel>tensor_vec \<psi>1 \<psi>2\<parallel> = 1"
    by (smt (verit) cpx_vec_length_inner_prod inner_prod_csqrt norm1 norm2 of_real_eq_1_iff 
        one_power2 power2_eq_square tensor_inner_prod)
  show ?thesis
    unfolding quantum_state_def using dim norm_tensor by simp
qed

lemma tensor_mat_vec_mult:
  assumes A: "A \<in> carrier_mat nr nc" and B: "B \<in> carrier_mat mr mc"
      and v: "dim_vec v = nc" and w: "dim_vec w = mc"
  shows "(A \<Otimes> B) *\<^sub>v tensor_vec v w = tensor_vec (A *\<^sub>v v) (B *\<^sub>v w)"
proof (rule eq_vecI)
  have Av: "dim_vec (A *\<^sub>v v) = nr" and Bw: "dim_vec (B *\<^sub>v w) = mr" using A B by simp_all
  have AB: "A \<Otimes> B \<in> carrier_mat (nr * mr) (nc * mc)" using A B by (intro carrier_matI) simp_all
  have tv: "tensor_vec v w \<in> carrier_vec (nc * mc)" by (rule carrier_vecI[OF tensor_vec_dim[OF v w]])
  fix i assume "i < dim_vec (tensor_vec (A *\<^sub>v v) (B *\<^sub>v w))"
  hence i: "i < nr * mr" by (simp add: tensor_vec_dim[OF Av Bw])
  have dv: "i div mr < nr" using i less_mult_imp_div_less by blast
  have md: "i mod mr < mr" using i by (cases mr) simp_all
  have rhs: "tensor_vec (A *\<^sub>v v) (B *\<^sub>v w) $ i =
             (\<Sum>a<nc. A $$ (i div mr, a) * v $ a) * (\<Sum>b<mc. B $$ (i mod mr, b) * w $ b)"
    unfolding tensor_vec_index[OF Av Bw i] mult_mat_vec_index[OF A carrier_vecI[OF v] dv]
              mult_mat_vec_index[OF B carrier_vecI[OF w] md] atLeast0LessThan ..
  show "((A \<Otimes> B) *\<^sub>v tensor_vec v w) $ i = tensor_vec (A *\<^sub>v v) (B *\<^sub>v w) $ i"
  proof (cases "nc = 0 \<or> mc = 0")
    case True
    thus ?thesis unfolding rhs mult_mat_vec_index[OF AB tv i] by auto
  next
    case False
    hence nc: "0 < nc" and mc: "0 < mc" by simp_all
    have "((A \<Otimes> B) *\<^sub>v tensor_vec v w) $ i = (\<Sum>k<nc * mc. (A \<Otimes> B) $$ (i, k) * tensor_vec v w $ k)"
      by (rule mult_mat_vec_index[OF AB tv i, unfolded atLeast0LessThan])
    also have "\<dots> = (\<Sum>k<nc * mc. (A $$ (i div mr, k div mc) * v $ (k div mc)) * (B $$ (i mod mr, k mod mc) * w $ (k mod mc)))"
      by (intro sum.cong refl)
         (simp add: index_tensor_mat[OF carrier_matD(1)[OF A] carrier_matD(2)[OF A] carrier_matD(1)[OF B] carrier_matD(2)[OF B] i _ nc mc]
                    tensor_vec_index[OF v w] mult_ac)
    also have "\<dots> = (\<Sum>a<nc. \<Sum>b<mc. (A $$ (i div mr, a) * v $ a) * (B $$ (i mod mr, b) * w $ b))"
      by (rule sum_div_mod)
    also have "\<dots> = (\<Sum>a<nc. A $$ (i div mr, a) * v $ a) * (\<Sum>b<mc. B $$ (i mod mr, b) * w $ b)"
      unfolding sum_product ..
    finally show ?thesis unfolding rhs .
  qed
qed (use A B in \<open>simp add: tensor_vec_dim\<close>)

lemma tensor_mat_vec_mult_right_id:
  assumes A: "A \<in> carrier_mat n n"
      and v: "dim_vec v = n"
      and w: "dim_vec w = m"
  shows "(A \<Otimes> 1\<^sub>m m) *\<^sub>v tensor_vec v w = tensor_vec (A *\<^sub>v v) w"
proof -
  have "(A \<Otimes> 1\<^sub>m m) *\<^sub>v tensor_vec v w =
        tensor_vec (A *\<^sub>v v) (1\<^sub>m m *\<^sub>v w)"
    using tensor_mat_vec_mult[OF A one_carrier_mat v w] .
  also have "\<dots> = tensor_vec (A *\<^sub>v v) w"
    using w Matrix.one_mult_mat_vec by force
  finally show ?thesis .
qed

lemma composite_measurement_prob:
  fixes M :: "complex Matrix.mat" and \<psi> :: "complex Matrix.vec" and \<phi> :: "complex Matrix.vec"
  assumes psi_st: "quantum_state n \<psi>" and phi_st: "quantum_state m \<phi>"
      and M_sq: "M \<in> carrier_mat n n"
  shows "meas_prob (M \<Otimes> 1\<^sub>m m) (tensor_vec \<psi> \<phi>) = meas_prob M \<psi>"
proof -
  have psi_dim: "dim_vec \<psi> = n" using psi_st by (auto simp: quantum_state_def)
  have phi_dim: "dim_vec \<phi> = m" using phi_st by (auto simp: quantum_state_def)
  have phi_norm: "\<parallel>\<phi>\<parallel> = 1" using phi_st by (auto simp: quantum_state_def)
  have mix: "(M \<Otimes> 1\<^sub>m m) *\<^sub>v (tensor_vec \<psi> \<phi>) = tensor_vec (M *\<^sub>v \<psi>) \<phi>"
    using tensor_mat_vec_mult_right_id[OF M_sq psi_dim phi_dim] .
  have norm_prod: "\<parallel>tensor_vec (M *\<^sub>v \<psi>) \<phi>\<parallel>^2 = \<parallel>M *\<^sub>v \<psi>\<parallel>^2 * \<parallel>\<phi>\<parallel>^2"
    by (smt (verit) Re_complex_of_real cpx_vec_length_inner_prod of_real_mult tensor_inner_prod)
  have eq: "\<parallel>tensor_vec (M *\<^sub>v \<psi>) \<phi>\<parallel>^2 = \<parallel>M *\<^sub>v \<psi>\<parallel>^2"
    using norm_prod phi_norm by simp
  show ?thesis
    unfolding meas_prob_def using mix eq by simp
qed

subsection \<open>Entanglement\<close>

text \<open>A state $\psi\in\Hil_A\otimes\Hil_B$ is \emph{entangled} if it is not a product
state $u\otimes v$.  The Bell state $\gamma=\tfrac1{\sqrt2}(\ket{00}+\ket{11})$ is
entangled.  The notes' first application of entanglement (A and B share $\gamma$; A measures
$\ketbra00,\ketbra11$ and gets each outcome with probability $\tfrac12$, after which B's
measurement is determined) is \<open>bell_measurement\<close> below.\<close>

definition entangled :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.vec \<Rightarrow> bool" where
  "entangled n m \<psi> \<equiv>
     dim_vec \<psi> = n * m \<and>
     \<not> (\<exists>u v. dim_vec u = n \<and> dim_vec v = m \<and> \<psi> = tensor_vec u v)"

definition bell_state :: "complex Matrix.vec" where
  "bell_state \<equiv> (1 / csqrt 2) \<cdot>\<^sub>v
                 (tensor_vec (unit_vec 2 0) (unit_vec 2 0) +
                  tensor_vec (unit_vec 2 1) (unit_vec 2 1))"

lemma bell_state_norm: "\<parallel>bell_state\<parallel> = 1"
proof -
  have eq: "bell_state = (1 / csqrt 2) \<cdot>\<^sub>v (unit_vec 4 0 + unit_vec 4 3)"
    unfolding bell_state_def by (simp add: tensor_unit_vec)
  have n2: "\<parallel>unit_vec 4 0 + unit_vec 4 3 :: complex Matrix.vec\<parallel> = sqrt 2"
    by (simp add: cpx_vec_length_def eval_nat_numeral)
  show ?thesis unfolding eq cpx_vec_length_smult n2 by (simp add: norm_divide field_simps)
qed

lemma bell_state_is_quantum_state:
  "quantum_state 4 bell_state"
proof -
  let ?u = "tensor_vec (unit_vec 2 0) (unit_vec 2 0)"
  let ?v = "tensor_vec (unit_vec 2 1) (unit_vec 2 1)"
  have du: "dim_vec ?u = 4" using tensor_vec_dim by simp
  have dv: "dim_vec ?v = 4" using tensor_vec_dim by simp
  have dim_sum: "dim_vec (?u + ?v) = 4" using du dv by simp
  then have dim_bell: "dim_vec bell_state = 4"
    unfolding bell_state_def by simp
  have norm_bell: "\<parallel>bell_state\<parallel> = 1"
    by (rule bell_state_norm)
  show ?thesis
    unfolding quantum_state_def using dim_bell norm_bell by simp
qed

lemma bell_state_entangled:
  "entangled 2 2 bell_state"
proof -
  have dim_bell: "dim_vec bell_state = 4"
    using bell_state_is_quantum_state unfolding quantum_state_def by simp

  have bell0: "bell_state $ 0 = 1 / csqrt 2"
    unfolding bell_state_def by (simp add: tensor_vec_dim tensor_vec_index)
  have bell2: "bell_state $ 2 = 0"
    unfolding bell_state_def by (simp add: tensor_vec_dim tensor_vec_index)
  have bell3: "bell_state $ 3 = 1 / csqrt 2"
    unfolding bell_state_def by (simp add: tensor_vec_dim tensor_vec_index)

  have not_product:
    "\<not> (\<exists>u v. dim_vec u = 2 \<and> dim_vec v = 2 \<and> bell_state = tensor_vec u v)"
  proof
    assume "\<exists>u v. dim_vec u = 2 \<and> dim_vec v = 2 \<and> bell_state = tensor_vec u v"
    then obtain u v where udim: "dim_vec u = 2" and vdim: "dim_vec v = 2"
      and eq: "bell_state = tensor_vec u v"
      by blast

    have uv0: "u $ 0 * v $ 0 = 1 / csqrt 2"
      using bell0 eq tensor_vec_index[OF udim vdim, of 0] by simp
    then have u0_nonzero: "u $ 0 \<noteq> 0" and v0_nonzero: "v $ 0 \<noteq> 0"
      by auto

    have uv2: "u $ 1 * v $ 0 = 0"
      using bell2 eq tensor_vec_index[OF udim vdim, of 2] by simp
    then have u1_zero: "u $ 1 = 0"
      using v0_nonzero by auto

    have uv3: "u $ 1 * v $ 1 = 1 / csqrt 2"
      using bell3 eq tensor_vec_index[OF udim vdim, of 3] by simp
    then have "1 / csqrt 2 = 0"
      using u1_zero by simp
    then show False
      by simp
  qed

  show ?thesis
    unfolding entangled_def using dim_bell not_product by simp
qed  (* If bell_state = u\<otimes>v then matrix [u₀v₀, u₀v₁; u₁v₀, u₁v₁] has rank 1.
        But the bell_state coefficient matrix [1/\<surd>2, 0; 0, 1/\<surd>2] has rank 2. *)

corollary entangled_iff_schmidt_rank:
  assumes u: "dim_vec u = n * m" and m: "0 < m" and u0: "u \<noteq> 0\<^sub>v (n * m)"
  shows "entangled n m u \<longleftrightarrow> 1 < schmidt_rank u m"
proof -
  have "schmidt_rank u m \<noteq> 0" using schmidt_rank_zero_iff[OF u m] u0 by simp
  thus ?thesis using schmidt_rank_one_iff_product[OF u m u0] u unfolding entangled_def by auto
qed

corollary schmidt_rank_bell_state: "schmidt_rank bell_state 2 = 2"
proof -
  have d: "dim_vec bell_state = 2 * 2" using bell_state_is_quantum_state unfolding quantum_state_def by simp
  have ne: "bell_state \<noteq> 0\<^sub>v (2 * 2)"
  proof
    assume z: "bell_state = 0\<^sub>v (2 * 2)"
    have "\<parallel>bell_state\<parallel> = 1" using bell_state_is_quantum_state unfolding quantum_state_def by simp
    moreover have "\<parallel>bell_state\<parallel> = 0" using cpx_vec_length_zero_iff[of bell_state] z d by simp
    ultimately show False by simp
  qed
  have "1 < schmidt_rank bell_state 2" using entangled_iff_schmidt_rank[OF d _ ne] bell_state_entangled by simp
  moreover have "schmidt_rank bell_state 2 \<le> 2" by (rule schmidt_rank_repr(2)[OF d _ schmidt_repr_exists[OF d]]) simp
  ultimately show ?thesis by simp
qed

end

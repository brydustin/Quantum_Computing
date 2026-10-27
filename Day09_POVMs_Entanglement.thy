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
  let ?Ps = "map (\<lambda>M. (M\<^sup>\<dagger>) * M) Ms"
  (* All M \<in> Ms are in carrier_mat n n by ms. *)
  have all_carrier: "\<forall>M \<in> set Ms. M \<in> carrier_mat n n"
    using ms by (simp add: measurement_system_def)
  have P_carrier: "\<forall>P \<in> set ?Ps. P \<in> carrier_mat n n"
    by (metis (no_types, lifting) all_carrier carrier_matD(2) carrier_matI dagger_of_dagger_is_id 
        dagger_of_prod dim_col_of_dagger imageE index_mult_mat(3) list.set_map)
  (* Each M\<^sup>\<dagger> * M is psd: hermitian (M\<^sup>\<dagger>M)\<^sup>\<dagger> = M\<^sup>\<dagger>M\<^sup>\<dagger>\<^sup>\<dagger> = M\<^sup>\<dagger>M, and
     \<langle>x | M\<^sup>\<dagger>M x\<rangle> = \<langle>Mx | Mx\<rangle> = \<parallel>Mx\<parallel>\<^sup>2 \<ge> 0. *)
  have P_psd: "\<forall>P \<in> set ?Ps. psd P"
  proof clarify
    fix P
    assume P_in: "P \<in> set ?Ps"
    then obtain M where M_in: "M \<in> set Ms" and P_def: "P = (M\<^sup>\<dagger>) * M"
      by auto

    have M_car: "M \<in> carrier_mat n n"
      using all_carrier M_in by blast
    hence P_car: "P \<in> carrier_mat n n"
      using P_carrier P_in by blast

    have P_herm: "hermitian P"
      unfolding P_def hermitian_def
      using M_car
      by (simp add: dagger_of_dagger_is_id dagger_of_prod)


    have quad_nonneg: "\<forall>x. dim_vec x = n \<longrightarrow> 0 \<le> Re \<langle>x | P *\<^sub>v x\<rangle>"
    proof (intro allI impI)
      fix x  :: "complex Matrix.vec"
      assume xdim: "dim_vec x = n"

      have Mx_dim: "dim_vec (M *\<^sub>v x) = n"
        using M_car xdim by simp

      have "\<langle>x | P *\<^sub>v x\<rangle> = \<langle>x | M\<^sup>\<dagger> *\<^sub>v (M *\<^sub>v x)\<rangle>"
        unfolding P_def
        using M_car xdim
        by (metis assoc_mult_mat_vec carrier_matD(1) carrier_vec_dim_vec dagger_def mat_carrier)
      also have "... = \<langle>(M\<^sup>\<dagger>)\<^sup>\<dagger> *\<^sub>v x | M *\<^sub>v x\<rangle>"
        using M_car xdim Mx_dim
        by (metis carrier_matD(2) dagger_of_dagger_is_id dim_col_of_dagger dim_mult_mat_vec 
            inner_prod_adjoint_swap inner_prod_cnj)
      also have "... = \<langle>M *\<^sub>v x | M *\<^sub>v x\<rangle>"
        using dagger_of_dagger_is_id by presburger
      finally have qf_eq: "\<langle>x | P *\<^sub>v x\<rangle> = \<langle>M *\<^sub>v x | M *\<^sub>v x\<rangle>" .

      have "0 \<le> Re \<langle>M *\<^sub>v x | M *\<^sub>v x\<rangle>"
        using Mx_dim
        using inner_prod_with_itself_Re by blast

      thus "0 \<le> Re \<langle>x | P *\<^sub>v x\<rangle>"
        using qf_eq by simp
    qed

    show "psd P"
      unfolding psd_def
      using P_car P_herm quad_nonneg by blast
  qed
  (* The sum equals I by definition of measurement_system. *)
  have "foldr (\<lambda>P acc. P + acc) ?Ps (0\<^sub>m n n)  = foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) Ms (0\<^sub>m n n)"
    by (induction Ms) simp_all
  also have "... = 1\<^sub>m n"
    using ms by (simp add: measurement_system_def)
  finally have id_sum: "foldr (\<lambda>P acc. P + acc) ?Ps (0\<^sub>m n n) = 1\<^sub>m n" .
  show ?thesis
    unfolding povm_def using P_carrier P_psd id_sum by auto
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
  (* For each P\<in>Ps, psd_sqrt_exists gives a Q with Q\<^sup>2 = P, Q psd, Q hermitian.
     Take M = Q.  Then M\<^sup>\<dagger>M = Q\<^sup>\<dagger>Q = Q\<^sup>2 = P. *)
  have psd_each: "\<forall>P \<in> set Ps. P \<in> carrier_mat n n \<and> psd P"
    using pv by (simp add: povm_def)
  have sum_id: "foldr (\<lambda>P acc. P + acc) Ps (0\<^sub>m n n) = 1\<^sub>m n"
    using pv by (simp add: povm_def)
  (* Construct the list of square roots. *)
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
  (* From tensor_inner_prod: \<langle>\<psi>1\<otimes>\<psi>2 | \<psi>1\<otimes>\<psi>2\<rangle> = \<langle>\<psi>1|\<psi>1\<rangle>\<sqdot>\<langle>\<psi>2|\<psi>2\<rangle> = 1\<sqdot>1 = 1. *)
  have norm_tensor: "\<parallel>tensor_vec \<psi>1 \<psi>2\<parallel> = 1"
    by (smt (verit) cpx_vec_length_inner_prod inner_prod_csqrt norm1 norm2 of_real_eq_1_iff 
        one_power2 power2_eq_square tensor_inner_prod)
  show ?thesis
    unfolding quantum_state_def using dim norm_tensor by simp
qed

lemma tensor_mat_vec_mult:
  assumes A: "A \<in> carrier_mat nr nc"
      and B: "B \<in> carrier_mat mr mc"
      and v: "dim_vec v = nc"
      and w: "dim_vec w = mc"
  shows "(A \<Otimes> B) *\<^sub>v tensor_vec v w = tensor_vec (A *\<^sub>v v) (B *\<^sub>v w)"
proof (rule eq_vecI)
  have vcar: "v \<in> carrier_vec nc"
    using carrier_vec_dim_vec v by blast

  have wcar: "w \<in> carrier_vec mc"
    using carrier_vec_dim_vec w by blast
  have dim_Av: "dim_vec (A *\<^sub>v v) = nr"
    using A v by simp
  have dim_Bw: "dim_vec (B *\<^sub>v w) = mr"
    using B w by simp
  show "dim_vec ((A \<Otimes> B) *\<^sub>v tensor_vec v w) = dim_vec (tensor_vec (A *\<^sub>v v) (B *\<^sub>v w))"
    using A B v w dim_Av dim_Bw by (simp add: tensor_vec_dim)
next
  fix i
  assume i: "i < dim_vec (tensor_vec (A *\<^sub>v v) (B *\<^sub>v w))"
  have vcar: "v \<in> carrier_vec nc"
    using carrier_vec_dim_vec v by blast
  have wcar: "w \<in> carrier_vec mc"
    using carrier_vec_dim_vec w by blast
  have dim_Av: "dim_vec (A *\<^sub>v v) = nr"
    using A v by simp
  have dim_Bw: "dim_vec (B *\<^sub>v w) = mr"
    using B w by simp
  have i_lt: "i < nr * mr"
    using i dim_Av dim_Bw by (simp add: tensor_vec_dim)
  show "((A \<Otimes> B) *\<^sub>v tensor_vec v w) $ i = tensor_vec (A *\<^sub>v v) (B *\<^sub>v w) $ i"
  proof (cases "nc = 0 \<or> mc = 0")
    case True
    have lhs: "((A \<Otimes> B) *\<^sub>v tensor_vec v w) $ i = 0"
      using A B v w i_lt True
      by (simp add: mult_mat_vec_index tensor_vec_dim,
          smt (verit, ccfv_SIG) carrier_matD(2) conjugate_square_eq_0_vec 
          cscalar_prod_is_inner_prod_swap dim_col_tensor_mat dim_vec
          index_row(2) inner_prod_with_row_bra_vec mult_0_right mult_cancel_left row_bra_vec 
          tensor_vec_dim vcar vec_of_dim_0 wcar)
    have rhs: "tensor_vec (A *\<^sub>v v) (B *\<^sub>v w) $ i = 0"
      using A B v w i_lt True
      by (smt (verit, ccfv_threshold) carrier_matD(1,2) dim_Av dim_Bw dim_col_tensor_mat 
          dim_row_tensor_mat index_mult_mat_vec index_row(2) less_mult_imp_div_less lhs 
          mod_less_divisor mult_eq_0_iff not_gr_zero tensor_vec_dim tensor_vec_index vec_of_dim_0)      
    show ?thesis
      using lhs rhs by simp
  next
    case False
    then have nc_pos: "nc > 0" and mc_pos: "mc > 0"
      by auto
    have mr_pos: "mr > 0"
      using i_lt by (cases mr) auto
    let ?f = "\<lambda>k. (A \<Otimes> B) $$ (i, k) * tensor_vec v w $ k"
    have AB_car: "A \<Otimes> B \<in> carrier_mat (nr * mr) (nc * mc)"
      using A B by auto
    have tvw_car: "tensor_vec v w \<in> carrier_vec (nc * mc)"
      using v w by (metis carrier_vec_dim_vec tensor_vec_dim)
    have lhs_sum: "((A \<Otimes> B) *\<^sub>v tensor_vec v w) $ i = (\<Sum>k = 0..<nc * mc. ?f k)"
      using mult_mat_vec_index[OF AB_car tvw_car i_lt] .
    have group_sum: "(\<Sum>k = 0..<nc * mc. ?f k) = (\<Sum>a = 0..<nc. \<Sum>b = 0..<mc. ?f (a * mc + b))"
    proof -
      have "(\<Sum>k = 0..<nc * mc. ?f k) = (\<Sum>a<nc. sum ?f {a * mc..<a * mc + mc})"
        using sum.nat_group[of ?f mc nc]
        by (simp add: atLeast0LessThan)
      also have "\<dots> = (\<Sum>a = 0..<nc. \<Sum>b = 0..<mc. ?f (a * mc + b))"
      proof (rule sum.cong)
        show "{..<nc} = {0..<nc}"
          by auto
      next
        fix a
        assume a: "a \<in> {0..<nc}"
        show "sum ?f {a * mc..<a * mc + mc} =
              (\<Sum>b = 0..<mc. ?f (a * mc + b))"
        proof (rule sum.reindex_bij_witness[where i = "\<lambda>b. a * mc + b" and j = "\<lambda>x. x - a * mc"])
          show "\<And>b. b \<in> {0..<mc} \<Longrightarrow> a * mc + b \<in> {a * mc..<a * mc + mc}"
            by simp
          show "\<And>x. x \<in> {a * mc..<a * mc + mc} \<Longrightarrow> x - a * mc \<in> {0..<mc}"
            by fastforce
          show "\<And>x. x \<in> {a * mc..<a * mc + mc} \<Longrightarrow> a * mc + (x - a * mc) = x"
            by simp
          show "\<And>b. b \<in> {0..<mc} \<Longrightarrow> a * mc + b - a * mc = b"
            by simp
          show "\<And>x. x \<in> {a * mc..<a * mc + mc} \<Longrightarrow> ?f (a * mc + (x - a * mc)) = ?f x"
            by simp
        qed
      qed
      finally show ?thesis.
    qed
    have expand: "\<And>a b. a < nc \<Longrightarrow> b < mc \<Longrightarrow>
       ?f (a * mc + b) = (A $$ (i div mr, a) * v $ a) * (B $$ (i mod mr, b) * w $ b)"
    proof -
      fix a b
      assume a: "a < nc" and b: "b < mc"
      have k_lt: "a * mc + b < nc * mc"
        by (metis False a b diff_is_0_eq diff_zero div_less_iff_less_mult 
            mult.commute not_less split_div)
      have div_k: "(a * mc + b) div mc = a"
        using b by simp
      have mod_k: "(a * mc + b) mod mc = b"
        using b by simp
      have mat_idx: "(A \<Otimes> B) $$ (i, a * mc + b) = A $$ (i div mr, a) * B $$ (i mod mr, b)"
        using A B i_lt k_lt nc_pos mc_pos div_k mod_k by auto      
      have vec_idx: "tensor_vec v w $ (a * mc + b) = v $ a * w $ b"
        using tensor_vec_index[OF v w k_lt] div_k mod_k by simp
      show "?f (a * mc + b) = (A $$ (i div mr, a) * v $ a) * (B $$ (i mod mr, b) * w $ b)"
        using mat_idx vec_idx by (simp add: algebra_simps)
    qed
    have lhs: "((A \<Otimes> B) *\<^sub>v tensor_vec v w) $ i =
       (\<Sum>a = 0..<nc. \<Sum>b = 0..<mc. (A $$ (i div mr, a) * v $ a) * (B $$ (i mod mr, b) * w $ b))"
    proof -
      have "((A \<Otimes> B) *\<^sub>v tensor_vec v w) $ i = (\<Sum>k = 0..<nc * mc. ?f k)"
        by (rule lhs_sum)
      also have "\<dots> = (\<Sum>a = 0..<nc. \<Sum>b = 0..<mc. ?f (a * mc + b))"
        by (rule group_sum)
      also have "\<dots> = (\<Sum>a = 0..<nc. \<Sum>b = 0..<mc.
                        (A $$ (i div mr, a) * v $ a) * (B $$ (i mod mr, b) * w $ b))"
      proof (rule sum.cong[OF refl], rule sum.cong[OF refl])
        fix a b
        assume "a \<in> {0..<nc}" and "b \<in> {0..<mc}"
        then have "a < nc" and "b < mc" by auto
        then show "?f (a * mc + b) =
                   (A $$ (i div mr, a) * v $ a) * (B $$ (i mod mr, b) * w $ b)"
          by (rule expand)
      qed
      finally show ?thesis .
    qed


    have div_lt: "i div mr < nr"
      using i_lt mr_pos by (simp add: less_mult_imp_div_less)
    have mod_lt: "i mod mr < mr"
      using mr_pos by simp
    have rhs: "tensor_vec (A *\<^sub>v v) (B *\<^sub>v w) $ i =
       (\<Sum>a = 0..<nc. A $$ (i div mr, a) * v $ a) * (\<Sum>b = 0..<mc. B $$ (i mod mr, b) * w $ b)"
    proof -
      have "tensor_vec (A *\<^sub>v v) (B *\<^sub>v w) $ i = (A *\<^sub>v v) $ (i div mr) * (B *\<^sub>v w) $ (i mod mr)"
        using tensor_vec_index[OF dim_Av dim_Bw i_lt].
      also have "\<dots> = (\<Sum>a = 0..<nc. A $$ (i div mr, a) * v $ a) *
                      (\<Sum>b = 0..<mc. B $$ (i mod mr, b) * w $ b)"
        using mult_mat_vec_index[OF A vcar div_lt]
              mult_mat_vec_index[OF B wcar mod_lt]
        by simp
      finally show ?thesis.
    qed
    have "(\<Sum>a = 0..<nc. \<Sum>b = 0..<mc.
          (A $$ (i div mr, a) * v $ a) * (B $$ (i mod mr, b) * w $ b)) =
          (\<Sum>a = 0..<nc. A $$ (i div mr, a) * v $ a) *
          (\<Sum>b = 0..<mc. B $$ (i mod mr, b) * w $ b)"
      by (simp add: sum_product)
    then show ?thesis
      using lhs rhs by simp
  qed
qed

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
  (* Step 1: (M \<otimes> I_m)(\<psi> \<otimes> \<phi>) = (M\<psi>) \<otimes> \<phi> -- mixed product property *)
  have mix: "(M \<Otimes> 1\<^sub>m m) *\<^sub>v (tensor_vec \<psi> \<phi>) = tensor_vec (M *\<^sub>v \<psi>) \<phi>"
    using tensor_mat_vec_mult_right_id[OF M_sq psi_dim phi_dim] .
  (* Step 2: \<parallel>(M\<psi>)\<otimes>\<phi>\<parallel>² = \<parallel>M\<psi>\<parallel>² \<sqdot> \<parallel>\<phi>\<parallel>² = \<parallel>M\<psi>\<parallel>² \<sqdot> 1 *)
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

lemma bell_state_norm:
  "\<parallel>bell_state\<parallel> = 1"
proof -
  let ?u = "tensor_vec (unit_vec 2 0) (unit_vec 2 0)"
  let ?v = "tensor_vec (unit_vec 2 1) (unit_vec 2 1)"
  have du: "dim_vec ?u = 4" using tensor_vec_dim by simp
  have dv: "dim_vec ?v = 4" using tensor_vec_dim by simp
  have dsum: "dim_vec (?u + ?v) = 4" using du dv by simp
  have inner_uu: "\<langle>?u | ?u\<rangle> = 1"
    by (smt (verit) cpx_vec_length_inner_prod numeral_2_eq_2 of_real_1 power2_eq_square power_one tensor_inner_prod unit_cpx_vec_length zero_less_Suc)
  have inner_vv: "\<langle>?v | ?v\<rangle> = 1"
    by (smt (verit) Suc_1 cpx_vec_length_inner_prod lessI of_real_1 power2_eq_square power_one tensor_inner_prod unit_cpx_vec_length)
  have inner_uv: "\<langle>?u | ?v\<rangle> = 0"
    by (smt (verit) One_nat_def index_unit_vec(3) lessI mult_zero_right numeral_2_eq_2 one_neq_zero orthogonal_unit_vec tensor_inner_prod zero_less_Suc)
  have inner_vu: "\<langle>?v | ?u\<rangle> = 0"
    using inner_uv inner_prod_cnj[of ?u ?v] du dv by simp
  have inner_sum: "\<langle>?u + ?v | ?u + ?v\<rangle> = 2"
  proof -
    have "\<langle>?u + ?v | ?u + ?v\<rangle>
        = \<langle>?u | ?u + ?v\<rangle> + \<langle>?v | ?u + ?v\<rangle>"
      by (smt (verit, best) complex_cnj_add dsum dv index_unit_vec(3)
          inner_prod_cnj inner_prod_right_add' tensor_vec_dim)
    also have "... = (\<langle>?u | ?u\<rangle> + \<langle>?u | ?v\<rangle>) + (\<langle>?v | ?u\<rangle> + \<langle>?v | ?v\<rangle>)"
      using du dv inner_prod_right_add' by presburger
    also have "... = \<langle>?u | ?u\<rangle> + \<langle>?u | ?v\<rangle> + \<langle>?v | ?u\<rangle> + \<langle>?v | ?v\<rangle>"
      by (simp add: algebra_simps)
    also have "... = 2"
      using inner_uu inner_vv inner_uv inner_vu by simp
    finally show ?thesis.
  qed
  have sq_norm: "(\<parallel>?u + ?v\<parallel>)\<^sup>2 = 2"
  proof -
    have "complex_of_real ((\<parallel>?u + ?v\<parallel>)\<^sup>2) = \<langle>?u + ?v | ?u + ?v\<rangle>"
      using cpx_vec_length_inner_prod[of "?u + ?v"] by simp
    also have "\<dots> = 2" by (rule inner_sum)
    finally have "complex_of_real ((\<parallel>?u + ?v\<parallel>)\<^sup>2) = complex_of_real 2" by simp
    thus ?thesis using of_real_eq_iff by blast
  qed
  then have norm_nonneg: "\<parallel>?u + ?v\<parallel> \<ge> 0"
    by (smt (verit, ccfv_SIG) Re_complex_of_real cpx_vec_length_inner_prod csqrt_of_real_nonneg 
        inner_prod_csqrt inner_prod_with_itself_Im real_sqrt_abs)
  then have norm_sum: "\<parallel>?u + ?v\<parallel> = sqrt 2"
    using sq_norm 
    by (metis real_sqrt_abs2 real_sqrt_power abs_of_nonneg power2_eq_square)
  have smult_form: "bell_state = (1 / csqrt 2) \<cdot>\<^sub>v (?u + ?v)"
    unfolding bell_state_def by simp
  have "\<parallel>bell_state\<parallel> = cmod (1 / csqrt 2) * \<parallel>?u + ?v\<parallel>"
    using smult_form cpx_vec_length_smult[of "1 / csqrt 2" "?u + ?v"] by simp
  also have "cmod (1 / csqrt 2) = 1 / sqrt 2"
    by (simp add: norm_divide)
  also have "\<dots> * \<parallel>?u + ?v\<parallel> = 1 / sqrt 2 * sqrt 2"
    using norm_sum by simp
  also have "\<dots> = 1"
    by (simp add: field_simps)
  finally show ?thesis.
qed

lemma bell_state_is_quantum_state:
  "quantum_state 4 bell_state"
proof -
  let ?u = "tensor_vec (unit_vec 2 0) (unit_vec 2 0)"
  let ?v = "tensor_vec (unit_vec 2 1) (unit_vec 2 1)"
  (* Step 1: each tensor has dim 4. *)
  have du: "dim_vec ?u = 4" using tensor_vec_dim by simp
  have dv: "dim_vec ?v = 4" using tensor_vec_dim by simp
  have dim_sum: "dim_vec (?u + ?v) = 4" using du dv by simp
  then have dim_bell: "dim_vec bell_state = 4"
    unfolding bell_state_def by simp
  (* Step 2: \<parallel>(1/\<surd>2)(?u + ?v)\<parallel>\<^sup>2 = (1/2)(\<langle>?u+?v|?u+?v\<rangle>) = (1/2)(1+0+0+1) = 1 *)
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

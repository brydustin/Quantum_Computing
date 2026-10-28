(*  Title:   Day15_Partial_Traces.thy
    Author:  Dustin Bryant, after Vern Paulsen's lecture of 30 September 2011 (Day 15)
*)

theory Day15_Partial_Traces
  imports Day13_Density_Matrices
begin

section \<open>Day 15 (30 September 2011): traces, tensor products of operators, partial traces\<close>

text \<open>\begin{notesprop}
For any orthonormal basis $\{u_1,\dots,u_n\}$ of $\C^n$, $\tr(A)=\sum_i\braket{u_i}{Au_i}$.
\end{notesprop}\<close>

theorem trace_via_onb:
  fixes A :: "complex Matrix.mat"
  assumes sq: "A \<in> carrier_mat n n"
      and orth: "orthonormal_list n vs"
      and full: "length vs = n"
  shows "Tr A = (\<Sum>i<n. \<langle>vs ! i | A *\<^sub>v vs ! i\<rangle>)"
proof -
  let ?V = "mat_of_cols n vs"
  have U: "unitary ?V"
    using orth full by (rule orthonormal_mat_unitary)
  have Vrow: "dim_row ?V = n"
    by (simp add: mat_of_cols_def)
  have Vcol: "dim_col ?V = n"
    using full by (simp add: mat_of_cols_def)
  have Arow: "dim_row A = n" and Acol: "dim_col A = n"
    using sq by auto

  have diag:
    "\<And>i. i < n \<Longrightarrow>
      ((?V\<^sup>\<dagger> * A * ?V) $$ (i, i)) = \<langle>vs ! i | A *\<^sub>v vs ! i\<rangle>"
  proof -
    fix i assume i_lt: "i < n"
    have vi_dim: "dim_vec (vs ! i) = n"
      using orth full i_lt by (simp add: orthonormal_listD_dim)
    have AV_entry:
      "\<And>k. k < n \<Longrightarrow> (A * ?V) $$ (k, i) = (A *\<^sub>v vs ! i) $ k"
    proof -
      fix k assume k_lt: "k < n"
      have "(A * ?V) $$ (k, i) = (\<Sum>j<n. A $$ (k, j) * ?V $$ (j, i))"
        using Arow Acol Vrow Vcol k_lt i_lt by simp
      also have "\<dots> = (\<Sum>j<n. A $$ (k, j) * (vs ! i) $ j)"
        using full i_lt by (intro sum.cong refl) (simp add: mat_of_cols_def)
      also have "\<dots> = (A *\<^sub>v vs ! i) $ k"
        using Arow Acol vi_dim k_lt
        by (simp add: scalar_prod_def lessThan_atLeast0)
      finally show "(A * ?V) $$ (k, i) = (A *\<^sub>v vs ! i) $ k" .
    qed

    have "((?V\<^sup>\<dagger> * A * ?V) $$ (i, i)) =
          ((?V\<^sup>\<dagger> * (A * ?V)) $$ (i, i))"
      using sq Vrow Vcol by (metis Vrow assoc_mult_mat carrier_mat_triv dim_col_of_dagger)
    also have "\<dots> = (\<Sum>k<n. (?V\<^sup>\<dagger>) $$ (i, k) * (A * ?V) $$ (k, i))"
      using Arow Acol Vrow Vcol i_lt by simp
    also have "\<dots> = (\<Sum>k<n. cnj ((vs ! i) $ k) * (A *\<^sub>v vs ! i) $ k)"
      using full i_lt by (intro sum.cong refl, metis AV_entry Vcol case_prod_conv dagger_def 
                          index_mat(1) lessThan_iff mat_of_cols_carrier(2) mat_of_cols_def) 
    also have "\<dots> = \<langle>vs ! i | A *\<^sub>v vs ! i\<rangle>"
      using Arow vi_dim by (simp add: inner_prod_def lessThan_atLeast0)
    finally show "((?V\<^sup>\<dagger> * A * ?V) $$ (i, i)) =  \<langle>vs ! i | A *\<^sub>v vs ! i\<rangle>".
  qed

  have "Tr (?V\<^sup>\<dagger> * A * ?V) =
        (\<Sum>i<n. ((?V\<^sup>\<dagger> * A * ?V) $$ (i, i)))"
    using Vrow Vcol Arow Acol by (simp add: Tr_def)
  also have "\<dots> = (\<Sum>i<n. \<langle>vs ! i | A *\<^sub>v vs ! i\<rangle>)"
    by (intro sum.cong refl) (simp add: diag)
  finally have "Tr (?V\<^sup>\<dagger> * A * ?V) =
                (\<Sum>i<n. \<langle>vs ! i | A *\<^sub>v vs ! i\<rangle>)" .
  moreover have "Tr (?V\<^sup>\<dagger> * A * ?V) = Tr A"
    using U Arow Acol Vrow by (subst Tr_unitary_conjugation, simp_all)
  ultimately show ?thesis
    by simp
qed

text \<open>\begin{notesprop}
$\tr(R\otimes T)=\tr(R)\tr(T)$.
\end{notesprop}\<close>

theorem trace_tensor:
  fixes R T :: "complex Matrix.mat"
  assumes Rsq: "R \<in> carrier_mat m m"
      and Tsq: "T \<in> carrier_mat p p"
      and m_pos: "0 < m" and p_pos: "0 < p"
  shows "Tr (R \<Otimes> T) = Tr R * Tr T"
proof -
  have drR: "dim_row R = m" using Rsq by auto
  have dcR: "dim_col R = m" using Rsq by auto
  have drT: "dim_row T = p" using Tsq by auto
  have dcT: "dim_col T = p" using Tsq by auto
  have RT_car: "R \<Otimes> T \<in> carrier_mat (m*p) (m*p)"
    using Rsq Tsq by auto

  \<comment> \<open>Diagonal entries factor via \<open>index_tensor_mat\<close>.\<close>
  have ent: "\<And>i k. i < m \<Longrightarrow> k < p \<Longrightarrow>
             (R \<Otimes> T) $$ (i * p + k, i * p + k) = R $$ (i, i) * T $$ (k, k)"
  proof -
    fix i k assume i_lt: "i < m" and k_lt: "k < p"
    have rb: "i * p + k < m * p"
    proof -
      have "i * p + k < (i + 1) * p" using k_lt by simp
      moreover have "(i + 1) * p \<le> m * p"
      proof -
        have "i + 1 \<le> m" using i_lt by simp
        thus "(i + 1) * p \<le> m * p" by (rule mult_le_mono1)
      qed
      ultimately show ?thesis by linarith
    qed
    have dv: "(i * p + k) div p = i" using k_lt by simp
    have md: "(i * p + k) mod p = k" using k_lt by simp
    have "(R \<Otimes> T) $$ (i * p + k, i * p + k)
          = R $$ ((i*p+k) div p, (i*p+k) div p)
            * T $$ ((i*p+k) mod p, (i*p+k) mod p)"
      using index_tensor_mat[OF drR dcR drT dcT rb rb m_pos p_pos] .
    also have "\<dots> = R $$ (i, i) * T $$ (k, k)"
      using dv md by simp
    finally show "(R \<Otimes> T) $$ (i * p + k, i * p + k) = R $$ (i, i) * T $$ (k, k)" .
  qed

  \<comment> \<open>Bijection \<open>{..<m}\<close> x \<open>{..<p}\<close> -> \<open>{..<m*p}\<close> via (i, k) |-> i*p + k.\<close>
  have bij: "bij_betw (\<lambda>(i, k). i * p + k) ({..<m} \<times> {..<p}) {..<m*p}"
  proof (rule bij_betwI[where g = "\<lambda>r. (r div p, r mod p)"])
    show "(\<lambda>(i, k). i * p + k) \<in> {..<m} \<times> {..<p} \<rightarrow> {..<m*p}"
    proof
      fix z assume z_in: "z \<in> {..<m} \<times> {..<p}"
      then obtain i k where z: "z = (i, k)" and i_lt: "i < m" and k_lt: "k < p"
        by blast
      have "i * p + k < (i + 1) * p" using k_lt by simp
      moreover have "(i + 1) * p \<le> m * p"
      proof -
        have "i + 1 \<le> m" using i_lt by simp
        thus "(i + 1) * p \<le> m * p" by (rule mult_le_mono1)
      qed
      ultimately have "i * p + k < m * p" by linarith
      thus "(case z of (i, k) \<Rightarrow> i * p + k) \<in> {..<m*p}"
        using z by simp
    qed
  next
    show "(\<lambda>r. (r div p, r mod p)) \<in> {..<m*p} \<rightarrow> {..<m} \<times> {..<p}"
      using p_pos by (auto simp: less_mult_imp_div_less)
  next
    fix z assume z_in: "z \<in> {..<m} \<times> {..<p}"
    then obtain i k where z: "z = (i, k)" and i_lt: "i < m" and k_lt: "k < p"
      by blast
    show "(\<lambda>r. (r div p, r mod p)) ((\<lambda>(i, k). i * p + k) z) = z"
      using z k_lt by simp
  next
    fix r assume r_in: "r \<in> {..<m*p}"
    show "(\<lambda>(i, k). i * p + k) ((\<lambda>r. (r div p, r mod p)) r) = r"
      by simp
  qed

  have "Tr (R \<Otimes> T) = (\<Sum>r<m*p. (R \<Otimes> T) $$ (r, r))"
    using RT_car by (simp add: Tr_def, 
        smt (verit, del_insts) carrier_matD(1,2) 
             dim_col_tensor_mat dim_row_tensor_mat lessThan_iff sum.cong)
  also have "\<dots> = (\<Sum>(i, k) \<in> {..<m} \<times> {..<p}.
                    (R \<Otimes> T) $$ (i * p + k, i * p + k))"
    using sum.reindex_bij_betw[OF bij, symmetric, of "\<lambda>r. (R \<Otimes> T) $$ (r, r)"]
    by (simp add: case_prod_beta)
  also have "\<dots> = (\<Sum>(i, k) \<in> {..<m} \<times> {..<p}. R $$ (i, i) * T $$ (k, k))"
    by (intro sum.cong refl) (auto simp: ent)
  also have "\<dots> = (\<Sum>i<m. \<Sum>k<p. R $$ (i, i) * T $$ (k, k))"
    by (simp add: sum.cartesian_product)
  also have "\<dots> = (\<Sum>i<m. R $$ (i, i)) * (\<Sum>k<p. T $$ (k, k))"
    by (simp add: sum_product)
  also have "\<dots> = Tr R * Tr T"
    using Rsq Tsq by (simp add: Tr_def)
  finally show ?thesis.
qed

subsection \<open>The isomorphism $L(\Hil_A)\otimes L(\Hil_B)\cong L(\Hil_A\otimes\Hil_B)$\<close>

text \<open>\begin{notesprop}
In finite dimensions the map $\Gamma:L(\Hil_A)\otimes L(\Hil_B)\to L(\Hil_A\otimes\Hil_B)$,
$R\otimes T\mapsto R\otimes T$, is a vector-space isomorphism (both sides have dimension
$m^2p^2$ and $\Gamma$ is injective).
\end{notesprop}
Formally, $L(\Hil_A)\otimes L(\Hil_B)$ is represented in coordinates as $M_{m^2,p^2}$ and
$\Gamma$ as the reindexing $M_{m^2,p^2}\to M_{mp}$; it is an explicit linear isomorphism
with explicit inverse.\<close>

text \<open>Postulate 4$'$ (Day 16) and the composite ensembles of Day 14: tensor products of positive
matrices are positive, and tensor products of density matrices are density matrices.\<close>

text \<open>Products of densities are densities: if $A=\sum_ia_ia_i^*$ and $B=\sum_jb_jb_j^*$ then
\[ A\otimes B=\sum_{i,j}(a_i\otimes b_j)(a_i\otimes b_j)^*\ge0,\qquad \Tr(A\otimes B)=\Tr A\,\Tr B. \]\<close>

lemma psd_tensor:
  fixes A B :: "complex Matrix.mat"
  assumes A: "A \<in> carrier_mat m m" and B: "B \<in> carrier_mat p p"
      and pA: "psd A" and pB: "psd B"
  shows "psd (A \<Otimes> B)"
proof -
  obtain vs :: "complex Matrix.vec list"
    where vl: "length vs = m" and vd: "\<forall>v \<in> set vs. dim_vec v = m" and vA: "outer_sum m vs = A"
    using psd_kraus_decomp[OF A pA] by blast
  obtain ws :: "complex Matrix.vec list"
    where wl: "length ws = p" and wd: "\<forall>w \<in> set ws. dim_vec w = p" and wB: "outer_sum p ws = B"
    using psd_kraus_decomp[OF B pB] by blast
  let ?V = "mat_of_cols m vs" and ?W = "mat_of_cols p ws"
  have Vc: "?V \<in> carrier_mat m m" using mat_of_cols_carrier(1)[of m vs] vl by simp
  have Wc: "?W \<in> carrier_mat p p" using mat_of_cols_carrier(1)[of p ws] wl by simp
  have A_eq: "A = ?V * (?V\<^sup>\<dagger>)" using vA by (simp add: outer_sum_def)
  have B_eq: "B = ?W * (?W\<^sup>\<dagger>)" using wB by (simp add: outer_sum_def)
  have "A \<Otimes> B = (?V * (?V\<^sup>\<dagger>)) \<Otimes> (?W * (?W\<^sup>\<dagger>))" using A_eq B_eq by simp
  also have "\<dots> = (?V \<Otimes> ?W) * ((?V\<^sup>\<dagger>) \<Otimes> (?W\<^sup>\<dagger>))"
    using tensor_mat_mult[of ?V "?V\<^sup>\<dagger>" ?W "?W\<^sup>\<dagger>"] Vc Wc by simp
  also have "(?V\<^sup>\<dagger>) \<Otimes> (?W\<^sup>\<dagger>) = (?V \<Otimes> ?W)\<^sup>\<dagger>" by (simp add: hermite_cnj_of_tensor)
  finally have VW: "A \<Otimes> B = (?V \<Otimes> ?W) * ((?V \<Otimes> ?W)\<^sup>\<dagger>)" .
  have VWc: "?V \<Otimes> ?W \<in> carrier_mat (m * p) (m * p)"
    using Vc Wc unfolding carrier_mat_def by (simp add: dim_row_tensor_mat dim_col_tensor_mat)
  have VWd: "(?V \<Otimes> ?W)\<^sup>\<dagger> \<in> carrier_mat (m * p) (m * p)"
    using VWc unfolding carrier_mat_def by (simp add: dagger_def)
  have "psd (((?V \<Otimes> ?W)\<^sup>\<dagger>)\<^sup>\<dagger> * ((?V \<Otimes> ?W)\<^sup>\<dagger>))" by (rule psd_MdagM[OF VWd])
  thus ?thesis using VW by (simp add: dagger_of_dagger_is_id)
qed

lemma density_matrix_tensor:
  fixes A B :: "complex Matrix.mat"
  assumes dA: "density_matrix m A" and dB: "density_matrix p B"
      and m: "0 < m" and p: "0 < p"
  shows "density_matrix (m * p) (A \<Otimes> B)"
proof -
  have A: "A \<in> carrier_mat m m" and B: "B \<in> carrier_mat p p"
    and pA: "psd A" and pB: "psd B" and tA: "Tr A = 1" and tB: "Tr B = 1"
    using dA dB by (auto simp: density_matrix_def)
  have car: "A \<Otimes> B \<in> carrier_mat (m * p) (m * p)" using A B by auto
  show ?thesis
    unfolding density_matrix_def
    using car psd_tensor[OF A B pA pB] trace_tensor[OF A B m p] tA tB by simp
qed

proposition L_tensor_dim:
  fixes m p :: nat
  shows "m^2 * p^2 = (m * p)^2"
  by (simp add: power2_eq_square mult.assoc mult.left_commute)

definition operator_tensor_iso_map :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "operator_tensor_iso_map m p c \<equiv>
     Matrix.mat (m*p) (m*p)
       (\<lambda>(r,s). c $$ ((r div p) * m + (s div p), (r mod p) * p + (s mod p)))"

text \<open>The coordinate model: $L(\Hil_A)\otimes L(\Hil_B)$ is $M_{m^2,p^2}$, the entry in row $(i,i')$ and
column $(k,k')$ being the coefficient of $E_{ii'}\otimes E_{kk'}$.  $\Gamma$ moves it to position
$((i,k),(i',k'))$ of an $mp\times mp$ matrix,
\[ \Gamma(c)_{ip+k,\;i'p+k'}=c_{im+i',\;kp+k'}, \]
so $\Gamma(\sum c\,E_{ii'}\otimes E_{kk'})$ is the same sum with $\otimes$ the Kronecker product.
Being a reindexing, it is linear and bijective.\<close>

lemma operator_tensor_iso_map_carrier [simp]:
  "operator_tensor_iso_map m p c \<in> carrier_mat (m*p) (m*p)"
  by (simp add: operator_tensor_iso_map_def)

lemma operator_tensor_iso_map_row_bound:
  fixes m p r s :: nat
  assumes p_pos: "0 < p" and "r < m*p" and "s < m*p"
  shows "(r div p) * m + (s div p) < m*m"
proof -
  have rdiv: "r div p < m"
    using div_less_iff_less_mult[OF p_pos, of r m] assms(2) by simp
  have sdiv: "s div p < m"
    using div_less_iff_less_mult[OF p_pos, of s m] assms(3) by simp
  have "(r div p) * m + (s div p) < (r div p) * m + m"
    using sdiv by simp
  also have "\<dots> = Suc (r div p) * m"
    by simp
  also have "\<dots> \<le> m * m"
    using rdiv by (metis Suc_leI mult.commute mult_le_mono2)
  finally show ?thesis .
qed

lemma operator_tensor_iso_map_col_bound:
  fixes p r s :: nat
  assumes p_pos: "0 < p"
  shows "(r mod p) * p + (s mod p) < p*p"
proof -
  have rmod: "r mod p < p"
    using mod_less_divisor[of p r] p_pos by simp
  have smod: "s mod p < p"
    using mod_less_divisor[of p s] p_pos by simp
  have "(r mod p) * p + (s mod p) < (r mod p) * p + p"
    using smod by simp
  also have "\<dots> = Suc (r mod p) * p"
    by simp
  also have "\<dots> \<le> p * p"
    using rmod by (metis Suc_leI mult.commute mult_le_mono2)
  finally show ?thesis .
qed

definition operator_tensor_iso_inv :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "operator_tensor_iso_inv m p x \<equiv>
     Matrix.mat (m*m) (p*p)
       (\<lambda>(a,b). x $$ ((a div m) * p + (b div p), (a mod m) * p + (b mod p)))"

definition operator_tensor_coordinate_space ::
  "nat \<Rightarrow> nat \<Rightarrow> (complex, complex Matrix.mat) linear_structure" where
  "operator_tensor_coordinate_space m p \<equiv> mat_linear_structure (m*m) (p*p)"

definition bipartite_operator_space ::
  "nat \<Rightarrow> nat \<Rightarrow> (complex, complex Matrix.mat) linear_structure" where
  "bipartite_operator_space m p \<equiv> mat_linear_structure (m*p) (m*p)"

lemma operator_tensor_iso_inv_carrier [simp]:
  "operator_tensor_iso_inv m p x \<in> carrier_mat (m*m) (p*p)"
  by (simp add: operator_tensor_iso_inv_def)

lemma operator_tensor_iso_inv_row_bound:
  fixes m p a b :: nat
  assumes m_pos: "0 < m" and p_pos: "0 < p" and "a < m*m" and "b < p*p"
  shows "(a div m) * p + (b div p) < m*p"
proof -
  have adiv: "a div m < m"
    using div_less_iff_less_mult[OF m_pos, of a m] assms(3) by simp
  have bdiv: "b div p < p"
    using div_less_iff_less_mult[OF p_pos, of b p] assms(4) by simp
  have "(a div m) * p + (b div p) < (a div m) * p + p"
    using bdiv by simp
  also have "\<dots> = Suc (a div m) * p"
    by simp
  also have "\<dots> \<le> m * p"
    using adiv by (metis Suc_leI mult_le_mono1)
  finally show ?thesis .
qed

lemma operator_tensor_iso_inv_col_bound:
  fixes m p a b :: nat
  assumes m_pos: "0 < m" and p_pos: "0 < p"
  shows "(a mod m) * p + (b mod p) < m*p"
proof -
  have amod: "a mod m < m"
    using mod_less_divisor[of m a] m_pos by simp
  have bmod: "b mod p < p"
    using mod_less_divisor[of p b] p_pos by simp
  have "(a mod m) * p + (b mod p) < (a mod m) * p + p"
    using bmod by simp
  also have "\<dots> = Suc (a mod m) * p"
    by simp
  also have "\<dots> \<le> m * p"
    using amod by (metis Suc_leI mult_le_mono1)
  finally show ?thesis .
qed

lemma operator_tensor_iso_map_add:
  assumes p_pos: "0 < p"
      and x: "x \<in> carrier_mat (m*m) (p*p)"
      and y: "y \<in> carrier_mat (m*m) (p*p)"
  shows "operator_tensor_iso_map m p (x + y) =
         operator_tensor_iso_map m p x + operator_tensor_iso_map m p y"
proof (rule eq_matI, goal_cases)
  case (1 i j)
  then have i: "i < m*p" and j: "j < m*p"
    by (simp_all add: operator_tensor_iso_map_def)
  have row: "(i div p) * m + (j div p) < m*m"
    using operator_tensor_iso_map_row_bound[OF p_pos i j] .
  have col: "(i mod p) * p + (j mod p) < p*p"
    using operator_tensor_iso_map_col_bound[OF p_pos, of i j] .
  show ?case
    using i j row col x y by (simp add: operator_tensor_iso_map_def)
next
  case 2
  show ?case by (simp add: operator_tensor_iso_map_def)
next
  case 3
  show ?case by (simp add: operator_tensor_iso_map_def)
qed

lemma operator_tensor_iso_map_zero:
  assumes p_pos: "0 < p"
  shows "operator_tensor_iso_map m p (0\<^sub>m (m*m) (p*p)) = 0\<^sub>m (m*p) (m*p)"
  by (smt (verit) add_inv_exists_mat assoc_add_mat operator_tensor_iso_map_add 
      operator_tensor_iso_map_carrier p_pos right_add_zero_mat zero_carrier_mat)  

lemma operator_tensor_iso_map_smult:
  assumes p_pos: "0 < p"
      and x: "x \<in> carrier_mat (m*m) (p*p)"
  shows "operator_tensor_iso_map m p (c \<cdot>\<^sub>m x) =
         c \<cdot>\<^sub>m operator_tensor_iso_map m p x"
proof (rule eq_matI, goal_cases)
  case (1 i j)
  then have i: "i < m*p" and j: "j < m*p"
    by (simp_all add: operator_tensor_iso_map_def)
  have row: "(i div p) * m + (j div p) < m*m"
    using operator_tensor_iso_map_row_bound[OF p_pos i j] .
  have col: "(i mod p) * p + (j mod p) < p*p"
    using operator_tensor_iso_map_col_bound[OF p_pos, of i j] .
  show ?case
    using i j row col x by (simp add: operator_tensor_iso_map_def)
next
  case 2
  show ?case by (simp add: operator_tensor_iso_map_def)
next
  case 3
  show ?case by (simp add: operator_tensor_iso_map_def)
qed

lemma operator_tensor_iso_inv_add:
  assumes m_pos: "0 < m"
      and p_pos: "0 < p"
      and x: "x \<in> carrier_mat (m*p) (m*p)"
      and y: "y \<in> carrier_mat (m*p) (m*p)"
  shows "operator_tensor_iso_inv m p (x + y) =
         operator_tensor_iso_inv m p x + operator_tensor_iso_inv m p y"
proof (rule eq_matI, goal_cases)
  case (1 a b)
  then have a: "a < m*m" and b: "b < p*p"
    by (simp_all add: operator_tensor_iso_inv_def)
  have row: "(a div m) * p + (b div p) < m*p"
    using operator_tensor_iso_inv_row_bound[OF m_pos p_pos a b] .
  have col: "(a mod m) * p + (b mod p) < m*p"
    using operator_tensor_iso_inv_col_bound[OF m_pos p_pos, of a b] .
  show ?case
    using a b row col x y by (simp add: operator_tensor_iso_inv_def)
next
  case 2
  show ?case by (simp add: operator_tensor_iso_inv_def)
next
  case 3
  show ?case by (simp add: operator_tensor_iso_inv_def)
qed

lemma operator_tensor_iso_inv_zero:
  assumes m_pos: "0 < m" and p_pos: "0 < p"
  shows "operator_tensor_iso_inv m p (0\<^sub>m (m*p) (m*p)) = 0\<^sub>m (m*m) (p*p)"
  by (smt (verit) add_inv_exists_mat assoc_add_mat m_pos operator_tensor_iso_inv_add 
      operator_tensor_iso_inv_carrier p_pos right_add_zero_mat zero_carrier_mat)
 

lemma operator_tensor_iso_inv_smult:
  assumes m_pos: "0 < m"
      and p_pos: "0 < p"
      and x: "x \<in> carrier_mat (m*p) (m*p)"
  shows "operator_tensor_iso_inv m p (c \<cdot>\<^sub>m x) =
         c \<cdot>\<^sub>m operator_tensor_iso_inv m p x"
proof (rule eq_matI, goal_cases)
  case (1 a b)
  then have a: "a < m*m" and b: "b < p*p"
    by (simp_all add: operator_tensor_iso_inv_def)
  have row: "(a div m) * p + (b div p) < m*p"
    using operator_tensor_iso_inv_row_bound[OF m_pos p_pos a b] .
  have col: "(a mod m) * p + (b mod p) < m*p"
    using operator_tensor_iso_inv_col_bound[OF m_pos p_pos, of a b] .
  show ?case
    using a b row col x by (simp add: operator_tensor_iso_inv_def)
next
  case 2
  show ?case by (simp add: operator_tensor_iso_inv_def)
next
  case 3
  show ?case by (simp add: operator_tensor_iso_inv_def)
qed

proposition operator_tensor_space_isomorphism:
  assumes m_pos: "0 < m"
      and p_pos: "0 < p"
  shows "is_isomorphism_between
           (operator_tensor_coordinate_space m p)
           (bipartite_operator_space m p)
           (operator_tensor_iso_map m p)"
proof -
  let ?V = "operator_tensor_coordinate_space m p"
  let ?W = "bipartite_operator_space m p"
  let ?F = "operator_tensor_iso_map m p"
  let ?G = "operator_tensor_iso_inv m p"

  have F_linear: "linear_structure_map ?V ?W ?F"
    unfolding linear_structure_map_def operator_tensor_coordinate_space_def
      bipartite_operator_space_def mat_linear_structure_def
    by (auto intro: operator_tensor_iso_map_zero[OF p_pos]
               operator_tensor_iso_map_add[OF p_pos]
               operator_tensor_iso_map_smult[OF p_pos])

  have G_linear: "linear_structure_map ?W ?V ?G"
    unfolding linear_structure_map_def operator_tensor_coordinate_space_def
      bipartite_operator_space_def mat_linear_structure_def
    by (auto intro: operator_tensor_iso_inv_zero[OF m_pos p_pos]
               operator_tensor_iso_inv_add[OF m_pos p_pos]
               operator_tensor_iso_inv_smult[OF m_pos p_pos])

  have GF: "\<And>x. x \<in> ls_carrier ?V \<Longrightarrow> ?G (?F x) = x"
  proof -
    fix x
    assume x: "x \<in> ls_carrier ?V"
    then have xc: "x \<in> carrier_mat (m*m) (p*p)"
      by (simp add: operator_tensor_coordinate_space_def mat_linear_structure_def)
    show "?G (?F x) = x"
    proof (rule eq_matI)
      show "dim_row (?G (?F x)) = dim_row x"
        using xc by (simp add: operator_tensor_iso_inv_def)
      show "dim_col (?G (?F x)) = dim_col x"
        using xc by (simp add: operator_tensor_iso_inv_def)
    next
      fix a b
      assume ab: "a < dim_row x" "b < dim_col x"
      then have a: "a < m*m" and b: "b < p*p"
        using xc by auto
      have adiv: "a div m < m"
        using a m_pos by (simp add: div_less_iff_less_mult)
      have amod: "a mod m < m"
        using m_pos by simp
      have bdiv: "b div p < p"
        using b p_pos by (simp add: div_less_iff_less_mult)
      have bmod: "b mod p < p"
        using p_pos by simp
      have row: "(a div m) * p + (b div p) < m * p"
        using operator_tensor_iso_inv_row_bound[OF m_pos p_pos a b] .
      have col: "(a mod m) * p + (b mod p) < m * p"
        using operator_tensor_iso_inv_col_bound[OF m_pos p_pos, of a b] .
      have div_row: "((a div m) * p + (b div p)) div p = a div m"
        using bdiv by simp
      have div_col: "((a mod m) * p + (b mod p)) div p = a mod m"
        using bmod by simp
      have mod_row: "((a div m) * p + (b div p)) mod p = b div p"
        using bdiv by simp
      have mod_col: "((a mod m) * p + (b mod p)) mod p = b mod p"
        using bmod by simp
      have recomb_a: "(a div m) * m + (a mod m) = a"
        by simp
      have recomb_b: "(b div p) * p + (b mod p) = b"
        by simp
      show "?G (?F x) $$ (a,b) = x $$ (a,b)"
        using a b row col div_row div_col mod_row mod_col recomb_a recomb_b
        by (simp add: operator_tensor_iso_inv_def operator_tensor_iso_map_def)
    qed
  qed

  have FG: "\<And>y. y \<in> ls_carrier ?W \<Longrightarrow> ?F (?G y) = y"
  proof -
    fix y
    assume y: "y \<in> ls_carrier ?W"
    then have yc: "y \<in> carrier_mat (m*p) (m*p)"
      by (simp add: bipartite_operator_space_def mat_linear_structure_def)
    show "?F (?G y) = y"
    proof (rule eq_matI)
      show "dim_row (?F (?G y)) = dim_row y"
        using yc by (simp add: operator_tensor_iso_map_def)
      show "dim_col (?F (?G y)) = dim_col y"
        using yc by (simp add: operator_tensor_iso_map_def)
    next
      fix r s
      assume rs: "r < dim_row y" "s < dim_col y"
      then have r: "r < m*p" and s: "s < m*p"
        using yc by auto
      have rdiv: "r div p < m"
        using r p_pos by (simp add: div_less_iff_less_mult)
      have sdiv: "s div p < m"
        using s p_pos by (simp add: div_less_iff_less_mult)
      have rmod: "r mod p < p"
        using p_pos by simp
      have smod: "s mod p < p"
        using p_pos by simp
      have row: "(r div p) * m + (s div p) < m * m"
        using operator_tensor_iso_map_row_bound[OF p_pos r s] .
      have col: "(r mod p) * p + (s mod p) < p * p"
        using operator_tensor_iso_map_col_bound[OF p_pos, of r s] .
      have div_row: "((r div p) * m + (s div p)) div m = r div p"
        using sdiv by simp
      have mod_row: "((r div p) * m + (s div p)) mod m = s div p"
        using sdiv by simp
      have div_col: "((r mod p) * p + (s mod p)) div p = r mod p"
        using smod by simp
      have mod_col: "((r mod p) * p + (s mod p)) mod p = s mod p"
        using smod by simp
      have recomb_r: "(r div p) * p + (r mod p) = r"
        by simp
      have recomb_s: "(s div p) * p + (s mod p) = s"
        by simp
      show "?F (?G y) $$ (r,s) = y $$ (r,s)"
        using r s row col div_row mod_row div_col mod_col recomb_r recomb_s
        by (simp add: operator_tensor_iso_inv_def operator_tensor_iso_map_def)
    qed
  qed

  show ?thesis
    unfolding is_isomorphism_between_def
    using F_linear G_linear GF FG by blast
qed

corollary operator_tensor_space_isomorphic:
  assumes "0 < m" and "0 < p"
  shows "is_isomorphic_to
           (operator_tensor_coordinate_space m p)
           (bipartite_operator_space m p)"
  using operator_tensor_space_isomorphism[OF assms]
  by (auto simp: is_isomorphic_to_def)

text \<open>D15-3: in the coordinate model $L(\Hil_A)\otimes L(\Hil_B)=M_{m^2\times p^2}$ the elementary
tensor $R\otimes T$ is the matrix $(R_{ij}T_{kl})_{(im+j,\,kp+l)}$.  The isomorphism $\Gamma$ of
\<open>operator_tensor_space_isomorphism\<close> sends it to the Kronecker product $R\otimes T$, and $\Gamma$ is
the only linear map that does.\<close>

definition op_elem :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "op_elem m p Ra Tb = Matrix.mat (m * m) (p * p) (\<lambda>(a, b). Ra $$ (a div m, a mod m) * Tb $$ (b div p, b mod p))"

theorem gamma_elementary:
  assumes Ra: "Ra \<in> carrier_mat m m" and Tb: "Tb \<in> carrier_mat p p"
  shows "operator_tensor_iso_map m p (op_elem m p Ra Tb) = Ra \<Otimes> Tb"
proof (rule eq_matI)
  fix r s assume "r < dim_row (Ra \<Otimes> Tb)" "s < dim_col (Ra \<Otimes> Tb)"
  hence rs: "r < m * p" "s < m * p" using Ra Tb by auto
  have m0: "0 < m" and p0: "0 < p" using rs by (auto intro: gr0I)
  have rd: "r div p < m" "s div p < m" using rs by (auto simp: less_mult_imp_div_less)
  have a: "(r div p) * m + s div p < m * m" and b: "(r mod p) * p + s mod p < p * p"
  proof -
    have "(r div p) * m + s div p < (r div p) * m + m" using rd by simp
    also have "\<dots> = (Suc (r div p)) * m" by simp
    also have "\<dots> \<le> m * m" using rd(1) by (intro mult_le_mono1) simp
    finally show "(r div p) * m + s div p < m * m" .
    have "(r mod p) * p + s mod p < (r mod p) * p + p" using p0 by simp
    also have "\<dots> = (Suc (r mod p)) * p" by simp
    also have "\<dots> \<le> p * p" using p0 by (intro mult_le_mono1) (simp add: Suc_leI)
    finally show "(r mod p) * p + s mod p < p * p" .
  qed
  have "operator_tensor_iso_map m p (op_elem m p Ra Tb) $$ (r, s)
        = Ra $$ (((r div p) * m + s div p) div m, ((r div p) * m + s div p) mod m)
          * Tb $$ (((r mod p) * p + s mod p) div p, ((r mod p) * p + s mod p) mod p)"
    using rs a b by (simp add: operator_tensor_iso_map_def op_elem_def)
  also have "\<dots> = Ra $$ (r div p, s div p) * Tb $$ (r mod p, s mod p)" using rd(2) m0 p0 by simp
  also have "\<dots> = (Ra \<Otimes> Tb) $$ (r, s)" using Ra Tb rs m0 p0 by (simp add: index_tensor_mat)
  finally show "operator_tensor_iso_map m p (op_elem m p Ra Tb) $$ (r, s) = (Ra \<Otimes> Tb) $$ (r, s)" .
qed (use Ra Tb in \<open>auto simp: operator_tensor_iso_map_def\<close>)

definition unit_mat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
  "unit_mat K1 K2 a b = Matrix.mat K1 K2 (\<lambda>(i, j). if i = a \<and> j = b then 1 else 0)"

lemma unit_mat_carrier [simp]: "unit_mat K1 K2 a b \<in> carrier_mat K1 K2" by (simp add: unit_mat_def)

text \<open>The unit matrices of $M_{m^2\times p^2}$ are elementary tensors of unit matrices.\<close>

lemma unit_mat_op_elem:
  assumes a: "a < m * m" and b: "b < p * p"
  shows "unit_mat (m * m) (p * p) a b = op_elem m p (unit_mat m m (a div m) (a mod m)) (unit_mat p p (b div p) (b mod p))"
proof (rule eq_matI)
  fix i j assume "i < dim_row (op_elem m p (unit_mat m m (a div m) (a mod m)) (unit_mat p p (b div p) (b mod p)))"
    "j < dim_col (op_elem m p (unit_mat m m (a div m) (a mod m)) (unit_mat p p (b div p) (b mod p)))"
  hence ij: "i < m * m" "j < p * p" by (simp_all add: op_elem_def)
  have m0: "0 < m" and p0: "0 < p" using a b by (auto intro: gr0I)
  have e: "x = y \<longleftrightarrow> x div k = y div k \<and> x mod k = y mod k" for x y k :: nat
  proof
    assume h: "x div k = y div k \<and> x mod k = y mod k"
    have "x = x div k * k + x mod k" by simp
    also have "\<dots> = y div k * k + y mod k" using h by simp
    also have "\<dots> = y" by simp
    finally show "x = y" .
  qed simp
  show "unit_mat (m * m) (p * p) a b $$ (i, j) = op_elem m p (unit_mat m m (a div m) (a mod m)) (unit_mat p p (b div p) (b mod p)) $$ (i, j)"
    using ij m0 p0 a b by (auto simp: unit_mat_def op_elem_def less_mult_imp_div_less e[of i a m] e[of j b p])
qed (simp_all add: op_elem_def unit_mat_def)

text \<open>A linear map on $M_{K_1\times K_2}$ is determined by its values on the unit matrices.\<close>

definition linear_mat_on :: "nat \<Rightarrow> nat \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow> bool" where
  "linear_mat_on K1 K2 \<Phi> \<longleftrightarrow>
     (\<forall>x y. x \<in> carrier_mat K1 K2 \<longrightarrow> y \<in> carrier_mat K1 K2 \<longrightarrow> \<Phi> (x + y) = \<Phi> x + \<Phi> y)
   \<and> (\<forall>c x. x \<in> carrier_mat K1 K2 \<longrightarrow> \<Phi> (c \<cdot>\<^sub>m x) = c \<cdot>\<^sub>m \<Phi> x)"

lemma vec_to_mat_unit:
  assumes k: "k < K1 * K2"
  shows "vec_to_mat K1 K2 (unit_vec (K1 * K2) k) = unit_mat K1 K2 (k div K2) (k mod K2)"
proof (rule eq_matI)
  fix i j assume ij: "i < dim_row (unit_mat K1 K2 (k div K2) (k mod K2))" "j < dim_col (unit_mat K1 K2 (k div K2) (k mod K2))"
  hence i: "i < K1" and j: "j < K2" by (simp_all add: unit_mat_def)
  have lt: "i * K2 + j < K1 * K2"
  proof -
    have "i * K2 + j < Suc i * K2" using j by simp
    also have "\<dots> \<le> K1 * K2" using i by (intro mult_le_mono1) simp
    finally show ?thesis .
  qed
  have "(i * K2 + j = k) \<longleftrightarrow> (i = k div K2 \<and> j = k mod K2)"
  proof
    assume "i * K2 + j = k" thus "i = k div K2 \<and> j = k mod K2" using j by auto
  next
    assume "i = k div K2 \<and> j = k mod K2" thus "i * K2 + j = k" by (simp add: div_mult_mod_eq)
  qed
  thus "vec_to_mat K1 K2 (unit_vec (K1 * K2) k) $$ (i, j) = unit_mat K1 K2 (k div K2) (k mod K2) $$ (i, j)"
    using i j lt by (simp add: vec_to_mat_def unit_mat_def unit_vec_def)
qed (simp_all add: vec_to_mat_def unit_mat_def)

lemma linear_mat_unique:
  assumes l1: "linear_mat_on K1 K2 \<Phi>" and l2: "linear_mat_on K1 K2 \<Psi>"
    and dims: "\<And>x. x \<in> carrier_mat K1 K2 \<Longrightarrow> dim_row (\<Phi> x) = Q1 \<and> dim_col (\<Phi> x) = Q2 \<and> dim_row (\<Psi> x) = Q1 \<and> dim_col (\<Psi> x) = Q2"
    and e: "\<And>a b. a < K1 \<Longrightarrow> b < K2 \<Longrightarrow> \<Phi> (unit_mat K1 K2 a b) = \<Psi> (unit_mat K1 K2 a b)"
    and c: "c \<in> carrier_mat K1 K2"
  shows "\<Phi> c = \<Psi> c"
proof (rule eq_matI)
  have K20: "K2 = 0 \<or> 0 < K2" by auto
  have uc: "vec_to_mat K1 K2 x \<in> carrier_mat K1 K2" for x by (simp add: vec_to_mat_def)
  have lin: "linear_on (K1 * K2) (\<lambda>x. F (vec_to_mat K1 K2 x) $$ (r, s))" if l: "linear_mat_on K1 K2 F"
    and rs: "\<And>x. x \<in> carrier_mat K1 K2 \<Longrightarrow> r < dim_row (F x) \<and> s < dim_col (F x)" for F r s
  proof -
    have add: "vec_to_mat K1 K2 (x + y) = vec_to_mat K1 K2 x + vec_to_mat K1 K2 y" if "dim_vec x = K1 * K2" "dim_vec y = K1 * K2" for x y
    proof (rule eq_matI)
      fix i j assume "i < dim_row (vec_to_mat K1 K2 x + vec_to_mat K1 K2 y)" "j < dim_col (vec_to_mat K1 K2 x + vec_to_mat K1 K2 y)"
      hence i: "i < K1" and j: "j < K2" by (simp_all add: vec_to_mat_def)
      have "i * K2 + j < K1 * K2"
      proof -
        have "i * K2 + j < Suc i * K2" using j by simp
        also have "\<dots> \<le> K1 * K2" using i by (intro mult_le_mono1) simp
        finally show ?thesis .
      qed
      thus "vec_to_mat K1 K2 (x + y) $$ (i, j) = (vec_to_mat K1 K2 x + vec_to_mat K1 K2 y) $$ (i, j)" using i j that by (simp add: vec_to_mat_def)
    qed (simp_all add: vec_to_mat_def)
    have sm: "vec_to_mat K1 K2 (a \<cdot>\<^sub>v x) = a \<cdot>\<^sub>m vec_to_mat K1 K2 x" if "dim_vec x = K1 * K2" for a x
      by (rule eq_matI) (use that mult_index_lt in \<open>simp_all add: vec_to_mat_def\<close>)
    show ?thesis unfolding linear_on_def
    proof (intro conjI allI impI)
      fix x y :: "complex Matrix.vec" assume x: "dim_vec x = K1 * K2" and y: "dim_vec y = K1 * K2"
      have rs': "r < dim_row (F (vec_to_mat K1 K2 x))" "s < dim_col (F (vec_to_mat K1 K2 x))"
        "r < dim_row (F (vec_to_mat K1 K2 y))" "s < dim_col (F (vec_to_mat K1 K2 y))" using rs uc by auto
      show "F (vec_to_mat K1 K2 (x + y)) $$ (r, s) = F (vec_to_mat K1 K2 x) $$ (r, s) + F (vec_to_mat K1 K2 y) $$ (r, s)"
        unfolding add[OF x y] using l uc rs' unfolding linear_mat_on_def by simp
    next
      fix a and x :: "complex Matrix.vec" assume x: "dim_vec x = K1 * K2"
      have rs': "r < dim_row (F (vec_to_mat K1 K2 x))" "s < dim_col (F (vec_to_mat K1 K2 x))" using rs uc by auto
      show "F (vec_to_mat K1 K2 (a \<cdot>\<^sub>v x)) $$ (r, s) = a * F (vec_to_mat K1 K2 x) $$ (r, s)"
        unfolding sm[OF x] using l uc rs' unfolding linear_mat_on_def by simp
    qed
  qed
  show "dim_row (\<Phi> c) = dim_row (\<Psi> c)" "dim_col (\<Phi> c) = dim_col (\<Psi> c)" using dims[OF c] by simp_all
  fix r s assume "r < dim_row (\<Psi> c)" "s < dim_col (\<Psi> c)"
  hence rs: "r < Q1" "s < Q2" using dims[OF c] by simp_all
  have r1: "\<And>x. x \<in> carrier_mat K1 K2 \<Longrightarrow> r < dim_row (\<Phi> x) \<and> s < dim_col (\<Phi> x)" using dims rs by auto
  have r2: "\<And>x. x \<in> carrier_mat K1 K2 \<Longrightarrow> r < dim_row (\<Psi> x) \<and> s < dim_col (\<Psi> x)" using dims rs by auto
  let ?x = "mat_to_vec c"
  have x: "dim_vec ?x = K1 * K2" by (rule dim_mat_to_vec[OF c])
  have "\<Phi> c $$ (r, s) = \<Phi> (vec_to_mat K1 K2 ?x) $$ (r, s)" unfolding vec_to_mat_mat_to_vec[OF c] ..
  also have "\<dots> = (\<Sum>k<K1 * K2. ?x $ k * \<Phi> (vec_to_mat K1 K2 (unit_vec (K1 * K2) k)) $$ (r, s))"
    by (rule linear_on_expand[OF lin[where F = \<Phi> and r = r and s = s, OF l1 r1] x])
  also have "\<dots> = (\<Sum>k<K1 * K2. ?x $ k * \<Psi> (vec_to_mat K1 K2 (unit_vec (K1 * K2) k)) $$ (r, s))"
  proof (rule sum.cong[OF refl])
    fix k assume "k \<in> {..<K1 * K2}"
    hence k: "k < K1 * K2" by simp
    have K2: "0 < K2" using k by (cases K2) auto
    have "k div K2 < K1" "k mod K2 < K2" using k K2 by (simp_all add: less_mult_imp_div_less)
    thus "?x $ k * \<Phi> (vec_to_mat K1 K2 (unit_vec (K1 * K2) k)) $$ (r, s) = ?x $ k * \<Psi> (vec_to_mat K1 K2 (unit_vec (K1 * K2) k)) $$ (r, s)"
      unfolding vec_to_mat_unit[OF k] using e by simp
  qed
  also have "\<dots> = \<Psi> (vec_to_mat K1 K2 ?x) $$ (r, s)"
    by (rule linear_on_expand[OF lin[where F = \<Psi> and r = r and s = s, OF l2 r2] x, symmetric])
  finally show "\<Phi> c $$ (r, s) = \<Psi> c $$ (r, s)" unfolding vec_to_mat_mat_to_vec[OF c] .
qed

theorem gamma_unique:
  assumes p0: "0 < p" and l: "linear_mat_on (m * m) (p * p) \<Phi>"
    and dims: "\<And>x. x \<in> carrier_mat (m * m) (p * p) \<Longrightarrow> \<Phi> x \<in> carrier_mat (m * p) (m * p)"
    and e: "\<And>Ra Tb. Ra \<in> carrier_mat m m \<Longrightarrow> Tb \<in> carrier_mat p p \<Longrightarrow> \<Phi> (op_elem m p Ra Tb) = Ra \<Otimes> Tb"
    and c: "c \<in> carrier_mat (m * m) (p * p)"
  shows "\<Phi> c = operator_tensor_iso_map m p c"
proof (rule linear_mat_unique[OF l _ _ _ c])
  show "linear_mat_on (m * m) (p * p) (operator_tensor_iso_map m p)"
    unfolding linear_mat_on_def using operator_tensor_iso_map_add[OF p0] operator_tensor_iso_map_smult[OF p0] by blast
  show "\<And>x. x \<in> carrier_mat (m * m) (p * p) \<Longrightarrow> dim_row (\<Phi> x) = m * p \<and> dim_col (\<Phi> x) = m * p
          \<and> dim_row (operator_tensor_iso_map m p x) = m * p \<and> dim_col (operator_tensor_iso_map m p x) = m * p"
    using dims by (auto simp: operator_tensor_iso_map_def)
  fix a b assume a: "a < m * m" and b: "b < p * p"
  show "\<Phi> (unit_mat (m * m) (p * p) a b) = operator_tensor_iso_map m p (unit_mat (m * m) (p * p) a b)"
    unfolding unit_mat_op_elem[OF a b] by (simp add: e gamma_elementary)
qed

subsection \<open>Partial traces\<close>

text \<open>\begin{notesdef}
Identify $L(\Hil_A\otimes\Hil_B)=L(\Hil_A)\otimes L(\Hil_B)$ and define
$\tr_B(\sum_lR_l\otimes T_l)=\sum_l\tr(T_l)R_l\in L(\Hil_A)$ and
$\tr_A(\sum_lR_l\otimes T_l)=\sum_l\tr(R_l)T_l\in L(\Hil_B)$; also written $X^A=\tr_B(X)$,
$X^B=\tr_A(X)$.  Well defined by the universal property, since $(R,T)\mapsto\tr(T)R$ is
bilinear.
\end{notesdef}
The formal definitions use the block formulas of Day 16: an $mp\times mp$ matrix is indexed by
pairs $(i,k)$, $i<m$, $k<p$, with flat index $ip+k$ ($\Hil_A$ is the major factor, matching
$(A\otimes B)_{(r,c)}=A_{(r\div p,\,c\div p)}B_{(r\bmod p,\,c\bmod p)}$), and
$(\tr_BX)_{ij}=\sum_{k<p}X_{ip+k,\,jp+k}$, $(\tr_AX)_{ij}=\sum_{k<m}X_{kp+i,\,kp+j}$.  The
defining property on elementary tensors is proved below.  The formal text writes $\tr_BX$ and
$\tr_AX$ for $X\in M_m\otimes M_p$ as \<open>partial_trace_B m p X\<close> and \<open>partial_trace_A m p X\<close>, and
\<open>partial_trace_on S AB X\<close> (displayed \<open>tr\<^bsub>S\<^esub>\<^bsup>AB\<^esup> X\<close>) traces out the factor $S$ of the
bipartite space $AB$.\<close>

record 'lab qspace =
  qdim :: nat
  qlabel :: 'lab

record 'lab bipartite_space =
  left_space :: "'lab qspace"
  right_space :: "'lab qspace"

definition partial_trace_B :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "partial_trace_B m p x \<equiv>
     Matrix.mat m m (\<lambda>(i, j). \<Sum>k<p. x $$ (i * p + k, j * p + k))"

definition partial_trace_A :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "partial_trace_A m p x \<equiv>
     Matrix.mat p p (\<lambda>(i, j). \<Sum>k<m. x $$ (k * p + i, k * p + j))"

definition partial_trace_on ::
  "'lab qspace \<Rightarrow> 'lab bipartite_space \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "partial_trace_on s ab x \<equiv>
     (if s = right_space ab then
        partial_trace_B (qdim (left_space ab)) (qdim (right_space ab)) x
      else if s = left_space ab then
        partial_trace_A (qdim (left_space ab)) (qdim (right_space ab)) x
      else 0\<^sub>m 0 0)"

notation partial_trace_on ("tr\<^bsub>_\<^esub>\<^bsup>_\<^esup> _" [1000, 1000, 1000] 1000)

lemma partial_trace_on_right:
  fixes S :: "'lab qspace" and AB :: "'lab bipartite_space"
  assumes "S = right_space AB"
  shows "tr\<^bsub>S\<^esub>\<^bsup>AB\<^esup> x =
         partial_trace_B (qdim (left_space AB)) (qdim (right_space AB)) x"
  using assms by (simp add: partial_trace_on_def)

lemma partial_trace_on_left:
  fixes S :: "'lab qspace" and AB :: "'lab bipartite_space"
  assumes "S = left_space AB"
      and "left_space AB \<noteq> right_space AB"
  shows "tr\<^bsub>S\<^esub>\<^bsup>AB\<^esup> x =
         partial_trace_A (qdim (left_space AB)) (qdim (right_space AB)) x"
  using assms by (simp add: partial_trace_on_def)

lemma dim_row_partial_trace_B [simp]: "dim_row (partial_trace_B m p x) = m"
  by (simp add: partial_trace_B_def)

lemma dim_col_partial_trace_B [simp]: "dim_col (partial_trace_B m p x) = m"
  by (simp add: partial_trace_B_def)

lemma partial_trace_B_carrier [simp]:
  "partial_trace_B m p x \<in> carrier_mat m m"
  by auto

lemma dim_row_partial_trace_A [simp]: "dim_row (partial_trace_A m p x) = p"
  by (simp add: partial_trace_A_def)

lemma dim_col_partial_trace_A [simp]: "dim_col (partial_trace_A m p x) = p"
  by (simp add: partial_trace_A_def)

text \<open>On product operators the partial traces keep one factor and trace out the other:
\[ \tr_B(R\otimes T)=\Tr(T)\,R,\qquad \tr_A(R\otimes T)=\Tr(R)\,T, \]
entrywise $\sum_kR_{ij}T_{kk}=R_{ij}\Tr T$.\<close>

lemma partial_trace_B_tensor:
  fixes R T :: "complex Matrix.mat"
  assumes Rsq: "R \<in> carrier_mat m m"
      and Tsq: "T \<in> carrier_mat p p"
      and m_pos: "0 < m" and p_pos: "0 < p"
  shows "partial_trace_B m p (R \<Otimes> T) = Tr T \<cdot>\<^sub>m R"
proof (rule eq_matI)
  show "dim_row (partial_trace_B m p (R \<Otimes> T)) = dim_row (Tr T \<cdot>\<^sub>m R)"
    using Rsq by simp
  show "dim_col (partial_trace_B m p (R \<Otimes> T)) = dim_col (Tr T \<cdot>\<^sub>m R)"
    using Rsq by simp
next
  fix i j
  assume ij: "i < dim_row (Tr T \<cdot>\<^sub>m R)" "j < dim_col (Tr T \<cdot>\<^sub>m R)"
  from ij Rsq have i_lt: "i < m" and j_lt: "j < m" by auto

  have drR: "dim_row R = m" using Rsq by auto
  have dcR: "dim_col R = m" using Rsq by auto
  have drT: "dim_row T = p" using Tsq by auto
  have dcT: "dim_col T = p" using Tsq by auto

  have ent_eq: "\<And>k. k < p \<Longrightarrow>
                (R \<Otimes> T) $$ (i * p + k, j * p + k) = R $$ (i, j) * T $$ (k, k)"
  proof -
    fix k assume k_lt: "k < p"
    have rb: "i * p + k < m * p"
    proof -
      have "i * p + k < (i + 1) * p" using k_lt by simp
      moreover have "(i + 1) * p \<le> m * p"
      proof -
        have "i + 1 \<le> m" using i_lt by simp
        thus "(i + 1) * p \<le> m * p" by (rule mult_le_mono1)
      qed
      ultimately show ?thesis by linarith
    qed
    have cb: "j * p + k < m * p"
    proof -
      have "j * p + k < (j + 1) * p" using k_lt by simp
      moreover have "(j + 1) * p \<le> m * p"
      proof -
        have "j + 1 \<le> m" using j_lt by simp
        thus "(j + 1) * p \<le> m * p" by (rule mult_le_mono1)
      qed
      ultimately show ?thesis by linarith
    qed
    have dv1: "(i * p + k) div p = i" using k_lt by simp
    have dv2: "(j * p + k) div p = j" using k_lt by simp
    have md1: "(i * p + k) mod p = k" using k_lt by simp
    have md2: "(j * p + k) mod p = k" using k_lt by simp
    have "(R \<Otimes> T) $$ (i * p + k, j * p + k)
          = R $$ ((i*p+k) div p, (j*p+k) div p) * T $$ ((i*p+k) mod p, (j*p+k) mod p)"
      using index_tensor_mat[OF drR dcR drT dcT rb cb m_pos p_pos] .
    also have "\<dots> = R $$ (i, j) * T $$ (k, k)"
      using dv1 dv2 md1 md2 by simp
    finally show "(R \<Otimes> T) $$ (i * p + k, j * p + k) = R $$ (i, j) * T $$ (k, k)" .
  qed

  have "partial_trace_B m p (R \<Otimes> T) $$ (i, j)
        = (\<Sum>k<p. (R \<Otimes> T) $$ (i * p + k, j * p + k))"
    using i_lt j_lt by (simp add: partial_trace_B_def)
  also have "\<dots> = (\<Sum>k<p. R $$ (i, j) * T $$ (k, k))"
    using ent_eq by (intro sum.cong refl) simp
  also have "\<dots> = R $$ (i, j) * (\<Sum>k<p. T $$ (k, k))"
    by (simp add: sum_distrib_left)
  also have "\<dots> = R $$ (i, j) * Tr T"
    using Tsq by (simp add: Tr_def)
  also have "\<dots> = Tr T * R $$ (i, j)"
    by (simp add: mult.commute)
  also have "\<dots> = (Tr T \<cdot>\<^sub>m R) $$ (i, j)"
    using i_lt j_lt Rsq by simp
  finally show "partial_trace_B m p (R \<Otimes> T) $$ (i, j) = (Tr T \<cdot>\<^sub>m R) $$ (i, j)" .
qed

lemma partial_trace_A_tensor:
  fixes R T :: "complex Matrix.mat"
  assumes Rsq: "R \<in> carrier_mat m m"
      and Tsq: "T \<in> carrier_mat p p"
      and m_pos: "0 < m" and p_pos: "0 < p"
  shows "partial_trace_A m p (R \<Otimes> T) = Tr R \<cdot>\<^sub>m T"
proof (rule eq_matI)
  show "dim_row (partial_trace_A m p (R \<Otimes> T)) = dim_row (Tr R \<cdot>\<^sub>m T)"
    using Tsq by simp
  show "dim_col (partial_trace_A m p (R \<Otimes> T)) = dim_col (Tr R \<cdot>\<^sub>m T)"
    using Tsq by simp
next
  fix i j
  assume ij: "i < dim_row (Tr R \<cdot>\<^sub>m T)" "j < dim_col (Tr R \<cdot>\<^sub>m T)"
  from ij Tsq have i_lt: "i < p" and j_lt: "j < p" by auto

  have drR: "dim_row R = m" using Rsq by auto
  have dcR: "dim_col R = m" using Rsq by auto
  have drT: "dim_row T = p" using Tsq by auto
  have dcT: "dim_col T = p" using Tsq by auto

  have ent_eq: "\<And>k. k < m \<Longrightarrow>
                (R \<Otimes> T) $$ (k * p + i, k * p + j) = R $$ (k, k) * T $$ (i, j)"
  proof -
    fix k assume k_lt: "k < m"
    have rb: "k * p + i < m * p"
    proof -
      have "k * p + i < (k + 1) * p" using i_lt by simp
      moreover have "(k + 1) * p \<le> m * p"
      proof -
        have "k + 1 \<le> m" using k_lt by simp
        thus "(k + 1) * p \<le> m * p" by (rule mult_le_mono1)
      qed
      ultimately show ?thesis by linarith
    qed
    have cb: "k * p + j < m * p"
    proof -
      have "k * p + j < (k + 1) * p" using j_lt by simp
      moreover have "(k + 1) * p \<le> m * p"
      proof -
        have "k + 1 \<le> m" using k_lt by simp
        thus "(k + 1) * p \<le> m * p" by (rule mult_le_mono1)
      qed
      ultimately show ?thesis by linarith
    qed
    have dv1: "(k * p + i) div p = k" using i_lt by simp
    have dv2: "(k * p + j) div p = k" using j_lt by simp
    have md1: "(k * p + i) mod p = i" using i_lt by simp
    have md2: "(k * p + j) mod p = j" using j_lt by simp
    have "(R \<Otimes> T) $$ (k * p + i, k * p + j)
          = R $$ ((k*p+i) div p, (k*p+j) div p) * T $$ ((k*p+i) mod p, (k*p+j) mod p)"
      using index_tensor_mat[OF drR dcR drT dcT rb cb m_pos p_pos] .
    also have "\<dots> = R $$ (k, k) * T $$ (i, j)"
      using dv1 dv2 md1 md2 by simp
    finally show "(R \<Otimes> T) $$ (k * p + i, k * p + j) = R $$ (k, k) * T $$ (i, j)" .
  qed

  have "partial_trace_A m p (R \<Otimes> T) $$ (i, j)
        = (\<Sum>k<m. (R \<Otimes> T) $$ (k * p + i, k * p + j))"
    using i_lt j_lt by (simp add: partial_trace_A_def)
  also have "\<dots> = (\<Sum>k<m. R $$ (k, k) * T $$ (i, j))"
    using ent_eq by (intro sum.cong refl) simp
  also have "\<dots> = (\<Sum>k<m. R $$ (k, k)) * T $$ (i, j)"
    by (simp add: sum_distrib_right)
  also have "\<dots> = Tr R * T $$ (i, j)"
    using Rsq by (simp add: Tr_def)
  also have "\<dots> = (Tr R \<cdot>\<^sub>m T) $$ (i, j)"
    using i_lt j_lt Tsq by simp
  finally show "partial_trace_A m p (R \<Otimes> T) $$ (i, j) = (Tr R \<cdot>\<^sub>m T) $$ (i, j)" .
qed

subsection \<open>Partial traces and measurements\<close>

text \<open>Writing $\rho=\sum_lR_l\otimes T_l$,
\[ p_\alpha(\rho)=\tr((M_\alpha^*M_\alpha\otimes I)\rho)=\sum_l\tr(M_\alpha^*M_\alpha R_l)\tr(T_l)
   =\tr\bigl(M_\alpha^*M_\alpha\,\tr_B(\rho)\bigr)=p_\alpha(\rho^A): \]
lab A only sees $\rho^A$, and symmetrically lab B only sees $\rho^B$.  Check: $\tr(\rho^A)=\tr\rho=1$,
and $\rho\ge0$ implies $\rho^A\ge0$.\<close>

text \<open>Key identity: measurements in lab A only see $\rho^A=\tr_B\rho$.\<close>

theorem partial_trace_measurement:
  fixes meas :: "complex Matrix.mat" and \<rho> :: "complex Matrix.mat"
  assumes M_sq: "meas \<in> carrier_mat m m"
      and dm: "density_matrix (m * p) \<rho>"
      and p_pos: "0 < p"
  shows "Tr (((meas\<^sup>\<dagger> * meas) \<Otimes> 1\<^sub>m p) * \<rho>) =
         Tr (meas\<^sup>\<dagger> * meas * partial_trace_B m p \<rho>)"
proof -
  define M where M_def: "M = (meas\<^sup>\<dagger>) * meas"

  have rho_carr: "\<rho> \<in> carrier_mat (m * p) (m * p)"
    using dm by (auto simp: density_matrix_def)
  have rho_row: "dim_row \<rho> = m * p" and rho_col: "dim_col \<rho> = m * p"
    using rho_carr by auto

  have Mdag_carr: "meas\<^sup>\<dagger> \<in> carrier_mat m m"
    using M_sq by auto
  have M_carr: "M \<in> carrier_mat m m"
    unfolding M_def using Mdag_carr M_sq by simp
  have M_row: "dim_row M = m" and M_col: "dim_col M = m"
    using M_carr by auto

  have I_row: "dim_row (1\<^sub>m p :: complex Matrix.mat) = p"
   and I_col: "dim_col (1\<^sub>m p :: complex Matrix.mat) = p"
    by simp_all

  have MI_carr: "(M \<Otimes> 1\<^sub>m p) \<in> carrier_mat (m * p) (m * p)"
    using M_carr by simp
  have MI_row: "dim_row (M \<Otimes> 1\<^sub>m p) = m * p"
   and MI_col: "dim_col (M \<Otimes> 1\<^sub>m p) = m * p"
    using MI_carr by auto

  have ptB_carr: "partial_trace_B m p \<rho> \<in> carrier_mat m m"
    by simp

  have main_eq:
    "Tr ((M \<Otimes> 1\<^sub>m p) * \<rho>) = Tr (M * partial_trace_B m p \<rho>)"
  proof (cases "m = 0")
    case True
    have lhs0: "Tr ((M \<Otimes> 1\<^sub>m p) * \<rho>) = 0"
      using True MI_carr rho_carr by (simp add: Tr_def)
    have rhs0: "Tr (M * partial_trace_B m p \<rho>) = 0"
      using True M_carr ptB_carr by (simp add: Tr_def)
    show ?thesis using lhs0 rhs0 by simp
  next
    case False
    then have m_pos: "0 < m" by simp

    have bij: "bij_betw (\<lambda>(i, a). i * p + a) ({..<m} \<times> {..<p}) {..<m * p}"
    proof (rule bij_betwI[where g = "\<lambda>r. (r div p, r mod p)"])
      show "(\<lambda>(i, a). i * p + a) \<in> {..<m} \<times> {..<p} \<rightarrow> {..<m * p}"
      proof
        fix z assume z_in: "z \<in> {..<m} \<times> {..<p}"
        then obtain i a where z: "z = (i, a)" and i_lt: "i < m" and a_lt: "a < p"
          by blast
        have "i * p + a < (i + 1) * p" using a_lt by simp
        moreover have "(i + 1) * p \<le> m * p"
          using i_lt by (intro mult_le_mono1) simp
        ultimately have "i * p + a < m * p" by linarith
        thus "(case z of (i, a) \<Rightarrow> i * p + a) \<in> {..<m * p}"
          using z by simp
      qed
    next
      show "(\<lambda>r. (r div p, r mod p)) \<in> {..<m * p} \<rightarrow> {..<m} \<times> {..<p}"
        using p_pos by (auto simp: less_mult_imp_div_less)
    next
      fix z assume z_in: "z \<in> {..<m} \<times> {..<p}"
      then obtain i a where z: "z = (i, a)" and a_lt: "a < p" by blast
      show "(\<lambda>r. (r div p, r mod p)) ((\<lambda>(i, a). i * p + a) z) = z"
        using z a_lt by simp
    next
      fix r assume "r \<in> {..<m * p}"
      show "(\<lambda>(i, a). i * p + a) ((\<lambda>r. (r div p, r mod p)) r) = r"
        by simp
    qed

    have ipa_lt: "\<And>i a. i < m \<Longrightarrow> a < p \<Longrightarrow> i * p + a < m * p"
    proof -
      fix i a :: nat assume i_lt: "i < m" and a_lt: "a < p"
      have "i * p + a < (i + 1) * p" using a_lt by simp
      also have "\<dots> \<le> m * p" using i_lt by (intro mult_le_mono1) simp
      finally show "i * p + a < m * p" .
    qed

    have tens_entry:
      "\<And>i a j b. i < m \<Longrightarrow> a < p \<Longrightarrow> j < m \<Longrightarrow> b < p \<Longrightarrow>
         (M \<Otimes> 1\<^sub>m p) $$ (i * p + a, j * p + b)
         = M $$ (i, j) * (1\<^sub>m p :: complex Matrix.mat) $$ (a, b)"
    proof -
      fix i a j b :: nat
      assume i_lt: "i < m" and a_lt: "a < p"
         and j_lt: "j < m" and b_lt: "b < p"
      have rb: "i * p + a < m * p" using ipa_lt[OF i_lt a_lt] .
      have cb: "j * p + b < m * p" using ipa_lt[OF j_lt b_lt] .
      have dv1: "(i * p + a) div p = i" using a_lt by simp
      have dv2: "(j * p + b) div p = j" using b_lt by simp
      have md1: "(i * p + a) mod p = a" using a_lt by simp
      have md2: "(j * p + b) mod p = b" using b_lt by simp
      have "(M \<Otimes> 1\<^sub>m p) $$ (i * p + a, j * p + b)
            = M $$ ((i*p+a) div p, (j*p+b) div p)
              * (1\<^sub>m p :: complex Matrix.mat) $$ ((i*p+a) mod p, (j*p+b) mod p)"
        using index_tensor_mat[OF M_row M_col I_row I_col rb cb m_pos p_pos] .
      also have "\<dots> = M $$ (i, j) * (1\<^sub>m p :: complex Matrix.mat) $$ (a, b)"
        using dv1 dv2 md1 md2 by simp
      finally show "(M \<Otimes> 1\<^sub>m p) $$ (i * p + a, j * p + b)
                    = M $$ (i, j) * (1\<^sub>m p :: complex Matrix.mat) $$ (a, b)" .
    qed

    have prod_carr: "(M \<Otimes> 1\<^sub>m p) * \<rho> \<in> carrier_mat (m * p) (m * p)"
      using MI_carr rho_carr by simp

    have "Tr ((M \<Otimes> 1\<^sub>m p) * \<rho>)
          = (\<Sum>r < m * p. ((M \<Otimes> 1\<^sub>m p) * \<rho>) $$ (r, r))"
      using prod_carr M_row rho_col by (simp add: Tr_def)

    also have "\<dots> = (\<Sum>r < m * p. \<Sum>s < m * p.
                       (M \<Otimes> 1\<^sub>m p) $$ (r, s) * \<rho> $$ (s, r))"
    proof (intro sum.cong refl)
      fix r assume "r \<in> {..<m * p}"
      then have r_lt: "r < m * p" by simp
      have "((M \<Otimes> 1\<^sub>m p) * \<rho>) $$ (r, r) = Matrix.row (M \<Otimes> 1\<^sub>m p) r \<bullet> Matrix.col \<rho> r"
        using r_lt MI_carr rho_carr by force
      also have "\<dots> = (\<Sum>s < m * p. (M \<Otimes> 1\<^sub>m p) $$ (r, s) * \<rho> $$ (s, r))"
        using r_lt MI_carr rho_carr MI_col MI_row
        by (simp add: scalar_prod_def lessThan_atLeast0, force)
      finally show "((M \<Otimes> 1\<^sub>m p) * \<rho>) $$ (r, r)
                    = (\<Sum>s < m * p. (M \<Otimes> 1\<^sub>m p) $$ (r, s) * \<rho> $$ (s, r))".
    qed
    also have "\<dots> = (\<Sum>r < m * p. \<Sum>(j, b) \<in> {..<m} \<times> {..<p}.
                       (M \<Otimes> 1\<^sub>m p) $$ (r, j * p + b) * \<rho> $$ (j * p + b, r))"
    proof (intro sum.cong refl)
      fix r assume "r \<in> {..<m * p}"
      show "(\<Sum>s < m * p. (M \<Otimes> 1\<^sub>m p) $$ (r, s) * \<rho> $$ (s, r))
            = (\<Sum>(j, b) \<in> {..<m} \<times> {..<p}.
                 (M \<Otimes> 1\<^sub>m p) $$ (r, j * p + b) * \<rho> $$ (j * p + b, r))"
        using sum.reindex_bij_betw[OF bij, symmetric,
                of "\<lambda>s. (M \<Otimes> 1\<^sub>m p) $$ (r, s) * \<rho> $$ (s, r)"]
        by (simp add: case_prod_beta)
    qed

    also have "\<dots> = (\<Sum>(i, a) \<in> {..<m} \<times> {..<p}. \<Sum>(j, b) \<in> {..<m} \<times> {..<p}.
                       (M \<Otimes> 1\<^sub>m p) $$ (i * p + a, j * p + b)
                       * \<rho> $$ (j * p + b, i * p + a))"
      using sum.reindex_bij_betw[OF bij, symmetric,
              of "\<lambda>r. \<Sum>(j, b) \<in> {..<m} \<times> {..<p}.
                        (M \<Otimes> 1\<^sub>m p) $$ (r, j * p + b) * \<rho> $$ (j * p + b, r)"]
      by (simp add: case_prod_beta)

    also have "\<dots> = (\<Sum>i < m. \<Sum>a < p. \<Sum>j < m. \<Sum>b < p.
                       (M \<Otimes> 1\<^sub>m p) $$ (i * p + a, j * p + b)
                       * \<rho> $$ (j * p + b, i * p + a))"
      by (simp add: sum.cartesian_product[symmetric])

    also have "\<dots> = (\<Sum>i < m. \<Sum>a < p. \<Sum>j < m. \<Sum>b < p.
                       M $$ (i, j) * (1\<^sub>m p :: complex Matrix.mat) $$ (a, b)
                       * \<rho> $$ (j * p + b, i * p + a))"
    proof (intro sum.cong refl)
      fix i a j b
      assume "i \<in> {..<m}" "a \<in> {..<p}" "j \<in> {..<m}" "b \<in> {..<p}"
      then have "i < m" "a < p" "j < m" "b < p" by simp_all
      thus "(M \<Otimes> 1\<^sub>m p) $$ (i * p + a, j * p + b)
            * \<rho> $$ (j * p + b, i * p + a)
            = M $$ (i, j) * (1\<^sub>m p :: complex Matrix.mat) $$ (a, b)
              * \<rho> $$ (j * p + b, i * p + a)"
        using tens_entry by simp
    qed

    also have "\<dots> = (\<Sum>i < m. \<Sum>a < p. \<Sum>j < m.
                       M $$ (i, j) * \<rho> $$ (j * p + a, i * p + a))"
    proof (intro sum.cong refl)
      fix i a j
      assume "i \<in> {..<m}" "a \<in> {..<p}" "j \<in> {..<m}"
      then have i_lt: "i < m" and a_lt: "a < p" and j_lt: "j < m"
        by simp_all
      have "(\<Sum>b < p. M $$ (i, j) * (1\<^sub>m p :: complex Matrix.mat) $$ (a, b)
                       * \<rho> $$ (j * p + b, i * p + a))
            = (\<Sum>b < p. (if a = b
                          then M $$ (i, j) * \<rho> $$ (j * p + b, i * p + a)
                          else 0))"
        using a_lt by (intro sum.cong refl) auto
      also have "\<dots> = (\<Sum>b < p. (if a = b
                                  then M $$ (i, j) * \<rho> $$ (j * p + a, i * p + a)
                                  else 0))"
        by (intro sum.cong refl) auto
      also have "\<dots> = M $$ (i, j) * \<rho> $$ (j * p + a, i * p + a)"
        using a_lt by simp
      finally show "(\<Sum>b < p. M $$ (i, j) * (1\<^sub>m p :: complex Matrix.mat) $$ (a, b)
                       * \<rho> $$ (j * p + b, i * p + a))
                    = M $$ (i, j) * \<rho> $$ (j * p + a, i * p + a)".
    qed

    also have "\<dots> = (\<Sum>i < m. \<Sum>j < m. \<Sum>a < p.
                       M $$ (i, j) * \<rho> $$ (j * p + a, i * p + a))"
    proof (rule sum.cong[OF refl])
      fix i assume "i \<in> {..<m}"
      show "(\<Sum>a < p. \<Sum>j < m. M $$ (i, j) * \<rho> $$ (j * p + a, i * p + a))
            = (\<Sum>j < m. \<Sum>a < p. M $$ (i, j) * \<rho> $$ (j * p + a, i * p + a))"
        by (rule sum.swap)
    qed
    also have "\<dots> = (\<Sum>i < m. \<Sum>j < m.
                       M $$ (i, j) * (\<Sum>a < p. \<rho> $$ (j * p + a, i * p + a)))"
      by (simp add: sum_distrib_left)

    also have "\<dots> = (\<Sum>i < m. \<Sum>j < m.
                       M $$ (i, j) * partial_trace_B m p \<rho> $$ (j, i))"
      by (intro sum.cong refl) (simp add: partial_trace_B_def)

    also have "\<dots> = (\<Sum>i < m. (M * partial_trace_B m p \<rho>) $$ (i, i))"
    proof (intro sum.cong refl)
      fix i assume "i \<in> {..<m}"
      then have i_lt: "i < m" by simp
      have "(M * partial_trace_B m p \<rho>) $$ (i, i)
            = (\<Sum>j < m. M $$ (i, j) * partial_trace_B m p \<rho> $$ (j, i))"
        using i_lt M_carr ptB_carr
        by (simp add: scalar_prod_def lessThan_atLeast0)
      thus "(\<Sum>j < m. M $$ (i, j) * partial_trace_B m p \<rho> $$ (j, i))
            = (M * partial_trace_B m p \<rho>) $$ (i, i)"
        by simp
    qed

    also have "\<dots> = Tr (M * partial_trace_B m p \<rho>)"
      using M_carr ptB_carr by (simp add: Tr_def)

    finally show "Tr ((M \<Otimes> 1\<^sub>m p) * \<rho>) = Tr (M * partial_trace_B m p \<rho>)".
  qed

  show ?thesis
    using main_eq by (simp add: M_def)
qed

text \<open>The check: the partial trace preserves the trace, Hermiticity and positivity (D15-6).\<close>

lemma partial_trace_B_trace:
  fixes X :: "complex Matrix.mat"
  assumes Xsq: "X \<in> carrier_mat (m * p) (m * p)"
      and p_pos: "0 < p"
  shows "Tr (partial_trace_B m p X) = Tr X"
proof -
  have Xrow: "dim_row X = m * p" and Xcol: "dim_col X = m * p"
    using Xsq by auto

  have bij: "bij_betw (\<lambda>(i, k). i * p + k) ({..<m} \<times> {..<p}) {..<m*p}"
  proof (rule bij_betwI[where g = "\<lambda>r. (r div p, r mod p)"])
    show "(\<lambda>(i, k). i * p + k) \<in> {..<m} \<times> {..<p} \<rightarrow> {..<m*p}"
    proof
      fix z assume z_in: "z \<in> {..<m} \<times> {..<p}"
      then obtain i k where z: "z = (i, k)" and i_lt: "i < m" and k_lt: "k < p"
        by blast
      have "i * p + k < (i + 1) * p"
        using k_lt by simp
      moreover have "(i + 1) * p \<le> m * p"
      proof -
        have "i + 1 \<le> m"
          using i_lt by simp
        thus "(i + 1) * p \<le> m * p"
          by (rule mult_le_mono1)
      qed
      ultimately have "i * p + k < m * p"
        by linarith
      thus "(case z of (i, k) \<Rightarrow> i * p + k) \<in> {..<m*p}"
        using z by simp
    qed
  next
    show "(\<lambda>r. (r div p, r mod p)) \<in> {..<m*p} \<rightarrow> {..<m} \<times> {..<p}"
      using p_pos by (auto simp: less_mult_imp_div_less)
  next
    fix z assume z_in: "z \<in> {..<m} \<times> {..<p}"
    then obtain i k where z: "z = (i, k)" and k_lt: "k < p"
      by blast
    show "(\<lambda>r. (r div p, r mod p)) ((\<lambda>(i, k). i * p + k) z) = z"
      using z k_lt by simp
  next
    fix r assume r_in: "r \<in> {..<m*p}"
    show "(\<lambda>(i, k). i * p + k) ((\<lambda>r. (r div p, r mod p)) r) = r"
      by simp
  qed

  have "Tr (partial_trace_B m p X) =
        (\<Sum>i<m. partial_trace_B m p X $$ (i, i))"
    by (simp add: Tr_def)
  also have "\<dots> = (\<Sum>i<m. \<Sum>k<p. X $$ (i * p + k, i * p + k))"
    by (intro sum.cong refl) (simp add: partial_trace_B_def)
  also have "\<dots> = (\<Sum>(i, k) \<in> {..<m} \<times> {..<p}. X $$ (i * p + k, i * p + k))"
    by (simp add: sum.cartesian_product)
  also have "\<dots> = (\<Sum>r<m*p. X $$ (r, r))"
    using sum.reindex_bij_betw[OF bij, symmetric, of "\<lambda>r. X $$ (r, r)"]
    by (simp add: case_prod_beta)
  also have "\<dots> = Tr X"
    using Xrow Xcol by (simp add: Tr_def)
  finally show ?thesis .
qed

lemma partial_trace_B_hermitian:
  fixes X :: "complex Matrix.mat"
  assumes Xsq: "X \<in> carrier_mat (m * p) (m * p)"
      and herm: "hermitian X"
  shows "hermitian (partial_trace_B m p X)"
proof -
  have Xrow: "dim_row X = m * p" and Xcol: "dim_col X = m * p"
    using Xsq by auto
  have entry:
    "\<And>i j. i < m \<Longrightarrow> j < m \<Longrightarrow>
      partial_trace_B m p X $$ (i, j) =
      cnj (partial_trace_B m p X $$ (j, i))"
  proof -
    fix i j assume i_lt: "i < m" and j_lt: "j < m"
    have "partial_trace_B m p X $$ (i, j) =
          (\<Sum>k<p. X $$ (i * p + k, j * p + k))"
      using i_lt j_lt by (simp add: partial_trace_B_def)
    also have "\<dots> = (\<Sum>k<p. cnj (X $$ (j * p + k, i * p + k)))"
    proof (intro sum.cong refl)
      fix k assume k_mem: "k \<in> {..<p}"
      then have k_lt: "k < p" by simp
      have row_lt: "i * p + k < m * p"
      proof -
        have "i * p + k < (i + 1) * p" using k_lt by simp
        moreover have "(i + 1) * p \<le> m * p"
        proof -
          have "i + 1 \<le> m" using i_lt by simp
          thus "(i + 1) * p \<le> m * p" by (rule mult_le_mono1)
        qed
        ultimately show ?thesis by linarith
      qed
      have col_lt: "j * p + k < m * p"
      proof -
        have "j * p + k < (j + 1) * p" using k_lt by simp
        moreover have "(j + 1) * p \<le> m * p"
        proof -
          have "j + 1 \<le> m" using j_lt by simp
          thus "(j + 1) * p \<le> m * p" by (rule mult_le_mono1)
        qed
        ultimately show ?thesis by linarith
      qed
      show "X $$ (i * p + k, j * p + k) =
            cnj (X $$ (j * p + k, i * p + k))"
      proof -
        have Xdag: "X\<^sup>\<dagger> = X"
          using herm by (simp add: hermitian_def)
        have "X $$ (i * p + k, j * p + k) =
              (X\<^sup>\<dagger> $$ (i * p + k, j * p + k))"
          using Xdag by simp
        also have "\<dots> = cnj (X $$ (j * p + k, i * p + k))"
          using Xrow Xcol row_lt col_lt by (simp add: dagger_def)
        finally show ?thesis .
      qed
    qed
    also have "\<dots> = cnj (\<Sum>k<p. X $$ (j * p + k, i * p + k))"
      by simp
    also have "\<dots> = cnj (partial_trace_B m p X $$ (j, i))"
      using i_lt j_lt by (simp add: partial_trace_B_def)
    finally show "partial_trace_B m p X $$ (i, j) =
                  cnj (partial_trace_B m p X $$ (j, i))" .
  qed
  show ?thesis
    unfolding hermitian_def
  proof (rule eq_matI)
    show "dim_row ((partial_trace_B m p X)\<^sup>\<dagger>) = dim_row (partial_trace_B m p X)"
      by simp
    show "dim_col ((partial_trace_B m p X)\<^sup>\<dagger>) = dim_col (partial_trace_B m p X)"
      by simp
  next
    fix i j
    assume ij: "i < dim_row (partial_trace_B m p X)" "j < dim_col (partial_trace_B m p X)"
    then have i_lt: "i < m" and j_lt: "j < m"
      by simp_all
    show "(partial_trace_B m p X)\<^sup>\<dagger> $$ (i, j) =
          partial_trace_B m p X $$ (i, j)"
      using i_lt j_lt entry[OF i_lt j_lt] entry[OF j_lt i_lt]
      by (simp add: dagger_def)
  qed
qed

lemma partial_trace_B_is_density:
  fixes X :: "complex Matrix.mat"
  assumes dm: "density_matrix (m * p) X"
      and p_pos: "0 < p"
  shows "density_matrix m (partial_trace_B m p X)"
proof -
  have Xsq: "X \<in> carrier_mat (m * p) (m * p)"
    using dm by (auto simp: density_matrix_def)
  have Xpsd: "psd X"
    using dm by (auto simp: density_matrix_def)
  have Xherm: "hermitian X"
    using Xpsd by (rule psd_hermitian)
  have carr: "partial_trace_B m p X \<in> carrier_mat m m"
    by simp
  have herm: "hermitian (partial_trace_B m p X)"
    using partial_trace_B_hermitian[OF Xsq Xherm] .
  have nonneg:
    "\<And>v. dim_vec v = m \<Longrightarrow> Re \<langle>v | partial_trace_B m p X *\<^sub>v v\<rangle> \<ge> 0"
  proof -
    fix v :: "complex Matrix.vec"
    assume vdim: "dim_vec v = m"

    define wk where wk_def:
      "wk k = Matrix.vec (m * p) (\<lambda>t. if t mod p = k then v $ (t div p) else 0)"

    have wk_dim: "\<And>k. dim_vec (wk k) = m * p"
      using \<open>wk \<equiv> \<lambda>k. Matrix.vec (m * p) (\<lambda>t. if t mod p = k then v $ (t div p) else 0)\<close> 
        dim_vec by blast

    have wk_nonneg:
      "\<And>k. k < p \<Longrightarrow> Re \<langle>wk k | X *\<^sub>v wk k\<rangle> \<ge> 0"
      using Xpsd
      unfolding psd_def
      using Xsq wk_dim by fastforce

    have pt_expand:
      "\<langle>v | partial_trace_B m p X *\<^sub>v v\<rangle>
       = (\<Sum>k<p. \<langle>wk k | X *\<^sub>v wk k\<rangle>)"
    proof -
      have lhs_entry:
        "\<langle>v | partial_trace_B m p X *\<^sub>v v\<rangle>
         = (\<Sum>i<m. \<Sum>j<m. cnj (v $ i) *
              (partial_trace_B m p X $$ (i,j)) * (v $ j))"
        using vdim
        unfolding inner_prod_def scalar_prod_def
        using atLeast0LessThan inner_T_double_sum inner_prod_def by auto

      also have "... =
         (\<Sum>i<m. \<Sum>j<m. cnj (v $ i) *
            (\<Sum>k<p. X $$ (i * p + k, j * p + k)) * (v $ j))"
        using Xsq
        unfolding partial_trace_B_def
        by simp

      also have "... =
         (\<Sum>i<m. \<Sum>j<m. \<Sum>k<p.
             cnj (v $ i) * X $$ (i * p + k, j * p + k) * (v $ j))"
        by (simp add: sum_distrib_left sum_distrib_right mult.assoc)

      also have "... =
         (\<Sum>i<m. \<Sum>k<p. \<Sum>j<m.
             cnj (v $ i) * X $$ (i * p + k, j * p + k) * (v $ j))"
        by (intro sum.cong[OF refl] sum.swap)

      also have "... =
         (\<Sum>k<p. \<Sum>i<m. \<Sum>j<m.
             cnj (v $ i) * X $$ (i * p + k, j * p + k) * (v $ j))"
        by (rule sum.swap)

      also have "... = (\<Sum>k<p. \<langle>wk k | X *\<^sub>v wk k\<rangle>)"
      proof (rule sum.cong[OF refl])
        fix k
        assume "k \<in> {..<p}"
        then have k_lt: "k < p"
          by simp

        have ipk_lt: "\<And>i. i < m \<Longrightarrow> i * p + k < m * p"
        proof -
          fix i :: nat
          assume i_lt: "i < m"
          have "i * p + k < i * p + p" using k_lt by simp
          also have "\<dots> = (i + 1) * p" by simp
          also have "\<dots> \<le> m * p"
            using i_lt by (intro mult_le_mono1) simp
          finally show "i * p + k < m * p" .
        qed

        have wk_eval:
          "\<And>a. a < m * p \<Longrightarrow>
                 (wk k) $ a = (if a mod p = k then v $ (a div p) else 0)"
          using \<open>wk \<equiv> \<lambda>k. Matrix.vec (m * p) (\<lambda>t. if t mod p = k then v $ (t div p) else 0)\<close>
          by simp

        have wk_at: "\<And>i. i < m \<Longrightarrow> (wk k) $ (i * p + k) = v $ i"
        proof -
          fix i :: nat assume i_lt: "i < m"
          have bnd: "i * p + k < m * p" using ipk_lt[OF i_lt] .
          have md: "(i * p + k) mod p = k" using k_lt by simp
          have dv: "(i * p + k) div p = i" using k_lt by simp
          show "(wk k) $ (i * p + k) = v $ i"
            using wk_eval[OF bnd] md dv by simp
        qed

        have wk_zero:
          "\<And>a. a < m * p \<Longrightarrow> a mod p \<noteq> k \<Longrightarrow> (wk k) $ a = 0"
          using wk_eval by simp

        have inj_ipk: "inj_on (\<lambda>i. i * p + k) {..<m}"
          using p_pos by (auto simp: inj_on_def)

        have B_eq:
          "(\<lambda>i. i * p + k) ` {..<m} = {a. a < m * p \<and> a mod p = k}"
        proof (intro equalityI subsetI)
          fix x assume "x \<in> (\<lambda>i. i * p + k) ` {..<m}"
          then obtain i where x_eq: "x = i * p + k" and i_lt: "i < m"
            by auto
          have "x < m * p" using ipk_lt[OF i_lt] x_eq by simp
          moreover have "x mod p = k" using x_eq k_lt by simp
          ultimately show "x \<in> {a. a < m * p \<and> a mod p = k}" by simp
        next
          fix x assume "x \<in> {a. a < m * p \<and> a mod p = k}"
          then have x_lt: "x < m * p" and x_mod: "x mod p = k" by auto
          have div_lt: "x div p < m"
            using x_lt p_pos less_mult_imp_div_less by blast
          have x_eq: "x = (x div p) * p + k"
            using x_mod by (metis div_mult_mod_eq)
          from div_lt x_eq show "x \<in> (\<lambda>i. i * p + k) ` {..<m}"
            by (auto intro!:)
        qed

        let ?B = "{a. a < m * p \<and> a mod p = k}"

        have B_subset: "?B \<subseteq> {..<m * p}" by auto

        have idx:
          "\<langle>wk k | X *\<^sub>v wk k\<rangle>
           = (\<Sum>a<m*p. \<Sum>b<m*p. cnj ((wk k) $ a) * X $$ (a,b) * ((wk k) $ b))"
          unfolding inner_prod_def scalar_prod_def
          using wk_dim[of k] Xsq inner_T_double_sum inner_prod_def lessThan_atLeast0
          by auto

        also have "\<dots> =
           (\<Sum>a \<in> ?B. \<Sum>b<m*p. cnj ((wk k) $ a) * X $$ (a,b) * ((wk k) $ b))"
        proof (rule sum.mono_neutral_right)
          show "finite {..<m * p}" by simp
          show "?B \<subseteq> {..<m * p}" by auto
          show "\<forall>a \<in> {..<m * p} - ?B.
                  (\<Sum>b<m*p. cnj ((wk k) $ a) * X $$ (a,b) * ((wk k) $ b)) = 0"
          proof
            fix a assume "a \<in> {..<m * p} - ?B"
            then have a_lt: "a < m * p" and a_md: "a mod p \<noteq> k" by auto
            hence "(wk k) $ a = 0" using wk_zero by simp
            thus "(\<Sum>b<m*p. cnj ((wk k) $ a) * X $$ (a,b) * ((wk k) $ b)) = 0"
              by simp
          qed
        qed

        also have "\<dots> =
           (\<Sum>a \<in> ?B. \<Sum>b \<in> ?B. cnj ((wk k) $ a) * X $$ (a,b) * ((wk k) $ b))"
        proof (rule sum.cong[OF refl])
          fix a assume "a \<in> ?B"
          show "(\<Sum>b<m*p. cnj ((wk k) $ a) * X $$ (a,b) * ((wk k) $ b))
               = (\<Sum>b \<in> ?B. cnj ((wk k) $ a) * X $$ (a,b) * ((wk k) $ b))"
          proof (rule sum.mono_neutral_right)
            show "finite {..<m * p}" by simp
            show "?B \<subseteq> {..<m * p}" by auto
            show "\<forall>b \<in> {..<m * p} - ?B.
                    cnj ((wk k) $ a) * X $$ (a,b) * ((wk k) $ b) = 0"
            proof
              fix b assume "b \<in> {..<m * p} - ?B"
              then have b_lt: "b < m * p" and b_md: "b mod p \<noteq> k" by auto
              hence "(wk k) $ b = 0" using wk_zero by simp
              thus "cnj ((wk k) $ a) * X $$ (a,b) * ((wk k) $ b) = 0"
                by simp
            qed
          qed
        qed

        also have "\<dots> =
           (\<Sum>i<m. \<Sum>j<m.
              cnj ((wk k) $ (i * p + k)) * X $$ (i * p + k, j * p + k)
              * ((wk k) $ (j * p + k)))"
          using B_eq[symmetric] inj_ipk
          by (simp add: sum.reindex)

        also have "\<dots> =
           (\<Sum>i<m. \<Sum>j<m. cnj (v $ i) * X $$ (i * p + k, j * p + k) * (v $ j))"
          using wk_at by (intro sum.cong refl) simp

        finally have wk_eq:
          "\<langle>wk k | X *\<^sub>v wk k\<rangle>
           = (\<Sum>i<m. \<Sum>j<m. cnj (v $ i) * X $$ (i * p + k, j * p + k) * (v $ j))" .

        show
          "(\<Sum>i<m. \<Sum>j<m. cnj (v $ i) * X $$ (i * p + k, j * p + k) * (v $ j))
           = \<langle>wk k | X *\<^sub>v wk k\<rangle>"
          using wk_eq by simp
      qed

      finally show ?thesis .
    qed

    have "Re \<langle>v | partial_trace_B m p X *\<^sub>v v\<rangle>
          = Re (\<Sum>k<p. \<langle>wk k | X *\<^sub>v wk k\<rangle>)"
      using pt_expand by simp
    also have "... = (\<Sum>k<p. Re \<langle>wk k | X *\<^sub>v wk k\<rangle>)"
      by simp
    also have "... \<ge> 0"
      using wk_nonneg
      by (meson lessThan_iff sum_nonneg) 
    finally show "Re \<langle>v | partial_trace_B m p X *\<^sub>v v\<rangle> \<ge> 0".
  qed

  have psd: "psd (partial_trace_B m p X)"
    unfolding psd_def using herm nonneg by simp
  have tr: "Tr (partial_trace_B m p X) = 1"
    using partial_trace_B_trace[OF Xsq p_pos] dm
    by (simp add: density_matrix_def)
  show ?thesis
    unfolding density_matrix_def using carr psd tr by simp
qed

subsection \<open>The partial trace over $A$ (D15-6)\<close>

text \<open>Reordering the basis: for a bijection $\sigma$ of $\{0,\dots,N-1\}$ the matrix
$(x_{\sigma(r)\sigma(s)})$ has the trace of $X$ and is Hermitian, resp.\ positive, with $X$.\<close>

definition perm_conj :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "perm_conj N \<sigma> X = Matrix.mat N N (\<lambda>(r, s). X $$ (\<sigma> r, \<sigma> s))"

lemma perm_conj_carrier [simp]: "perm_conj N \<sigma> X \<in> carrier_mat N N"
  by (simp add: perm_conj_def)

lemma perm_conj_dims [simp]: "dim_row (perm_conj N \<sigma> X) = N" "dim_col (perm_conj N \<sigma> X) = N"
  by (simp_all add: perm_conj_def)

text \<open>Conjugation by a permutation, $X\mapsto(X_{\sigma(r)\sigma(s)})_{r,s}$, preserves the trace, Hermitian
matrices and positivity.\<close>

lemma perm_conj_trace:
  assumes \<sigma>: "bij_betw \<sigma> {..<N} {..<N}" and X: "X \<in> carrier_mat N N"
  shows "Tr (perm_conj N \<sigma> X) = Tr X"
proof -
  have "Tr (perm_conj N \<sigma> X) = (\<Sum>r<N. X $$ (\<sigma> r, \<sigma> r))"
    by (simp add: Tr_def perm_conj_def)
  also have "\<dots> = (\<Sum>r<N. X $$ (r, r))"
    using sum.reindex_bij_betw[OF \<sigma>, of "\<lambda>r. X $$ (r, r)"] by simp
  also have "\<dots> = Tr X" using X by (simp add: Tr_def)
  finally show ?thesis .
qed

lemma perm_conj_hermitian:
  assumes \<sigma>: "\<And>r. r < N \<Longrightarrow> \<sigma> r < N" and X: "X \<in> carrier_mat N N" and h: "hermitian X"
  shows "hermitian (perm_conj N \<sigma> X)"
  unfolding hermitian_def
proof (rule eq_matI)
  have Xd: "X\<^sup>\<dagger> = X" using h by (simp add: hermitian_def)
  fix r s assume "r < dim_row (perm_conj N \<sigma> X)" "s < dim_col (perm_conj N \<sigma> X)"
  hence r: "r < N" and s: "s < N" by simp_all
  have "X $$ (\<sigma> r, \<sigma> s) = X\<^sup>\<dagger> $$ (\<sigma> r, \<sigma> s)" using Xd by simp
  also have "\<dots> = cnj (X $$ (\<sigma> s, \<sigma> r))" using X \<sigma>[OF r] \<sigma>[OF s] by (simp add: dagger_def)
  finally show "(perm_conj N \<sigma> X)\<^sup>\<dagger> $$ (r, s) = perm_conj N \<sigma> X $$ (r, s)"
    using r s by (simp add: dagger_def perm_conj_def)
qed (simp_all add: dagger_def)

lemma perm_conj_psd:
  assumes \<sigma>: "bij_betw \<sigma> {..<N} {..<N}" and X: "X \<in> carrier_mat N N" and ps: "psd X"
  shows "psd (perm_conj N \<sigma> X)"
proof -
  have \<sigma>N: "\<And>r. r < N \<Longrightarrow> \<sigma> r < N" using bij_betwE[OF \<sigma>] by auto
  define \<tau> where "\<tau> = inv_into {..<N} \<sigma>"
  have \<tau>\<sigma>: "\<And>r. r < N \<Longrightarrow> \<tau> (\<sigma> r) = r" unfolding \<tau>_def using bij_betw_inv_into_left[OF \<sigma>] by simp
  have h: "hermitian (perm_conj N \<sigma> X)" by (rule perm_conj_hermitian[OF \<sigma>N X psd_hermitian[OF ps]])
  have q: "0 \<le> Re (Quantum.inner_prod v (perm_conj N \<sigma> X *\<^sub>v v))" if v: "dim_vec v = N" for v
  proof -
    define w where "w = Matrix.vec N (\<lambda>t. v $ \<tau> t)"
    have wd: "dim_vec w = N" by (simp add: w_def)
    have w\<sigma>: "\<And>r. r < N \<Longrightarrow> w $ \<sigma> r = v $ r" using \<sigma>N \<tau>\<sigma> by (simp add: w_def)
    have "Quantum.inner_prod v (perm_conj N \<sigma> X *\<^sub>v v)
          = (\<Sum>r = 0..<N. \<Sum>s = 0..<N. cnj (v $ r) * perm_conj N \<sigma> X $$ (r, s) * v $ s)"
      by (rule inner_T_double_sum[OF perm_conj_carrier v v])
    also have "\<dots> = (\<Sum>r<N. \<Sum>s<N. cnj (w $ \<sigma> r) * X $$ (\<sigma> r, \<sigma> s) * w $ \<sigma> s)"
      by (simp add: perm_conj_def w\<sigma> atLeast0LessThan)
    also have "\<dots> = (\<Sum>a<N. \<Sum>b<N. cnj (w $ a) * X $$ (a, b) * w $ b)"
    proof -
      have inner: "\<And>a. (\<Sum>s<N. cnj (w $ a) * X $$ (a, \<sigma> s) * w $ \<sigma> s) = (\<Sum>b<N. cnj (w $ a) * X $$ (a, b) * w $ b)"
        using sum.reindex_bij_betw[OF \<sigma>, of "\<lambda>b. cnj (w $ _) * X $$ (_, b) * w $ b"] by simp
      have "(\<Sum>r<N. \<Sum>s<N. cnj (w $ \<sigma> r) * X $$ (\<sigma> r, \<sigma> s) * w $ \<sigma> s)
            = (\<Sum>r<N. \<Sum>b<N. cnj (w $ \<sigma> r) * X $$ (\<sigma> r, b) * w $ b)"
        by (rule sum.cong) (simp_all add: inner)
      also have "\<dots> = (\<Sum>a<N. \<Sum>b<N. cnj (w $ a) * X $$ (a, b) * w $ b)"
        using sum.reindex_bij_betw[OF \<sigma>, of "\<lambda>a. \<Sum>b<N. cnj (w $ a) * X $$ (a, b) * w $ b"] by simp
      finally show ?thesis .
    qed
    also have "\<dots> = Quantum.inner_prod w (X *\<^sub>v w)"
      using inner_T_double_sum[OF X wd wd] by (simp add: atLeast0LessThan)
    finally have e: "Quantum.inner_prod v (perm_conj N \<sigma> X *\<^sub>v v) = Quantum.inner_prod w (X *\<^sub>v w)" .
    have "\<forall>x. dim_vec x = dim_row X \<longrightarrow> 0 \<le> Re (Quantum.inner_prod x (X *\<^sub>v x))" using ps unfolding psd_def by blast
    thus ?thesis unfolding e using wd carrier_matD(1)[OF X] by simp
  qed
  show ?thesis unfolding psd_def using h q by simp
qed

text \<open>Exchanging the factors: with $\sigma(i m+k)=k p+i$ ($i<p$, $k<m$), tracing out $A$ is tracing out
$B$ after the exchange.\<close>

definition swap_index :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "swap_index m p r = (r mod m) * p + r div m"

lemma swap_index_less:
  assumes "r < m * p" shows "swap_index m p r < m * p"
proof -
  have m: "0 < m" using assms by (cases m) auto
  have "r div m < p" using assms by (simp add: less_mult_imp_div_less mult.commute)
  moreover have "r mod m < m" using m by simp
  ultimately have "(r mod m) * p + r div m < (r mod m) * p + p" by simp
  also have "\<dots> = Suc (r mod m) * p" by simp
  also have "\<dots> \<le> m * p" using \<open>r mod m < m\<close> by (intro mult_le_mono1) simp
  finally show ?thesis unfolding swap_index_def .
qed

lemma swap_index_bij: "bij_betw (swap_index m p) {..<m * p} {..<m * p}"
proof (rule bij_betwI[where g = "swap_index p m"])
  show "swap_index m p \<in> {..<m * p} \<rightarrow> {..<m * p}" using swap_index_less by auto
  show "swap_index p m \<in> {..<m * p} \<rightarrow> {..<m * p}" using swap_index_less[of _ p m] by (auto simp: mult.commute)
next
  fix r assume r: "r \<in> {..<m * p}"
  hence r': "r < m * p" by simp
  have m: "0 < m" and p: "0 < p" using r' by (cases m; cases p; auto)+
  have d: "r div m < p" using r' by (simp add: less_mult_imp_div_less mult.commute)
  show "swap_index p m (swap_index m p r) = r"
    unfolding swap_index_def using d m p div_mult_mod_eq[of r m] by (simp add: mult.commute)
next
  fix r assume r: "r \<in> {..<m * p}"
  hence r': "r < m * p" by simp
  have m: "0 < m" and p: "0 < p" using r' by (cases m; cases p; auto)+
  have d: "r div p < m" using r' by (simp add: less_mult_imp_div_less)
  show "swap_index m p (swap_index p m r) = r"
    unfolding swap_index_def using d m p div_mult_mod_eq[of r p] by (simp add: mult.commute)
qed

text \<open>The index permutation $r\mapsto(r\bmod m)\,p+r\div m$ exchanges the two tensor factors and turns
$\tr_A$ into $\tr_B$; the properties of $\tr_A$ follow from those of $\tr_B$.\<close>

lemma partial_trace_A_as_B:
  assumes X: "X \<in> carrier_mat (m * p) (m * p)"
  shows "partial_trace_A m p X = partial_trace_B p m (perm_conj (m * p) (swap_index m p) X)"
proof (rule eq_matI)
  fix i j assume "i < dim_row (partial_trace_B p m (perm_conj (m * p) (swap_index m p) X))"
    "j < dim_col (partial_trace_B p m (perm_conj (m * p) (swap_index m p) X))"
  hence i: "i < p" and j: "j < p" by (simp_all add: partial_trace_B_def)
  have lt: "\<And>i k. i < p \<Longrightarrow> k < m \<Longrightarrow> i * m + k < m * p"
  proof -
    fix i k assume "i < p" "k < m"
    have "i * m + k < Suc i * m" using \<open>k < m\<close> by simp
    also have "\<dots> \<le> p * m" using \<open>i < p\<close> by (intro mult_le_mono1) simp
    finally show "i * m + k < m * p" by (simp add: mult.commute)
  qed
  have "partial_trace_B p m (perm_conj (m * p) (swap_index m p) X) $$ (i, j)
        = (\<Sum>k<m. X $$ (swap_index m p (i * m + k), swap_index m p (j * m + k)))"
    using i j lt by (simp add: partial_trace_B_def perm_conj_def)
  also have "\<dots> = (\<Sum>k<m. X $$ (k * p + i, k * p + j))"
    by (rule sum.cong) (simp_all add: swap_index_def)
  also have "\<dots> = partial_trace_A m p X $$ (i, j)" using i j by (simp add: partial_trace_A_def)
  finally show "partial_trace_A m p X $$ (i, j) = partial_trace_B p m (perm_conj (m * p) (swap_index m p) X) $$ (i, j)" ..
qed (simp_all add: partial_trace_A_def partial_trace_B_def)

theorem partial_trace_A_trace:
  assumes X: "X \<in> carrier_mat (m * p) (m * p)" and m: "0 < m"
  shows "Tr (partial_trace_A m p X) = Tr X"
proof -
  have Y: "perm_conj (m * p) (swap_index m p) X \<in> carrier_mat (p * m) (p * m)" by (simp add: mult.commute)
  have "Tr (partial_trace_A m p X) = Tr (perm_conj (m * p) (swap_index m p) X)"
    unfolding partial_trace_A_as_B[OF X] by (rule partial_trace_B_trace[OF Y m])
  also have "\<dots> = Tr X" by (rule perm_conj_trace[OF swap_index_bij X])
  finally show ?thesis .
qed

theorem partial_trace_A_hermitian:
  assumes X: "X \<in> carrier_mat (m * p) (m * p)" and h: "hermitian X"
  shows "hermitian (partial_trace_A m p X)"
proof -
  have Y: "perm_conj (m * p) (swap_index m p) X \<in> carrier_mat (p * m) (p * m)" by (simp add: mult.commute)
  have "hermitian (perm_conj (m * p) (swap_index m p) X)"
    by (rule perm_conj_hermitian[OF swap_index_less X h])
  thus ?thesis unfolding partial_trace_A_as_B[OF X] by (rule partial_trace_B_hermitian[OF Y])
qed

theorem partial_trace_A_is_density:
  assumes dm: "density_matrix (m * p) X" and m: "0 < m"
  shows "density_matrix p (partial_trace_A m p X)"
proof -
  have X: "X \<in> carrier_mat (m * p) (m * p)" and ps: "psd X" and tr: "Tr X = 1"
    using dm by (auto simp: density_matrix_def)
  let ?Y = "perm_conj (m * p) (swap_index m p) X"
  have "density_matrix (p * m) ?Y"
    unfolding density_matrix_def
    using perm_conj_psd[OF swap_index_bij X ps] perm_conj_trace[OF swap_index_bij X] tr
    by (simp add: mult.commute)
  thus ?thesis unfolding partial_trace_A_as_B[OF X] by (rule partial_trace_B_is_density[OF _ m])
qed

end

(*  Title:   Day15_Partial_Traces.thy
    Author:  Dustin Bryant, after Vern Paulsen's lecture of 30 September 2011 (Day 15)
*)

theory Day15_Partial_Traces
  imports Day14_Pure_States
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

lemma operator_tensor_iso_map_carrier [simp]:
  "operator_tensor_iso_map m p c \<in> carrier_mat (m*p) (m*p)"
  by (simp add: operator_tensor_iso_map_def)

lemma operator_tensor_iso_map_entry:
  assumes "r < m*p" and "s < m*p"
  shows "operator_tensor_iso_map m p c $$ (r,s) =
         c $$ ((r div p) * m + (s div p), (r mod p) * p + (s mod p))"
  using assms by (simp add: operator_tensor_iso_map_def)

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

lemma operator_tensor_iso_inv_entry:
  assumes "a < m*m" and "b < p*p"
  shows "operator_tensor_iso_inv m p x $$ (a,b) =
         x $$ ((a div m) * p + (b div p), (a mod m) * p + (b mod p))"
  using assms by (simp add: operator_tensor_iso_inv_def)

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
defining property on elementary tensors is proved below.\<close>

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

lemma partial_trace_A_carrier [simp]:
  "partial_trace_A m p x \<in> carrier_mat p p"
  by auto


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

end

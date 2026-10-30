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
  have Vc: "?V \<in> carrier_mat n n" using mat_of_cols_carrier(1)[of n vs] full by simp
  have vs: "\<And>i. i < n \<Longrightarrow> vs ! i \<in> carrier_vec n"
    using orthonormal_listD_dim[OF orth] full by (intro carrier_vecI) simp
  have "Tr A = Tr (?V\<^sup>\<dagger> * A * ?V)"
    using Tr_unitary_conjugation[OF orthonormal_mat_unitary[OF orth full]] sq Vc by simp
  also have "\<dots> = (\<Sum>i<n. (?V\<^sup>\<dagger> * (A * ?V)) $$ (i, i))"
    unfolding assoc_mult_mat[OF dagger_carrier[OF Vc] sq Vc]
    by (rule Tr_carrier[OF mult_carrier_mat[OF dagger_carrier[OF Vc] mult_carrier_mat[OF sq Vc]]])
  also have "\<dots> = (\<Sum>i<n. \<langle>vs ! i | A *\<^sub>v vs ! i\<rangle>)"
  proof (intro sum.cong refl)
    fix i assume "i \<in> {..<n}"
    hence i: "i < n" by simp
    have i1: "i < dim_row (?V\<^sup>\<dagger>)" and i2: "i < dim_col (A * ?V)" and il: "i < length vs"
      using Vc sq i full by simp_all
    have "(?V\<^sup>\<dagger> * (A * ?V)) $$ (i, i) = (?V\<^sup>\<dagger> *\<^sub>v (A *\<^sub>v vs ! i)) $ i"
      by (simp only: index_mult_mat(1)[OF i1 i2] col_mult2[OF sq Vc i] col_mat_of_cols[OF il vs[OF i]]
                     index_mult_mat_vec[OF i1])
    also have "\<dots> = \<langle>vs ! i | A *\<^sub>v vs ! i\<rangle>"
      by (intro mat_of_cols_dagger_mult_vec_index) (use sq full i orth in \<open>auto simp: orthonormal_list_def\<close>)
    finally show "(?V\<^sup>\<dagger> * (A * ?V)) $$ (i, i) = \<langle>vs ! i | A *\<^sub>v vs ! i\<rangle>" .
  qed
  finally show ?thesis .
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
  have ent: "\<And>i j. i < m * p \<Longrightarrow> j < m * p \<Longrightarrow>
             (R \<Otimes> T) $$ (i, j) = R $$ (i div p, j div p) * T $$ (i mod p, j mod p)"
    using index_tensor_mat[OF carrier_matD[OF Rsq] carrier_matD[OF Tsq] _ _ m_pos p_pos] .
  have RT: "R \<Otimes> T \<in> carrier_mat (m * p) (m * p)" using Rsq Tsq by auto
  have "Tr (R \<Otimes> T) = (\<Sum>r<m * p. R $$ (r div p, r div p) * T $$ (r mod p, r mod p))"
    unfolding Tr_carrier[OF RT] by (intro sum.cong refl) (simp add: ent)
  also have "\<dots> = (\<Sum>i<m. \<Sum>k<p. R $$ (i, i) * T $$ (k, k))"
    by (rule sum_div_mod[where n = m and m = p and g = "\<lambda>i k. R $$ (i, i) * T $$ (k, k)"])
  also have "\<dots> = Tr R * Tr T" unfolding Tr_carrier[OF Rsq] Tr_carrier[OF Tsq] by (simp add: sum_product)
  finally show ?thesis .
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
  by (rule mult_index_lt[OF less_mult_imp_div_less[OF assms(2)] less_mult_imp_div_less[OF assms(3)]])

lemma operator_tensor_iso_map_col_bound:
  fixes p r s :: nat
  assumes p_pos: "0 < p"
  shows "(r mod p) * p + (s mod p) < p*p"
  by (rule mult_index_lt[OF mod_less_divisor[OF p_pos] mod_less_divisor[OF p_pos]])

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
  by (rule mult_index_lt[OF less_mult_imp_div_less[OF assms(3)] less_mult_imp_div_less[OF assms(4)]])

lemma operator_tensor_iso_inv_col_bound:
  fixes m p a b :: nat
  assumes m_pos: "0 < m" and p_pos: "0 < p"
  shows "(a mod m) * p + (b mod p) < m*p"
  by (rule mult_index_lt[OF mod_less_divisor[OF m_pos] mod_less_divisor[OF p_pos]])

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
  using operator_tensor_iso_map_row_bound[OF p_pos] operator_tensor_iso_map_col_bound[OF p_pos]
  by (intro eq_matI) (auto simp: operator_tensor_iso_map_def)

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
  using operator_tensor_iso_inv_row_bound[OF m_pos p_pos] operator_tensor_iso_inv_col_bound[OF m_pos p_pos]
  by (intro eq_matI) (auto simp: operator_tensor_iso_inv_def)

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
  have GF: "?G (?F x) = x" if "x \<in> ls_carrier ?V" for x
  proof -
    have xc: "x \<in> carrier_mat (m*m) (p*p)"
      using that by (simp add: operator_tensor_coordinate_space_def mat_linear_structure_def)
    show ?thesis
    proof (rule eq_matI)
      fix a b assume "a < dim_row x" "b < dim_col x"
      hence a: "a < m*m" and b: "b < p*p" using xc by auto
      have "b div p < p" using b p_pos by (simp add: div_less_iff_less_mult)
      thus "?G (?F x) $$ (a,b) = x $$ (a,b)"
        using a b p_pos operator_tensor_iso_inv_row_bound[OF m_pos p_pos a b]
              operator_tensor_iso_inv_col_bound[OF m_pos p_pos, of a b]
        by (simp add: operator_tensor_iso_inv_def operator_tensor_iso_map_def)
    qed (use xc in \<open>simp_all add: operator_tensor_iso_inv_def\<close>)
  qed
  have FG: "?F (?G y) = y" if "y \<in> ls_carrier ?W" for y
  proof -
    have yc: "y \<in> carrier_mat (m*p) (m*p)"
      using that by (simp add: bipartite_operator_space_def mat_linear_structure_def)
    show ?thesis
    proof (rule eq_matI)
      fix r s assume "r < dim_row y" "s < dim_col y"
      hence r: "r < m*p" and s: "s < m*p" using yc by auto
      have "s div p < m" using s p_pos by (simp add: div_less_iff_less_mult)
      thus "?F (?G y) $$ (r,s) = y $$ (r,s)"
        using r s p_pos operator_tensor_iso_map_row_bound[OF p_pos r s]
              operator_tensor_iso_map_col_bound[OF p_pos, of r s]
        by (simp add: operator_tensor_iso_inv_def operator_tensor_iso_map_def)
    qed (use yc in \<open>simp_all add: operator_tensor_iso_map_def\<close>)
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
  show "unit_mat (m * m) (p * p) a b $$ (i, j) = op_elem m p (unit_mat m m (a div m) (a mod m)) (unit_mat p p (b div p) (b mod p)) $$ (i, j)"
    using ij m0 p0 a b
    by (auto simp: unit_mat_def op_elem_def less_mult_imp_div_less nat_eq_iff_div_mod[of i a m] nat_eq_iff_div_mod[of j b p])
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

text_raw \<open>
\begin{center}\normalfont
\begin{tikzpicture}[x=1cm,y=1cm]
\draw[thick, fill=blue!8] (0,0) rectangle (1.2,1.4); \node at (0.6,0.7) {$X$};
\draw[thick] (-0.8,1.05) -- (0,1.05) node[pos=0, left, font=\small] {$A$};
\draw[thick] (1.2,1.05) -- (2.0,1.05) node[right, font=\small] {$A$};
\draw[thick] (-0.3,0.35) -- (0,0.35); \draw[thick] (1.2,0.35) -- (1.5,0.35);
\draw[thick, orange!85!black] (-0.3,0.35) .. controls (-0.8,0.35) and (-0.8,-0.5) .. (0.6,-0.5) .. controls (2.0,-0.5) and (2.0,0.35) .. (1.5,0.35);
\node[font=\small, orange!85!black] at (0.6,-0.75) {$B$ traced out};
\node[font=\small, anchor=west] at (2.8,0.7) {$=\ \tr_B X$, \quad $\tr_B(R\otimes T)=\tr(T)\,R$};
\end{tikzpicture}
\end{center}
\<close>

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
  fix i j assume "i < dim_row (Tr T \<cdot>\<^sub>m R)" "j < dim_col (Tr T \<cdot>\<^sub>m R)"
  hence ij: "i < m" "j < m" using Rsq by auto
  have "(R \<Otimes> T) $$ (i * p + k, j * p + k) = R $$ (i, j) * T $$ (k, k)" if k: "k < p" for k
    unfolding index_tensor_mat[OF carrier_matD(1)[OF Rsq] carrier_matD(2)[OF Rsq] carrier_matD(1)[OF Tsq]
                               carrier_matD(2)[OF Tsq] mult_index_lt[OF ij(1) k] mult_index_lt[OF ij(2) k] m_pos p_pos]
    using k by simp
  thus "partial_trace_B m p (R \<Otimes> T) $$ (i, j) = (Tr T \<cdot>\<^sub>m R) $$ (i, j)"
    using ij Rsq Tsq by (simp add: partial_trace_B_def Tr_def sum_distrib_left mult.commute)
qed (use Rsq in auto)

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

text \<open>$\Tr((N\otimes I)\rho)=\Tr(N\,\tr_B\rho)$: reindex $r=ip+a$, $s=jp+b$ and sum out $\delta_{ab}$.\<close>

lemma Tr_tensor_one_partial_trace_B:
  fixes N \<rho> :: "complex Matrix.mat"
  assumes N: "N \<in> carrier_mat m m" and \<rho>: "\<rho> \<in> carrier_mat (m * p) (m * p)" and p: "0 < p"
  shows "Tr ((N \<Otimes> 1\<^sub>m p) * \<rho>) = Tr (N * partial_trace_B m p \<rho>)"
proof -
  let ?g = "\<lambda>i a j b. if a = b then N $$ (i, j) * \<rho> $$ (j * p + b, i * p + a) else 0"
  have NI: "N \<Otimes> 1\<^sub>m p \<in> carrier_mat (m * p) (m * p)" using N by (intro carrier_matI) simp_all
  have "Tr ((N \<Otimes> 1\<^sub>m p) * \<rho>) = (\<Sum>r<m * p. \<Sum>s<m * p. (N \<Otimes> 1\<^sub>m p) $$ (r, s) * \<rho> $$ (s, r))"
    by (rule Tr_mult_entry[OF NI \<rho>])
  also have "\<dots> = (\<Sum>r<m * p. \<Sum>s<m * p. ?g (r div p) (r mod p) (s div p) (s mod p))"
  proof (intro sum.cong refl)
    fix r s assume "r \<in> {..<m * p}" "s \<in> {..<m * p}"
    hence rs: "r < m * p" "s < m * p" by simp_all
    have m: "0 < m" using rs by (cases m) simp_all
    show "(N \<Otimes> 1\<^sub>m p) $$ (r, s) * \<rho> $$ (s, r) = ?g (r div p) (r mod p) (s div p) (s mod p)"
      unfolding index_tensor_mat[OF carrier_matD(1)[OF N] carrier_matD(2)[OF N] index_one_mat(2) index_one_mat(3) rs m p]
                index_one_mat(1)[OF mod_less_divisor[OF p] mod_less_divisor[OF p]] div_mult_mod_eq
      by simp
  qed
  also have "\<dots> = (\<Sum>i<m. \<Sum>a<p. \<Sum>j<m. \<Sum>b<p. ?g i a j b)" by (rule sum_div_mod2[where g = ?g])
  also have "\<dots> = (\<Sum>i<m. \<Sum>a<p. \<Sum>j<m. N $$ (i, j) * \<rho> $$ (j * p + a, i * p + a))"
    by (intro sum.cong refl) (simp add: sum.delta')
  also have "\<dots> = (\<Sum>i<m. \<Sum>j<m. N $$ (i, j) * partial_trace_B m p \<rho> $$ (j, i))"
    by (rule sum.cong[OF refl])
       (simp add: sum.swap[of _ "{..<p}" "{..<m}"] sum_distrib_left partial_trace_B_def)
  also have "\<dots> = Tr (N * partial_trace_B m p \<rho>)"
    by (rule Tr_mult_entry[OF N partial_trace_B_carrier, symmetric])
  finally show ?thesis .
qed

theorem partial_trace_measurement:
  fixes meas :: "complex Matrix.mat" and \<rho> :: "complex Matrix.mat"
  assumes M_sq: "meas \<in> carrier_mat m m"
      and dm: "density_matrix (m * p) \<rho>"
      and p_pos: "0 < p"
  shows "Tr (((meas\<^sup>\<dagger> * meas) \<Otimes> 1\<^sub>m p) * \<rho>) =
         Tr (meas\<^sup>\<dagger> * meas * partial_trace_B m p \<rho>)"
  using dm unfolding density_matrix_def
  by (intro Tr_tensor_one_partial_trace_B[OF mult_carrier_mat[OF dagger_carrier[OF M_sq] M_sq] _ p_pos]) simp

text \<open>The check: the partial trace preserves the trace, Hermiticity and positivity (D15-6).\<close>

lemma partial_trace_B_trace:
  fixes X :: "complex Matrix.mat"
  assumes Xsq: "X \<in> carrier_mat (m * p) (m * p)"
      and p_pos: "0 < p"
  shows "Tr (partial_trace_B m p X) = Tr X"
proof -
  have "Tr (partial_trace_B m p X) = (\<Sum>i<m. \<Sum>k<p. X $$ (i * p + k, i * p + k))"
    by (simp add: Tr_def partial_trace_B_def)
  also have "\<dots> = (\<Sum>r<m * p. X $$ (r div p * p + r mod p, r div p * p + r mod p))"
    by (rule sum_div_mod[where g = "\<lambda>i k. X $$ (i * p + k, i * p + k)", symmetric])
  also have "\<dots> = Tr X" using Xsq by (simp add: Tr_def)
  finally show ?thesis .
qed

lemma partial_trace_B_hermitian:
  fixes X :: "complex Matrix.mat"
  assumes Xsq: "X \<in> carrier_mat (m * p) (m * p)"
      and herm: "hermitian X"
  shows "hermitian (partial_trace_B m p X)"
  unfolding hermitian_def
proof (rule eq_matI)
  fix i j assume "i < dim_row (partial_trace_B m p X)" "j < dim_col (partial_trace_B m p X)"
  hence ij: "i < m" "j < m" by simp_all
  have "X $$ (j * p + k, i * p + k) = cnj (X $$ (i * p + k, j * p + k))" if k: "k < p" for k
    by (rule hermitian_index[OF herm])
       (simp_all add: carrier_matD[OF Xsq] mult_index_lt[OF ij(2) k] mult_index_lt[OF ij(1) k])
  thus "(partial_trace_B m p X)\<^sup>\<dagger> $$ (i, j) = partial_trace_B m p X $$ (i, j)"
    using ij by (simp add: dagger_def partial_trace_B_def cnj_sum)
qed (simp_all add: dagger_def)

text \<open>$\braket v{\tr_B(X)v}=\sum_a\braket{v\otimes e_a}{X(v\otimes e_a)}\ge0$.\<close>

lemma partial_trace_B_is_density:
  fixes X :: "complex Matrix.mat"
  assumes dm: "density_matrix (m * p) X"
      and p_pos: "0 < p"
  shows "density_matrix m (partial_trace_B m p X)"
proof -
  have X: "X \<in> carrier_mat (m * p) (m * p)" and Xpsd: "psd X" and tr: "Tr X = 1"
    using dm by (auto simp: density_matrix_def)
  have nonneg: "0 \<le> Re \<langle>v | partial_trace_B m p X *\<^sub>v v\<rangle>" if v: "dim_vec v = m" for v
  proof -
    let ?w = "\<lambda>a. tensor_vec v (unit_vec p a)"
    have w: "dim_vec (?w a) = m * p" for a by (simp add: tensor_vec_dim v)
    have each: "\<langle>?w a | X *\<^sub>v ?w a\<rangle> = (\<Sum>i<m. \<Sum>j<m. cnj (v $ i) * (X $$ (i * p + a, j * p + a) * v $ j))"
      if a: "a < p" for a
    proof -
      let ?g = "\<lambda>i b j c. if c = a then if b = a then cnj (v $ i) * (X $$ (i * p + b, j * p + c) * v $ j) else 0 else 0"
      have "\<langle>?w a | X *\<^sub>v ?w a\<rangle> = (\<Sum>r<m * p. \<Sum>s<m * p. cnj (?w a $ r) * (X $$ (r, s) * ?w a $ s))"
        unfolding inner_prod_sum[OF w dim_mult_mat_vec[of X "?w a", unfolded carrier_matD(1)[OF X]]] atLeast0LessThan
        by (rule sum.cong[OF refl])
           (simp add: mult_mat_vec_index[OF X carrier_vecI[OF w]] atLeast0LessThan sum_distrib_left)
      also have "\<dots> = (\<Sum>r<m * p. \<Sum>s<m * p. ?g (r div p) (r mod p) (s div p) (s mod p))"
      proof (intro sum.cong refl)
        fix r s assume "r \<in> {..<m * p}" "s \<in> {..<m * p}"
        hence rs: "r < m * p" "s < m * p" by simp_all
        show "cnj (?w a $ r) * (X $$ (r, s) * ?w a $ s) = ?g (r div p) (r mod p) (s div p) (s mod p)"
          unfolding tensor_vec_index[OF v index_unit_vec(3) rs(1)] tensor_vec_index[OF v index_unit_vec(3) rs(2)]
                    div_mult_mod_eq
          using p_pos a by simp
      qed
      also have "\<dots> = (\<Sum>i<m. \<Sum>b<p. \<Sum>j<m. \<Sum>c<p. ?g i b j c)" by (rule sum_div_mod2[where g = ?g])
      also have "\<dots> = (\<Sum>i<m. \<Sum>j<m. \<Sum>b<p. \<Sum>c<p. ?g i b j c)"
        by (rule sum.cong[OF refl]) (rule sum.swap)
      also have "\<dots> = (\<Sum>i<m. \<Sum>j<m. cnj (v $ i) * (X $$ (i * p + a, j * p + a) * v $ j))"
        by (intro sum.cong refl) (simp add: sum.delta a)
      finally show ?thesis .
    qed
    have nn: "0 \<le> Re \<langle>?w a | X *\<^sub>v ?w a\<rangle>" for a
      using Xpsd w[of a] unfolding psd_def carrier_matD[OF X] by blast
    have "\<langle>v | partial_trace_B m p X *\<^sub>v v\<rangle> = (\<Sum>i<m. \<Sum>j<m. \<Sum>a<p. cnj (v $ i) * (X $$ (i * p + a, j * p + a) * v $ j))"
      unfolding inner_prod_sum[OF v dim_mult_mat_vec[of "partial_trace_B m p X" v, unfolded dim_row_partial_trace_B]] atLeast0LessThan
      by (rule sum.cong[OF refl])
         (simp add: partial_trace_B_def scalar_prod_def v atLeast0LessThan sum_distrib_left sum_distrib_right)
    also have "\<dots> = (\<Sum>a<p. \<langle>?w a | X *\<^sub>v ?w a\<rangle>)"
      by (simp add: each sum.swap[of _ "{..<m}" "{..<p}"])
    finally have "Re \<langle>v | partial_trace_B m p X *\<^sub>v v\<rangle> = (\<Sum>a<p. Re \<langle>?w a | X *\<^sub>v ?w a\<rangle>)"
      by (simp add: Re_sum)
    thus ?thesis by (simp add: sum_nonneg nn)
  qed
  have "psd (partial_trace_B m p X)"
    unfolding psd_def using partial_trace_B_hermitian[OF X psd_hermitian[OF Xpsd]] nonneg by simp
  thus ?thesis unfolding density_matrix_def using partial_trace_B_trace[OF X p_pos] tr by simp
qed

subsection \<open>The partial trace over $A$ (D15-6)\<close>

text \<open>Reordering the basis: for a bijection $\sigma$ of $\{0,\dots,N-1\}$ the matrix
$(x_{\sigma(r)\sigma(s)})$ has the trace of $X$ and is Hermitian, resp.\ positive, with $X$.\<close>

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

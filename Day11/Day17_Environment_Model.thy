theory Day17_Environment_Model
  imports Day22_Minimal_Kraus
begin

section \<open>Day 17: the environment model of noise\<close>

text \<open>Day 17, the environment model of noise: a state $\rho$ of lab $A$ meets an environment in
the state $\ket\varphi$, the pair evolves by a unitary $U$ on $\C^m\otimes\C^p$, and lab $A$ sees
$\operatorname{tr}_E(U(\rho\otimes\ketbra\varphi\varphi)U^*)=\sum_iW_i\rho W_i^*$ with
$\sum_iW_i^*W_i=I$.  The index of $\C^m\otimes\C^p$ is $a\,p+i$ (lab index $a$, environment
index $i$), and $W_i$ is the matrix with entries $\sum_kU_{(a,i),(c,k)}\varphi_k$, i.e.\ the
notes' $W_i=\sum_kU_{ik}\alpha_k$ for the blocks $U_{ik}$ of $U$.\<close>

definition env_kraus :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.vec \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
  "env_kraus m p U \<phi> i = Matrix.mat m m (\<lambda>(a,c). \<Sum>k<p. U $$ (a * p + i, c * p + k) * \<phi> $ k)"

lemma env_kraus_carrier [simp]: "env_kraus m p U \<phi> i \<in> carrier_mat m m"
  by (simp add: env_kraus_def)

lemma env_kraus_dims [simp]: "dim_row (env_kraus m p U \<phi> i) = m" "dim_col (env_kraus m p U \<phi> i) = m"
  by (simp_all add: env_kraus_def)

lemma env_kraus_index: "a < m \<Longrightarrow> c < m \<Longrightarrow> env_kraus m p U \<phi> i $$ (a,c) = (\<Sum>k<p. U $$ (a * p + i, c * p + k) * \<phi> $ k)"
  by (simp add: env_kraus_def)

lemma sum_split_mp:
  fixes f :: "nat \<Rightarrow> 'a::comm_monoid_add"
  shows "(\<Sum>x < m * p. f x) = (\<Sum>c<m. \<Sum>k<p. f (c * p + k))"
proof -
  have "(\<Sum>x < m * p. f x) = (\<Sum>c<m. sum f {c * p..<c * p + p})" by (rule sum.nat_group[symmetric])
  also have "\<dots> = (\<Sum>c<m. \<Sum>k<p. f (c * p + k))"
  proof (rule sum.cong[OF refl])
    fix c :: nat
    show "sum f {c * p..<c * p + p} = (\<Sum>k<p. f (c * p + k))"
      by (rule sum.reindex_bij_witness[where i="\<lambda>k. c * p + k" and j="\<lambda>x. x - c * p"]) auto
  qed
  finally show ?thesis .
qed

lemma tensor_outer_index:
  fixes \<rho> :: "complex Matrix.mat" and \<phi> :: "complex Matrix.vec"
  assumes \<rho>: "\<rho> \<in> carrier_mat m m" and \<phi>: "dim_vec \<phi> = p"
      and c: "c < m" and d: "d < m" and k: "k < p" and l: "l < p"
  shows "Tensor.tensor_mat \<rho> (\<phi> \<oslash> \<phi>) $$ (c * p + k, d * p + l) = \<rho> $$ (c,d) * (\<phi> $ k * cnj (\<phi> $ l))"
proof -
  have oc: "\<phi> \<oslash> \<phi> \<in> carrier_mat p p" by (rule outer_prod_carrier[OF \<phi> \<phi>])
  have mp: "0 < m" "0 < p" using c k by simp_all
  have "Tensor.tensor_mat \<rho> (\<phi> \<oslash> \<phi>) $$ (c * p + k, d * p + l)
        = \<rho> $$ ((c * p + k) div p, (d * p + l) div p) * (\<phi> \<oslash> \<phi>) $$ ((c * p + k) mod p, (d * p + l) mod p)"
    by (rule index_tensor_mat) (use carrier_matD[OF \<rho>] carrier_matD[OF oc] mult_index_lt[OF c k] mult_index_div_mod[OF k] mult_index_lt[OF d l] mult_index_div_mod[OF l] mp in simp_all)
  also have "\<dots> = \<rho> $$ (c,d) * (\<phi> $ k * cnj (\<phi> $ l))"
    unfolding mult_index_div_mod[OF k] mult_index_div_mod[OF l] using outer_prod_index[of k \<phi> l \<phi>] \<phi> k l by simp
  finally show ?thesis .
qed

text \<open>The entries of $U(\rho\otimes\ketbra\varphi\varphi)U^*$.\<close>

lemma env_entry:
  fixes U \<rho> :: "complex Matrix.mat" and \<phi> :: "complex Matrix.vec"
  assumes U: "U \<in> carrier_mat (m * p) (m * p)" and \<rho>: "\<rho> \<in> carrier_mat m m" and \<phi>: "dim_vec \<phi> = p"
      and x: "x < m * p" and y: "y < m * p"
  shows "(U * Tensor.tensor_mat \<rho> (\<phi> \<oslash> \<phi>) * (U\<^sup>\<dagger>)) $$ (x,y)
         = (\<Sum>d<m. \<Sum>c<m. (\<Sum>k<p. U $$ (x, c * p + k) * \<phi> $ k) * \<rho> $$ (c,d)
              * cnj (\<Sum>l<p. U $$ (y, d * p + l) * \<phi> $ l))"
proof -
  let ?T = "Tensor.tensor_mat \<rho> (\<phi> \<oslash> \<phi>)"
  have Tc: "?T \<in> carrier_mat (m * p) (m * p)" using \<rho> outer_prod_carrier[OF \<phi> \<phi>] by auto
  have UT: "U * ?T \<in> carrier_mat (m * p) (m * p)" using U Tc by auto
  have Ud: "U\<^sup>\<dagger> \<in> carrier_mat (m * p) (m * p)" by (rule dagger_carrier[OF U])
  have "(U * ?T * (U\<^sup>\<dagger>)) $$ (x,y) = (\<Sum>w < m * p. (U * ?T) $$ (x,w) * (U\<^sup>\<dagger>) $$ (w,y))"
    by (rule mat_mult_entry[OF UT Ud x y])
  also have "\<dots> = (\<Sum>w < m * p. (\<Sum>z < m * p. U $$ (x,z) * ?T $$ (z,w)) * cnj (U $$ (y,w)))"
  proof (rule sum.cong[OF refl])
    fix w assume "w \<in> {..< m * p}"
    hence w: "w < m * p" by simp
    show "(U * ?T) $$ (x,w) * (U\<^sup>\<dagger>) $$ (w,y) = (\<Sum>z < m * p. U $$ (x,z) * ?T $$ (z,w)) * cnj (U $$ (y,w))"
      using mat_mult_entry[OF U Tc x w] U w y by (simp add: dagger_def)
  qed
  also have "\<dots> = (\<Sum>d<m. \<Sum>l<p. (\<Sum>c<m. \<Sum>k<p. U $$ (x, c * p + k) * ?T $$ (c * p + k, d * p + l))
                    * cnj (U $$ (y, d * p + l)))"
    by (simp only: sum_split_mp)
  also have "\<dots> = (\<Sum>d<m. \<Sum>l<p. (\<Sum>c<m. \<Sum>k<p. U $$ (x, c * p + k) * (\<rho> $$ (c,d) * (\<phi> $ k * cnj (\<phi> $ l))))
                    * cnj (U $$ (y, d * p + l)))"
    by (intro sum.cong refl) (simp add: tensor_outer_index[OF \<rho> \<phi>])
  also have "\<dots> = (\<Sum>d<m. \<Sum>c<m. (\<Sum>k<p. U $$ (x, c * p + k) * \<phi> $ k) * \<rho> $$ (c,d)
              * cnj (\<Sum>l<p. U $$ (y, d * p + l) * \<phi> $ l))"
  proof (rule sum.cong[OF refl])
    fix d
    define F where "F = (\<lambda>c k l. U $$ (x, c * p + k) * \<phi> $ k * \<rho> $$ (c,d) * cnj (\<phi> $ l) * cnj (U $$ (y, d * p + l)))"
    have "(\<Sum>l<p. (\<Sum>c<m. \<Sum>k<p. U $$ (x, c * p + k) * (\<rho> $$ (c,d) * (\<phi> $ k * cnj (\<phi> $ l))))
              * cnj (U $$ (y, d * p + l))) = (\<Sum>l<p. \<Sum>c<m. \<Sum>k<p. F c k l)"
      unfolding F_def by (simp add: sum_distrib_left sum_distrib_right mult_ac)
    also have "\<dots> = (\<Sum>c<m. \<Sum>l<p. \<Sum>k<p. F c k l)" by (rule sum.swap)
    also have "\<dots> = (\<Sum>c<m. \<Sum>k<p. \<Sum>l<p. F c k l)" by (rule sum.cong[OF refl]) (rule sum.swap)
    also have "\<dots> = (\<Sum>c<m. (\<Sum>k<p. U $$ (x, c * p + k) * \<phi> $ k) * \<rho> $$ (c,d)
              * cnj (\<Sum>l<p. U $$ (y, d * p + l) * \<phi> $ l))"
      unfolding F_def by (simp add: sum_distrib_left sum_distrib_right mult_ac)
    finally show "(\<Sum>l<p. (\<Sum>c<m. \<Sum>k<p. U $$ (x, c * p + k) * (\<rho> $$ (c,d) * (\<phi> $ k * cnj (\<phi> $ l))))
              * cnj (U $$ (y, d * p + l)))
        = (\<Sum>c<m. (\<Sum>k<p. U $$ (x, c * p + k) * \<phi> $ k) * \<rho> $$ (c,d)
              * cnj (\<Sum>l<p. U $$ (y, d * p + l) * \<phi> $ l))" .
  qed
  finally show ?thesis .
qed

theorem environment_model:
  fixes U \<rho> :: "complex Matrix.mat" and \<phi> :: "complex Matrix.vec"
  assumes U: "U \<in> carrier_mat (m * p) (m * p)" and Uu: "unitary U"
      and \<phi>: "dim_vec \<phi> = p" and \<phi>1: "\<langle>\<phi>|\<phi>\<rangle> = 1" and \<rho>: "\<rho> \<in> carrier_mat m m"
  defines "Ws \<equiv> map (env_kraus m p U \<phi>) [0..<p]"
  shows "partial_trace_B m p (U * Tensor.tensor_mat \<rho> (\<phi> \<oslash> \<phi>) * (U\<^sup>\<dagger>)) = kraus_map_dim m Ws \<rho>"
    and "kraus_operators m m Ws"
proof -
  have Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat m m" unfolding Ws_def by auto
  let ?W = "env_kraus m p U \<phi>"
  show "partial_trace_B m p (U * Tensor.tensor_mat \<rho> (\<phi> \<oslash> \<phi>) * (U\<^sup>\<dagger>)) = kraus_map_dim m Ws \<rho>"
  proof (rule eq_matI)
    fix a b assume "a < dim_row (kraus_map_dim m Ws \<rho>)" "b < dim_col (kraus_map_dim m Ws \<rho>)"
    hence a: "a < m" and b: "b < m" using kraus_map_dim_carrier[OF Ws_c \<rho>] by simp_all
    have "partial_trace_B m p (U * Tensor.tensor_mat \<rho> (\<phi> \<oslash> \<phi>) * (U\<^sup>\<dagger>)) $$ (a,b)
          = (\<Sum>i<p. (U * Tensor.tensor_mat \<rho> (\<phi> \<oslash> \<phi>) * (U\<^sup>\<dagger>)) $$ (a * p + i, b * p + i))"
      using a b by (simp add: partial_trace_B_def)
    also have "\<dots> = (\<Sum>i<p. (?W i * \<rho> * ((?W i)\<^sup>\<dagger>)) $$ (a,b))"
    proof (rule sum.cong[OF refl])
      fix i assume "i \<in> {..<p}"
      hence i: "i < p" by simp
      have W: "?W i \<in> carrier_mat m m" by simp
      have WR: "?W i * \<rho> \<in> carrier_mat m m" by (rule mult_carrier_mat[OF W \<rho>])
      have Wd: "(?W i)\<^sup>\<dagger> \<in> carrier_mat m m" by (rule dagger_carrier[OF W])
      have "(?W i * \<rho> * ((?W i)\<^sup>\<dagger>)) $$ (a,b) = (\<Sum>d<m. (?W i * \<rho>) $$ (a,d) * ((?W i)\<^sup>\<dagger>) $$ (d,b))"
        by (rule mat_mult_entry[OF WR Wd a b])
      also have "\<dots> = (\<Sum>d<m. \<Sum>c<m. (\<Sum>k<p. U $$ (a * p + i, c * p + k) * \<phi> $ k) * \<rho> $$ (c,d)
              * cnj (\<Sum>l<p. U $$ (b * p + i, d * p + l) * \<phi> $ l))"
      proof (rule sum.cong[OF refl])
        fix d assume "d \<in> {..<m}"
        hence d: "d < m" by simp
        show "(?W i * \<rho>) $$ (a,d) * ((?W i)\<^sup>\<dagger>) $$ (d,b) = (\<Sum>c<m. (\<Sum>k<p. U $$ (a * p + i, c * p + k) * \<phi> $ k) * \<rho> $$ (c,d)
              * cnj (\<Sum>l<p. U $$ (b * p + i, d * p + l) * \<phi> $ l))"
          unfolding mat_mult_entry[OF W \<rho> a d] using a b d
          by (simp add: dagger_def env_kraus_index sum_distrib_right)
      qed
      finally show "(U * Tensor.tensor_mat \<rho> (\<phi> \<oslash> \<phi>) * (U\<^sup>\<dagger>)) $$ (a * p + i, b * p + i)
                    = (?W i * \<rho> * ((?W i)\<^sup>\<dagger>)) $$ (a,b)"
        using env_entry[OF U \<rho> \<phi> mult_index_lt[OF a i] mult_index_lt[OF b i]] by simp
    qed
    also have "\<dots> = kraus_map_dim m Ws \<rho> $$ (a,b)"
      unfolding kraus_map_dim_entry_sum_list[OF Ws_c \<rho> a b] unfolding Ws_def
      by (simp add: interv_sum_list_conv_sum_set_nat atLeast0LessThan)
    finally show "partial_trace_B m p (U * Tensor.tensor_mat \<rho> (\<phi> \<oslash> \<phi>) * (U\<^sup>\<dagger>)) $$ (a,b) = kraus_map_dim m Ws \<rho> $$ (a,b)" .
  qed (use kraus_map_dim_carrier[OF Ws_c \<rho>] in simp_all)
  have UU: "(U\<^sup>\<dagger>) * U = 1\<^sub>m (m * p)" using Uu U unfolding unitary_def by simp
  have tp: "sum_wdag_w m Ws = 1\<^sub>m m"
  proof (rule eq_matI)
    fix c d assume "c < dim_row (1\<^sub>m m :: complex Matrix.mat)" "d < dim_col (1\<^sub>m m :: complex Matrix.mat)"
    hence c: "c < m" and d: "d < m" by simp_all
    define G where "G = (\<lambda>x. cnj (\<Sum>k<p. U $$ (x, c * p + k) * \<phi> $ k) * (\<Sum>l<p. U $$ (x, d * p + l) * \<phi> $ l))"
    have "sum_wdag_w m Ws $$ (c,d) = (\<Sum>i<p. (((?W i)\<^sup>\<dagger>) * ?W i) $$ (c,d))"
      unfolding sum_wdag_w_entry[OF Ws_c c d] unfolding Ws_def
      by (simp add: interv_sum_list_conv_sum_set_nat atLeast0LessThan)
    also have "\<dots> = (\<Sum>i<p. \<Sum>a<m. G (a * p + i))"
    proof (rule sum.cong[OF refl])
      fix i assume "i \<in> {..<p}"
      have W: "?W i \<in> carrier_mat m m" by simp
      show "(((?W i)\<^sup>\<dagger>) * ?W i) $$ (c,d) = (\<Sum>a<m. G (a * p + i))"
        unfolding mat_mult_entry[OF dagger_carrier[OF W] W c d] G_def
        by (rule sum.cong[OF refl]) (use c d in \<open>simp add: dagger_def env_kraus_index\<close>)
    qed
    also have "\<dots> = (\<Sum>a<m. \<Sum>i<p. G (a * p + i))" by (rule sum.swap)
    also have "\<dots> = (\<Sum>x < m * p. G x)" by (rule sum_split_mp[symmetric])
    also have "\<dots> = (\<Sum>k<p. \<Sum>l<p. cnj (\<phi> $ k) * \<phi> $ l * (\<Sum>x < m * p. cnj (U $$ (x, c * p + k)) * U $$ (x, d * p + l)))"
      unfolding G_def by (simp add: sum_distrib_left sum_distrib_right mult_ac sum.swap[of _ "{..<m*p}"])
    also have "\<dots> = (\<Sum>k<p. \<Sum>l<p. cnj (\<phi> $ k) * \<phi> $ l * (if c = d \<and> k = l then 1 else 0))"
    proof (intro sum.cong refl)
      fix k l assume "k \<in> {..<p}" "l \<in> {..<p}"
      hence k: "k < p" and l: "l < p" by simp_all
      have "(\<Sum>x < m * p. cnj (U $$ (x, c * p + k)) * U $$ (x, d * p + l)) = ((U\<^sup>\<dagger>) * U) $$ (c * p + k, d * p + l)"
        unfolding mat_mult_entry[OF dagger_carrier[OF U] U mult_index_lt[OF c k] mult_index_lt[OF d l]]
        by (rule sum.cong[OF refl]) (use U mult_index_lt[OF c k] in \<open>simp add: dagger_def\<close>)
      also have "\<dots> = (if c = d \<and> k = l then 1 else 0)"
      proof -
        have "c * p + k = d * p + l \<longleftrightarrow> c = d \<and> k = l"
          using mult_index_div_mod[OF k] mult_index_div_mod[OF l] by metis
        thus ?thesis unfolding UU using mult_index_lt[OF c k] mult_index_lt[OF d l] by simp
      qed
      finally show "cnj (\<phi> $ k) * \<phi> $ l * (\<Sum>x < m * p. cnj (U $$ (x, c * p + k)) * U $$ (x, d * p + l))
                    = cnj (\<phi> $ k) * \<phi> $ l * (if c = d \<and> k = l then 1 else 0)" by simp
    qed
    also have "\<dots> = (if c = d then \<langle>\<phi>|\<phi>\<rangle> else 0)"
    proof (cases "c = d")
      case True
      have "(\<Sum>k<p. \<Sum>l<p. cnj (\<phi> $ k) * \<phi> $ l * (if c = d \<and> k = l then 1 else 0)) = (\<Sum>k<p. cnj (\<phi> $ k) * \<phi> $ k)"
        using True by (simp add: if_distrib cong: if_cong)
      also have "\<dots> = \<langle>\<phi>|\<phi>\<rangle>" unfolding inner_prod_sum[OF \<phi> \<phi>] atLeast0LessThan ..
      finally show ?thesis using True by simp
    qed simp
    also have "\<dots> = 1\<^sub>m m $$ (c,d)" using c d \<phi>1 by simp
    finally show "sum_wdag_w m Ws $$ (c,d) = 1\<^sub>m m $$ (c,d)" .
  qed (use sum_wdag_w_carrier Ws_c in auto)
  show "kraus_operators m m Ws" unfolding kraus_operators_altdef using Ws_c tp by simp
qed

end

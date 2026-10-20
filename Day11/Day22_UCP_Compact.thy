theory Day22_UCP_Compact
  imports Day16_Block_Form Day19_Choi_TP_Unital Day27_Positive_Map_Criterion
begin

section \<open>Day 22: $\mathrm{UCP}(M_n,M_d)$ is compact (D22-4)\<close>

text \<open>The notes: $\mathrm{UCP}(M_n,M_d)$ is convex and compact, closed because the conditions are
closed and bounded because $\Phi(I)=I$ forces $0\le\Phi(E_{ii})\le I$.  The space $L(M_n,M_d)$ carries
no topology in this development; the Choi matrix is a linear bijection onto $M_{nd}$, so the
statement is made in Choi coordinates: the Choi matrices of linear UCP maps are exactly the
positive $P$ whose diagonal blocks sum to $I_d$ (\<open>ucp_choi_image\<close>, with the inverse Choi map
\<open>choi_inv\<close>), and that set is compact (\<open>compact_ucp_choi_set\<close>): it is closed, and it lies in
$d$ times the compact set of unit-trace positive matrices.\<close>

text \<open>In Choi coordinates a linear map $\Phi:M_n\to M_d$ is UCP iff $P_\Phi\ge0$ and
$\sum_iR_{ii}=I_d$ (@{thm [source] choi_ucp_iff}); the set of such $P$ is compact.  Dimensions are
cardinalities of finite types, $n=|{'n}|$, $d=|{'d}|$, so that the typed matrices of
\<open>Separable_Cone\<close> (a Euclidean space) can be used.\<close>

definition ucp_choi_set :: "(complex, 'n :: finite \<times> 'd :: finite, 'n \<times> 'd) lmat set" where
  "ucp_choi_set = {M. psd_lmat M \<and> (\<forall>a < CARD('d). \<forall>b < CARD('d).
      (\<Sum>i<CARD('n). unwrap_lm M $$ (i * CARD('d) + a, i * CARD('d) + b)) = (if a = b then 1 else 0))}"

lemma closed_block_sum_eq:
  assumes a: "a < CARD('d :: finite)" and b: "b < CARD('d)"
  shows "closed {M :: (complex, 'n :: finite \<times> 'd, 'n \<times> 'd) lmat.
                  (\<Sum>i<CARD('n). unwrap_lm M $$ (i * CARD('d) + a, i * CARD('d) + b)) = c}"
proof -
  have cont: "continuous_on UNIV (\<lambda>M :: (complex, 'n \<times> 'd, 'n \<times> 'd) lmat.
                 \<Sum>i<CARD('n). unwrap_lm M $$ (i * CARD('d) + a, i * CARD('d) + b))"
  proof (rule continuous_on_sum)
    fix i assume "i \<in> {..<CARD('n)}"
    hence i: "i < CARD('n)" by simp
    have "i * CARD('d) + a < CARD('n \<times> 'd)" "i * CARD('d) + b < CARD('n \<times> 'd)"
      using idx_bound[OF i a] idx_bound[OF i b] by (simp_all add: card_prod)
    thus "continuous_on UNIV (\<lambda>M :: (complex, 'n \<times> 'd, 'n \<times> 'd) lmat. unwrap_lm M $$ (i * CARD('d) + a, i * CARD('d) + b))"
      by (rule continuous_on_unwrap_lm_index)
  qed
  have eq: "{M :: (complex, 'n \<times> 'd, 'n \<times> 'd) lmat. (\<Sum>i<CARD('n). unwrap_lm M $$ (i * CARD('d) + a, i * CARD('d) + b)) = c}
          = (\<lambda>M. \<Sum>i<CARD('n). unwrap_lm M $$ (i * CARD('d) + a, i * CARD('d) + b)) -` {c}" by auto
  show ?thesis unfolding eq
  proof (rule continuous_closed_vimage)
    show "closed {c}" by simp
    fix M show "continuous (at M) (\<lambda>M :: (complex, 'n \<times> 'd, 'n \<times> 'd) lmat.
                   \<Sum>i<CARD('n). unwrap_lm M $$ (i * CARD('d) + a, i * CARD('d) + b))"
      using cont continuous_on_eq_continuous_at by blast
  qed
qed

lemma closed_ucp_choi_set: "closed (ucp_choi_set :: (complex, 'n :: finite \<times> 'd :: finite, 'n \<times> 'd) lmat set)"
proof -
  have eq: "(ucp_choi_set :: (complex, 'n \<times> 'd, 'n \<times> 'd) lmat set) = {M. psd_lmat M} \<inter>
      (\<Inter>a \<in> {..<CARD('d)}. \<Inter>b \<in> {..<CARD('d)}. {M. (\<Sum>i<CARD('n). unwrap_lm M $$ (i * CARD('d) + a, i * CARD('d) + b)) = (if a = b then 1 else 0)})"
    unfolding ucp_choi_set_def by auto
  show ?thesis unfolding eq
    by (intro closed_Int closed_psd_lmat closed_INT ballI closed_block_sum_eq) simp_all
qed

lemma ucp_choi_set_trace:
  assumes "M \<in> (ucp_choi_set :: (complex, 'n :: finite \<times> 'd :: finite, 'n \<times> 'd) lmat set)"
  shows "Tr_lmat M = of_nat CARD('d)"
proof -
  have bs: "\<And>a. a < CARD('d) \<Longrightarrow> (\<Sum>i<CARD('n). unwrap_lm M $$ (i * CARD('d) + a, i * CARD('d) + a)) = 1"
    using assms unfolding ucp_choi_set_def by auto
  have "Tr_lmat M = (\<Sum>r<CARD('n) * CARD('d). unwrap_lm M $$ (r, r))"
    by (simp add: Tr_lmat_def card_prod atLeast0LessThan)
  also have "\<dots> = (\<Sum>i<CARD('n). \<Sum>a<CARD('d). unwrap_lm M $$ (i * CARD('d) + a, i * CARD('d) + a))"
    by (rule sum_mp_reindex)
  also have "\<dots> = (\<Sum>a<CARD('d). \<Sum>i<CARD('n). unwrap_lm M $$ (i * CARD('d) + a, i * CARD('d) + a))"
    by (rule sum.swap)
  also have "\<dots> = (\<Sum>a<CARD('d). 1)" by (rule sum.cong) (simp_all add: bs)
  finally show ?thesis by simp
qed

theorem compact_ucp_choi_set: "compact (ucp_choi_set :: (complex, 'n :: finite \<times> 'd :: finite, 'n \<times> 'd) lmat set)"
proof -
  let ?S = "{M :: (complex, 'n \<times> 'd, 'n \<times> 'd) lmat. psd_lmat M \<and> Tr_lmat M = 1}"
  let ?c = "real CARD('d)"
  have cS: "compact ((\<lambda>M. ?c *\<^sub>R M) ` ?S)"
    by (rule compact_continuous_image[OF continuous_on_scaleR[OF continuous_on_const continuous_on_id] compact_unit_trace_psd_lmat])
  have sub: "(ucp_choi_set :: (complex, 'n \<times> 'd, 'n \<times> 'd) lmat set) \<subseteq> (\<lambda>M. ?c *\<^sub>R M) ` ?S"
  proof
    fix M :: "(complex, 'n \<times> 'd, 'n \<times> 'd) lmat" assume M: "M \<in> ucp_choi_set"
    have c0: "0 < ?c" by simp
    have "psd_lmat ((1 / ?c) *\<^sub>R M)"
    proof -
      have pM: "psd (unwrap_lm M)" using M unfolding ucp_choi_set_def by simp
      have "psd (complex_of_real (1 / ?c) \<cdot>\<^sub>m unwrap_lm M)" by (rule psd_smult_nonneg[OF _ pM unwrap_lm_carrier]) simp
      thus ?thesis unfolding psd_lmat_def unwrap_lm_scaleR_mat .
    qed
    moreover have "Tr_lmat ((1 / ?c) *\<^sub>R M) = 1"
      using ucp_choi_set_trace[OF M] c0 by (simp add: Tr_lmat_scaleR scaleR_conv_of_real)
    moreover have "M = ?c *\<^sub>R ((1 / ?c) *\<^sub>R M)" using c0 by simp
    ultimately show "M \<in> (\<lambda>M. ?c *\<^sub>R M) ` ?S" by blast
  qed
  have "compact ((\<lambda>M. ?c *\<^sub>R M) ` ?S \<inter> ucp_choi_set)" by (rule compact_Int_closed[OF cS closed_ucp_choi_set])
  moreover have "(\<lambda>M. ?c *\<^sub>R M) ` ?S \<inter> ucp_choi_set = ucp_choi_set" using sub by blast
  ultimately show ?thesis by simp
qed

text \<open>The inverse of the Choi map: $\Phi_P(X)=\sum_{i,j}x_{ij}P_{ij}$ with $P_{ij}$ the $(i,j)$ block.\<close>

definition choi_inv :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "choi_inv n d P X = Matrix.mat d d (\<lambda>(a, b). \<Sum>i<n. \<Sum>j<n. X $$ (i, j) * P $$ (i * d + a, j * d + b))"

lemma choi_inv_lin: "lin_on n d (carrier_mat n n) (choi_inv n d P)"
  unfolding lin_on_def
proof (intro conjI ballI allI)
  fix A B :: "complex Matrix.mat" assume A: "A \<in> carrier_mat n n" and B: "B \<in> carrier_mat n n"
  show "choi_inv n d P (A + B) = choi_inv n d P A + choi_inv n d P B"
  proof (rule eq_matI)
    fix a b assume "a < dim_row (choi_inv n d P A + choi_inv n d P B)" "b < dim_col (choi_inv n d P A + choi_inv n d P B)"
    hence a: "a < d" and b: "b < d" by (simp_all add: choi_inv_def)
    have "(\<Sum>i<n. \<Sum>j<n. (A + B) $$ (i, j) * P $$ (i * d + a, j * d + b))
          = (\<Sum>i<n. \<Sum>j<n. A $$ (i, j) * P $$ (i * d + a, j * d + b)) + (\<Sum>i<n. \<Sum>j<n. B $$ (i, j) * P $$ (i * d + a, j * d + b))"
    proof -
      have "(\<Sum>i<n. \<Sum>j<n. (A + B) $$ (i, j) * P $$ (i * d + a, j * d + b))
            = (\<Sum>i<n. \<Sum>j<n. A $$ (i, j) * P $$ (i * d + a, j * d + b) + B $$ (i, j) * P $$ (i * d + a, j * d + b))"
        by (intro sum.cong refl) (use A B in \<open>simp add: distrib_right\<close>)
      thus ?thesis by (simp add: sum.distrib)
    qed
    thus "choi_inv n d P (A + B) $$ (a, b) = (choi_inv n d P A + choi_inv n d P B) $$ (a, b)"
      using a b by (simp add: choi_inv_def)
  qed (simp_all add: choi_inv_def)
next
  fix A :: "complex Matrix.mat" and c :: complex assume A: "A \<in> carrier_mat n n"
  show "choi_inv n d P (c \<cdot>\<^sub>m A) = c \<cdot>\<^sub>m choi_inv n d P A"
  proof (rule eq_matI)
    fix a b assume "a < dim_row (c \<cdot>\<^sub>m choi_inv n d P A)" "b < dim_col (c \<cdot>\<^sub>m choi_inv n d P A)"
    hence a: "a < d" and b: "b < d" by (simp_all add: choi_inv_def)
    have "(\<Sum>i<n. \<Sum>j<n. (c \<cdot>\<^sub>m A) $$ (i, j) * P $$ (i * d + a, j * d + b))
          = c * (\<Sum>i<n. \<Sum>j<n. A $$ (i, j) * P $$ (i * d + a, j * d + b))"
    proof -
      have "(\<Sum>i<n. \<Sum>j<n. (c \<cdot>\<^sub>m A) $$ (i, j) * P $$ (i * d + a, j * d + b))
            = (\<Sum>i<n. \<Sum>j<n. c * (A $$ (i, j) * P $$ (i * d + a, j * d + b)))"
        by (intro sum.cong refl) (use A in \<open>simp add: mult_ac\<close>)
      thus ?thesis by (simp add: sum_distrib_left)
    qed
    thus "choi_inv n d P (c \<cdot>\<^sub>m A) $$ (a, b) = (c \<cdot>\<^sub>m choi_inv n d P A) $$ (a, b)"
      using a b by (simp add: choi_inv_def)
  qed (simp_all add: choi_inv_def)
qed (simp add: choi_inv_def)

lemma choi_matrix_choi_inv:
  assumes P: "P \<in> carrier_mat (n * d) (n * d)"
  shows "choi_matrix n d (choi_inv n d P) = P"
proof (rule eq_matI)
  fix r c assume "r < dim_row P" "c < dim_col P"
  hence r: "r < n * d" and c: "c < n * d" using P by auto
  have d: "0 < d" using r by (cases d) auto
  have rd: "r div d < n" "c div d < n" using r c by (simp_all add: less_mult_imp_div_less)
  have "choi_matrix n d (choi_inv n d P) $$ (r, c)
        = (\<Sum>i<n. \<Sum>j<n. (if i = r div d \<and> j = c div d then 1 else 0) * P $$ (i * d + r mod d, j * d + c mod d))"
    using r c rd d by (simp add: choi_matrix_def choi_inv_def mat_unit_def)
  also have "\<dots> = (\<Sum>i<n. \<Sum>j<n. if i = r div d \<and> j = c div d then P $$ (r, c) else 0)"
    by (intro sum.cong refl) auto
  also have "\<dots> = P $$ (r, c)" by (rule double_delta[OF rd])
  finally show "choi_matrix n d (choi_inv n d P) $$ (r, c) = P $$ (r, c)" .
qed (use P in \<open>simp_all add: choi_matrix_def\<close>)

lemma block_sum_entry:
  assumes P: "P \<in> carrier_mat (n * d) (n * d)" and a: "a < d" and b: "b < d"
  shows "msum d d (\<lambda>i. block_of_mat d P i i) [0..<n] $$ (a, b) = (\<Sum>i<n. P $$ (i * d + a, i * d + b))"
  using a b by (simp add: msum_index block_of_mat_def sum_list_distinct_conv_sum_set atLeast0LessThan)

text \<open>UCP in Choi coordinates is exactly \<^const>\<open>ucp_choi_set\<close>, so it is compact.\<close>

theorem ucp_choi_image:
  "(\<lambda>\<Phi>. wrap_lm (choi_matrix CARD('n) CARD('d) \<Phi>) :: (complex, 'n :: finite \<times> 'd :: finite, 'n \<times> 'd) lmat)
     ` {\<Phi>. lin_on CARD('n) CARD('d) (carrier_mat CARD('n) CARD('n)) \<Phi> \<and> \<Phi> \<in> UCP CARD('n) CARD('d)}
   = ucp_choi_set"
proof (intro equalityI subsetI)
  let ?n = "CARD('n)" and ?d = "CARD('d)"
  have n: "0 < ?n" and d: "0 < ?d" by simp_all
  fix M assume "M \<in> (\<lambda>\<Phi>. wrap_lm (choi_matrix ?n ?d \<Phi>) :: (complex, 'n \<times> 'd, 'n \<times> 'd) lmat)
     ` {\<Phi>. lin_on ?n ?d (carrier_mat ?n ?n) \<Phi> \<and> \<Phi> \<in> UCP ?n ?d}"
  then obtain \<Phi> where L: "lin_on ?n ?d (carrier_mat ?n ?n) \<Phi>" and U: "\<Phi> \<in> UCP ?n ?d"
    and M: "M = wrap_lm (choi_matrix ?n ?d \<Phi>)" by blast
  have Cc: "choi_matrix ?n ?d \<Phi> \<in> carrier_mat CARD('n \<times> 'd) CARD('n \<times> 'd)" by (simp add: choi_matrix_def card_prod)
  have uM: "unwrap_lm M = choi_matrix ?n ?d \<Phi>" unfolding M by (rule unwrap_wrap_lm[OF Cc])
  have ch: "psd (choi_matrix ?n ?d \<Phi>) \<and> msum ?d ?d (\<lambda>i. block_of_mat ?d (choi_matrix ?n ?d \<Phi>) i i) [0..<?n] = 1\<^sub>m ?d"
    using choi_ucp_iff[OF L n d] U by (simp add: UCP_def)
  have Cc': "choi_matrix ?n ?d \<Phi> \<in> carrier_mat (?n * ?d) (?n * ?d)" by (simp add: choi_matrix_def)
  show "M \<in> ucp_choi_set"
    unfolding ucp_choi_set_def
  proof (intro CollectI conjI allI impI)
    show "psd_lmat M" unfolding psd_lmat_def uM using ch by simp
    fix a b assume a: "a < ?d" and b: "b < ?d"
    show "(\<Sum>i<?n. unwrap_lm M $$ (i * ?d + a, i * ?d + b)) = (if a = b then 1 else 0)"
      unfolding uM using block_sum_entry[OF Cc' a b] ch a b by simp
  qed
next
  let ?n = "CARD('n)" and ?d = "CARD('d)"
  have n: "0 < ?n" and d: "0 < ?d" by simp_all
  fix M :: "(complex, 'n \<times> 'd, 'n \<times> 'd) lmat" assume M: "M \<in> ucp_choi_set"
  have Pc: "unwrap_lm M \<in> carrier_mat (?n * ?d) (?n * ?d)" using unwrap_lm_carrier[of M] by (simp add: card_prod)
  let ?\<Phi> = "choi_inv ?n ?d (unwrap_lm M)"
  have L: "lin_on ?n ?d (carrier_mat ?n ?n) ?\<Phi>" by (rule choi_inv_lin)
  have C: "choi_matrix ?n ?d ?\<Phi> = unwrap_lm M" by (rule choi_matrix_choi_inv[OF Pc])
  have ps: "psd (unwrap_lm M)" and bs: "\<And>a b. a < ?d \<Longrightarrow> b < ?d \<Longrightarrow>
      (\<Sum>i<?n. unwrap_lm M $$ (i * ?d + a, i * ?d + b)) = (if a = b then 1 else 0)"
    using M unfolding ucp_choi_set_def psd_lmat_def by auto
  have "msum ?d ?d (\<lambda>i. block_of_mat ?d (unwrap_lm M) i i) [0..<?n] = 1\<^sub>m ?d"
  proof (rule eq_matI)
    fix a b assume "a < dim_row (1\<^sub>m ?d)" "b < dim_col (1\<^sub>m ?d)"
    hence a: "a < ?d" and b: "b < ?d" by simp_all
    show "msum ?d ?d (\<lambda>i. block_of_mat ?d (unwrap_lm M) i i) [0..<?n] $$ (a, b) = 1\<^sub>m ?d $$ (a, b)"
      using block_sum_entry[OF Pc a b] bs[OF a b] a b by simp
  qed (use msum_carrier[of "[0..<?n]" "\<lambda>i. block_of_mat ?d (unwrap_lm M) i i" ?d ?d] in auto)
  hence "completely_positive ?n ?d ?\<Phi> \<and> unital_map ?n ?d ?\<Phi>" using choi_ucp_iff[OF L n d] C ps by simp
  hence U: "?\<Phi> \<in> UCP ?n ?d" by (simp add: UCP_def)
  have "wrap_lm (choi_matrix ?n ?d ?\<Phi>) = M" unfolding C by (rule unwrap_lm_inverse)
  thus "M \<in> (\<lambda>\<Phi>. wrap_lm (choi_matrix ?n ?d \<Phi>) :: (complex, 'n \<times> 'd, 'n \<times> 'd) lmat)
     ` {\<Phi>. lin_on ?n ?d (carrier_mat ?n ?n) \<Phi> \<and> \<Phi> \<in> UCP ?n ?d}" using L U by force
qed

corollary compact_ucp:
  "compact ((\<lambda>\<Phi>. wrap_lm (choi_matrix CARD('n) CARD('d) \<Phi>) :: (complex, 'n :: finite \<times> 'd :: finite, 'n \<times> 'd) lmat)
     ` {\<Phi>. lin_on CARD('n) CARD('d) (carrier_mat CARD('n) CARD('n)) \<Phi> \<and> \<Phi> \<in> UCP CARD('n) CARD('d)})"
  unfolding ucp_choi_image by (rule compact_ucp_choi_set)

end

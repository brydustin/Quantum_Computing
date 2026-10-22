theory HHL_Optimality
  imports HHL_Discussion
begin

section \<open>Optimality of HHL: Theorems 4--6\<close>

text \<open>App.~A5 of the paper.  Complexity classes (BQP, PSPACE, BPP, PP) and the oracle lower bounds
it cites are not in the AFP (\<open>Cook_Levin\<close> has only P and NP), so each theorem is formalised
up to the external fact it invokes: the reduction, the measurement it needs, the speedup
iteration, and the exponent arithmetic, with the cited lower bound as a hypothesis in the form
the proof uses.  The quantum search bound for Theorem 4(2) is the AFP's
\<open>Compressed_Oracles\<close> result, restated in the separate session \<open>Vern_Paulsen_QC_Search\<close>.\<close>

subsection \<open>The measurement $M_0$\<close>

text \<open>Clock in $[T,2T)$ and outcome $P$ has probability $e^{-2}/(1+e^{-2}+e^{-4})\,\norm{P\,U_T\cdots U_1\psi}^2$,
independently of $P$; with $P=\ket i\bra i$ this samples the circuit's output distribution
(the remark before Theorem 5).\<close>

context
  fixes T m :: nat and Ug :: "nat \<Rightarrow> complex Matrix.mat"
  assumes T0: "0 < T" and Ug: "\<forall>j. 1 \<le> j \<longrightarrow> j \<le> T \<longrightarrow> Ug j \<in> carrier_mat m m \<and> unitary (Ug j)"
begin


theorem red_M0_prob:
  assumes \<psi>: "dim_vec \<psi> = m" "\<parallel>\<psi>\<parallel> = 1" and P: "P \<in> carrier_mat m m"
  shows "(\<Sum>c\<in>{T..<2 * T}. \<parallel>P *\<^sub>v blk m (red_x T m Ug \<psi>) c\<parallel>\<^sup>2) / (\<Sum>c<3 * T. \<parallel>blk m (red_x T m Ug \<psi>) c\<parallel>\<^sup>2)
         = exp (- 2) / (1 + exp (- 2) + exp (- 4)) * \<parallel>P *\<^sub>v (circ m Ug T *\<^sub>v \<psi>)\<parallel>\<^sup>2"
proof -
  let ?x = "circ m Ug T *\<^sub>v \<psi>" and ?b = "blk m (red_x T m Ug \<psi>)"
  have Wm: "circ m Ug T = W T m Ug T" using W_middle[OF T0 Ug, of T] by simp
  have Cc: "circ m Ug T \<in> carrier_mat m m" using W_carrier[OF T0 Ug, of T] unfolding Wm .
  have xc: "?x \<in> carrier_vec m" by (rule carrier_vecI) (use Cc \<psi>(1) in simp)
  have nx: "\<parallel>?x\<parallel> = 1"
  proof -
    have "\<parallel>W T m Ug T *\<^sub>v \<psi>\<parallel> = \<parallel>\<psi>\<parallel>" by (rule unitary_vnorm[OF W_carrier[OF T0 Ug] W_unitary[OF T0 Ug] \<psi>(1)])
    thus ?thesis using Wm \<psi>(2) by simp
  qed
  have each: "\<parallel>P *\<^sub>v ?b c\<parallel>\<^sup>2 = \<parallel>?b c\<parallel>\<^sup>2 * \<parallel>P *\<^sub>v ?x\<parallel>\<^sup>2" if c: "c \<in> {T..<2 * T}" for c
  proof -
    let ?k = "complex_of_real (red_coeff T c)"
    have "?b c = ?k \<cdot>\<^sub>v (W T m Ug c *\<^sub>v \<psi>)" using c by (intro red_x_blocks[OF T0 Ug \<psi>(1)]) auto
    also have "W T m Ug c = circ m Ug T" using c by (intro W_middle[OF T0 Ug]) simp_all
    finally have bc: "?b c = ?k \<cdot>\<^sub>v ?x" .
    have "P *\<^sub>v ?b c = ?k \<cdot>\<^sub>v (P *\<^sub>v ?x)" unfolding bc by (rule mult_mat_vec[OF P xc])
    hence "\<parallel>P *\<^sub>v ?b c\<parallel> = cmod ?k * \<parallel>P *\<^sub>v ?x\<parallel>" by (simp add: cpx_vec_length_smult)
    moreover have "\<parallel>?b c\<parallel> = cmod ?k" unfolding bc cpx_vec_length_smult nx by simp
    ultimately show ?thesis by (simp add: power_mult_distrib)
  qed
  have "(\<Sum>c\<in>{T..<2 * T}. \<parallel>P *\<^sub>v ?b c\<parallel>\<^sup>2) = (\<Sum>c\<in>{T..<2 * T}. \<parallel>?b c\<parallel>\<^sup>2) * \<parallel>P *\<^sub>v ?x\<parallel>\<^sup>2"
    by (simp add: each sum_distrib_right)
  hence "(\<Sum>c\<in>{T..<2 * T}. \<parallel>P *\<^sub>v ?b c\<parallel>\<^sup>2) / (\<Sum>c<3 * T. \<parallel>?b c\<parallel>\<^sup>2)
         = (\<Sum>c\<in>{T..<2 * T}. \<parallel>?b c\<parallel>\<^sup>2) / (\<Sum>c<3 * T. \<parallel>?b c\<parallel>\<^sup>2) * \<parallel>P *\<^sub>v ?x\<parallel>\<^sup>2" by simp
  also have "\<dots> = exp (- 2) / (1 + exp (- 2) + exp (- 4)) * \<parallel>P *\<^sub>v ?x\<parallel>\<^sup>2"
  proof -
    have "(\<Sum>c\<in>{T..<2 * T}. \<parallel>?b c\<parallel>\<^sup>2) / (\<Sum>c<3 * T. \<parallel>?b c\<parallel>\<^sup>2) = exp (- 2) / (1 + exp (- 2) + exp (- 4))"
      by (rule red_clock_prob(1)[OF T0 Ug \<psi>])
    thus ?thesis by simp
  qed
  finally show ?thesis .
qed

end

subsection \<open>(A34): the Hermitian dilation\<close>

lemma vnorm_append_sq: "\<parallel>a @\<^sub>v c\<parallel>\<^sup>2 = \<parallel>a\<parallel>\<^sup>2 + \<parallel>c\<parallel>\<^sup>2"
proof -
  have "(\<Sum>i<dim_vec a + dim_vec c. (cmod ((a @\<^sub>v c) $ i))\<^sup>2)
        = (\<Sum>i<dim_vec a. (cmod (a $ i))\<^sup>2) + (\<Sum>j<dim_vec c. (cmod (c $ j))\<^sup>2)"
    unfolding sum_split_add by (simp add: index_append_vec)
  thus ?thesis by (simp add: cpx_vec_length_def sum_nonneg)
qed

lemma shift_bounds:
  fixes e :: real
  assumes U: "U \<in> carrier_mat n n" and iso: "\<And>v. dim_vec v = n \<Longrightarrow> \<parallel>U *\<^sub>v v\<parallel> = \<parallel>v\<parallel>"
    and v: "dim_vec v = n" and e: "0 \<le> e"
  shows "(1 - e) * \<parallel>v\<parallel> \<le> \<parallel>(1\<^sub>m n - complex_of_real e \<cdot>\<^sub>m U) *\<^sub>v v\<parallel>"
    and "\<parallel>(1\<^sub>m n - complex_of_real e \<cdot>\<^sub>m U) *\<^sub>v v\<parallel> \<le> (1 + e) * \<parallel>v\<parallel>"
proof -
  let ?u = "U *\<^sub>v v"
  have vc: "v \<in> carrier_vec n" by (rule carrier_vecI[OF v])
  have A: "(1\<^sub>m n - complex_of_real e \<cdot>\<^sub>m U) *\<^sub>v v = v - complex_of_real e \<cdot>\<^sub>v ?u"
  proof -
    have "(1\<^sub>m n - complex_of_real e \<cdot>\<^sub>m U) *\<^sub>v v = 1\<^sub>m n *\<^sub>v v - (complex_of_real e \<cdot>\<^sub>m U) *\<^sub>v v"
      by (rule minus_mult_distrib_mat_vec[OF one_carrier_mat smult_carrier_mat[OF U] vc])
    thus ?thesis using vc smult_mat_mult_vec[OF U carrier_vecI[OF v]] by simp
  qed
  have du: "dim_vec ?u = n" using U by simp
  have nu: "\<parallel>complex_of_real e \<cdot>\<^sub>v ?u\<parallel> = e * \<parallel>v\<parallel>" unfolding cpx_vec_length_smult iso[OF v] using e by simp
  show "\<parallel>(1\<^sub>m n - complex_of_real e \<cdot>\<^sub>m U) *\<^sub>v v\<parallel> \<le> (1 + e) * \<parallel>v\<parallel>"
  proof -
    have "\<parallel>v - complex_of_real e \<cdot>\<^sub>v ?u\<parallel> \<le> \<parallel>v - 0\<^sub>v n\<parallel> + \<parallel>0\<^sub>v n - complex_of_real e \<cdot>\<^sub>v ?u\<parallel>"
      by (rule vnorm_diff_le[where n = n]) (use U v du in simp_all)
    also have "\<parallel>v - 0\<^sub>v n\<parallel> = \<parallel>v\<parallel>" using v by (simp add: cpx_vec_length_def)
    also have "\<parallel>0\<^sub>v n - complex_of_real e \<cdot>\<^sub>v ?u\<parallel> = \<parallel>complex_of_real e \<cdot>\<^sub>v ?u\<parallel>" using du by (simp add: cpx_vec_length_def)
    finally show ?thesis unfolding A nu by (simp add: algebra_simps)
  qed
  show "(1 - e) * \<parallel>v\<parallel> \<le> \<parallel>(1\<^sub>m n - complex_of_real e \<cdot>\<^sub>m U) *\<^sub>v v\<parallel>"
  proof -
    have "\<bar>\<parallel>v\<parallel> - \<parallel>complex_of_real e \<cdot>\<^sub>v ?u\<parallel>\<bar> \<le> \<parallel>v - complex_of_real e \<cdot>\<^sub>v ?u\<parallel>" by (rule vnorm_reverse) (use U v in simp)
    thus ?thesis unfolding A nu by (simp add: algebra_simps abs_le_iff)
  qed
qed

lemma red_A_carrier: "red_A T m Ug \<in> carrier_mat (3 * T * m) (3 * T * m)"
  unfolding red_A_def by (rule minus_carrier_mat[OF smult_carrier_mat[OF red_U_carrier]])

lemma red_A_dagger:
  "(red_A T m Ug)\<^sup>\<dagger> = 1\<^sub>m (3 * T * m) - complex_of_real (exp (- 1 / real T)) \<cdot>\<^sub>m ((red_U T m Ug)\<^sup>\<dagger>)"
proof (rule eq_matI)
  fix i j assume "i < dim_row (1\<^sub>m (3 * T * m) - complex_of_real (exp (- 1 / real T)) \<cdot>\<^sub>m ((red_U T m Ug)\<^sup>\<dagger>))"
    "j < dim_col (1\<^sub>m (3 * T * m) - complex_of_real (exp (- 1 / real T)) \<cdot>\<^sub>m ((red_U T m Ug)\<^sup>\<dagger>))"
  hence ij: "i < 3 * T * m" "j < 3 * T * m" using carrier_matD[OF red_U_carrier[of T m Ug]] by simp_all
  show "(red_A T m Ug)\<^sup>\<dagger> $$ (i, j) = (1\<^sub>m (3 * T * m) - complex_of_real (exp (- 1 / real T)) \<cdot>\<^sub>m ((red_U T m Ug)\<^sup>\<dagger>)) $$ (i, j)"
    using ij carrier_matD[OF red_U_carrier[of T m Ug]] by (simp add: dagger_def red_A_def)
qed (simp_all add: red_A_def)

context
  fixes T m :: nat and Ug :: "nat \<Rightarrow> complex Matrix.mat"
  assumes T0: "0 < T" and Ug: "\<forall>j. 1 \<le> j \<longrightarrow> j \<le> T \<longrightarrow> Ug j \<in> carrier_mat m m \<and> unitary (Ug j)"
begin


lemma red_U_unitary: "unitary (red_U T m Ug)"
  by (rule unitary_of_isometry[OF red_U_carrier]) (rule red_U_norm[OF T0 Ug], simp)

lemma red_U_dagger_norm: "dim_vec v = 3 * T * m \<Longrightarrow> \<parallel>(red_U T m Ug)\<^sup>\<dagger> *\<^sub>v v\<parallel> = \<parallel>v\<parallel>"
  by (rule unitary_isometry[OF unitary_dagger_is_unitary[OF red_U_unitary]]) (use carrier_matD[OF red_U_carrier[of T m Ug]] in simp)

text \<open>(A34): the Hermitian dilation of $A=I-e^{-1/T}\mathcal U$ has the same condition-number bound.\<close>

theorem red_dilation:
  fixes w :: "complex Matrix.vec"
  assumes w: "dim_vec w = 3 * T * m + 3 * T * m"
  shows "hermitian (herm_embed (red_A T m Ug))"
    and "(1 - exp (- 1 / real T)) * \<parallel>w\<parallel> \<le> \<parallel>herm_embed (red_A T m Ug) *\<^sub>v w\<parallel>"
    and "\<parallel>herm_embed (red_A T m Ug) *\<^sub>v w\<parallel> \<le> (1 + exp (- 1 / real T)) * \<parallel>w\<parallel>"
proof -
  let ?D = "3 * T * m" and ?e = "exp (- 1 / real T)" and ?A = "red_A T m Ug"
  let ?a = "vec_first w ?D" and ?c = "vec_last w ?D"
  show "hermitian (herm_embed ?A)" by (rule herm_embed_hermitian[OF red_A_carrier])
  have wc: "w = ?a @\<^sub>v ?c" by (rule sym, rule vec_first_last_append, rule carrier_vecI[OF w])
  have da: "dim_vec ?a = ?D" and dc: "dim_vec ?c = ?D" by simp_all
  have Hw: "herm_embed ?A *\<^sub>v w = (?A *\<^sub>v ?c) @\<^sub>v (?A\<^sup>\<dagger> *\<^sub>v ?a)"
    by (subst wc, rule herm_embed_mult[OF red_A_carrier da dc])
  have e0: "0 \<le> ?e" and e1: "?e < 1" using T0 by simp_all
  have Ac: "(1 - ?e) * \<parallel>?c\<parallel> \<le> \<parallel>?A *\<^sub>v ?c\<parallel>" "\<parallel>?A *\<^sub>v ?c\<parallel> \<le> (1 + ?e) * \<parallel>?c\<parallel>"
    using red_A_bounds(1)[OF T0 Ug dc] red_A_bounds(2)[OF T0 Ug dc] by simp_all
  have Ad: "(1 - ?e) * \<parallel>?a\<parallel> \<le> \<parallel>?A\<^sup>\<dagger> *\<^sub>v ?a\<parallel>" "\<parallel>?A\<^sup>\<dagger> *\<^sub>v ?a\<parallel> \<le> (1 + ?e) * \<parallel>?a\<parallel>"
    unfolding red_A_dagger
    using shift_bounds[OF dagger_carrier[OF red_U_carrier] red_U_dagger_norm da e0] by simp_all
  have nw: "\<parallel>w\<parallel>\<^sup>2 = \<parallel>?a\<parallel>\<^sup>2 + \<parallel>?c\<parallel>\<^sup>2" by (subst wc, rule vnorm_append_sq)
  have nH: "\<parallel>herm_embed ?A *\<^sub>v w\<parallel>\<^sup>2 = \<parallel>?A *\<^sub>v ?c\<parallel>\<^sup>2 + \<parallel>?A\<^sup>\<dagger> *\<^sub>v ?a\<parallel>\<^sup>2" unfolding Hw by (rule vnorm_append_sq)
  have lo: "((1 - ?e) * \<parallel>w\<parallel>)\<^sup>2 \<le> \<parallel>herm_embed ?A *\<^sub>v w\<parallel>\<^sup>2"
  proof -
    have ne: "0 \<le> 1 - ?e" using e1 by simp
    have "((1 - ?e) * \<parallel>?c\<parallel>)\<^sup>2 \<le> \<parallel>?A *\<^sub>v ?c\<parallel>\<^sup>2" by (rule power_mono[OF Ac(1) mult_nonneg_nonneg[OF ne vnorm_ge0]])
    moreover have "((1 - ?e) * \<parallel>?a\<parallel>)\<^sup>2 \<le> \<parallel>?A\<^sup>\<dagger> *\<^sub>v ?a\<parallel>\<^sup>2" by (rule power_mono[OF Ad(1) mult_nonneg_nonneg[OF ne vnorm_ge0]])
    ultimately show ?thesis unfolding nH power_mult_distrib nw by (simp add: algebra_simps)
  qed
  have hi: "\<parallel>herm_embed ?A *\<^sub>v w\<parallel>\<^sup>2 \<le> ((1 + ?e) * \<parallel>w\<parallel>)\<^sup>2"
  proof -
    have "\<parallel>?A *\<^sub>v ?c\<parallel>\<^sup>2 \<le> ((1 + ?e) * \<parallel>?c\<parallel>)\<^sup>2" by (rule power_mono[OF Ac(2) vnorm_ge0])
    moreover have "\<parallel>?A\<^sup>\<dagger> *\<^sub>v ?a\<parallel>\<^sup>2 \<le> ((1 + ?e) * \<parallel>?a\<parallel>)\<^sup>2" by (rule power_mono[OF Ad(2) vnorm_ge0])
    ultimately show ?thesis unfolding nH power_mult_distrib nw by (simp add: algebra_simps)
  qed
  show "(1 - ?e) * \<parallel>w\<parallel> \<le> \<parallel>herm_embed ?A *\<^sub>v w\<parallel>" using lo by (rule power2_le_imp_le) (rule vnorm_ge0)
  show "\<parallel>herm_embed ?A *\<^sub>v w\<parallel> \<le> (1 + ?e) * \<parallel>w\<parallel>" using hi by (rule power2_le_imp_le) (use e0 vnorm_ge0[of w] in simp)
qed

theorem red_dilation_solution:
  assumes \<psi>: "dim_vec \<psi> = m"
  shows "herm_embed (red_A T m Ug) *\<^sub>v (0\<^sub>v (3 * T * m) @\<^sub>v red_x T m Ug \<psi>) = ket0 T m \<psi> @\<^sub>v 0\<^sub>v (3 * T * m)"
proof -
  have dx: "dim_vec (red_x T m Ug \<psi>) = 3 * T * m" by (rule dim_red_x[OF T0 Ug])
  have "herm_embed (red_A T m Ug) *\<^sub>v (0\<^sub>v (3 * T * m) @\<^sub>v red_x T m Ug \<psi>)
        = (red_A T m Ug *\<^sub>v red_x T m Ug \<psi>) @\<^sub>v ((red_A T m Ug)\<^sup>\<dagger> *\<^sub>v 0\<^sub>v (3 * T * m))"
    by (rule herm_embed_mult[OF red_A_carrier]) (simp_all add: dx)
  also have "red_A T m Ug *\<^sub>v red_x T m Ug \<psi> = ket0 T m \<psi>" by (rule red_inverse[OF T0 Ug \<psi>])
  also have "(red_A T m Ug)\<^sup>\<dagger> *\<^sub>v 0\<^sub>v (3 * T * m) = 0\<^sub>v (3 * T * m)"
  proof (rule eq_vecI)
    fix i assume "i < dim_vec (0\<^sub>v (3 * T * m))"
    thus "((red_A T m Ug)\<^sup>\<dagger> *\<^sub>v 0\<^sub>v (3 * T * m)) $ i = 0\<^sub>v (3 * T * m) $ i"
      using carrier_matD[OF dagger_carrier[OF red_A_carrier[of T m Ug]]] by (simp add: scalar_prod_def)
  qed (use carrier_matD[OF dagger_carrier[OF red_A_carrier[of T m Ug]]] in simp)
  finally show ?thesis .
qed

end

text \<open>The paper also demands $\kappa^{-1}I\le A\le I$, which (A34) cannot meet: its diagonal is
zero, so $\braket{e_i}{Ae_i}=0$.  What holds is $\kappa^{-1}\le\lvert A\rvert\le1$ after scaling.\<close>

lemma herm_embed_diag:
  assumes A: "A \<in> carrier_mat M N" and i: "i < M + N"
  shows "herm_embed A $$ (i, i) = 0"
  using A i by (simp add: herm_embed_def four_block_mat_def)


subsection \<open>(A36)--(A37): measuring the first qubit\<close>

text \<open>As written, $C\vec y=(\vec b,0)$ with $C=\begin{pmatrix}0&\tilde B\\\tilde B^*&0\end{pmatrix}$
forces the top half of $\vec y$ to vanish, so its first qubit is always $1$.  The fix is to
permute the whole dilation: a permutation fixing $0$ (so $\vec b=\ket0$ stays) that moves the
coordinates accepted by $M_0$ into the top half and fills the rest of it with coordinates where
the solution vanishes.  No padding is needed.\<close>

definition perm_conj :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "perm_conj n \<sigma> G = Matrix.mat n n (\<lambda>(i, j). G $$ (\<sigma> i, \<sigma> j))"

definition perm_vec :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> complex Matrix.vec \<Rightarrow> complex Matrix.vec" where
  "perm_vec n \<sigma> y = Matrix.vec n (\<lambda>i. y $ \<sigma> i)"

lemma dim_perm_vec [simp]: "dim_vec (perm_vec n \<sigma> y) = n" by (simp add: perm_vec_def)
lemma perm_conj_carrier: "perm_conj n \<sigma> G \<in> carrier_mat n n" by (simp add: perm_conj_def)

context
  fixes n :: nat and \<sigma> :: "nat \<Rightarrow> nat"
  assumes \<sigma>: "bij_betw \<sigma> {..<n} {..<n}"
begin

lemma perm_index_lt: "i < n \<Longrightarrow> \<sigma> i < n" using bij_betwE[OF \<sigma>] by blast

lemma perm_index_sum: "(\<Sum>i<n. f (\<sigma> i)) = (\<Sum>j<n. f j)"
  using sum.reindex_bij_betw[OF \<sigma>] .

lemma perm_conj_mult:
  assumes G: "G \<in> carrier_mat n n" and y: "dim_vec y = n"
  shows "perm_conj n \<sigma> G *\<^sub>v perm_vec n \<sigma> y = perm_vec n \<sigma> (G *\<^sub>v y)"
proof (rule eq_vecI)
  fix i assume "i < dim_vec (perm_vec n \<sigma> (G *\<^sub>v y))"
  hence i: "i < n" by simp
  have "(perm_conj n \<sigma> G *\<^sub>v perm_vec n \<sigma> y) $ i = (\<Sum>j<n. G $$ (\<sigma> i, \<sigma> j) * y $ \<sigma> j)"
    using i by (simp add: perm_conj_def perm_vec_def scalar_prod_def atLeast0LessThan)
  also have "\<dots> = (\<Sum>k<n. G $$ (\<sigma> i, k) * y $ k)" by (rule perm_index_sum)
  also have "\<dots> = perm_vec n \<sigma> (G *\<^sub>v y) $ i"
    using i G y perm_index_lt[OF i] by (simp add: perm_vec_def scalar_prod_def atLeast0LessThan)
  finally show "(perm_conj n \<sigma> G *\<^sub>v perm_vec n \<sigma> y) $ i = perm_vec n \<sigma> (G *\<^sub>v y) $ i" .
qed (simp add: perm_conj_def)

lemma perm_vec_norm: "dim_vec y = n \<Longrightarrow> \<parallel>perm_vec n \<sigma> y\<parallel> = \<parallel>y\<parallel>"
  using perm_index_sum[of "\<lambda>j. (cmod (y $ j))\<^sup>2"] by (simp add: cpx_vec_length_def perm_vec_def)

lemma perm_conj_hermitian:
  assumes G: "G \<in> carrier_mat n n" "hermitian G"
  shows "hermitian (perm_conj n \<sigma> G)"
proof -
  have Hd: "G\<^sup>\<dagger> = G" using G(2) by (simp add: hermitian_def)
  have "(perm_conj n \<sigma> G)\<^sup>\<dagger> = perm_conj n \<sigma> G"
  proof (rule eq_matI)
    fix i j assume "i < dim_row (perm_conj n \<sigma> G)" "j < dim_col (perm_conj n \<sigma> G)"
    hence ij: "i < n" "j < n" by (simp_all add: perm_conj_def)
    have "cnj (G $$ (\<sigma> j, \<sigma> i)) = G\<^sup>\<dagger> $$ (\<sigma> i, \<sigma> j)"
      using G(1) perm_index_lt[OF ij(1)] perm_index_lt[OF ij(2)] by (simp add: dagger_def)
    thus "(perm_conj n \<sigma> G)\<^sup>\<dagger> $$ (i, j) = perm_conj n \<sigma> G $$ (i, j)"
      unfolding Hd using ij by (simp add: perm_conj_def dagger_def)
  qed (simp_all add: perm_conj_def)
  thus ?thesis by (simp add: hermitian_def)
qed

lemma perm_vec_surj:
  assumes w: "dim_vec w = n"
  obtains y where "dim_vec y = n" "w = perm_vec n \<sigma> y"
proof
  let ?\<tau> = "inv_into {..<n} \<sigma>"
  show "dim_vec (perm_vec n ?\<tau> w) = n" by simp
  show "w = perm_vec n \<sigma> (perm_vec n ?\<tau> w)"
  proof (rule eq_vecI)
    fix i assume "i < dim_vec (perm_vec n \<sigma> (perm_vec n ?\<tau> w))"
    hence i: "i < n" by simp
    have "?\<tau> (\<sigma> i) = i" using \<sigma> i by (simp add: bij_betw_def)
    thus "w $ i = perm_vec n \<sigma> (perm_vec n ?\<tau> w) $ i" using i perm_index_lt[OF i] by (simp add: perm_vec_def)
  qed (simp add: w)
qed

end

lemma first_half_perm:
  fixes D :: nat and S :: "nat set"
  assumes S: "S \<subseteq> {D..<2 * D}" "card S < D"
  obtains \<sigma> where "bij_betw \<sigma> {..<2 * D} {..<2 * D}" "\<sigma> 0 = 0" "S \<subseteq> \<sigma> ` {..<D}" "\<sigma> ` {..<D} \<subseteq> S \<union> {..<D}"
proof -
  have fS: "finite S" using S(1) finite_subset by blast
  have "D - 1 - card S \<le> card {1..<D}" by simp
  then obtain Z where Z: "Z \<subseteq> {1..<D}" "card Z = D - 1 - card S" "finite Z"
    by (rule obtain_subset_with_card_n)
  let ?A = "S \<union> Z"
  have SZ: "S \<inter> Z = {}" using S(1) Z(1) by (force simp: subset_iff)
  have cA: "card ?A = D - 1" using card_Un_disjoint[OF fS Z(3) SZ] Z(2) S(2) by simp
  obtain h1 where h1: "bij_betw h1 {1..<D} ?A"
    using finite_same_card_bij[of "{1..<D}" ?A] cA fS Z(3) by auto
  let ?R = "{..<2 * D} - {0} - ?A"
  have A2: "?A \<subseteq> {1..<2 * D}" using S(1) Z(1) by (force simp: subset_iff)
  have cR: "card ?R = D"
  proof -
    have "?A \<subseteq> {..<2 * D} - {0}" using A2 by auto
    hence "card ?R = card ({..<2 * D} - {0}) - card ?A" by (intro card_Diff_subset) (use fS Z(3) in auto)
    also have "card ({..<2 * D} - {0}) = 2 * D - 1" using S(2) by (simp add: card_Diff_singleton)
    finally show ?thesis using cA S(2) by simp
  qed
  obtain h2 where h2: "bij_betw h2 {D..<2 * D} ?R"
    using finite_same_card_bij[of "{D..<2 * D}" ?R] cR by auto
  define \<sigma> where "\<sigma> i = (if i = 0 then 0 else if i < D then h1 i else h2 i)" for i
  have b0: "bij_betw \<sigma> {0} {0}" by (simp add: \<sigma>_def bij_betw_def)
  have b1: "bij_betw \<sigma> {1..<D} ?A" using h1 by (rule bij_betw_cong[THEN iffD1, rotated]) (simp add: \<sigma>_def)
  have b2: "bij_betw \<sigma> {D..<2 * D} ?R"
    using h2 by (rule bij_betw_cong[THEN iffD1, rotated]) (use S(2) in \<open>auto simp: \<sigma>_def\<close>)
  have b01: "bij_betw \<sigma> ({0} \<union> {1..<D}) ({0} \<union> ?A)" by (rule bij_betw_combine[OF b0 b1]) (use A2 in auto)
  have "bij_betw \<sigma> (({0} \<union> {1..<D}) \<union> {D..<2 * D}) (({0} \<union> ?A) \<union> ?R)"
    by (rule bij_betw_combine[OF b01 b2]) auto
  moreover have "({0} \<union> {1..<D}) \<union> {D..<2 * D} = {..<2 * D}" using S(2) by auto
  moreover have "({0} \<union> ?A) \<union> ?R = {..<2 * D}" using A2 S(2) by auto
  ultimately have bij: "bij_betw \<sigma> {..<2 * D} {..<2 * D}" by simp
  have img: "\<sigma> ` {..<D} = {0} \<union> ?A"
  proof -
    have "{..<D} = {0} \<union> {1..<D}" using S(2) by auto
    thus ?thesis using bij_betw_imp_surj_on[OF b01] by simp
  qed
  show ?thesis
  proof
    show "bij_betw \<sigma> {..<2 * D} {..<2 * D}" by (rule bij)
    show "\<sigma> 0 = 0" by (simp add: \<sigma>_def)
    show "S \<subseteq> \<sigma> ` {..<D}" unfolding img by auto
    show "\<sigma> ` {..<D} \<subseteq> S \<union> {..<D}" unfolding img using Z(1) S(2) by auto
  qed
qed

lemma proj_set_norm:
  assumes A: "A \<subseteq> {..<m}" and v: "dim_vec v = m"
  shows "\<parallel>proj_set m A *\<^sub>v v\<parallel>\<^sup>2 = (\<Sum>i\<in>A. (cmod (v $ i))\<^sup>2)"
proof -
  have e: "(proj_set m A *\<^sub>v v) $ i = (if i \<in> A then v $ i else 0)" if i: "i < m" for i
    using i by (simp add: proj_set_mult_vec[OF v])
  have d: "dim_vec (proj_set m A *\<^sub>v v) = m" by simp
  have "\<parallel>proj_set m A *\<^sub>v v\<parallel>\<^sup>2 = (\<Sum>i<m. (cmod ((proj_set m A *\<^sub>v v) $ i))\<^sup>2)"
    unfolding cpx_vec_length_def d by (simp add: sum_nonneg)
  also have "\<dots> = (\<Sum>i<m. (cmod (if i \<in> A then v $ i else 0))\<^sup>2)" by (rule sum.cong[OF refl]) (subst e, simp_all)
  also have "\<dots> = (\<Sum>i\<in>A. (cmod (v $ i))\<^sup>2)"
    using A by (intro sum.mono_neutral_cong_right) auto
  finally show ?thesis .
qed

lemma acc_set:
  fixes T m D :: nat and A :: "nat set"
  assumes T0: "0 < T" and m: "0 < m" and A: "A \<subseteq> {..<m}" and D: "D = 3 * T * m"
  defines "S \<equiv> (\<lambda>(c, i). D + c * m + i) ` ({T..<2 * T} \<times> A)"
  shows "S \<subseteq> {D..<2 * D}" and "card S < D" and "inj_on (\<lambda>(c, i). D + c * m + i) ({T..<2 * T} \<times> A)"
proof -
  show inj: "inj_on (\<lambda>(c, i). D + c * m + i) ({T..<2 * T} \<times> A)"
  proof (rule inj_onI, clarify)
    fix c i c' i' assume "c \<in> {T..<2 * T}" "i \<in> A" "c' \<in> {T..<2 * T}" "i' \<in> A" and e: "D + c * m + i = D + c' * m + i'"
    hence im: "i < m" "i' < m" using A by auto
    have e': "c * m + i = c' * m + i'" using e by simp
    have "c = c'" using arg_cong[OF e', of "\<lambda>r. r div m"] im m by simp
    moreover have "i = i'" using arg_cong[OF e', of "\<lambda>r. r mod m"] im by simp
    ultimately show "c = c' \<and> i = i'" by simp
  qed
  show "S \<subseteq> {D..<2 * D}"
  proof
    fix r assume "r \<in> S"
    then obtain c i where c: "T \<le> c" "c < 2 * T" and i: "i \<in> A" and r: "r = D + c * m + i" unfolding S_def by auto
    have "c * m + i < 2 * T * m + m" using c i A by (intro add_less_le_mono mult_strict_right_mono) (auto simp: m)
    also have "\<dots> \<le> D" using D T0 by (simp add: algebra_simps)
    finally show "r \<in> {D..<2 * D}" using r by simp
  qed
  have fA: "finite A" using A finite_subset by blast
  have "card S \<le> card ({T..<2 * T} \<times> A)" unfolding S_def by (rule card_image_le) (simp add: fA)
  also have "\<dots> = T * card A" by (simp add: card_cartesian_product)
  also have "\<dots> \<le> T * m" using card_mono[OF _ A] by simp
  also have "\<dots> < D" using D T0 m by simp
  finally show "card S < D" .
qed

context
  fixes T m :: nat and Ug :: "nat \<Rightarrow> complex Matrix.mat"
  assumes T0: "0 < T" and Ug: "\<forall>j. 1 \<le> j \<longrightarrow> j \<le> T \<longrightarrow> Ug j \<in> carrier_mat m m \<and> unitary (Ug j)"
begin

lemma opt_circ_dim: "dim_vec (circ m Ug T *\<^sub>v v) = m" using W_carrier[OF T0 Ug, of T] W_middle[OF T0 Ug, of T] by simp

lemma ket0_unit: "0 < m \<Longrightarrow> ket0 T m (unit_vec m 0) @\<^sub>v 0\<^sub>v (3 * T * m) = unit_vec (3 * T * m + 3 * T * m) 0"
proof -
  assume m: "0 < m"
  have k: "ket0 T m (unit_vec m 0) = reg_sum (3 * T) m (\<lambda>c. if c = 0 then unit_vec m 0 else 0\<^sub>v m)"
    by (rule ket0_def[OF T0 Ug])
  show ?thesis
  proof (rule eq_vecI)
    fix r assume "r < dim_vec (unit_vec (3 * T * m + 3 * T * m) 0)"
    hence r: "r < 3 * T * m + 3 * T * m" by simp
    show "(ket0 T m (unit_vec m 0) @\<^sub>v 0\<^sub>v (3 * T * m)) $ r = unit_vec (3 * T * m + 3 * T * m) 0 $ r"
    proof (cases "r < 3 * T * m")
      case True
      have "r div m = 0 \<and> r mod m = 0 \<longleftrightarrow> r = 0" using m by (metis div_mult_mod_eq mult_0_right add_0 div_0 mod_0)
      thus ?thesis using True r m unfolding k by (auto simp: reg_sum_def index_append_vec unit_vec_def)
    next
      case False
      thus ?thesis using r unfolding k by (auto simp: index_append_vec unit_vec_def)
    qed
  qed (simp add: k)
qed

theorem red_first_qubit:
  assumes m: "0 < m" and A: "A \<subseteq> {..<m}"
  defines "Dm \<equiv> 3 * T * m"
  obtains \<sigma> where "bij_betw \<sigma> {..<Dm + Dm} {..<Dm + Dm}" and "\<sigma> 0 = 0"
    and "hermitian (perm_conj (Dm + Dm) \<sigma> (herm_embed (red_A T m Ug)))"
    and "\<And>w. dim_vec w = Dm + Dm \<Longrightarrow> (1 - exp (- 1 / real T)) * \<parallel>w\<parallel> \<le> \<parallel>perm_conj (Dm + Dm) \<sigma> (herm_embed (red_A T m Ug)) *\<^sub>v w\<parallel>
              \<and> \<parallel>perm_conj (Dm + Dm) \<sigma> (herm_embed (red_A T m Ug)) *\<^sub>v w\<parallel> \<le> (1 + exp (- 1 / real T)) * \<parallel>w\<parallel>"
    and "perm_conj (Dm + Dm) \<sigma> (herm_embed (red_A T m Ug)) *\<^sub>v perm_vec (Dm + Dm) \<sigma> (0\<^sub>v Dm @\<^sub>v red_x T m Ug (unit_vec m 0))
           = unit_vec (Dm + Dm) 0"
    and "(\<Sum>i<Dm. (cmod (perm_vec (Dm + Dm) \<sigma> (0\<^sub>v Dm @\<^sub>v red_x T m Ug (unit_vec m 0)) $ i))\<^sup>2)
           / \<parallel>perm_vec (Dm + Dm) \<sigma> (0\<^sub>v Dm @\<^sub>v red_x T m Ug (unit_vec m 0))\<parallel>\<^sup>2
         = exp (- 2) / (1 + exp (- 2) + exp (- 4)) * (\<Sum>i\<in>A. (cmod ((circ m Ug T *\<^sub>v unit_vec m 0) $ i))\<^sup>2)"
proof -
  let ?\<psi> = "unit_vec m 0 :: complex Matrix.vec" and ?H = "herm_embed (red_A T m Ug)"
  let ?x = "red_x T m Ug ?\<psi>" and ?f = "\<lambda>(c, i). Dm + c * m + i"
  let ?z = "0\<^sub>v Dm @\<^sub>v ?x"
  define S where "S = ?f ` ({T..<2 * T} \<times> A)"
  have S: "S \<subseteq> {Dm..<2 * Dm}" "card S < Dm" "inj_on ?f ({T..<2 * T} \<times> A)"
    unfolding S_def using acc_set[OF T0 m A, of Dm] by (simp_all add: Dm_def)
  obtain \<sigma> where \<sigma>: "bij_betw \<sigma> {..<2 * Dm} {..<2 * Dm}" "\<sigma> 0 = 0" "S \<subseteq> \<sigma> ` {..<Dm}" "\<sigma> ` {..<Dm} \<subseteq> S \<union> {..<Dm}"
    by (rule first_half_perm[OF S(1,2)])
  have DmDm: "2 * Dm = Dm + Dm" by simp
  have bij: "bij_betw \<sigma> {..<Dm + Dm} {..<Dm + Dm}" using \<sigma>(1) unfolding DmDm .
  let ?C = "perm_conj (Dm + Dm) \<sigma> ?H"
  have Hc: "?H \<in> carrier_mat (Dm + Dm) (Dm + Dm)" unfolding Dm_def by (rule herm_embed_carrier[OF red_A_carrier])
  have dx: "dim_vec ?x = Dm" unfolding Dm_def by (rule dim_red_x[OF T0 Ug])
  have dz: "dim_vec ?z = Dm + Dm" using dx by simp
  have \<psi>: "dim_vec ?\<psi> = m" "\<parallel>?\<psi>\<parallel> = 1" using m by (simp_all add: cpx_vec_length_def unit_vec_def lessThan_atLeast0 sum.atLeast_Suc_lessThan[OF m])
  show ?thesis
  proof
    show "bij_betw \<sigma> {..<Dm + Dm} {..<Dm + Dm}" by (rule bij)
    show "\<sigma> 0 = 0" by (rule \<sigma>(2))
    show "hermitian ?C" by (rule perm_conj_hermitian[OF bij Hc herm_embed_hermitian[OF red_A_carrier]])
    fix w :: "complex Matrix.vec" assume w: "dim_vec w = Dm + Dm"
    obtain y where y: "dim_vec y = Dm + Dm" "w = perm_vec (Dm + Dm) \<sigma> y" by (rule perm_vec_surj[OF bij w])
    have Cw: "?C *\<^sub>v w = perm_vec (Dm + Dm) \<sigma> (?H *\<^sub>v y)" unfolding y(2) by (rule perm_conj_mult[OF bij Hc y(1)])
    have nCw: "\<parallel>?C *\<^sub>v w\<parallel> = \<parallel>?H *\<^sub>v y\<parallel>" unfolding Cw by (rule perm_vec_norm[OF bij]) (use Hc in simp)
    have nw: "\<parallel>w\<parallel> = \<parallel>y\<parallel>" unfolding y(2) by (rule perm_vec_norm[OF bij y(1)])
    have yD: "dim_vec y = 3 * T * m + 3 * T * m" using y(1) by (simp add: Dm_def)
    show "(1 - exp (- 1 / real T)) * \<parallel>w\<parallel> \<le> \<parallel>?C *\<^sub>v w\<parallel> \<and> \<parallel>?C *\<^sub>v w\<parallel> \<le> (1 + exp (- 1 / real T)) * \<parallel>w\<parallel>"
      unfolding nCw nw using red_dilation(2)[OF T0 Ug yD] red_dilation(3)[OF T0 Ug yD] by simp
  next
    have "?C *\<^sub>v perm_vec (Dm + Dm) \<sigma> ?z = perm_vec (Dm + Dm) \<sigma> (?H *\<^sub>v ?z)" by (rule perm_conj_mult[OF bij Hc dz])
    also have "?H *\<^sub>v ?z = unit_vec (Dm + Dm) 0" using red_dilation_solution[OF T0 Ug \<psi>(1)] ket0_unit[OF m] by (simp add: Dm_def)
    also have "perm_vec (Dm + Dm) \<sigma> (unit_vec (Dm + Dm) 0) = unit_vec (Dm + Dm) 0"
    proof (rule eq_vecI)
      fix i assume "i < dim_vec (unit_vec (Dm + Dm) 0)"
      hence i: "i < Dm + Dm" by simp
      have "\<sigma> i = 0 \<longleftrightarrow> i = 0" using \<sigma>(2) bij_betw_imp_inj_on[OF bij] i by (metis inj_onD lessThan_iff zero_less_iff_neq_zero not_less0 add_pos_pos)
      thus "perm_vec (Dm + Dm) \<sigma> (unit_vec (Dm + Dm) 0) $ i = unit_vec (Dm + Dm) 0 $ i"
        using i perm_index_lt[OF bij i] by (simp add: perm_vec_def unit_vec_def)
    qed simp
    finally show "?C *\<^sub>v perm_vec (Dm + Dm) \<sigma> ?z = unit_vec (Dm + Dm) 0" .
  next
    let ?y = "perm_vec (Dm + Dm) \<sigma> ?z"
    have z_lo: "j < Dm \<Longrightarrow> ?z $ j = 0" for j using dx by (simp add: index_append_vec)
    have z_hi: "?z $ (Dm + r) = ?x $ r" if "r < Dm" for r using that dx by (simp add: index_append_vec)
    have inj: "inj_on \<sigma> {..<Dm}" using bij_betw_imp_inj_on[OF bij] by (rule inj_on_subset) auto
    have top: "(\<Sum>i<Dm. (cmod (?y $ i))\<^sup>2) = (\<Sum>j\<in>S. (cmod (?z $ j))\<^sup>2)"
    proof -
      have "(\<Sum>i<Dm. (cmod (?y $ i))\<^sup>2) = (\<Sum>i<Dm. (cmod (?z $ \<sigma> i))\<^sup>2)" by (rule sum.cong) (simp_all add: perm_vec_def)
      also have "\<dots> = (\<Sum>j\<in>\<sigma> ` {..<Dm}. (cmod (?z $ j))\<^sup>2)" by (rule sum.reindex[OF inj, symmetric, unfolded comp_def])
      also have "\<dots> = (\<Sum>j\<in>S. (cmod (?z $ j))\<^sup>2)"
      proof (rule sum.mono_neutral_cong_right)
        show "finite (\<sigma> ` {..<Dm})" by simp
        show "S \<subseteq> \<sigma> ` {..<Dm}" by (rule \<sigma>(3))
        show "\<forall>j\<in>\<sigma> ` {..<Dm} - S. (cmod (?z $ j))\<^sup>2 = 0" using \<sigma>(4) z_lo by auto
      qed simp
      finally show ?thesis .
    qed
    have acc: "(\<Sum>j\<in>S. (cmod (?z $ j))\<^sup>2) = (\<Sum>c\<in>{T..<2 * T}. \<parallel>proj_set m A *\<^sub>v blk m ?x c\<parallel>\<^sup>2)"
    proof -
      have "(\<Sum>j\<in>S. (cmod (?z $ j))\<^sup>2) = (\<Sum>p\<in>{T..<2 * T} \<times> A. (cmod (?z $ ?f p))\<^sup>2)"
        unfolding S_def by (rule sum.reindex[OF S(3), unfolded comp_def])
      also have "\<dots> = (\<Sum>c\<in>{T..<2 * T}. \<Sum>i\<in>A. (cmod (?x $ (c * m + i)))\<^sup>2)"
      proof -
        have eq: "(cmod (?z $ (Dm + c * m + i)))\<^sup>2 = (cmod (?x $ (c * m + i)))\<^sup>2" if "c \<in> {T..<2 * T}" "i \<in> A" for c i
        proof -
          have "c * m + i < 2 * T * m + m" using that A by (intro add_less_le_mono mult_strict_right_mono) (auto simp: m)
          also have "\<dots> \<le> Dm" using T0 by (simp add: Dm_def algebra_simps)
          finally show ?thesis using z_hi[of "c * m + i"] by (simp add: add.assoc)
        qed
        have "(\<Sum>p\<in>{T..<2 * T} \<times> A. (cmod (?z $ ?f p))\<^sup>2) = (\<Sum>(c, i)\<in>{T..<2 * T} \<times> A. (cmod (?x $ (c * m + i)))\<^sup>2)"
          by (rule sum.cong[OF refl]) (use eq in auto)
        also have "\<dots> = (\<Sum>c\<in>{T..<2 * T}. \<Sum>i\<in>A. (cmod (?x $ (c * m + i)))\<^sup>2)" by (rule sum.cartesian_product[symmetric])
        finally show ?thesis .
      qed
      also have "\<dots> = (\<Sum>c\<in>{T..<2 * T}. \<parallel>proj_set m A *\<^sub>v blk m ?x c\<parallel>\<^sup>2)"
        by (rule sum.cong[OF refl]) (use A in \<open>simp add: proj_set_norm blk_def subset_iff\<close>)
      finally show ?thesis .
    qed
    have ny: "\<parallel>?y\<parallel>\<^sup>2 = (\<Sum>c<3 * T. \<parallel>blk m ?x c\<parallel>\<^sup>2)"
    proof -
      have "\<parallel>?y\<parallel> = \<parallel>?z\<parallel>" by (rule perm_vec_norm[OF bij dz])
      hence "\<parallel>?y\<parallel>\<^sup>2 = \<parallel>0\<^sub>v Dm\<parallel>\<^sup>2 + \<parallel>?x\<parallel>\<^sup>2" using vnorm_append_sq by simp
      also have "\<parallel>0\<^sub>v Dm\<parallel> = 0" by (simp add: cpx_vec_length_def)
      also have "\<parallel>?x\<parallel>\<^sup>2 = (\<Sum>c<3 * T. \<parallel>blk m ?x c\<parallel>\<^sup>2)"
        using vnorm_reg_sum_sq[of "3 * T" "blk m ?x" m] reg_sum_blk[of ?x "3 * T" m] dx by (simp add: Dm_def)
      finally show ?thesis by simp
    qed
    show "(\<Sum>i<Dm. (cmod (?y $ i))\<^sup>2) / \<parallel>?y\<parallel>\<^sup>2
         = exp (- 2) / (1 + exp (- 2) + exp (- 4)) * (\<Sum>i\<in>A. (cmod ((circ m Ug T *\<^sub>v ?\<psi>) $ i))\<^sup>2)"
      unfolding top acc ny red_M0_prob[OF T0 Ug \<psi> proj_set_carrier]
      using proj_set_norm[OF A] opt_circ_dim by simp
  qed
qed

end

subsection \<open>Theorem 4: the speedup iteration\<close>

text \<open>If inversion took time $\kappa^{1-\delta}\mathrm{polylog}$, one step turns a $T$-gate circuit into one
with $T'\le T^{1-\delta}g$ gates, $g$ polynomial in the qubit count.  Iterating while
$T_{i+1}\le T_i^{1-\delta/2}$ ends with $T_\ell\le\max(g^{2/\delta},T_0^{(1-\delta/2)^m})$.\<close>

lemma speedup_powers:
  fixes T :: "nat \<Rightarrow> real" and \<delta> :: real
  assumes d: "0 < \<delta>" "\<delta> < 1" and T1: "\<And>i. i \<le> l \<Longrightarrow> 1 \<le> T i"
    and run: "\<And>i. i < l \<Longrightarrow> T (Suc i) \<le> T i powr (1 - \<delta> / 2)"
  shows "i \<le> l \<Longrightarrow> T i \<le> T 0 powr ((1 - \<delta> / 2) ^ i)"
proof (induction i)
  case 0
  show ?case using T1[of 0] by simp
next
  case (Suc i)
  have "T (Suc i) \<le> T i powr (1 - \<delta> / 2)" using run Suc.prems by simp
  also have "\<dots> \<le> (T 0 powr ((1 - \<delta> / 2) ^ i)) powr (1 - \<delta> / 2)"
    using Suc T1[of i] d by (intro powr_mono2) simp_all
  also have "\<dots> = T 0 powr ((1 - \<delta> / 2) ^ Suc i)" by (simp add: powr_powr mult.commute)
  finally show ?case .
qed

lemma speedup_stop:
  fixes x y g \<delta> :: real
  assumes d: "0 < \<delta>" and x: "1 \<le> x" and lo: "x powr (1 - \<delta> / 2) < y" and hi: "y \<le> x powr (1 - \<delta>) * g"
  shows "x < g powr (2 / \<delta>)"
proof -
  have "x powr (1 - \<delta>) * x powr (\<delta> / 2) < x powr (1 - \<delta>) * g"
    using lo hi by (simp add: powr_add[symmetric])
  hence xg: "x powr (\<delta> / 2) < g" using x by simp
  have "x = (x powr (\<delta> / 2)) powr (2 / \<delta>)" using d x by (simp add: powr_powr)
  also have "\<dots> < g powr (2 / \<delta>)" using xg d by (intro powr_less_mono2) simp_all
  finally show ?thesis .
qed

theorem speedup_iteration:
  fixes T :: "nat \<Rightarrow> real" and \<delta> g :: real
  assumes d: "0 < \<delta>" "\<delta> < 1" and lm: "l \<le> m" and T1: "\<And>i. i \<le> Suc l \<Longrightarrow> 1 \<le> T i"
    and run: "\<And>i. i < l \<Longrightarrow> T (Suc i) \<le> T i powr (1 - \<delta> / 2)"
    and stop: "l < m \<Longrightarrow> T l powr (1 - \<delta> / 2) < T (Suc l) \<and> T (Suc l) \<le> T l powr (1 - \<delta>) * g"
  shows "T l \<le> max (g powr (2 / \<delta>)) (T 0 powr ((1 - \<delta> / 2) ^ m))"
proof (cases "l < m")
  case True
  have "T l < g powr (2 / \<delta>)" using stop[OF True] T1[of l] d by (intro speedup_stop[of \<delta> _ "T (Suc l)"]) simp_all
  thus ?thesis by simp
next
  case False
  hence "l = m" using lm by simp
  thus ?thesis using speedup_powers[OF d, of l T l] T1 run by simp
qed

lemma qubit_growth:
  fixes T n :: "nat \<Rightarrow> real" and \<delta> :: real
  assumes d: "0 < \<delta>" "\<delta> < 1" and T1: "\<And>i. i \<le> l \<Longrightarrow> 1 \<le> T i"
    and run: "\<And>i. i < l \<Longrightarrow> T (Suc i) \<le> T i powr (1 - \<delta> / 2)"
    and grow: "\<And>i. i < l \<Longrightarrow> n (Suc i) = n i + log 2 (18 * T i)"
  shows "i \<le> l \<Longrightarrow> n i \<le> n 0 + i * log 2 18 + 2 / \<delta> * log 2 (T 0)"
proof -
  let ?r = "1 - \<delta> / 2"
  have L0: "0 \<le> log 2 (T 0)" using T1[of 0] by simp
  have step: "i \<le> l \<Longrightarrow> n i \<le> n 0 + i * log 2 18 + (\<Sum>j<i. ?r ^ j) * log 2 (T 0)" for i
  proof (induction i)
    case (Suc i)
    have Ti: "T i \<le> T 0 powr (?r ^ i)" using speedup_powers[where T = T and l = l, OF d T1 run] Suc.prems by simp
    have "log 2 (T i) \<le> log 2 (T 0 powr (?r ^ i))" using T1[of i] Suc.prems Ti by (intro log_mono) simp_all
    also have "\<dots> = ?r ^ i * log 2 (T 0)" using T1[of 0] by (simp add: log_powr)
    finally have lt: "log 2 (T i) \<le> ?r ^ i * log 2 (T 0)" .
    have "n (Suc i) = n i + log 2 18 + log 2 (T i)" using grow[of i] Suc.prems T1[of i] by (simp add: log_mult)
    also have "\<dots> \<le> n 0 + i * log 2 18 + (\<Sum>j<i. ?r ^ j) * log 2 (T 0) + log 2 18 + ?r ^ i * log 2 (T 0)"
      using Suc lt by simp
    finally show ?case by (simp add: algebra_simps)
  qed simp
  have geo: "(\<Sum>j<i. ?r ^ j) \<le> 2 / \<delta>" for i
  proof -
    have "(\<Sum>j<i. ?r ^ j) = (1 - ?r ^ i) / (1 - ?r)" using d by (simp add: sum_gp_strict)
    also have "\<dots> \<le> 1 / (1 - ?r)" using d by (intro divide_right_mono) simp_all
    finally show ?thesis by simp
  qed
  assume "i \<le> l"
  thus ?thesis using step[of i] mult_right_mono[OF geo[of i] L0] by simp
qed

lemma corrected_rounds:
  fixes \<delta> n0 T0 :: real
  assumes d: "0 < \<delta>" "\<delta> < 1" and n0: "1 \<le> n0" and T0: "0 \<le> T0" "T0 \<le> 2 powr (2 * n0)"
    and m: "2 / \<delta> * ln (2 * n0) \<le> real m"
  shows "T0 powr ((1 - \<delta> / 2) ^ m) \<le> 2"
proof -
  let ?r = "(1 - \<delta> / 2) ^ m"
  have "?r \<le> exp (- \<delta> / 2) ^ m"
    using exp_ge_add_one_self[of "- \<delta> / 2"] d by (intro power_mono) simp_all
  also have "\<dots> = exp (- (\<delta> / 2 * real m))" by (simp add: exp_of_nat_mult[symmetric] mult.commute)
  also have "\<dots> \<le> exp (- ln (2 * n0))" using m d by (simp add: field_simps)
  also have "\<dots> = 1 / (2 * n0)" using n0 by (simp add: exp_minus inverse_eq_divide)
  finally have r: "2 * n0 * ?r \<le> 1" using n0 by (simp add: field_simps)
  have r0: "0 \<le> ?r" using d by simp
  have "T0 powr ?r \<le> (2 powr (2 * n0)) powr ?r" using T0 r0 by (intro powr_mono2) simp_all
  also have "\<dots> = 2 powr (2 * n0 * ?r)" by (simp add: powr_powr)
  also have "\<dots> \<le> 2 powr 1" using r by (intro powr_mono) simp_all
  finally show ?thesis by simp
qed

lemma paper_rounds_insufficient:
  shows "2 / (1 / 2) * log 2 (2 * 2 ^ 64) / log 2 (log 2 (2 ^ 64)) = (130 / 3 :: real)"
    and "m \<le> 44 \<Longrightarrow> (2 ^ 64 :: real) < (2 powr (2 * 2 ^ 64)) powr ((1 - (1 / 2) / 2) ^ m)"
proof -
  have l65: "log 2 (2 * 2 ^ 64 :: real) = 65" using log_nat_power[of "2 :: real" 2 65] by simp
  have l6: "log 2 (log 2 (2 ^ 64 :: real)) = 6"
    using log_nat_power[of "2 :: real" 2 64] log_nat_power[of "2 :: real" 2 6] by simp
  show "2 / (1 / 2) * log 2 (2 * 2 ^ 64) / log 2 (log 2 (2 ^ 64)) = (130 / 3 :: real)" unfolding l65 l6 by simp
  assume m: "m \<le> 44"
  have p: "(3 / 4 :: real) ^ 44 \<le> (3 / 4) ^ m" using m by (intro power_decreasing) simp_all
  have "64 < 2 * 2 ^ 64 * (3 / 4 :: real) ^ 44" by (simp add: power_divide)
  also have "\<dots> \<le> 2 * 2 ^ 64 * (3 / 4) ^ m" by (rule mult_left_mono[OF p]) simp
  finally have e0: "64 < 2 * 2 ^ 64 * (3 / 4 :: real) ^ m" .
  have q: "1 - (1 / 2) / 2 = (3 / 4 :: real)" by simp
  have e: "64 < 2 * 2 ^ 64 * (1 - (1 / 2) / 2 :: real) ^ m" unfolding q by (rule e0)
  have "(2 ^ 64 :: real) = 2 powr 64" by (simp add: powr_realpow)
  also have "\<dots> < 2 powr (2 * 2 ^ 64 * (1 - (1 / 2) / 2) ^ m)" using e by (intro powr_less_mono) simp_all
  also have "\<dots> = (2 powr (2 * 2 ^ 64)) powr ((1 - (1 / 2) / 2) ^ m)" by (rule powr_powr[symmetric])
  finally show "(2 ^ 64 :: real) < (2 powr (2 * 2 ^ 64)) powr ((1 - (1 / 2) / 2) ^ m)" .
qed

text \<open>The paper takes $m=\frac2\delta\log(2n)/\log\log n$ and claims $T_m\le n_0$.  That $m$ is too
small: for $n_0=2^{64}$, $\delta=\frac12$ it is $130/3$, and $T_0^{(3/4)^{44}}$ with $T_0=2^{2n_0}$
still exceeds $2^{64}$.  Taking $m\ge\frac2\delta\ln(2n_0)$ gives $T_m\le2$.\<close>

theorem speedup_collapse:
  fixes T :: "nat \<Rightarrow> real" and \<delta> g n0 :: real
  assumes d: "0 < \<delta>" "\<delta> < 1" and n0: "1 \<le> n0" and T0: "T 0 \<le> 2 powr (2 * n0)"
    and m: "2 / \<delta> * ln (2 * n0) \<le> real m" and lm: "l \<le> m" and T1: "\<And>i. i \<le> Suc l \<Longrightarrow> 1 \<le> T i"
    and run: "\<And>i. i < l \<Longrightarrow> T (Suc i) \<le> T i powr (1 - \<delta> / 2)"
    and stop: "l < m \<Longrightarrow> T l powr (1 - \<delta> / 2) < T (Suc l) \<and> T (Suc l) \<le> T l powr (1 - \<delta>) * g"
  shows "T l \<le> max (g powr (2 / \<delta>)) 2"
proof -
  have "T 0 powr ((1 - \<delta> / 2) ^ m) \<le> 2" using T1[of 0] by (intro corrected_rounds[OF d n0 _ T0 m]) simp
  moreover have "T l \<le> max (g powr (2 / \<delta>)) (T 0 powr ((1 - \<delta> / 2) ^ m))"
    by (rule speedup_iteration[OF d lm T1 run stop]) simp_all
  ultimately show ?thesis by linarith
qed


subsection \<open>Growth rates\<close>

lemma exp_beats_poly:
  fixes a C k :: real and s :: nat
  assumes a: "0 < a" and k: "0 \<le> k"
  shows "\<exists>n\<ge>s. C * (real n + 1) powr k < 2 powr (a * real n)"
proof -
  define K where "K = nat \<lceil>k\<rceil>"
  define c where "c = min (a * ln 2 / (K + 1)) 1"
  have c0: "0 < c" using a by (simp add: c_def)
  define n where "n = max s (nat \<lceil>C / c ^ (K + 1)\<rceil>)"
  have s: "s \<le> n" by (simp add: n_def)
  have pos: "0 < 2 powr (a * real n)" by simp
  have lb: "(c * (real n + 1)) ^ (K + 1) \<le> 2 powr (a * real n)"
  proof -
    have "c * (real n + 1) \<le> 1 + a * ln 2 / (K + 1) * real n"
    proof -
      have "c * real n \<le> a * ln 2 / (K + 1) * real n" by (intro mult_right_mono) (simp_all add: c_def)
      moreover have "c \<le> 1" by (simp add: c_def)
      ultimately show ?thesis by (simp add: distrib_left)
    qed
    also have "\<dots> \<le> exp (a * ln 2 / (K + 1) * real n)" by (rule exp_ge_add_one_self)
    finally have "(c * (real n + 1)) ^ (K + 1) \<le> exp (a * ln 2 / (K + 1) * real n) ^ (K + 1)"
      using c0 by (intro power_mono) simp_all
    also have "\<dots> = exp (real (K + 1) * (a * ln 2 / (K + 1) * real n))" by (rule exp_of_nat_mult[symmetric])
    also have "\<dots> = 2 powr (a * real n)" by (simp add: powr_def)
    finally show ?thesis .
  qed
  show ?thesis
  proof (cases "C \<le> 0")
    case True
    hence "C * (real n + 1) powr k \<le> 0" by (simp add: mult_nonpos_nonneg)
    hence "C * (real n + 1) powr k < 2 powr (a * real n)" using pos by linarith
    thus ?thesis using s by blast
  next
    case False
    have Kk: "k \<le> real K" unfolding K_def using k le_of_int_ceiling[of k] by linarith
    have "(real n + 1) powr k \<le> (real n + 1) powr real K" using Kk by (intro powr_mono) simp_all
    also have "\<dots> = (real n + 1) ^ K" by (simp add: powr_realpow)
    finally have p: "(real n + 1) powr k \<le> (real n + 1) ^ K" .
    have cK: "0 < c ^ (K + 1)" using c0 by simp
    have "C / c ^ (K + 1) \<le> real n" unfolding n_def by linarith
    hence "C < c ^ (K + 1) * (real n + 1)" using cK by (simp add: divide_le_eq algebra_simps)
    hence "C * (real n + 1) ^ K < c ^ (K + 1) * (real n + 1) * (real n + 1) ^ K" by simp
    also have "\<dots> = (c * (real n + 1)) ^ (K + 1)" by (simp add: power_mult_distrib)
    finally have "C * (real n + 1) ^ K < 2 powr (a * real n)" using lb by simp
    moreover have "C * (real n + 1) powr k \<le> C * (real n + 1) ^ K" using p False by simp
    ultimately have "C * (real n + 1) powr k < 2 powr (a * real n)" by linarith
    thus ?thesis using s by blast
  qed
qed

lemma rate_bound:
  fixes a b C k :: real
  assumes k: "0 \<le> k" and h: "\<And>n. n1 \<le> n \<Longrightarrow> 2 powr (a * real n) \<le> C * (real n + 1) powr k * 2 powr (b * real n)"
  shows "a \<le> b"
proof (rule ccontr)
  assume "\<not> a \<le> b"
  then obtain n where n: "n1 \<le> n" and lt: "C * (real n + 1) powr k < 2 powr ((a - b) * real n)"
    using exp_beats_poly[where a = "a - b" and k = k and C = C and s = n1] k by auto
  have "C * (real n + 1) powr k * 2 powr (b * real n) < 2 powr ((a - b) * real n) * 2 powr (b * real n)"
    using lt by simp
  also have "\<dots> = 2 powr (a * real n)" by (simp add: powr_add[symmetric] algebra_simps)
  finally show False using h[OF n] by simp
qed

lemma powr_growth:
  fixes x a i r \<alpha> :: real
  assumes x: "0 \<le> x" "x \<le> a * (real n + 1) powr i * 2 powr (r * real n)" and a: "0 < a" and \<alpha>: "0 \<le> \<alpha>"
  shows "x powr \<alpha> \<le> a powr \<alpha> * (real n + 1) powr (i * \<alpha>) * 2 powr (r * \<alpha> * real n)"
proof -
  have "x powr \<alpha> \<le> (a * (real n + 1) powr i * 2 powr (r * real n)) powr \<alpha>" using x \<alpha> by (intro powr_mono2) simp_all
  also have "\<dots> = a powr \<alpha> * ((real n + 1) powr i) powr \<alpha> * (2 powr (r * real n)) powr \<alpha>"
    using a by (simp add: powr_mult)
  also have "\<dots> = a powr \<alpha> * (real n + 1) powr (i * \<alpha>) * 2 powr (r * \<alpha> * real n)"
    by (simp add: powr_powr mult_ac)
  finally show ?thesis .
qed


subsection \<open>Theorem 4(2) and 4(3)\<close>

text \<open>Relativised, the iteration yields a zero-finding program with polynomially many queries
for $N=2^n$; the AFP bound $sN\le(5q+11)^2$ (session \<open>Vern_Paulsen_QC_Search\<close>, with
$s\ge1/2-1/100$ for exhaustive search) rules this out.  The paper argues with OR; search is
what the simulated exhaustive computation solves.\<close>

theorem search_speedup_impossible:
  fixes q :: "nat \<Rightarrow> real" and s C k :: real
  assumes s: "0 < s" and k: "0 \<le> k"
    and lower: "\<And>n. n1 \<le> n \<Longrightarrow> s * 2 ^ n \<le> (5 * q n + 11)\<^sup>2"
    and upper: "\<And>n. n1 \<le> n \<Longrightarrow> 0 \<le> q n \<and> q n \<le> C * (real n + 1) powr k"
  shows False
proof -
  let ?D = "(5 * \<bar>C\<bar> + 11)\<^sup>2 / s"
  have "1 \<le> (0 :: real)"
  proof (rule rate_bound[of "2 * k" n1 1 ?D 0])
    fix n assume n: "n1 \<le> n"
    have P: "1 \<le> (real n + 1) powr k" using k by (intro ge_one_powr_ge_zero) simp_all
    have "5 * q n + 11 \<le> 5 * \<bar>C\<bar> * (real n + 1) powr k + 11 * (real n + 1) powr k"
    proof -
      have "C * (real n + 1) powr k \<le> \<bar>C\<bar> * (real n + 1) powr k" by (intro mult_right_mono) simp_all
      hence "q n \<le> \<bar>C\<bar> * (real n + 1) powr k" using upper[OF n] by linarith
      thus ?thesis using P by linarith
    qed
    also have "\<dots> = (5 * \<bar>C\<bar> + 11) * (real n + 1) powr k" by (simp add: algebra_simps)
    finally have "(5 * q n + 11)\<^sup>2 \<le> ((5 * \<bar>C\<bar> + 11) * (real n + 1) powr k)\<^sup>2"
      using upper[OF n] by (intro power_mono) simp_all
    also have "\<dots> = (5 * \<bar>C\<bar> + 11)\<^sup>2 * (real n + 1) powr (2 * k)"
    proof -
      have "((real n + 1) powr k)\<^sup>2 = (real n + 1) powr (2 * k)" by (simp only: power2_eq_square powr_add[symmetric] mult_2)
      thus ?thesis by (simp only: power_mult_distrib)
    qed
    finally have "s * 2 ^ n \<le> (5 * \<bar>C\<bar> + 11)\<^sup>2 * (real n + 1) powr (2 * k)" using lower[OF n] by linarith
    hence "2 ^ n \<le> ?D * (real n + 1) powr (2 * k)" using s by (simp add: field_simps)
    thus "2 powr (1 * real n) \<le> ?D * (real n + 1) powr (2 * k) * 2 powr (0 * real n)" by (simp add: powr_realpow)
  qed (use k in simp)
  thus False by simp
qed

text \<open>Theorem 4(3): an $n$-qubit, $\mathrm{poly}(n)$-gate circuit becomes a system with $\kappa\le2T+1$
and $N=6T2^n$, so a classical $\mathrm{poly}(\kappa,\log N)$ algorithm runs in $\mathrm{poly}(n)$.\<close>

lemma classical_simulation_poly:
  fixes T n k :: nat and c K \<kappa> R :: real
  assumes T: "1 \<le> T" "real T \<le> c * (real n + 1) ^ j" and \<kappa>: "0 \<le> \<kappa>" "\<kappa> \<le> 2 * real T + 1"
    and K: "0 \<le> K" and R: "R \<le> K * (\<kappa> + log 2 (6 * real T * 2 ^ n)) ^ k"
  shows "R \<le> K * (3 * c + 4) ^ k * (real n + 1) ^ ((j + 1) * k)"
proof -
  let ?p = "(real n + 1) ^ (j + 1)"
  have "0 < c * (real n + 1) ^ j" using T by linarith
  hence c0: "0 \<le> c" by (simp add: zero_less_mult_iff)
  have lT: "log 2 (real T) \<le> real T"
  proof -
    have "real T < 2 ^ T" by (metis of_nat_less_iff less_exp of_nat_numeral of_nat_power)
    hence "log 2 (real T) < log 2 (2 ^ T)" using T by (intro log_less) simp_all
    thus ?thesis by (simp add: log_nat_power)
  qed
  have l6: "log 2 (6 :: real) \<le> 3"
  proof -
    have "log 2 (6 :: real) \<le> log 2 8" by (intro log_mono) simp_all
    moreover have "log 2 (8 :: real) = 3" using log_nat_power[of "2 :: real" 2 3] by simp
    ultimately show ?thesis by linarith
  qed
  have "log 2 (6 * real T * 2 ^ n) = log 2 6 + log 2 (real T) + real n"
    using T by (simp add: log_mult log_nat_power)
  hence s: "\<kappa> + log 2 (6 * real T * 2 ^ n) \<le> 3 * real T + real n + 4" using \<kappa> lT l6 by linarith
  have p1: "1 \<le> ?p" by (rule one_le_power) simp
  have pj: "(real n + 1) ^ j \<le> ?p" by (intro power_increasing) simp_all
  have pn: "real n + 1 \<le> ?p" using power_increasing[of 1 "j + 1" "real n + 1"] by simp
  have "3 * real T \<le> 3 * c * ?p" using T(2) mult_left_mono[OF pj c0] by simp
  hence "\<kappa> + log 2 (6 * real T * 2 ^ n) \<le> (3 * c + 4) * ?p" using s pn p1 by (simp add: algebra_simps)
  moreover have "0 \<le> \<kappa> + log 2 (6 * real T * 2 ^ n)"
  proof -
    have a: "1 \<le> 6 * real T" using T(1) by simp
    have b: "1 \<le> (2 :: real) ^ n" by simp
    have "1 * 1 \<le> 6 * real T * 2 ^ n" by (rule mult_mono[OF a b]) simp_all
    hence "0 \<le> log 2 (6 * real T * 2 ^ n)" by simp
    thus ?thesis using \<kappa>(1) by linarith
  qed
  ultimately have "(\<kappa> + log 2 (6 * real T * 2 ^ n)) ^ k \<le> ((3 * c + 4) * ?p) ^ k" by (intro power_mono)
  hence "R \<le> K * ((3 * c + 4) * ?p) ^ k" using R mult_left_mono[OF _ K] by (meson order_trans)
  moreover have "((3 * c + 4) * ?p) ^ k = (3 * c + 4) ^ k * (real n + 1) ^ ((j + 1) * k)"
    by (simp only: power_mult_distrib power_mult)
  ultimately show ?thesis by (simp only: mult_ac)
qed

subsection \<open>Theorem 5\<close>

text \<open>Simon's problem gives a circuit with $T=2n+1$ gates on $3n$ qubits, so $\kappa\le4n+3$ and
$N=O(n2^{3n})$; with the classical $\Omega(2^{n/2})$ bound as hypothesis, $3\alpha+4\beta\ge\frac12$.\<close>

theorem simon_exponents:
  fixes \<alpha> \<beta> c K a b :: real and cost Nd \<kappa> :: "nat \<Rightarrow> real"
  assumes ab: "0 \<le> \<alpha>" "0 \<le> \<beta>" and c: "0 < c" and a: "0 < a"
    and lower: "\<And>n. n1 \<le> n \<Longrightarrow> c * 2 powr (real n / 2) \<le> cost n"
    and sim: "\<And>n. n1 \<le> n \<Longrightarrow> cost n \<le> K * (real n + 1) * Nd n powr \<alpha> * 2 powr (\<beta> * \<kappa> n)"
    and N: "\<And>n. 0 \<le> Nd n" "\<And>n. Nd n \<le> a * (real n + 1) powr 1 * 2 powr (3 * real n)"
    and kap: "\<And>n. \<kappa> n \<le> 4 * real n + b"
  shows "1 / 2 \<le> 3 * \<alpha> + 4 * \<beta>"
proof (rule rate_bound[of "1 + \<alpha>" n1 "1 / 2" "\<bar>K\<bar> * a powr \<alpha> * 2 powr (\<beta> * b) / c" "3 * \<alpha> + 4 * \<beta>"])
  fix n assume n: "n1 \<le> n"
  let ?P = "(real n + 1) powr (1 + \<alpha>)" and ?Q = "2 powr ((3 * \<alpha> + 4 * \<beta>) * real n)"
  have X: "Nd n powr \<alpha> \<le> a powr \<alpha> * (real n + 1) powr (1 * \<alpha>) * 2 powr (3 * \<alpha> * real n)"
    by (rule powr_growth[OF N(1) N(2) a ab(1)])
  have Y: "2 powr (\<beta> * \<kappa> n) \<le> 2 powr (\<beta> * b) * 2 powr (4 * \<beta> * real n)"
  proof -
    have "2 powr (\<beta> * \<kappa> n) \<le> 2 powr (\<beta> * (4 * real n + b))" using kap[of n] ab(2) by (intro powr_mono mult_left_mono) simp_all
    also have "\<dots> = 2 powr (\<beta> * b) * 2 powr (4 * \<beta> * real n)" by (simp add: powr_add[symmetric] algebra_simps)
    finally show ?thesis .
  qed
  have "c * 2 powr (real n / 2) \<le> K * (real n + 1) * Nd n powr \<alpha> * 2 powr (\<beta> * \<kappa> n)" using lower[OF n] sim[OF n] by linarith
  also have "\<dots> \<le> \<bar>K\<bar> * (real n + 1) * (a powr \<alpha> * (real n + 1) powr (1 * \<alpha>) * 2 powr (3 * \<alpha> * real n))
                   * (2 powr (\<beta> * b) * 2 powr (4 * \<beta> * real n))"
    using X Y by (intro mult_mono) simp_all
  also have "\<dots> = (\<bar>K\<bar> * a powr \<alpha> * 2 powr (\<beta> * b)) * ?P * ?Q"
  proof -
    have p: "(real n + 1) * (real n + 1) powr (1 * \<alpha>) = ?P" by (simp add: powr_add)
    have q: "2 powr (3 * \<alpha> * real n) * 2 powr (4 * \<beta> * real n) = ?Q" by (simp add: powr_add[symmetric] algebra_simps)
    show ?thesis unfolding p[symmetric] q[symmetric] by (simp only: mult_ac)
  qed
  finally have "c * 2 powr (real n / 2) \<le> (\<bar>K\<bar> * a powr \<alpha> * 2 powr (\<beta> * b)) * ?P * ?Q" .
  hence "2 powr (real n / 2) \<le> (\<bar>K\<bar> * a powr \<alpha> * 2 powr (\<beta> * b)) * ?P * ?Q / c"
    unfolding pos_le_divide_eq[OF c] by (simp only: mult_ac)
  thus "2 powr (1 / 2 * real n) \<le> \<bar>K\<bar> * a powr \<alpha> * 2 powr (\<beta> * b) / c * ?P * ?Q" by simp
qed (use ab in simp)


subsection \<open>Theorem 6\<close>

text \<open>Part 1: the state $\sum_z\ket z\ket{\varphi(z)}$ reads $1$ on its last qubit with probability
$\#\{z:\varphi(z)\}/2^n$; an estimate within $q/2^{n+1}$ of $q$ times it fixes the count, where
$q=e^{-2}/(1+e^{-2}+e^{-4})\le\frac14$ is the clock factor of $M_0$.  The paper's
$\epsilon=2^{-n-2}$ in part 2 is too coarse for this; $2^{-2n}$ (part 1) suffices for $n\ge5$.\<close>

definition count_state :: "nat \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> complex Matrix.vec" where
  "count_state n \<phi> = reg_sum (2 ^ n) 2
     (\<lambda>z. complex_of_real (1 / sqrt (2 ^ n)) \<cdot>\<^sub>v unit_vec 2 (if \<phi> z then 1 else 0))"

definition last_one_prob :: "nat \<Rightarrow> complex Matrix.vec \<Rightarrow> real" where
  "last_one_prob K v = (\<Sum>z<K. (cmod (blk 2 v z $ 1))\<^sup>2)"

lemma count_amp: "(cmod (1 / complex_of_real (sqrt (2 ^ n))))\<^sup>2 = 1 / 2 ^ n"
  by (simp add: norm_divide power_divide)

lemma count_state_block:
  "z < 2 ^ n \<Longrightarrow> blk 2 (count_state n \<phi>) z = complex_of_real (1 / sqrt (2 ^ n)) \<cdot>\<^sub>v unit_vec 2 (if \<phi> z then 1 else 0)"
  unfolding count_state_def by (rule blk_reg_sum) simp_all

lemma count_state_norm: "\<parallel>count_state n \<phi>\<parallel> = 1"
proof -
  have "\<parallel>count_state n \<phi>\<parallel>\<^sup>2 = (\<Sum>z<2 ^ n. \<parallel>complex_of_real (1 / sqrt (2 ^ n)) \<cdot>\<^sub>v unit_vec 2 (if \<phi> z then 1 else 0)\<parallel>\<^sup>2)"
    unfolding count_state_def by (rule vnorm_reg_sum_sq) simp
  also have "\<dots> = (\<Sum>z<(2::nat) ^ n. 1 / 2 ^ n)"
  proof (rule sum.cong[OF refl])
    fix z
    have u: "\<parallel>unit_vec 2 (if \<phi> z then 1 else 0)\<parallel> = 1"
      by (simp add: cpx_vec_length_def numeral_2_eq_2 lessThan_Suc unit_vec_def)
    show "\<parallel>complex_of_real (1 / sqrt (2 ^ n)) \<cdot>\<^sub>v unit_vec 2 (if \<phi> z then 1 else 0)\<parallel>\<^sup>2 = 1 / 2 ^ n"
      unfolding cpx_vec_length_smult u by (simp add: norm_divide power_divide)
  qed
  also have "\<dots> = 1" by simp
  finally have "\<parallel>count_state n \<phi>\<parallel> = 1 \<or> \<parallel>count_state n \<phi>\<parallel> = - 1" by (simp only: power2_eq_1_iff)
  thus ?thesis using vnorm_ge0[of "count_state n \<phi>"] by linarith
qed

text \<open>Measuring the last qubit gives $1$ with probability $\#\{z:\varphi(z)\}/2^n$.\<close>

theorem count_state_prob: "last_one_prob (2 ^ n) (count_state n \<phi>) = card {z. z < 2 ^ n \<and> \<phi> z} / 2 ^ n"
proof -
  have "last_one_prob (2 ^ n) (count_state n \<phi>) = (\<Sum>z<(2::nat) ^ n. if \<phi> z then 1 / 2 ^ n else 0)"
    unfolding last_one_prob_def
  proof (rule sum.cong[OF refl])
    fix z assume "z \<in> {..<(2::nat) ^ n}"
    hence z: "z < 2 ^ n" by simp
    show "(cmod (blk 2 (count_state n \<phi>) z $ 1))\<^sup>2 = (if \<phi> z then 1 / 2 ^ n else 0)"
      unfolding count_state_block[OF z] using count_amp[of n] by (simp add: unit_vec_def)
  qed
  also have "\<dots> = (\<Sum>z\<in>{z. z < 2 ^ n \<and> \<phi> z}. 1 / 2 ^ n)"
    by (simp add: sum.If_cases Collect_conj_eq lessThan_def Int_commute)
  also have "\<dots> = card {z. z < 2 ^ n \<and> \<phi> z} / 2 ^ n" by simp
  finally show ?thesis .
qed

lemma count_recover:
  fixes q e :: real and C C' :: nat
  assumes q: "0 < q" and e: "\<bar>e - q * C / 2 ^ n\<bar> < q / 2 ^ (n + 1)" "\<bar>e - q * C' / 2 ^ n\<bar> < q / 2 ^ (n + 1)"
  shows "C = C'"
proof -
  have t: "\<bar>a - b\<bar> \<le> \<bar>e - a\<bar> + \<bar>e - b\<bar>" for a b :: real by arith
  have h: "q / 2 ^ (n + 1) + q / 2 ^ (n + 1) = q / (2 ^ n :: real)" by (simp add: field_simps)
  have "\<bar>q * C / 2 ^ n - q * C' / 2 ^ n\<bar> < q / 2 ^ n" using t[of "q * C / 2 ^ n" "q * C' / 2 ^ n"] e h by linarith
  moreover have "q * C / 2 ^ n - q * C' / 2 ^ n = (q / 2 ^ n) * (real C - real C')" by (simp add: field_simps)
  moreover have p: "0 < q / (2 ^ n :: real)" using q by simp
  ultimately have "(q / 2 ^ n) * \<bar>real C - real C'\<bar> < (q / 2 ^ n) * 1" using q by (simp add: abs_mult)
  hence "\<bar>real C - real C'\<bar> < 1" using p by (simp only: mult_less_cancel_left_pos)
  thus ?thesis by linarith
qed

lemma clock_quarter: "exp (- 2) / (1 + exp (- 2) + exp (- 4)) \<le> (1 / 4 :: real)"
proof -
  have "(2 :: real) ^ 2 \<le> exp 1 ^ 2" using exp_ge_add_one_self[of 1] by (intro power_mono) simp_all
  also have "exp 1 ^ 2 = exp (2 :: real)" by (simp add: exp_of_nat_mult[symmetric])
  finally have e2: "exp (- 2) \<le> (1 / 4 :: real)" by (simp add: exp_minus field_simps)
  have p2: "0 < exp (- 2 :: real)" "0 < exp (- 4 :: real)" by simp_all
  have pos: "0 < 1 + exp (- 2) + exp (- 4 :: real)" using p2 by linarith
  have "4 * exp (- 2) \<le> 1 + exp (- 2) + exp (- 4 :: real)" using e2 p2 by linarith
  thus ?thesis using pos by (simp add: divide_le_eq)
qed

lemma paper_precision_insufficient:
  fixes q :: real and C :: nat
  assumes q: "0 < q" "q \<le> 1 / 4"
  shows "\<exists>e. \<bar>e - q * C / 2 ^ n\<bar> < 1 / 2 ^ (n + 2) \<and> \<bar>e - q * (C + 1) / 2 ^ n\<bar> < 1 / 2 ^ (n + 2)"
proof (intro exI conjI)
  let ?e = "q * (2 * C + 1) / 2 ^ (n + 1)"
  have d: "q / 2 ^ (n + 1) < 1 / 2 ^ (n + 2)" using q by (simp add: field_simps)
  have "\<bar>?e - q * C / 2 ^ n\<bar> = q / 2 ^ (n + 1)" using q by (simp add: field_simps)
  thus "\<bar>?e - q * C / 2 ^ n\<bar> < 1 / 2 ^ (n + 2)" using d by simp
  have "\<bar>?e - q * real (C + 1) / 2 ^ n\<bar> = q / 2 ^ (n + 1)" using q by (simp add: field_simps)
  thus "\<bar>?e - q * real (C + 1) / 2 ^ n\<bar> < 1 / 2 ^ (n + 2)" using d by simp
qed

lemma counting_precision:
  fixes q :: real
  assumes n: "5 \<le> n" and q: "1 / 10 \<le> q"
  shows "1 / 2 ^ (2 * n) < q / 2 ^ (n + 1)"
proof -
  let ?A = "(2 :: real) ^ n"
  have A: "32 \<le> ?A" using power_increasing[OF n, of "2 :: real"] by simp
  have B: "(2 :: real) ^ (2 * n) = ?A * ?A" by (simp only: mult_2 power_add)
  have C: "(2 :: real) ^ (n + 1) = 2 * ?A" by simp
  have "32 * ?A \<le> ?A * ?A" using A by (intro mult_right_mono) simp_all
  moreover have "1 * (?A * ?A) \<le> (10 * q) * (?A * ?A)" using q by (intro mult_right_mono) simp_all
  ultimately have lt: "2 * ?A < q * (?A * ?A)" using A by linarith
  have p: "0 < ?A" by simp
  show ?thesis unfolding B C using lt p by (simp add: divide_less_eq less_divide_eq)
qed

text \<open>Part 2: with the parity lower bound $\Omega(2^n)$ as hypothesis, $\alpha+\beta\ge1$.\<close>

theorem parity_exponents:
  fixes \<alpha> \<beta> c K a i j e :: real and cost Nd \<kappa> \<epsilon> :: "nat \<Rightarrow> real"
  assumes ab: "0 \<le> \<alpha>" "0 \<le> \<beta>" and c: "0 < c" and a: "0 < a" and ij: "0 \<le> i" "0 \<le> j"
    and lower: "\<And>n. n1 \<le> n \<Longrightarrow> c * 2 powr real n \<le> cost n"
    and sim: "\<And>n. n1 \<le> n \<Longrightarrow> cost n \<le> K * Nd n powr \<alpha> * \<kappa> n powr j / \<epsilon> n powr \<beta>"
    and N: "\<And>n. 0 \<le> Nd n" "\<And>n. Nd n \<le> a * (real n + 1) powr i * 2 powr (1 * real n)"
    and kap: "\<And>n. 0 \<le> \<kappa> n" "\<And>n. \<kappa> n \<le> a * (real n + 1) powr i * 2 powr (0 * real n)"
    and eps: "\<And>n. 2 powr (- (real n + e)) \<le> \<epsilon> n"
  shows "1 \<le> \<alpha> + \<beta>"
proof (rule rate_bound[of "i * \<alpha> + i * j" n1 1 "\<bar>K\<bar> * a powr \<alpha> * a powr j * 2 powr (\<beta> * e) / c" "\<alpha> + \<beta>"])
  fix n assume n: "n1 \<le> n"
  let ?P = "(real n + 1) powr (i * \<alpha> + i * j)" and ?Q = "2 powr ((\<alpha> + \<beta>) * real n)"
  have X: "Nd n powr \<alpha> \<le> a powr \<alpha> * (real n + 1) powr (i * \<alpha>) * 2 powr (1 * \<alpha> * real n)"
    by (rule powr_growth[OF N(1) N(2) a ab(1)])
  have Y: "\<kappa> n powr j \<le> a powr j * (real n + 1) powr (i * j) * 2 powr (0 * j * real n)"
    by (rule powr_growth[OF kap(1) kap(2) a ij(2)])
  have E: "1 / \<epsilon> n powr \<beta> \<le> 2 powr (\<beta> * e) * 2 powr (\<beta> * real n)"
  proof -
    have "0 < (2 :: real) powr (- (real n + e))" by simp
    hence e0: "0 < \<epsilon> n" using eps[of n] by linarith
    have "(2 powr (- (real n + e))) powr \<beta> \<le> \<epsilon> n powr \<beta>" using eps[of n] ab(2) by (intro powr_mono2) simp_all
    hence "1 / \<epsilon> n powr \<beta> \<le> 1 / (2 powr (- (real n + e))) powr \<beta>" using e0 by (intro divide_left_mono) simp_all
    also have "\<dots> = 2 powr (\<beta> * e) * 2 powr (\<beta> * real n)"
      by (simp add: powr_powr powr_minus_divide[symmetric] powr_add[symmetric] algebra_simps)
    finally show ?thesis .
  qed
  have "c * 2 powr real n \<le> K * Nd n powr \<alpha> * \<kappa> n powr j * (1 / \<epsilon> n powr \<beta>)" using lower[OF n] sim[OF n] by simp
  also have "\<dots> \<le> \<bar>K\<bar> * (a powr \<alpha> * (real n + 1) powr (i * \<alpha>) * 2 powr (1 * \<alpha> * real n))
                   * (a powr j * (real n + 1) powr (i * j) * 2 powr (0 * j * real n))
                   * (2 powr (\<beta> * e) * 2 powr (\<beta> * real n))"
    using X Y E by (intro mult_mono) simp_all
  also have "\<dots> = (\<bar>K\<bar> * a powr \<alpha> * a powr j * 2 powr (\<beta> * e)) * ?P * ?Q"
  proof -
    have p: "(real n + 1) powr (i * \<alpha>) * (real n + 1) powr (i * j) = ?P" by (simp add: powr_add)
    have q: "2 powr (1 * \<alpha> * real n) * 2 powr (\<beta> * real n) = ?Q" by (simp add: powr_add[symmetric] algebra_simps)
    have z: "2 powr (0 * j * real n) = (1 :: real)" by simp
    show ?thesis unfolding p[symmetric] q[symmetric] z by (simp only: mult_ac mult_1_right)
  qed
  finally have "c * 2 powr real n \<le> (\<bar>K\<bar> * a powr \<alpha> * a powr j * 2 powr (\<beta> * e)) * ?P * ?Q" .
  hence "2 powr real n \<le> (\<bar>K\<bar> * a powr \<alpha> * a powr j * 2 powr (\<beta> * e)) * ?P * ?Q / c"
    unfolding pos_le_divide_eq[OF c] by (simp only: mult_ac)
  thus "2 powr (1 * real n) \<le> \<bar>K\<bar> * a powr \<alpha> * a powr j * 2 powr (\<beta> * e) / c * ?P * ?Q" by simp
qed (use ab ij in simp)

end

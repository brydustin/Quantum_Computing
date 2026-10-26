(*  Title:   Day16_Density_Postulates.thy
    Author:  Dustin Bryant, after Vern Paulsen's lecture of 3 October 2011 (Day 16)
*)

theory Day16_Density_Postulates
  imports Day15_Partial_Traces
begin

section \<open>Day 16 (3 October 2011): partial traces in block form; the postulates for density matrices\<close>

text \<open>With matrix units $E_{ij}$ of $L(\Hil_B)$, every $X\in L(\Hil_A)\otimes L(\Hil_B)$ is uniquely
$X=\sum_{i,j}X_{ij}\otimes E_{ij}$ with $X_{ij}\in L(\Hil_A)$, and
$\tr_B(X)=\sum_iX_{ii}$, $\tr_A(X)=(\tr X_{ij})_{ij}$; symmetrically for
$X=\sum E_{kl}\otimes Y_{kl}$.  Choosing a basis $f_1,\dots,f_p$ of $\Hil_B$ identifies
$\Hil_A\otimes\Hil_B\cong\Hil_A^{(p)}=\Hil_A\oplus\cdots\oplus\Hil_A$ and
$L(\Hil_A\otimes\Hil_B)\cong M_p(L(\Hil_A))$, block matrices $(X_{ij})$ acting by
$(X_{ij})(h_j)_j=(\sum_jX_{ij}h_j)_i$; in block notation $\tr_B((X_{ij}))=X_{11}+\cdots+X_{pp}$ and
$\tr_A((X_{ij}))=(\tr X_{ij})$.

Reformulated postulates.  1$'$: the state of a system is a density matrix $\rho\in L(\Hil_A)$.
2$'$: closed evolution is $\rho\mapsto U\rho U^*$.  3$'$: a measurement system $\{M_\alpha\}$ with
$\sum M_\alpha^*M_\alpha=I$ yields outcome $\alpha$ with probability $\tr(M_\alpha^*M_\alpha\rho)$.
4$'$: systems with densities $\rho_1,\rho_2$ compose to $\rho_1\otimes\rho_2$ on $\Hil_A\otimes\Hil_B$.\<close>

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

end

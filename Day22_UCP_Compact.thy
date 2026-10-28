(*  Title:   Day22_UCP_Compact.thy
    Author:  Dustin Bryant, after Vern Paulsen's lecture of 17 October 2011 (Day 22)
*)

theory Day22_UCP_Compact
  imports
    Essential_Functional_Analysis.Lmat_Euclidean
    Day16_Block_Form
    Day22_Minimal_Kraus
    "HOL-Analysis.Convex"
    "HOL-Analysis.Convex_Euclidean_Space"
    "HOL-Analysis.Polytope"
    "HOL-Analysis.Starlike"
begin

subsection \<open>$\mathrm{UCP}(M_n,M_d)$ is compact (D22-4)\<close>

text \<open>The notes: $\mathrm{UCP}(M_n,M_d)$ is convex and compact, closed because the conditions are
closed and bounded because $\Phi(I)=I$ forces $0\le\Phi(E_{ii})\le I$.  The space $L(M_n,M_d)$ carries
no topology in this development; the Choi matrix is a linear bijection onto $M_{nd}$, so the
statement is made in Choi coordinates: the Choi matrices of linear UCP maps are exactly the
positive $P$ whose diagonal blocks sum to $I_d$ (\<open>ucp_choi_image\<close>, with the inverse Choi map
\<open>choi_inv\<close>), and that set is compact (\<open>compact_ucp_choi_set\<close>): it is closed, and it lies in
$d$ times the compact set of unit-trace positive matrices.\<close>

subsubsection \<open>Typed PSD predicate\<close>

definition psd_lmat :: "(complex, 'k :: finite, 'k) lmat \<Rightarrow> bool" where
  "psd_lmat M \<longleftrightarrow> psd (unwrap_lm M)"

lemma psd_lmat_unwrap [iff]:
  "psd_lmat (M :: (complex, 'k :: finite, 'k) lmat) \<longleftrightarrow> psd (unwrap_lm M)"
  unfolding psd_lmat_def by simp

subsubsection \<open>The positive matrices form a closed set\<close>

text \<open>Sub-lemmas for the closedness of PSD: the Hermitian half and the
nonneg-quadratic-form half.\<close>

lemma closed_entry_hermitian_eq:
  fixes i j :: nat
  assumes ij: "i < CARD('k :: finite)" "j < CARD('k)"
  shows "closed {M :: (complex, 'k, 'k) lmat.
                  unwrap_lm M $$ (i, j) = cnj (unwrap_lm M $$ (j, i))}"
proof -
  have cont_ij: "continuous_on UNIV (\<lambda>M :: (complex, 'k, 'k) lmat.
                                       unwrap_lm M $$ (i, j))"
    using continuous_on_unwrap_lm_index[OF ij] .
  have cont_ji: "continuous_on UNIV (\<lambda>M :: (complex, 'k, 'k) lmat.
                                       unwrap_lm M $$ (j, i))"
    using continuous_on_unwrap_lm_index[OF ij(2) ij(1)] .
  have cont_cnj_ji: "continuous_on UNIV (\<lambda>M :: (complex, 'k, 'k) lmat.
                                          cnj (unwrap_lm M $$ (j, i)))"
    using cont_ji continuous_on_cnj by blast
  have cont_diff: "continuous_on UNIV
                    (\<lambda>M :: (complex, 'k, 'k) lmat.
                       unwrap_lm M $$ (i, j) - cnj (unwrap_lm M $$ (j, i)))"
    using cont_ij cont_cnj_ji by (rule continuous_on_diff)
  have eq: "{M :: (complex, 'k, 'k) lmat.
              unwrap_lm M $$ (i, j) = cnj (unwrap_lm M $$ (j, i))}
          = (\<lambda>M. unwrap_lm M $$ (i, j) - cnj (unwrap_lm M $$ (j, i))) -` {0}"
    by auto
  show ?thesis
    unfolding eq
  proof (rule continuous_closed_vimage)
    show "closed {0::complex}" by simp
    fix M show "continuous (at M)
                  (\<lambda>M :: (complex, 'k, 'k) lmat.
                     unwrap_lm M $$ (i, j) - cnj (unwrap_lm M $$ (j, i)))"
      using cont_diff continuous_on_eq_continuous_at by blast
  qed
qed

lemma closed_hermitian_unwrap_lmat:
  "closed {M :: (complex, 'k :: finite, 'k) lmat. hermitian (unwrap_lm M)}"
proof -
  let ?I = "{(i, j). i < CARD('k) \<and> j < CARD('k)}"
  let ?S = "\<lambda>(i, j). {M :: (complex, 'k, 'k) lmat.
                       unwrap_lm M $$ (i, j) = cnj (unwrap_lm M $$ (j, i))}"

  have herm_eq:
    "{M :: (complex, 'k, 'k) lmat. hermitian (unwrap_lm M)}
     = (\<Inter>p \<in> ?I. ?S p)"
  proof safe
    fix x :: "(complex, 'k, 'k) lmat" and a b
    assume hx: "hermitian (unwrap_lm x)"
    assume a_lt: "a < CARD('k)"
    assume b_lt: "b < CARD('k)"

    have da: "a < dim_row (unwrap_lm x)"
      using a_lt by simp
    have db: "b < dim_col (unwrap_lm x)"
      using b_lt by simp
    show "unwrap_lm x $$ (a, b) = cnj (unwrap_lm x $$ (b, a))"
      by (rule hermitian_index[OF hx da db])
  next
    fix x :: "(complex, 'k, 'k) lmat"
    assume x_in: "x \<in> (\<Inter>p \<in> ?I. ?S p)"
    have entries:
      "\<And>a b. a < CARD('k) \<Longrightarrow> b < CARD('k)
       \<Longrightarrow> unwrap_lm x $$ (a, b) = cnj (unwrap_lm x $$ (b, a))"
    proof -
      fix a b
      assume ab: "a < CARD('k)" "b < CARD('k)"
      hence "(a, b) \<in> ?I"
        by simp
      with x_in have "x \<in> ?S (a, b)"
        by blast
      thus "unwrap_lm x $$ (a, b) = cnj (unwrap_lm x $$ (b, a))"
        by simp
    qed

    show "hermitian (unwrap_lm x)"
      unfolding hermitian_def
    proof (rule eq_matI)
      show "dim_row ((unwrap_lm x)\<^sup>\<dagger>) = dim_row (unwrap_lm x)"
        by simp
      show "dim_col ((unwrap_lm x)\<^sup>\<dagger>) = dim_col (unwrap_lm x)"
        by simp
    next
      fix i j
      assume ij:
        "i < dim_row (unwrap_lm x)"
        "j < dim_col (unwrap_lm x)"

      have i_lt: "i < CARD('k)"
        using ij(1) by simp
      have j_lt: "j < CARD('k)"
        using ij(2) by simp

      have ji:
        "unwrap_lm x $$ (j, i) = cnj (unwrap_lm x $$ (i, j))"
        using entries[OF j_lt i_lt] .

      show "((unwrap_lm x)\<^sup>\<dagger>) $$ (i, j) = unwrap_lm x $$ (i, j)"
        unfolding dagger_def using i_lt j_lt ji by simp
    qed
  qed

  show ?thesis
    unfolding herm_eq
    by (intro closed_INT, simp add: closed_entry_hermitian_eq) 
qed

lemma closed_nonneg_quad_form_lmat:
  fixes x :: "complex Matrix.vec"
  assumes xdim: "dim_vec x = CARD('k :: finite)"
  shows "closed {M :: (complex, 'k, 'k) lmat.
                  Re (\<langle>x | unwrap_lm M *\<^sub>v x\<rangle>) \<ge> 0}"
proof -
  let ?n = "CARD('k)"
  let ?f =
    "\<lambda>M :: (complex, 'k, 'k) lmat.
       Re (\<Sum>i = 0..<?n.
             \<Sum>j = 0..<?n.
               cnj (x $ i) * (unwrap_lm M $$ (i, j)) * (x $ j))"

  have quad_expand:
    "\<And>M :: (complex, 'k, 'k) lmat.
       Re (\<langle>x | unwrap_lm M *\<^sub>v x\<rangle>) = ?f M"
  proof -
    fix M :: "(complex, 'k, 'k) lmat"

    have rowM: "dim_row (unwrap_lm M) = ?n"
      by simp
    have colM: "dim_col (unwrap_lm M) = ?n"
      by simp

    have "\<langle>x | unwrap_lm M *\<^sub>v x\<rangle>
        = (\<Sum>i = 0..<dim_vec x.
             cnj (x $ i) * ((unwrap_lm M *\<^sub>v x) $ i))"
      by (simp add: Quantum.inner_prod_def xdim)
    also have "... =
        (\<Sum>i = 0..<?n.
             cnj (x $ i) * ((unwrap_lm M *\<^sub>v x) $ i))"
      using xdim by simp
    also have "... =
        (\<Sum>i = 0..<?n.
             cnj (x $ i) *
               (\<Sum>j = 0..<?n. unwrap_lm M $$ (i, j) * x $ j))"
    proof (rule sum.cong)
      show "{0..<?n} = {0..<?n}"
        by simp
    next
      fix i
      assume i: "i \<in> {0..<?n}"
      hence i_lt: "i < dim_row (unwrap_lm M)"
        using rowM by simp

      have "((unwrap_lm M *\<^sub>v x) $ i)
          = (\<Sum>j = 0..<dim_col (unwrap_lm M).
                unwrap_lm M $$ (i, j) * x $ j)"
        by (rule mult_mat_vec_index[OF carrier_mat_triv _ i_lt], rule carrier_vecI) (simp add: xdim)
      also have "... =
          (\<Sum>j = 0..<?n. unwrap_lm M $$ (i, j) * x $ j)"
        using colM by simp
      finally show
        "cnj (x $ i) * ((unwrap_lm M *\<^sub>v x) $ i)
         =
         cnj (x $ i) *
           (\<Sum>j = 0..<?n. unwrap_lm M $$ (i, j) * x $ j)"
        by simp
    qed
    also have "... =
        (\<Sum>i = 0..<?n.
          \<Sum>j = 0..<?n.
            cnj (x $ i) * (unwrap_lm M $$ (i, j)) * (x $ j))"
      by (simp add: sum_distrib_left algebra_simps)
    finally show
      "Re (\<langle>x | unwrap_lm M *\<^sub>v x\<rangle>) = ?f M"
      by simp
  qed

  have cont_terms:
    "\<And>i j. i < ?n \<Longrightarrow> j < ?n \<Longrightarrow>
      continuous_on UNIV
        (\<lambda>M :: (complex, 'k, 'k) lmat.
          cnj (x $ i) * (unwrap_lm M $$ (i, j)) * (x $ j))"
  proof -
    fix i j
    assume ij: "i < ?n" "j < ?n"

    have cont_entry:
      "continuous_on UNIV
        (\<lambda>M :: (complex, 'k, 'k) lmat. unwrap_lm M $$ (i, j))"
      using continuous_on_unwrap_lm_index[OF ij] .

    have h1: "continuous_on UNIV
        (\<lambda>M :: (complex, 'k, 'k) lmat.
          cnj (x $ i) * (unwrap_lm M $$ (i, j)))"
      using cont_entry
      by (rule continuous_on_mult [OF continuous_on_const])
    have h2: "continuous_on UNIV
        (\<lambda>M :: (complex, 'k, 'k) lmat. x $ j)"
      by (rule continuous_on_const)
    show "continuous_on UNIV
        (\<lambda>M :: (complex, 'k, 'k) lmat.
          cnj (x $ i) * (unwrap_lm M $$ (i, j)) * (x $ j))"
      using h1 h2 by (rule continuous_on_mult)
  qed

  have cont_sum_complex:
    "continuous_on UNIV
      (\<lambda>M :: (complex, 'k, 'k) lmat.
        \<Sum>i = 0..<?n.
          \<Sum>j = 0..<?n.
            cnj (x $ i) * (unwrap_lm M $$ (i, j)) * (x $ j))"
    by (intro continuous_on_sum cont_terms) auto

  have cont_f: "continuous_on UNIV ?f"
    using cont_sum_complex
    by (intro continuous_on_Re)

  have set_eq:
    "{M :: (complex, 'k, 'k) lmat.
        Re (\<langle>x | unwrap_lm M *\<^sub>v x\<rangle>) \<ge> 0}
     = ?f -` {0..}"
    using quad_expand by auto

  show ?thesis
    unfolding set_eq
  proof (rule continuous_closed_vimage)
    show "closed ({0..} :: real set)"
      by simp
  next
    fix M :: "(complex, 'k, 'k) lmat"
    show "continuous (at M) ?f"
      using cont_f continuous_on_eq_continuous_at by blast
  qed
qed

lemma closed_psd_lmat:
  "closed {M :: (complex, 'k :: finite, 'k) lmat. psd_lmat M}"
proof -
  let ?H = "{M :: (complex, 'k, 'k) lmat. hermitian (unwrap_lm M)}"
  let ?Q = "\<lambda>x. {M :: (complex, 'k, 'k) lmat. Re (\<langle>x | unwrap_lm M *\<^sub>v x\<rangle>) \<ge> 0}"
  have psd_eq:
    "{M :: (complex, 'k, 'k) lmat. psd_lmat M}
     = ?H \<inter> (\<Inter>x \<in> {y. dim_vec y = CARD('k)}. ?Q x)"
    unfolding psd_lmat_def psd_def by auto
  have closed_H: "closed ?H" by (rule closed_hermitian_unwrap_lmat)
  have closed_INT: "closed (\<Inter>x \<in> {y. dim_vec y = CARD('k)}. ?Q x)"
  proof (rule closed_INT, intro ballI)
    fix x :: "complex Matrix.vec"
    assume "x \<in> {y. dim_vec y = CARD('k)}"
    hence dim: "dim_vec x = CARD('k)" by simp
    show "closed {M :: (complex, 'k, 'k) lmat. Re (\<langle>x | unwrap_lm M *\<^sub>v x\<rangle>) \<ge> 0}"
      by (rule closed_nonneg_quad_form_lmat[OF dim])
  qed
  show ?thesis
    unfolding psd_eq using closed_H closed_INT by (rule closed_Int)
qed

subsubsection \<open>Trace on lmat\<close>

definition Tr_lmat :: "(complex, 'k :: finite, 'k) lmat \<Rightarrow> complex" where
  "Tr_lmat M = (\<Sum>i = 0..<CARD('k). unwrap_lm M $$ (i, i))"

lemma continuous_on_Tr_lmat:
  fixes S :: "(complex, 'k :: finite, 'k) lmat set"
  shows "continuous_on S Tr_lmat"
proof -
  have term_cont:
    "\<And>i. i < CARD('k)
       \<Longrightarrow> continuous_on S (\<lambda>M :: (complex, 'k, 'k) lmat. unwrap_lm M $$ (i, i))"
  proof -
    fix i :: nat
    assume i_lt: "i < CARD('k)"
    show "continuous_on S (\<lambda>M :: (complex, 'k, 'k) lmat. unwrap_lm M $$ (i, i))"
      using continuous_on_unwrap_lm_index[OF i_lt i_lt] .
  qed
  have sum_cont:
    "continuous_on S
       (\<lambda>M :: (complex, 'k, 'k) lmat.
          \<Sum>i = 0..<CARD('k). unwrap_lm M $$ (i, i))"
  proof (rule continuous_on_sum)
    fix i assume "i \<in> {0..<CARD('k)}"
    hence i_lt: "i < CARD('k)" by simp
    show "continuous_on S (\<lambda>M :: (complex, 'k, 'k) lmat. unwrap_lm M $$ (i, i))"
      by (rule term_cont [OF i_lt])
  qed
  show ?thesis using sum_cont unfolding Tr_lmat_def by simp
qed

lemma Tr_lmat_add:
  fixes M N :: "(complex, 'k :: finite, 'k) lmat"
  shows "Tr_lmat (M + N) = Tr_lmat M + Tr_lmat N"
proof -
  have step: "(\<Sum>i = 0..<CARD('k). unwrap_lm (M + N) $$ (i, i))
            = (\<Sum>i = 0..<CARD('k).
                 unwrap_lm M $$ (i, i) + unwrap_lm N $$ (i, i))"
    by (rule sum.cong) auto
  show ?thesis
    unfolding Tr_lmat_def using step by (simp add: sum.distrib)
qed

lemma Tr_lmat_scaleR:
  fixes M :: "(complex, 'k :: finite, 'k) lmat" and a :: real
  shows "Tr_lmat (a *\<^sub>R M) = a *\<^sub>R Tr_lmat M"
proof -
  have step: "(\<Sum>i = 0..<CARD('k). unwrap_lm (a *\<^sub>R M) $$ (i, i))
            = (\<Sum>i = 0..<CARD('k). a *\<^sub>R (unwrap_lm M $$ (i, i)))"
    by (rule sum.cong) auto
  show ?thesis
    unfolding Tr_lmat_def using step by (simp add: scaleR_sum_right)
qed

lemma Tr_lmat_zero [simp]:
  "Tr_lmat (0 :: (complex, 'k :: finite, 'k) lmat) = 0"
  unfolding Tr_lmat_def by simp

lemma Tr_lmat_sum_scaleR:
  fixes T :: "'a set" and u :: "'a \<Rightarrow> real"
    and f :: "'a \<Rightarrow> (complex, 'k :: finite, 'k) lmat"
  assumes "finite T"
  shows "Tr_lmat (\<Sum>t \<in> T. u t *\<^sub>R f t) = (\<Sum>t \<in> T. u t *\<^sub>R Tr_lmat (f t))"
  using assms
proof induction
  case empty thus ?case by simp
next
  case (insert t T)
  have "Tr_lmat (\<Sum>s \<in> insert t T. u s *\<^sub>R f s)
      = Tr_lmat (u t *\<^sub>R f t + (\<Sum>s \<in> T. u s *\<^sub>R f s))"
    using insert by simp
  also have "\<dots> = Tr_lmat (u t *\<^sub>R f t) + Tr_lmat (\<Sum>s \<in> T. u s *\<^sub>R f s)"
    by (rule Tr_lmat_add)
  also have "\<dots> = u t *\<^sub>R Tr_lmat (f t) + (\<Sum>s \<in> T. u s *\<^sub>R Tr_lmat (f s))"
    using insert.IH by (simp add: Tr_lmat_scaleR)
  also have "\<dots> = (\<Sum>s \<in> insert t T. u s *\<^sub>R Tr_lmat (f s))"
    using insert by simp
  finally show ?case .
qed

lemma closed_unit_trace_lmat:
  "closed {M :: (complex, 'k :: finite, 'k) lmat. Tr_lmat M = 1}"
proof -
  have eq: "{M :: (complex, 'k, 'k) lmat. Tr_lmat M = 1} = Tr_lmat -` {1}" by auto
  show ?thesis
    unfolding eq
  proof (rule continuous_closed_vimage)
    show "closed {1::complex}" by simp
    fix M :: "(complex, 'k, 'k) lmat"
    show "continuous (at M) Tr_lmat"
      using continuous_on_Tr_lmat continuous_on_eq_continuous_at by blast
  qed
qed

subsubsection \<open>Compactness of the unit-trace PSD slice\<close>

text \<open>For $\sigma\ge0$ with $\Tr\sigma=1$ and eigenvalues $\lambda_i\ge0$,
$\norm\sigma_{HS}^2=\sum_i\lambda_i^2\le\bigl(\sum_i\lambda_i\bigr)^2=1$.\<close>

lemma psd_entry_bound_by_diag:
  fixes M :: "complex Matrix.mat"
  assumes Mcar: "M \<in> carrier_mat n n"
      and Mpsd: "psd M"
      and i: "i < n" and j: "j < n"
  shows "(norm (M $$ (i, j)))\<^sup>2 \<le> Re (M $$ (i, i)) * Re (M $$ (j, j))"
proof -
  obtain W where Wc: "W \<in> carrier_mat n n" and Wpsd: "psd W" and WW: "W * W = M"
    using psd_sqrt_exists[OF Mcar Mpsd] by blast
  have M: "M $$ (a, b) = \<langle>Matrix.col W a | Matrix.col W b\<rangle>" if "a < n" "b < n" for a b
    using dagger_mult_inner[OF Wc that] psd_hermitian[OF Wpsd] WW unfolding hermitian_def by simp
  show ?thesis
    using cauchy_schwarz_ineq[of "Matrix.col W i" "Matrix.col W j"] Wc
    unfolding M[OF i j] M[OF i i] M[OF j j] times_complex.sel(1) inner_prod_with_itself_Im by simp
qed

lemma norm_lmat_le_of_psd_unit_trace:
  fixes M :: "(complex, 'k :: finite, 'k) lmat"
  assumes psd: "psd_lmat M" and tr: "Tr_lmat M = 1"
  shows "norm M \<le> 1"
proof (rule power2_le_imp_le)
  let ?M = "unwrap_lm M" and ?I = "{0..<CARD('k)}"
  have "?M \<in> carrier_mat CARD('k) CARD('k)" "psd ?M" using psd by simp_all
  note bound = psd_entry_bound_by_diag[OF this]
  have "(norm M)\<^sup>2 = inner M M" by (simp add: power2_norm_eq_inner)
  also have "\<dots> = (\<Sum>(i, j) \<in> ?I \<times> ?I. (norm (?M $$ (i, j)))\<^sup>2)"
    unfolding inner_lmat_def
    by (intro sum.cong refl) (auto simp: power2_norm_eq_inner [symmetric] split: prod.split)
  also have "\<dots> \<le> (\<Sum>(i, j) \<in> ?I \<times> ?I. Re (?M $$ (i, i)) * Re (?M $$ (j, j)))"
    using bound by (intro sum_mono) (auto split: prod.split)
  also have "\<dots> = (\<Sum>i \<in> ?I. Re (?M $$ (i, i))) * (\<Sum>j \<in> ?I. Re (?M $$ (j, j)))"
    unfolding sum_product sum.cartesian_product ..
  also have "\<dots> = 1"
    using tr unfolding Tr_lmat_def Re_sum[symmetric] by simp
  finally show "(norm M)\<^sup>2 \<le> 1\<^sup>2" by simp
qed simp

lemma compact_unit_trace_psd_lmat:
  "compact {M :: (complex, 'k :: finite, 'k) lmat. psd_lmat M \<and> Tr_lmat M = 1}"
proof -
  let ?S = "{M :: (complex, 'k, 'k) lmat. psd_lmat M \<and> Tr_lmat M = 1}"
  have closed_S: "closed ?S"
  proof -
    have eq: "?S = {M. psd_lmat M} \<inter> {M. Tr_lmat M = 1}" by auto
    show ?thesis
      unfolding eq using closed_psd_lmat closed_unit_trace_lmat by (rule closed_Int)
  qed
  have bounded_S: "bounded ?S"
  proof -
    have "\<forall>M \<in> ?S. norm M \<le> 1"
      using norm_lmat_le_of_psd_unit_trace by auto
    thus ?thesis by (rule bounded_iff [THEN iffD2, OF exI[where x = 1]])
  qed
  show ?thesis using closed_S bounded_S compact_eq_bounded_closed by blast
qed

subsubsection \<open>UCP maps in Choi coordinates\<close>

text \<open>In Choi coordinates a linear map $\Phi:M_n\to M_d$ is UCP iff $P_\Phi\ge0$ and
$\sum_iR_{ii}=I_d$ (@{thm [source] choi_ucp_iff}); the set of such $P$ is compact.  Dimensions are
cardinalities of finite types, $n=|{'n}|$, $d=|{'d}|$, so that the typed matrices (a Euclidean
space, \<open>Lmat_Euclidean\<close>) and the closed and compact sets of positive matrices above can be
used.\<close>

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
      using mult_index_lt[OF i a] mult_index_lt[OF i b] by (simp_all add: card_prod)
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

(*
  Title:    Lmat/Separable_Cone.thy
  Purpose:  Develop the separable-state cone in the typed lmat space.
            Define it, show it is closed in the Hilbert-Schmidt topology,
            apply HOL-Analysis separating_hyperplane_closed_point, and
            convert the separating direction to a hermitian entanglement
            witness; conclude with the Horodecki-style characterisation
            "separable iff every hermitian witness sees it nonneg".

  Status:   FULLY PROVEN.  No sorries.

            The main pieces (in order of appearance):
              separable_cone_lmat_closed
                - the separable cone is closed in HS topology.
              separable_cone_lmat_separating_hyperplane
                - rho not in cone => exists a in lmat with
                    inner a rho < 0 <= inner a sigma for all sigma in cone.
              entanglement_witness_re_tr
                - Re-Tr-form of the previous: witness is unwrap_lm-dagger.
              entanglement_witness_hermitian
                - witness can be chosen hermitian, side condition on sigma.
              separable_cone_lmat_hermitian
                - every element of the cone has hermitian unwrap (PSD).
              entanglement_witness_hermitian'
                - the side condition is automatic; clean witness statement.
              separable_iff_witness
                - Horodecki characterisation: rho in cone iff every
                  hermitian witness W that is nonneg-trace on the cone
                  is also nonneg-trace on rho.

            All built on Lmat_Euclidean's real_inner / euclidean_space /
            heine_borel typeclass instances and the HS norm / inner
            product / spectral machinery from Quantum_Computing.thy.
*)

theory Separable_Cone
  imports
    Lmat_Euclidean
    Vern_Paulsen_QC_3_10.Quantum_Computing_3_10
    Isabelle_Marries_Dirac.Tensor
    "HOL-Analysis.Convex"
    "HOL-Analysis.Convex_Euclidean_Space"
    "HOL-Analysis.Polytope"
    "HOL-Analysis.Starlike"
begin

text \<open>HOL-Hahn_Banach defines a locale also called \<open>continuous\<close>.
Hide its short name so that, in the proofs below, \<open>continuous\<close>
resolves to the topological-space predicate from
\<^theory>\<open>HOL.Topological_Spaces\<close>.\<close>

hide_const (open) Function_Norm.continuous

section \<open>Typed PSD predicate\<close>

definition psd_lmat :: "(complex, 'k :: finite, 'k) lmat \<Rightarrow> bool" where
  "psd_lmat M \<longleftrightarrow> psd (unwrap_lm M)"

lemma psd_lmat_unwrap [iff]:
  "psd_lmat (M :: (complex, 'k :: finite, 'k) lmat) \<longleftrightarrow> psd (unwrap_lm M)"
  unfolding psd_lmat_def by simp


section \<open>Typed tensor product\<close>

text \<open>Two square matrices with type-level dimensions \<open>'m, 'p\<close> tensor
to a square matrix with type-level dimension \<open>'m \<times> 'p\<close>.\<close>

lemma tensor_mat_carrier_lmat:
  fixes A B :: "complex Matrix.mat"
  assumes A: "A \<in> carrier_mat (CARD('m :: finite)) (CARD('m))"
      and B: "B \<in> carrier_mat (CARD('p :: finite)) (CARD('p))"
  shows "A \<Otimes> B \<in> carrier_mat (CARD('m \<times> 'p)) (CARD('m \<times> 'p))"
proof -
  have rA: "dim_row A = CARD('m)" and cA: "dim_col A = CARD('m)" using A by auto
  have rB: "dim_row B = CARD('p)" and cB: "dim_col B = CARD('p)" using B by auto
  have row: "dim_row (A \<Otimes> B) = CARD('m \<times> 'p)" using rA rB by simp
  have col: "dim_col (A \<Otimes> B) = CARD('m \<times> 'p)" using cA cB by simp
  show ?thesis using row col by auto
qed

definition tensor_lmat ::
  "(complex, 'm :: finite, 'm) lmat \<Rightarrow> (complex, 'p :: finite, 'p) lmat
   \<Rightarrow> (complex, 'm \<times> 'p, 'm \<times> 'p) lmat" where
  "tensor_lmat \<sigma> \<tau> = wrap_lm (unwrap_lm \<sigma> \<Otimes> unwrap_lm \<tau>)"

lemma unwrap_lm_tensor_lmat [simp]:
  fixes \<sigma> :: "(complex, 'm :: finite, 'm) lmat"
    and \<tau> :: "(complex, 'p :: finite, 'p) lmat"
  shows "unwrap_lm (tensor_lmat \<sigma> \<tau> :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat)
       = unwrap_lm \<sigma> \<Otimes> unwrap_lm \<tau>"
  unfolding tensor_lmat_def
  by (subst wrap_lm_inverse) (use tensor_mat_carrier_lmat in auto)


section \<open>The separable cone\<close>

text \<open>The set of \emph{separable matrices}: all nonneg combinations of
tensor products of typed PSD matrices.  Equivalently, the convex
conic hull of the product PSD set.\<close>

definition separable_lmat_gen :: "(complex, 'm :: finite \<times> 'p :: finite,
                                   'm \<times> 'p) lmat set" where
  "separable_lmat_gen =
     {tensor_lmat \<sigma> \<tau> | \<sigma> \<tau>.
        (psd_lmat \<sigma> :: bool) \<and> (psd_lmat \<tau> :: bool)}"

definition separable_cone_lmat :: "(complex, 'm :: finite \<times> 'p :: finite,
                                    'm \<times> 'p) lmat set" where
  "separable_cone_lmat = convex_cone hull separable_lmat_gen"

text \<open>Sanity: the cone contains 0, is convex, and is conic.\<close>

lemma separable_cone_lmat_convex_cone:
  "convex_cone (separable_cone_lmat
                  :: (complex, 'm :: finite \<times> 'p :: finite, 'm \<times> 'p) lmat set)"
  unfolding separable_cone_lmat_def
  by (rule convex_cone_convex_cone_hull)

lemma zero_in_separable_cone_lmat:
  "(0 :: (complex, 'm :: finite \<times> 'p :: finite, 'm \<times> 'p) lmat)
     \<in> separable_cone_lmat"
  unfolding separable_cone_lmat_def
  using convex_cone_hull_contains_0 by blast


section \<open>Step 1: PSD set is closed\<close>

text \<open>Sub-lemmas for the closedness of PSD: the Hermitian half and the
nonneg-quadratic-form half.\<close>

text \<open>The entry-projection \<open>M \<mapsto> unwrap_lm M $$ (i, j)\<close> is continuous
on lmat for valid index \<open>(i, j)\<close>.\<close>

lemma isCont_unwrap_lm_index:
  fixes x :: "('a :: real_normed_vector, 'm :: finite, 'n :: finite) lmat"
  assumes ij: "i < CARD('m)" "j < CARD('n)"
  shows "isCont (\<lambda>M. unwrap_lm M $$ (i, j)) x"
proof -
  have lim_id: "((\<lambda>y. y) \<longlongrightarrow> x) (at x)" by (rule tendsto_ident_at)
  have lim_entry: "((\<lambda>y. unwrap_lm y $$ (i, j)) \<longlongrightarrow> unwrap_lm x $$ (i, j)) (at x)"
    by (rule tendsto_unwrap_lm_index[OF lim_id ij(1) ij(2)])
  show ?thesis unfolding isCont_def using lim_entry by simp
qed

lemma continuous_on_unwrap_lm_index:
  fixes S :: "('a :: real_normed_vector, 'm :: finite, 'n :: finite) lmat set"
  assumes ij: "i < CARD('m)" "j < CARD('n)"
  shows "continuous_on S (\<lambda>M. unwrap_lm M $$ (i, j))"
  using isCont_unwrap_lm_index[OF ij]
  by (intro continuous_at_imp_continuous_on) auto

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
      by (metis da db hermitian_index hx)
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
        by (metis (no_types) dagger_def entries i_lt ij(2) index_mat(1) 
            prod.simps(2) unwrap_lm_dim_col unwrap_lm_dim_row)
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
        by (metis (no_types) carrier_vec_dim_vec i_lt mult_mat_vec_index 
            unwrap_lm_carrier unwrap_lm_dim_col unwrap_lm_dim_row xdim)
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


section \<open>Trace on lmat (sorried)\<close>

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


section \<open>Compactness of the unit-trace PSD slice\<close>

text \<open>For PSD \<open>\<sigma>\<close> with \<open>Tr \<sigma> = 1\<close>:
\<open>‖\<sigma>‖\<^sup>2\<^sub>H\<^sub>S = \<Sum>\<lambda>\<^sub>i\<^sup>2 \<le> (\<Sum>\<lambda>\<^sub>i)\<^sup>2 = 1\<close>
where \<open>\<lambda>\<^sub>i\<close> are the (nonneg) eigenvalues.\<close>

lemma psd_entry_bound_by_diag:
  fixes M :: "complex Matrix.mat"
  assumes Mcar: "M \<in> carrier_mat n n"
      and Mpsd: "psd M"
      and i: "i < n" and j: "j < n"
  shows "(norm (M $$ (i, j)))\<^sup>2 \<le> Re (M $$ (i, i)) * Re (M $$ (j, j))"
proof -
  obtain Q :: "complex Matrix.mat"
    where Qcar: "Q \<in> carrier_mat n n"
      and Qpsd: "psd Q"
      and QQ: "Q * Q = M"
    using psd_sqrt_exists [OF Mcar Mpsd] by blast
  have Qherm: "hermitian Q" using Qpsd by (rule psd_hermitian)
  have Qdr: "dim_row Q = n" using Qcar by simp
  have Qdc: "dim_col Q = n" using Qcar by simp
  have Qcnj:
    "\<And>a b. a < n \<Longrightarrow> b < n \<Longrightarrow> Q $$ (b, a) = cnj (Q $$ (a, b))"
  proof -
    fix a b assume a: "a < n" and b: "b < n"
    have e1: "(Q\<^sup>\<dagger>) $$ (a, b) = cnj (Q $$ (b, a))"
      unfolding dagger_def using Qdr Qdc a b by simp
    have qe: "Q $$ (a, b) = cnj (Q $$ (b, a))"
      using e1 Qherm by (simp add: hermitian_def)
    show "Q $$ (b, a) = cnj (Q $$ (a, b))"
      using qe by (metis complex_cnj_cnj)
  qed
  have Mij_sum:
    "M $$ (i, j) = (\<Sum>k = 0..<n. Q $$ (i, k) * cnj (Q $$ (j, k)))"
  proof -
    have "M $$ (i, j) = (Q * Q) $$ (i, j)" using QQ by simp
    also have "\<dots> = (\<Sum>k = 0..<n. Q $$ (i, k) * Q $$ (k, j))"
      using Qcar i j by (simp add: scalar_prod_def Matrix.row_def
                                     Matrix.col_def lessThan_atLeast0)
    also have "\<dots> = (\<Sum>k = 0..<n. Q $$ (i, k) * cnj (Q $$ (j, k)))"
    proof (rule sum.cong [OF refl])
      fix k assume k_in: "k \<in> {0..<n}"
      hence k_lt: "k < n" by simp
      have "Q $$ (k, j) = cnj (Q $$ (j, k))" using Qcnj [OF j k_lt] .
      thus "Q $$ (i, k) * Q $$ (k, j) = Q $$ (i, k) * cnj (Q $$ (j, k))"
        by simp
    qed
    finally show ?thesis .
  qed
  have diag_entry_sum:
    "\<And>l. l < n
       \<Longrightarrow> Re (M $$ (l, l)) = (\<Sum>k = 0..<n. (norm (Q $$ (l, k)))\<^sup>2)"
  proof -
    fix l assume l: "l < n"
    have "M $$ (l, l) = (Q * Q) $$ (l, l)" using QQ by simp
    also have "\<dots> = (\<Sum>k = 0..<n. Q $$ (l, k) * Q $$ (k, l))"
      using Qcar l by (simp add: scalar_prod_def Matrix.row_def
                                   Matrix.col_def lessThan_atLeast0)
    also have "\<dots> = (\<Sum>k = 0..<n. Q $$ (l, k) * cnj (Q $$ (l, k)))"
    proof (rule sum.cong [OF refl])
      fix k assume k_in: "k \<in> {0..<n}"
      hence k_lt: "k < n" by simp
      have "Q $$ (k, l) = cnj (Q $$ (l, k))" using Qcnj [OF l k_lt] .
      thus "Q $$ (l, k) * Q $$ (k, l) = Q $$ (l, k) * cnj (Q $$ (l, k))"
        by simp
    qed
    also have "\<dots> = (\<Sum>k = 0..<n. complex_of_real ((norm (Q $$ (l, k)))\<^sup>2))"
    proof (rule sum.cong [OF refl])
      fix k assume "k \<in> {0..<n}"
      show "Q $$ (l, k) * cnj (Q $$ (l, k))
          = complex_of_real ((norm (Q $$ (l, k)))\<^sup>2)"
        by (simp add: complex_mult_cnj power2_eq_square norm_complex_def)
    qed
    also have "\<dots> = complex_of_real (\<Sum>k = 0..<n. (norm (Q $$ (l, k)))\<^sup>2)"
      by simp
    finally have entry_eq:
      "M $$ (l, l) = complex_of_real (\<Sum>k = 0..<n. (norm (Q $$ (l, k)))\<^sup>2)" .
    thus "Re (M $$ (l, l)) = (\<Sum>k = 0..<n. (norm (Q $$ (l, k)))\<^sup>2)" by simp
  qed
  have Mii_real:
    "Re (M $$ (i, i)) = (\<Sum>k = 0..<n. (norm (Q $$ (i, k)))\<^sup>2)"
    using diag_entry_sum [OF i] .
  have Mjj_real:
    "Re (M $$ (j, j)) = (\<Sum>k = 0..<n. (norm (Q $$ (j, k)))\<^sup>2)"
    using diag_entry_sum [OF j] .
  have triangle:
    "norm (M $$ (i, j))
       \<le> (\<Sum>k = 0..<n. norm (Q $$ (i, k)) * norm (Q $$ (j, k)))"
  proof -
    have "norm (M $$ (i, j))
        = norm (\<Sum>k = 0..<n. Q $$ (i, k) * cnj (Q $$ (j, k)))"
      using Mij_sum by simp
    also have "\<dots> \<le> (\<Sum>k = 0..<n. norm (Q $$ (i, k) * cnj (Q $$ (j, k))))"
      by (rule norm_sum)
    also have "\<dots> = (\<Sum>k = 0..<n. norm (Q $$ (i, k)) * norm (Q $$ (j, k)))"
      by (simp add: norm_mult)
    finally show ?thesis .
  qed
  have CS:
    "(\<Sum>k = 0..<n. norm (Q $$ (i, k)) * norm (Q $$ (j, k)))\<^sup>2
       \<le> (\<Sum>k = 0..<n. (norm (Q $$ (i, k)))\<^sup>2)
        * (\<Sum>k = 0..<n. (norm (Q $$ (j, k)))\<^sup>2)"
    by (rule Cauchy_Schwarz_ineq_sum)
  have nn: "0 \<le> norm (M $$ (i, j))" by simp
  have sn: "0 \<le> (\<Sum>k = 0..<n. norm (Q $$ (i, k)) * norm (Q $$ (j, k)))"
    by (intro sum_nonneg) auto
  have sq_mono:
    "(norm (M $$ (i, j)))\<^sup>2
       \<le> (\<Sum>k = 0..<n. norm (Q $$ (i, k)) * norm (Q $$ (j, k)))\<^sup>2"
    using triangle nn sn by (simp add: power_mono)
  have "(norm (M $$ (i, j)))\<^sup>2
       \<le> (\<Sum>k = 0..<n. (norm (Q $$ (i, k)))\<^sup>2)
        * (\<Sum>k = 0..<n. (norm (Q $$ (j, k)))\<^sup>2)"
    using sq_mono CS by linarith
  thus ?thesis using Mii_real Mjj_real by simp
qed

lemma norm_lmat_le_of_psd_unit_trace:
  fixes M :: "(complex, 'k :: finite, 'k) lmat"
  assumes psd: "psd_lmat M" and tr: "Tr_lmat M = 1"
  shows "norm M \<le> 1"
proof -
  let ?n = "CARD('k)"
  have psd_unwrap: "psd (unwrap_lm M)" using psd by simp
  have unwrap_carr: "unwrap_lm M \<in> carrier_mat ?n ?n" by simp
  have Tr_lmat_unwrap: "Tr_lmat M = Tr (unwrap_lm M)"
    unfolding Tr_lmat_def Tr_def by (simp add: atLeast0LessThan)
  have norm_sq_eq:
    "(norm M)\<^sup>2 = (\<Sum>(i, j) \<in> {0..<?n} \<times> {0..<?n}.
                    (norm (unwrap_lm M $$ (i, j)))\<^sup>2)"
  proof -
    have "(norm M)\<^sup>2 = inner M M" by (simp add: power2_norm_eq_inner)
    also have "\<dots> = (\<Sum>(i, j) \<in> {0..<?n} \<times> {0..<?n}.
                      (norm (unwrap_lm M $$ (i, j)))\<^sup>2)"
      unfolding inner_lmat_def
      by (intro sum.cong refl)
         (auto simp: power2_norm_eq_inner [symmetric] split: prod.split)
    finally show ?thesis .
  qed
  have entry_bound:
    "\<And>i j. i < ?n \<Longrightarrow> j < ?n \<Longrightarrow>
       (norm (unwrap_lm M $$ (i, j)))\<^sup>2 \<le>
       Re (unwrap_lm M $$ (i, i)) * Re (unwrap_lm M $$ (j, j))"
    using psd_entry_bound_by_diag [OF unwrap_carr psd_unwrap] .
  have sum_bound:
    "(\<Sum>(i, j) \<in> {0..<?n} \<times> {0..<?n}. (norm (unwrap_lm M $$ (i, j)))\<^sup>2)
     \<le> (\<Sum>(i, j) \<in> {0..<?n} \<times> {0..<?n}.
          Re (unwrap_lm M $$ (i, i)) * Re (unwrap_lm M $$ (j, j)))"
  proof (rule sum_mono)
    fix x :: "nat \<times> nat"
    assume x_in: "x \<in> {0..<?n} \<times> {0..<?n}"
    obtain a b where x_eq: "x = (a, b)" by (cases x)
    from x_in x_eq have ab: "a < ?n" "b < ?n" by auto
    show "(case x of (i, j) \<Rightarrow> (norm (unwrap_lm M $$ (i, j)))\<^sup>2)
          \<le> (case x of (i, j) \<Rightarrow>
                Re (unwrap_lm M $$ (i, i)) * Re (unwrap_lm M $$ (j, j)))"
      using entry_bound [OF ab(1) ab(2)] by (simp add: x_eq)
  qed
  have prod_eq:
    "(\<Sum>(i, j) \<in> {0..<?n} \<times> {0..<?n}.
        Re (unwrap_lm M $$ (i, i)) * Re (unwrap_lm M $$ (j, j)))
     = (\<Sum>i = 0..<?n. Re (unwrap_lm M $$ (i, i)))
       * (\<Sum>j = 0..<?n. Re (unwrap_lm M $$ (j, j)))"
  proof -
    have "(\<Sum>(i, j) \<in> {0..<?n} \<times> {0..<?n}.
            Re (unwrap_lm M $$ (i, i)) * Re (unwrap_lm M $$ (j, j)))
        = (\<Sum>i = 0..<?n. \<Sum>j = 0..<?n.
            Re (unwrap_lm M $$ (i, i)) * Re (unwrap_lm M $$ (j, j)))"
      by (rule sum.cartesian_product [symmetric])
    also have "\<dots> = (\<Sum>i = 0..<?n. Re (unwrap_lm M $$ (i, i)))
                  * (\<Sum>j = 0..<?n. Re (unwrap_lm M $$ (j, j)))"
      by (rule sum_product [symmetric])
    finally show ?thesis .
  qed
  have Re_tr_one:
    "(\<Sum>i = 0..<?n. Re (unwrap_lm M $$ (i, i))) = 1"
  proof -
    have "(\<Sum>i = 0..<?n. Re (unwrap_lm M $$ (i, i)))
        = Re (\<Sum>i = 0..<?n. unwrap_lm M $$ (i, i))"
      by (rule Re_sum [symmetric])
    also have "\<dots> = Re (Tr (unwrap_lm M))"
      unfolding Tr_def by (simp add: atLeast0LessThan)
    also have "\<dots> = Re (Tr_lmat M)" using Tr_lmat_unwrap by simp
    also have "\<dots> = Re (1 :: complex)" using tr by simp
    also have "\<dots> = 1" by simp
    finally show ?thesis .
  qed
  have norm_sq_le: "(norm M)\<^sup>2 \<le> 1"
  proof -
    have "(norm M)\<^sup>2
        = (\<Sum>(i, j) \<in> {0..<?n} \<times> {0..<?n}.
            (norm (unwrap_lm M $$ (i, j)))\<^sup>2)"
      by (rule norm_sq_eq)
    also have "\<dots> \<le> (\<Sum>(i, j) \<in> {0..<?n} \<times> {0..<?n}.
                      Re (unwrap_lm M $$ (i, i)) * Re (unwrap_lm M $$ (j, j)))"
      using sum_bound .
    also have "\<dots> = (\<Sum>i = 0..<?n. Re (unwrap_lm M $$ (i, i)))
                  * (\<Sum>j = 0..<?n. Re (unwrap_lm M $$ (j, j)))"
      by (rule prod_eq)
    also have "\<dots> = 1 * 1" using Re_tr_one by simp
    also have "\<dots> = 1" by simp
    finally show ?thesis .
  qed
  have nn: "0 \<le> norm M" by (rule norm_ge_zero)
  show "norm M \<le> 1"
    using norm_sq_le nn
    by (smt (verit) one_power2 power2_le_imp_le)
qed

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


section \<open>Tensor continuity\<close>

text \<open>The typed tensor product is jointly continuous in both factors.\<close>

lemma continuous_on_tensor_lmat:
  fixes T :: "((complex, 'm :: finite, 'm) lmat
              \<times> (complex, 'p :: finite, 'p) lmat) set"
  shows "continuous_on T (\<lambda>(\<sigma>, \<tau>). tensor_lmat \<sigma> \<tau>
                                    :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat)"
proof (subst continuous_on_componentwise, intro ballI)
  fix b :: "(complex, 'm \<times> 'p, 'm \<times> 'p) lmat"
  assume "b \<in> Basis"
  hence "b \<in> Basis_lmat_set"
    unfolding Basis_lmat_def by simp
  then obtain I J u where b_eq: "b = lmat_axis I J u"
                     and I_lt: "I < CARD('m \<times> 'p)"
                     and J_lt: "J < CARD('m \<times> 'p)"
                     and uB: "u \<in> (Basis :: complex set)"
    unfolding Basis_lmat_set_def by auto
  let ?M = "CARD('m)"
  let ?P = "CARD('p)"
  have card_eq: "CARD('m \<times> 'p) = ?M * ?P" by simp
  have m_pos: "0 < ?M" by simp
  have p_pos: "0 < ?P" by simp
  have I_lt': "I < ?M * ?P" using I_lt card_eq by simp
  have J_lt': "J < ?M * ?P" using J_lt card_eq by simp
  have rA: "dim_row (unwrap_lm (\<sigma> :: (complex, 'm, 'm) lmat)) = ?M" for \<sigma> by simp
  have cA: "dim_col (unwrap_lm (\<sigma> :: (complex, 'm, 'm) lmat)) = ?M" for \<sigma> by simp
  have rB: "dim_row (unwrap_lm (\<tau> :: (complex, 'p, 'p) lmat)) = ?P" for \<tau> by simp
  have cB: "dim_col (unwrap_lm (\<tau> :: (complex, 'p, 'p) lmat)) = ?P" for \<tau> by simp
  have iI_lt: "I div ?P < ?M" using I_lt' p_pos
    by (metis div_less_iff_less_mult mult.commute)
  have iJ_lt: "J div ?P < ?M" using J_lt' p_pos
    by (metis div_less_iff_less_mult mult.commute)
  have iImod: "I mod ?P < ?P" using p_pos by simp
  have iJmod: "J mod ?P < ?P" using p_pos by simp
  have inner_eq:
    "\<And>\<sigma> :: (complex, 'm, 'm) lmat. \<And>\<tau> :: (complex, 'p, 'p) lmat.
       inner (tensor_lmat \<sigma> \<tau> :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat) b
       = inner (unwrap_lm \<sigma> $$ (I div ?P, J div ?P)
                * unwrap_lm \<tau> $$ (I mod ?P, J mod ?P)) u"
  proof -
    fix \<sigma> :: "(complex, 'm, 'm) lmat" and \<tau> :: "(complex, 'p, 'p) lmat"
    have e0: "inner (tensor_lmat \<sigma> \<tau> :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat)
                    (lmat_axis I J u :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat)
            = inner (unwrap_lm (tensor_lmat \<sigma> \<tau> :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat)
                       $$ (I, J)) u"
      by (rule inner_lmat_axis [OF I_lt J_lt])
    hence e1: "inner (tensor_lmat \<sigma> \<tau> :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat) b
            = inner (unwrap_lm (tensor_lmat \<sigma> \<tau> :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat)
                       $$ (I, J)) u"
      using b_eq by simp
    have e2: "unwrap_lm (tensor_lmat \<sigma> \<tau> :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat) $$ (I, J)
            = unwrap_lm \<sigma> $$ (I div ?P, J div ?P)
              * unwrap_lm \<tau> $$ (I mod ?P, J mod ?P)"
      using index_tensor_mat [OF rA cA rB cB I_lt' J_lt' m_pos p_pos] by simp
    show "inner (tensor_lmat \<sigma> \<tau> :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat) b
        = inner (unwrap_lm \<sigma> $$ (I div ?P, J div ?P)
                  * unwrap_lm \<tau> $$ (I mod ?P, J mod ?P)) u"
      using e1 e2 by simp
  qed
  have cont_sigma_entry:
    "continuous_on T
       (\<lambda>p. unwrap_lm (fst p :: (complex, 'm, 'm) lmat) $$ (I div ?P, J div ?P))"
  proof -
    have c_proj: "continuous_on T (fst :: ((complex, 'm, 'm) lmat \<times> (complex, 'p, 'p) lmat)
                                          \<Rightarrow> (complex, 'm, 'm) lmat)"
      by (rule continuous_on_fst [OF continuous_on_id])
    have c_entry: "continuous_on (fst ` T)
                    (\<lambda>\<sigma> :: (complex, 'm, 'm) lmat.
                       unwrap_lm \<sigma> $$ (I div ?P, J div ?P))"
      by (rule continuous_on_unwrap_lm_index [OF iI_lt iJ_lt])
    show ?thesis
      using continuous_on_compose [OF c_proj c_entry] by (simp add: o_def)
  qed
  have cont_tau_entry:
    "continuous_on T
       (\<lambda>p. unwrap_lm (snd p :: (complex, 'p, 'p) lmat) $$ (I mod ?P, J mod ?P))"
  proof -
    have c_proj: "continuous_on T (snd :: ((complex, 'm, 'm) lmat \<times> (complex, 'p, 'p) lmat)
                                          \<Rightarrow> (complex, 'p, 'p) lmat)"
      by (rule continuous_on_snd [OF continuous_on_id])
    have c_entry: "continuous_on (snd ` T)
                    (\<lambda>\<tau> :: (complex, 'p, 'p) lmat.
                       unwrap_lm \<tau> $$ (I mod ?P, J mod ?P))"
      by (rule continuous_on_unwrap_lm_index [OF iImod iJmod])
    show ?thesis
      using continuous_on_compose [OF c_proj c_entry] by (simp add: o_def)
  qed
  have cont_product: "continuous_on T
       (\<lambda>p. unwrap_lm (fst p) $$ (I div ?P, J div ?P)
            * unwrap_lm (snd p) $$ (I mod ?P, J mod ?P))"
    using cont_sigma_entry cont_tau_entry by (rule continuous_on_mult)
  have cont_inner: "continuous_on T
       (\<lambda>p. inner (unwrap_lm (fst p) $$ (I div ?P, J div ?P)
                    * unwrap_lm (snd p) $$ (I mod ?P, J mod ?P)) u)"
    using cont_product continuous_on_const by (rule continuous_on_inner)
  have target_eq:
    "\<And>p :: (complex, 'm, 'm) lmat \<times> (complex, 'p, 'p) lmat.
        inner ((\<lambda>(\<sigma>, \<tau>). tensor_lmat \<sigma> \<tau>
                  :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat) p) b
      = inner (unwrap_lm (fst p) $$ (I div ?P, J div ?P)
                * unwrap_lm (snd p) $$ (I mod ?P, J mod ?P)) u"
  proof -
    fix p :: "(complex, 'm, 'm) lmat \<times> (complex, 'p, 'p) lmat"
    obtain \<sigma> \<tau> where p_eq: "p = (\<sigma>, \<tau>)" by (cases p)
    have "inner ((\<lambda>(\<sigma>, \<tau>). tensor_lmat \<sigma> \<tau>
                  :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat) p) b
        = inner (tensor_lmat \<sigma> \<tau> :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat) b"
      using p_eq by simp
    also have "\<dots> = inner (unwrap_lm \<sigma> $$ (I div ?P, J div ?P)
                            * unwrap_lm \<tau> $$ (I mod ?P, J mod ?P)) u"
      by (rule inner_eq)
    also have "\<dots> = inner (unwrap_lm (fst p) $$ (I div ?P, J div ?P)
                            * unwrap_lm (snd p) $$ (I mod ?P, J mod ?P)) u"
      using p_eq by simp
    finally show "inner ((\<lambda>(\<sigma>, \<tau>). tensor_lmat \<sigma> \<tau>
                            :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat) p) b
                = inner (unwrap_lm (fst p) $$ (I div ?P, J div ?P)
                          * unwrap_lm (snd p) $$ (I mod ?P, J mod ?P)) u" .
  qed
  show "continuous_on T (\<lambda>x. inner ((\<lambda>(\<sigma>, \<tau>). tensor_lmat \<sigma> \<tau>
                                       :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat) x) b)"
    using cont_inner target_eq
    by (auto cong: continuous_on_cong)
qed


section \<open>The unit-trace product slice\<close>

definition Sprime :: "(complex, 'm :: finite \<times> 'p :: finite, 'm \<times> 'p) lmat set"
  where
  "Sprime =
   {\<rho>. \<exists>(\<sigma> :: (complex, 'm, 'm) lmat) (\<tau> :: (complex, 'p, 'p) lmat).
         \<rho> = tensor_lmat \<sigma> \<tau>
         \<and> psd_lmat \<sigma> \<and> Tr_lmat \<sigma> = 1
         \<and> psd_lmat \<tau> \<and> Tr_lmat \<tau> = 1}"

lemma Sprime_image:
  "(Sprime :: (complex, 'm :: finite \<times> 'p :: finite, 'm \<times> 'p) lmat set)
   = (\<lambda>(\<sigma>, \<tau>). tensor_lmat \<sigma> \<tau>) `
       ({\<sigma> :: (complex, 'm, 'm) lmat. psd_lmat \<sigma> \<and> Tr_lmat \<sigma> = 1}
        \<times> {\<tau> :: (complex, 'p, 'p) lmat. psd_lmat \<tau> \<and> Tr_lmat \<tau> = 1})"
  unfolding Sprime_def by auto

lemma compact_Sprime:
  "compact (Sprime :: (complex, 'm :: finite \<times> 'p :: finite, 'm \<times> 'p) lmat set)"
proof -
  let ?A = "{\<sigma> :: (complex, 'm, 'm) lmat. psd_lmat \<sigma> \<and> Tr_lmat \<sigma> = 1}"
  let ?B = "{\<tau> :: (complex, 'p, 'p) lmat. psd_lmat \<tau> \<and> Tr_lmat \<tau> = 1}"
  have cA: "compact ?A" by (rule compact_unit_trace_psd_lmat)
  have cB: "compact ?B" by (rule compact_unit_trace_psd_lmat)
  have prod_compact: "compact (?A \<times> ?B)" using cA cB by (rule compact_Times)
  have cont: "continuous_on (?A \<times> ?B)
                (\<lambda>(\<sigma>, \<tau>). tensor_lmat \<sigma> \<tau> :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat)"
    by (rule continuous_on_tensor_lmat)
  show ?thesis
    unfolding Sprime_image
    by (rule compact_continuous_image [OF cont prod_compact])
qed

text \<open>Reindex \<open>{0..<n*q}\<close> via (div, mod) into \<open>{0..<n} \<times> {0..<q}\<close>.\<close>

lemma sum_div_mod_split:
  fixes f :: "nat \<Rightarrow> nat \<Rightarrow> 'a :: comm_monoid_add"
  assumes q_pos: "0 < q"
  shows "(\<Sum>a = 0..<n. \<Sum>b = 0..<q. f a b)
       = (\<Sum>i = 0..<n * q. f (i div q) (i mod q))"
proof -
  have inner: "(\<Sum>(a, b) \<in> {0..<n} \<times> {0..<q}. f a b)
             = (\<Sum>i = 0..<n * q. f (i div q) (i mod q))"
  proof (rule sum.reindex_bij_witness
                [where j = "\<lambda>(a, b). a * q + b"
                  and i = "\<lambda>k. (k div q, k mod q)"])
    show "\<And>p. p \<in> {0..<n} \<times> {0..<q}
              \<Longrightarrow> (\<lambda>k. (k div q, k mod q)) ((\<lambda>(a, b). a * q + b) p) = p"
      using q_pos by auto
  next
    show "\<And>p. p \<in> {0..<n} \<times> {0..<q}
              \<Longrightarrow> (\<lambda>(a, b). a * q + b) p \<in> {0..<n * q}"
    proof -
      fix p assume p_in: "p \<in> {0..<n} \<times> {0..<q}"
      then obtain a b where p_eq: "p = (a, b)" and a_lt: "a < n" and b_lt: "b < q"
        by auto
      have "a + 1 \<le> n" using a_lt by simp
      hence "(a + 1) * q \<le> n * q" by (rule mult_le_mono1)
      hence "a * q + q \<le> n * q" by (simp add: distrib_right)
      hence "a * q + b < n * q" using b_lt by linarith
      thus "(\<lambda>(a, b). a * q + b) p \<in> {0..<n * q}" using p_eq by simp
    qed
  next
    show "\<And>k. k \<in> {0..<n * q}
              \<Longrightarrow> (\<lambda>(a, b). a * q + b) ((\<lambda>k. (k div q, k mod q)) k) = k"
      by simp
  next
    show "\<And>k. k \<in> {0..<n * q}
              \<Longrightarrow> (\<lambda>k. (k div q, k mod q)) k \<in> {0..<n} \<times> {0..<q}"
    proof -
      fix k :: nat assume k_in: "k \<in> {0..<n * q}"
      hence k_lt: "k < n * q" by simp
      have div_lt: "k div q < n" using k_lt q_pos
        by (metis atLeastLessThan_iff div_less_iff_less_mult less_nat_zero_code mult.commute)
      have mod_lt: "k mod q < q" using q_pos by simp
      show "(\<lambda>k. (k div q, k mod q)) k \<in> {0..<n} \<times> {0..<q}"
        using div_lt mod_lt by auto
    qed
  next
    show "\<And>p. p \<in> {0..<n} \<times> {0..<q}
              \<Longrightarrow> f ((\<lambda>(a, b). a * q + b) p div q)
                    ((\<lambda>(a, b). a * q + b) p mod q)
                  = (case p of (a, b) \<Rightarrow> f a b)"
      using q_pos by auto
  qed
  have outer: "(\<Sum>a = 0..<n. \<Sum>b = 0..<q. f a b)
             = (\<Sum>(a, b) \<in> {0..<n} \<times> {0..<q}. f a b)"
    by (subst sum.cartesian_product) simp
  show ?thesis using outer inner by simp
qed

lemma Tr_lmat_tensor:
  fixes \<sigma> :: "(complex, 'm :: finite, 'm) lmat"
    and \<tau> :: "(complex, 'p :: finite, 'p) lmat"
  shows "Tr_lmat (tensor_lmat \<sigma> \<tau> :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat)
       = Tr_lmat \<sigma> * Tr_lmat \<tau>"
proof -
  let ?M = "CARD('m)"
  let ?P = "CARD('p)"
  have card_eq: "CARD('m \<times> 'p) = ?M * ?P" by simp
  have m_pos: "0 < ?M" by simp
  have p_pos: "0 < ?P" by simp
  have un_eq: "unwrap_lm (tensor_lmat \<sigma> \<tau> :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat)
             = unwrap_lm \<sigma> \<Otimes> unwrap_lm \<tau>"
    by simp
  have rA: "dim_row (unwrap_lm \<sigma>) = ?M" by simp
  have cA: "dim_col (unwrap_lm \<sigma>) = ?M" by simp
  have rB: "dim_row (unwrap_lm \<tau>) = ?P" by simp
  have cB: "dim_col (unwrap_lm \<tau>) = ?P" by simp
  have step1: "Tr_lmat (tensor_lmat \<sigma> \<tau> :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat)
             = (\<Sum>i = 0..<?M * ?P.
                  (unwrap_lm \<sigma> \<Otimes> unwrap_lm \<tau>) $$ (i, i))"
    unfolding Tr_lmat_def using un_eq card_eq by simp
  have step2: "(\<Sum>i = 0..<?M * ?P. (unwrap_lm \<sigma> \<Otimes> unwrap_lm \<tau>) $$ (i, i))
             = (\<Sum>i = 0..<?M * ?P.
                  unwrap_lm \<sigma> $$ (i div ?P, i div ?P)
                  * unwrap_lm \<tau> $$ (i mod ?P, i mod ?P))"
  proof (rule sum.cong, simp)
    fix i assume i_in: "i \<in> {0..<?M * ?P}"
    hence i_lt: "i < ?M * ?P" by simp
    have div_lt: "i div ?P < ?M"
      using i_lt p_pos div_less_iff_less_mult by (metis mult.commute)
    have mod_lt: "i mod ?P < ?P" using p_pos by simp
    show "(unwrap_lm \<sigma> \<Otimes> unwrap_lm \<tau>) $$ (i, i)
        = unwrap_lm \<sigma> $$ (i div ?P, i div ?P)
          * unwrap_lm \<tau> $$ (i mod ?P, i mod ?P)"
      using index_tensor_mat[OF rA cA rB cB i_lt i_lt m_pos p_pos] .
  qed
  have step3: "(\<Sum>i = 0..<?M * ?P.
                  unwrap_lm \<sigma> $$ (i div ?P, i div ?P)
                  * unwrap_lm \<tau> $$ (i mod ?P, i mod ?P))
             = (\<Sum>q = 0..<?M. \<Sum>r = 0..<?P.
                  unwrap_lm \<sigma> $$ (q, q) * unwrap_lm \<tau> $$ (r, r))"
    using sum_div_mod_split [OF p_pos,
              where f = "\<lambda>q r. unwrap_lm \<sigma> $$ (q, q) * unwrap_lm \<tau> $$ (r, r)"]
    by simp
  have step4: "(\<Sum>q = 0..<?M. \<Sum>r = 0..<?P.
                  unwrap_lm \<sigma> $$ (q, q) * unwrap_lm \<tau> $$ (r, r))
             = (\<Sum>q = 0..<?M. unwrap_lm \<sigma> $$ (q, q))
               * (\<Sum>r = 0..<?P. unwrap_lm \<tau> $$ (r, r))"
    by (simp add: sum_product)
  show ?thesis
    using step1 step2 step3 step4 unfolding Tr_lmat_def by simp
qed

lemma zero_not_in_Sprime:
  "(0 :: (complex, 'm :: finite \<times> 'p :: finite, 'm \<times> 'p) lmat) \<notin> Sprime"
proof
  assume "(0 :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat) \<in> Sprime"
  then obtain \<sigma> \<tau> where eq: "(0 :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat) = tensor_lmat \<sigma> \<tau>"
                  and tr_s: "Tr_lmat (\<sigma> :: (complex, 'm, 'm) lmat) = 1"
                  and tr_t: "Tr_lmat (\<tau> :: (complex, 'p, 'p) lmat) = 1"
    unfolding Sprime_def by auto
  have "Tr_lmat (0 :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat) = 0"
    unfolding Tr_lmat_def by simp
  also have "Tr_lmat (0 :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat)
              = Tr_lmat (tensor_lmat \<sigma> \<tau> :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat)"
    using eq by simp
  also have "\<dots> = Tr_lmat \<sigma> * Tr_lmat \<tau>" by (rule Tr_lmat_tensor)
  also have "\<dots> = 1" using tr_s tr_t by simp
  finally have "(0 :: complex) = 1" by simp
  thus False by simp
qed


section \<open>Closedness of the separable cone\<close>

text \<open>
Proof strategy (uses the typeclass tower from \<open>Lmat_Euclidean\<close>):

Let \<open>S' = {tensor_lmat \<sigma> \<tau> | \<sigma> \<tau>. psd_lmat \<sigma> \<and> psd_lmat \<tau> \<and>
                                Tr (unwrap_lm \<sigma>) = 1 \<and> Tr (unwrap_lm \<tau>) = 1}\<close>
be the unit-trace product slice.

\begin{enumerate}
\item \textbf{S' is compact.}
  \begin{itemize}
  \item \<open>{\<sigma> :: lmat. psd_lmat \<sigma>}\<close> is closed (entry-wise lift of the
        Hermitian condition + entry-wise lift of the quadratic-form
        nonnegativity, both via \<open>tendsto_unwrap_lm_index\<close>).
  \item \<open>{\<sigma> :: lmat. Re (Tr (unwrap_lm \<sigma>)) = 1}\<close> is closed (trace is
        continuous in entries, via \<open>tendsto_unwrap_lm_index\<close>).
  \item PSD + unit-trace is bounded: \<open>norm \<sigma>\<^sup>2 = Re Tr (\<sigma>\<^sup>\<dagger> \<sigma>) \<le> Tr \<sigma> \<cdot> \<lambda>\<^sub>m\<^sub>a\<^sub>x \<le> 1\<close>.
  \item Closed + bounded in finite-dimensional \<open>real_inner\<close> = compact
        (\<open>bounded_closed_imp_seq_compact\<close> + heine_borel).
  \item \<open>tensor_lmat\<close> is continuous (entries are bilinear in
        the entries of the factors, lifts via the typeclass).
  \item \<open>S'\<close> is the image of (compact) \<times> (compact) under
        \<open>tensor_lmat\<close>, hence compact.
  \end{itemize}

\item \textbf{convex hull S' is compact} via \<open>compact_convex_hull\<close>
  (applies because every euclidean_space is a real_inner finite-dimensional
  space).

\item \textbf{0 \<notin> convex hull S'.} Every element of \<open>convex hull S'\<close> has
  trace 1 (linear combinations of trace-1 matrices with nonneg
  coefficients summing to 1), while 0 has trace 0.

\item \textbf{separable_lmat_gen = conic hull S'.} Each \<open>tensor_lmat \<sigma> \<tau>\<close>
  with \<open>\<sigma>, \<tau>\<close> PSD equals \<open>(Tr \<sigma> \<cdot> Tr \<tau>) \<cdot> tensor_lmat (\<sigma>/Tr \<sigma>) (\<tau>/Tr \<tau>)\<close>
  when traces are positive, and equals \<open>0\<close> when one trace is 0
  (in which case the corresponding factor is itself 0 because
  PSD + Tr = 0 \<Rightarrow> 0).

\item \textbf{Putting it together.}
  \<open>separable_cone_lmat = convex_cone hull separable_lmat_gen
                       = convex_cone hull (conic hull S')
                       = convex_cone hull S'
                       = conic hull (convex hull S')\<close>
  (the last by \<open>convex_cone_hull_separate_nonempty\<close>).
  Apply \<open>closed_conic_hull\<close> with the (compact, \<open>0 \<notin> \<dots>\<close>) clause.
\end{enumerate}

The infrastructure for all of these steps is now available
(\<open>norm\<close>, \<open>inner\<close>, \<open>dist\<close>, \<open>compact\<close>,
\<open>convex\<close>, \<open>convex_cone\<close>, etc. all defined for typed lmat
via the euclidean_space + heine_borel instances).
\<close>

text \<open>The convex cone hulls of \<open>separable_lmat_gen\<close> and \<open>Sprime\<close>
coincide: every \<open>tensor_lmat \<sigma> \<tau>\<close> with \<open>\<sigma>, \<tau>\<close> PSD can be rescaled
into \<open>Sprime\<close> by dividing by traces (when nonzero) or replaced by
0 when a trace is zero.\<close>

text \<open>The hard direction depends on three facts that each lift a
spectral / bilinearity property:

  psd_lmat_scaleR     – PSD preserved under nonneg real scaling
  psd_lmat_zero_trace_zero  – PSD with Tr = 0 is the zero matrix
  tensor_lmat_scaleR_{left,right}  – tensor is bilinear over real scaling
  psd_lmat_Tr_real_nonneg   – Tr of PSD is a real nonneg complex.

These reduce \<open>tensor \<sigma> \<tau>\<close> with \<open>\<sigma>, \<tau>\<close> PSD to
\<open>(Tr \<sigma> * Tr \<tau>) *\<^sub>R tensor (\<sigma>/Tr \<sigma>) (\<tau>/Tr \<tau>)\<close> when traces are positive,
or to 0 when one is zero — both forms in \<open>convex_cone hull Sprime\<close>.\<close>

lemma Sprime_subset_separable_lmat_gen:
  "(Sprime :: (complex, 'm :: finite \<times> 'p :: finite, 'm \<times> 'p) lmat set)
   \<subseteq> separable_lmat_gen"
proof
  fix x :: "(complex, 'm \<times> 'p, 'm \<times> 'p) lmat"
  assume "x \<in> Sprime"
  then obtain \<sigma> \<tau>
    where x_eq: "x = tensor_lmat \<sigma> \<tau>"
      and \<sigma>_psd: "psd_lmat (\<sigma> :: (complex, 'm, 'm) lmat)"
      and \<tau>_psd: "psd_lmat (\<tau> :: (complex, 'p, 'p) lmat)"
    unfolding Sprime_def by auto
  show "x \<in> separable_lmat_gen"
    unfolding separable_lmat_gen_def using x_eq \<sigma>_psd \<tau>_psd by auto
qed

text \<open>The four spectral / bilinearity helpers needed for the
hard direction.  Each is a one-line lift of a JNF fact, but the
JNF facts (spectral closure and tensor scaleR) live outside the
parent heap so they are stated as targeted sorries here for the
moment.\<close>

lemma psd_lmat_Tr_real_nonneg:
  fixes M :: "(complex, 'k :: finite, 'k) lmat"
  assumes M_psd: "psd_lmat M"
  shows "Im (Tr_lmat M) = 0 \<and> 0 \<le> Re (Tr_lmat M)"
proof -
  let ?n = "CARD('k)"
  have M_unwrap_psd: "psd (unwrap_lm M)" using M_psd by simp
  have M_carr: "unwrap_lm M \<in> carrier_mat ?n ?n" by simp
  have hermM: "hermitian (unwrap_lm M)" using M_unwrap_psd by (rule psd_hermitian)
  have diag_real_nn:
    "\<And>i. i < ?n
       \<Longrightarrow> Im (unwrap_lm M $$ (i, i)) = 0 \<and> 0 \<le> Re (unwrap_lm M $$ (i, i))"
  proof -
    fix i :: nat assume i_lt: "i < ?n"
    have e_inner: "\<langle>unit_vec ?n i | unwrap_lm M *\<^sub>v unit_vec ?n i\<rangle>
                 = unwrap_lm M $$ (i, i)"
      using inner_unit_T_unit [OF M_carr i_lt i_lt] .
    have e_dim_n: "dim_vec (unit_vec ?n i :: complex Matrix.vec) = ?n"
      by simp
    have e_dim_r: "dim_vec (unit_vec ?n i :: complex Matrix.vec) = dim_row (unwrap_lm M)"
      by simp
    have re_nn: "0 \<le> Re \<langle>unit_vec ?n i | unwrap_lm M *\<^sub>v unit_vec ?n i\<rangle>"
      using M_unwrap_psd e_dim_r unfolding psd_def by blast
    have quad_real: "\<langle>unit_vec ?n i | unwrap_lm M *\<^sub>v unit_vec ?n i\<rangle> \<in> \<real>"
      using hermitian_iff_real_quad_form [OF M_carr, THEN iffD1, OF hermM,
                                          rule_format, OF e_dim_n] .
    have im_zero: "Im \<langle>unit_vec ?n i | unwrap_lm M *\<^sub>v unit_vec ?n i\<rangle> = 0"
      using quad_real complex_is_Real_iff by auto
    show "Im (unwrap_lm M $$ (i, i)) = 0 \<and> 0 \<le> Re (unwrap_lm M $$ (i, i))"
      using e_inner re_nn im_zero by simp
  qed
  have im_tr: "Im (Tr_lmat M) = 0"
    unfolding Tr_lmat_def
    by (subst Im_sum) (auto simp: diag_real_nn)
  have re_tr: "0 \<le> Re (Tr_lmat M)"
    unfolding Tr_lmat_def
    by (subst Re_sum) (auto intro: sum_nonneg simp: diag_real_nn)
  show ?thesis using im_tr re_tr by simp
qed

lemma psd_lmat_zero_trace_zero:
  fixes M :: "(complex, 'k :: finite, 'k) lmat"
  assumes M_psd: "psd_lmat M" and tr_zero: "Tr_lmat M = 0"
  shows "M = 0"
proof -
  let ?n = "CARD('k)"
  have psd_unwrap: "psd (unwrap_lm M)" using M_psd by simp
  have unwrap_carr: "unwrap_lm M \<in> carrier_mat ?n ?n" by simp
  obtain Q :: "complex Matrix.mat" where
      Q_carr: "Q \<in> carrier_mat ?n ?n"
    and Q_psd: "psd Q"
    and QQ: "Q * Q = unwrap_lm M"
    using psd_sqrt_exists [OF unwrap_carr psd_unwrap] by blast
  have Q_herm: "hermitian Q" using Q_psd by (rule psd_hermitian)
  have Q_dag: "Q\<^sup>\<dagger> = Q" using Q_herm by (simp add: hermitian_def)
  have ip_self_eq:
    "\<langle>\<langle> Q | Q \<rangle>\<rangle> = Tr (Q\<^sup>\<dagger> * Q)"
    by (rule hs_inner_prod_self_as_trace)
  have Tr_unwrap_eq_Tr_QQ: "Tr (unwrap_lm M) = Tr (Q * Q)"
    using QQ by simp
  have Tr_lmat_unwrap: "Tr_lmat M = Tr (unwrap_lm M)"
    unfolding Tr_lmat_def Tr_def
    by (simp add: atLeast0LessThan)
  have ip_zero: "\<langle>\<langle> Q | Q \<rangle>\<rangle> = 0"
  proof -
    have "\<langle>\<langle> Q | Q \<rangle>\<rangle> = Tr (Q\<^sup>\<dagger> * Q)" by (rule ip_self_eq)
    also have "\<dots> = Tr (Q * Q)" using Q_dag by simp
    also have "\<dots> = Tr (unwrap_lm M)" using QQ by simp
    also have "\<dots> = Tr_lmat M" using Tr_lmat_unwrap by simp
    also have "\<dots> = 0" using tr_zero .
    finally show ?thesis .
  qed
  have Q_dim_row: "dim_row Q = ?n" using Q_carr by simp
  have Q_dim_col: "dim_col Q = ?n" using Q_carr by simp
  have Q_entries_zero:
    "\<And>i j. i < ?n \<Longrightarrow> j < ?n \<Longrightarrow> Q $$ (i, j) = 0"
    using ip_zero hs_inner_prod_eq_zero_imp Q_dim_row Q_dim_col by force
  have Q_zero: "Q = 0\<^sub>m ?n ?n"
    using Q_carr Q_entries_zero by (intro eq_matI) (auto simp: zero_mat_def)
  have unwrap_M_zero: "unwrap_lm M = 0\<^sub>m ?n ?n"
  proof -
    have "unwrap_lm M = Q * Q" using QQ by simp
    also have "\<dots> = (0\<^sub>m ?n ?n :: complex Matrix.mat) * 0\<^sub>m ?n ?n"
      using Q_zero by simp
    also have "\<dots> = 0\<^sub>m ?n ?n" by simp
    finally show ?thesis .
  qed
  have "unwrap_lm M = unwrap_lm (0 :: (complex, 'k, 'k) lmat)"
    using unwrap_M_zero by simp
  thus "M = 0" by (simp only: unwrap_lm_inject)
qed

lemma psd_smult_nonneg_local:
  fixes A :: "complex Matrix.mat" and c :: real
  assumes c: "0 \<le> c"
      and A: "psd A" and Ac: "A \<in> carrier_mat n n"
  shows "psd (complex_of_real c \<cdot>\<^sub>m A)"
proof -
  have A_dagger: "A\<^sup>\<dagger> = A" using A by (simp add: psd_def hermitian_def)
  have A_quad: "\<And>x. dim_vec x = n \<Longrightarrow> Re \<langle>x | A *\<^sub>v x\<rangle> \<ge> 0"
    using A Ac by (simp add: psd_def)
  have herm_cA: "(complex_of_real c \<cdot>\<^sub>m A)\<^sup>\<dagger> = complex_of_real c \<cdot>\<^sub>m A"
  proof -
    have "(complex_of_real c \<cdot>\<^sub>m A)\<^sup>\<dagger>
        = (cnj (complex_of_real c)) \<cdot>\<^sub>m (A\<^sup>\<dagger>)"
      by (rule dagger_of_smult)
    also have "\<dots> = complex_of_real c \<cdot>\<^sub>m A" using A_dagger by simp
    finally show ?thesis .
  qed
  have smult_mv:
    "\<And>x. x \<in> carrier_vec n \<Longrightarrow>
         (complex_of_real c \<cdot>\<^sub>m A) *\<^sub>v x = complex_of_real c \<cdot>\<^sub>v (A *\<^sub>v x)"
  proof -
    fix x :: "complex Matrix.vec" assume x_car: "x \<in> carrier_vec n"
    show "(complex_of_real c \<cdot>\<^sub>m A) *\<^sub>v x = complex_of_real c \<cdot>\<^sub>v (A *\<^sub>v x)"
    proof (rule eq_vecI)
      show "dim_vec ((complex_of_real c \<cdot>\<^sub>m A) *\<^sub>v x)
          = dim_vec (complex_of_real c \<cdot>\<^sub>v (A *\<^sub>v x))"
        using Ac by simp
    next
      fix i assume "i < dim_vec (complex_of_real c \<cdot>\<^sub>v (A *\<^sub>v x))"
      hence i: "i < n" using Ac by simp
      have r1: "Matrix.row A i \<in> carrier_vec n" using Ac i by auto
      have i_dr: "i < dim_row A" using i Ac by simp
      have "((complex_of_real c \<cdot>\<^sub>m A) *\<^sub>v x) $ i
            = Matrix.row (complex_of_real c \<cdot>\<^sub>m A) i \<bullet> x"
        using i Ac by auto
      also have "\<dots> = (complex_of_real c \<cdot>\<^sub>v Matrix.row A i) \<bullet> x"
        using row_smult[OF i_dr] by simp
      also have "\<dots> = complex_of_real c * (Matrix.row A i \<bullet> x)"
        using r1 x_car by simp
      also have "\<dots> = complex_of_real c * (A *\<^sub>v x) $ i"
        using i Ac by auto
      also have "\<dots> = (complex_of_real c \<cdot>\<^sub>v (A *\<^sub>v x)) $ i"
        using i Ac by auto
      finally show "((complex_of_real c \<cdot>\<^sub>m A) *\<^sub>v x) $ i
                  = (complex_of_real c \<cdot>\<^sub>v (A *\<^sub>v x)) $ i" .
    qed
  qed
  have quad: "\<And>x. dim_vec x = dim_row (complex_of_real c \<cdot>\<^sub>m A)
                  \<Longrightarrow> Re \<langle>x | (complex_of_real c \<cdot>\<^sub>m A) *\<^sub>v x\<rangle> \<ge> 0"
  proof -
    fix x :: "complex Matrix.vec"
    assume dx: "dim_vec x = dim_row (complex_of_real c \<cdot>\<^sub>m A)"
    hence dx': "dim_vec x = n" using Ac by simp
    have x_car: "x \<in> carrier_vec n" using dx' by auto
    have "\<langle>x | (complex_of_real c \<cdot>\<^sub>m A) *\<^sub>v x\<rangle>
        = \<langle>x | complex_of_real c \<cdot>\<^sub>v (A *\<^sub>v x)\<rangle>"
      using smult_mv[OF x_car] by simp
    also have "\<dots> = complex_of_real c * \<langle>x | A *\<^sub>v x\<rangle>"
      by (rule inner_prod_right_smult')
    finally have eq: "\<langle>x | (complex_of_real c \<cdot>\<^sub>m A) *\<^sub>v x\<rangle>
                    = complex_of_real c * \<langle>x | A *\<^sub>v x\<rangle>" .
    have Re_split: "Re (complex_of_real c * \<langle>x | A *\<^sub>v x\<rangle>)
                  = c * Re \<langle>x | A *\<^sub>v x\<rangle>"
      by simp
    have "0 \<le> c * Re \<langle>x | A *\<^sub>v x\<rangle>"
      using c A_quad[OF dx'] by (rule mult_nonneg_nonneg)
    thus "0 \<le> Re \<langle>x | (complex_of_real c \<cdot>\<^sub>m A) *\<^sub>v x\<rangle>"
      using eq Re_split by simp
  qed
  show ?thesis
    unfolding psd_def hermitian_def using herm_cA quad by blast
qed

lemma unwrap_lm_scaleR_eq:
  fixes M :: "(complex, 'm :: finite, 'n :: finite) lmat" and a :: real
  shows "unwrap_lm (a *\<^sub>R M) = complex_of_real a \<cdot>\<^sub>m unwrap_lm M"
proof (rule eq_matI)
  show "dim_row (unwrap_lm (a *\<^sub>R M)) = dim_row (complex_of_real a \<cdot>\<^sub>m unwrap_lm M)"
    by simp
  show "dim_col (unwrap_lm (a *\<^sub>R M)) = dim_col (complex_of_real a \<cdot>\<^sub>m unwrap_lm M)"
    by simp
next
  fix i j
  assume "i < dim_row (complex_of_real a \<cdot>\<^sub>m unwrap_lm M)"
     and "j < dim_col (complex_of_real a \<cdot>\<^sub>m unwrap_lm M)"
  hence ij: "i < CARD('m)" "j < CARD('n)" by simp_all
  have "unwrap_lm (a *\<^sub>R M) $$ (i, j) = a *\<^sub>R (unwrap_lm M $$ (i, j))"
    using ij by (rule unwrap_lm_scaleR_index)
  also have "\<dots> = complex_of_real a * (unwrap_lm M $$ (i, j))"
    by (simp add: scaleR_conv_of_real)
  also have "\<dots> = (complex_of_real a \<cdot>\<^sub>m unwrap_lm M) $$ (i, j)"
    using ij by simp
  finally show "unwrap_lm (a *\<^sub>R M) $$ (i, j)
              = (complex_of_real a \<cdot>\<^sub>m unwrap_lm M) $$ (i, j)" .
qed

lemma psd_lmat_scaleR_nonneg:
  fixes M :: "(complex, 'k :: finite, 'k) lmat" and a :: real
  assumes M_psd: "psd_lmat M" and a_nn: "0 \<le> a"
  shows "psd_lmat (a *\<^sub>R M)"
proof -
  have M_jnf_psd: "psd (unwrap_lm M)" using M_psd by simp
  have M_jnf_carr: "unwrap_lm M \<in> carrier_mat (CARD('k)) (CARD('k))" by simp
  have psd_jnf: "psd (complex_of_real a \<cdot>\<^sub>m unwrap_lm M)"
    by (rule psd_smult_nonneg_local [OF a_nn M_jnf_psd M_jnf_carr])
  have unwrap_eq: "unwrap_lm (a *\<^sub>R M) = complex_of_real a \<cdot>\<^sub>m unwrap_lm M"
    by (rule unwrap_lm_scaleR_eq)
  have "psd (unwrap_lm (a *\<^sub>R M))"
    using psd_jnf unwrap_eq by simp
  thus ?thesis by simp
qed

lemma tensor_lmat_scaleR_left:
  fixes a :: real
    and \<sigma> :: "(complex, 'm :: finite, 'm) lmat"
    and \<tau> :: "(complex, 'p :: finite, 'p) lmat"
  shows "(tensor_lmat (a *\<^sub>R \<sigma>) \<tau>
            :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat)
       = a *\<^sub>R tensor_lmat \<sigma> \<tau>"
proof (subst lmat_eq_iff_entries, intro allI impI)
  fix I J :: nat
  assume IJ: "I < CARD('m \<times> 'p)" "J < CARD('m \<times> 'p)"
  let ?M = "CARD('m)"
  let ?P = "CARD('p)"
  have card_eq: "CARD('m \<times> 'p) = ?M * ?P" by simp
  have m_pos: "0 < ?M" by simp
  have p_pos: "0 < ?P" by simp
  have I_lt: "I < ?M * ?P" using IJ(1) card_eq by simp
  have J_lt: "J < ?M * ?P" using IJ(2) card_eq by simp
  have I_div: "I div ?P < ?M" using I_lt p_pos
    by (metis div_less_iff_less_mult mult.commute)
  have J_div: "J div ?P < ?M" using J_lt p_pos
    by (metis div_less_iff_less_mult mult.commute)
  have I_mod: "I mod ?P < ?P" using p_pos by simp
  have J_mod: "J mod ?P < ?P" using p_pos by simp
  have rA: "dim_row (unwrap_lm \<sigma>) = ?M" "dim_col (unwrap_lm \<sigma>) = ?M" by simp_all
  have rA': "dim_row (unwrap_lm (a *\<^sub>R \<sigma>)) = ?M" "dim_col (unwrap_lm (a *\<^sub>R \<sigma>)) = ?M"
    by simp_all
  have rB: "dim_row (unwrap_lm \<tau>) = ?P" "dim_col (unwrap_lm \<tau>) = ?P" by simp_all
  have lhs_entry:
    "unwrap_lm (tensor_lmat (a *\<^sub>R \<sigma>) \<tau> :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat) $$ (I, J)
      = unwrap_lm (a *\<^sub>R \<sigma>) $$ (I div ?P, J div ?P)
        * unwrap_lm \<tau> $$ (I mod ?P, J mod ?P)"
  proof -
    have "unwrap_lm (tensor_lmat (a *\<^sub>R \<sigma>) \<tau>
                       :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat) $$ (I, J)
        = (unwrap_lm (a *\<^sub>R \<sigma>) \<Otimes> unwrap_lm \<tau>) $$ (I, J)" by simp
    also have "\<dots> = unwrap_lm (a *\<^sub>R \<sigma>) $$ (I div ?P, J div ?P)
                    * unwrap_lm \<tau> $$ (I mod ?P, J mod ?P)"
      using index_tensor_mat [OF rA'(1) rA'(2) rB(1) rB(2) I_lt J_lt m_pos p_pos] .
    finally show ?thesis .
  qed
  have rhs_entry:
    "unwrap_lm (a *\<^sub>R tensor_lmat \<sigma> \<tau> :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat) $$ (I, J)
      = a *\<^sub>R (unwrap_lm (tensor_lmat \<sigma> \<tau> :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat) $$ (I, J))"
    using IJ unwrap_lm_scaleR_index by simp
  have tensor_entry:
    "unwrap_lm (tensor_lmat \<sigma> \<tau> :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat) $$ (I, J)
      = unwrap_lm \<sigma> $$ (I div ?P, J div ?P)
        * unwrap_lm \<tau> $$ (I mod ?P, J mod ?P)"
  proof -
    have "unwrap_lm (tensor_lmat \<sigma> \<tau> :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat) $$ (I, J)
        = (unwrap_lm \<sigma> \<Otimes> unwrap_lm \<tau>) $$ (I, J)" by simp
    also have "\<dots> = unwrap_lm \<sigma> $$ (I div ?P, J div ?P)
                    * unwrap_lm \<tau> $$ (I mod ?P, J mod ?P)"
      using index_tensor_mat [OF rA(1) rA(2) rB(1) rB(2) I_lt J_lt m_pos p_pos] .
    finally show ?thesis .
  qed
  have sigma_scaled:
    "unwrap_lm (a *\<^sub>R \<sigma>) $$ (I div ?P, J div ?P)
      = complex_of_real a * (unwrap_lm \<sigma> $$ (I div ?P, J div ?P))"
    using I_div J_div by (simp add: scaleR_conv_of_real)
  have lhs_simp:
    "unwrap_lm (tensor_lmat (a *\<^sub>R \<sigma>) \<tau> :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat) $$ (I, J)
      = complex_of_real a *
        (unwrap_lm \<sigma> $$ (I div ?P, J div ?P)
         * unwrap_lm \<tau> $$ (I mod ?P, J mod ?P))"
    using lhs_entry sigma_scaled by (simp add: mult.assoc)
  have rhs_simp:
    "unwrap_lm (a *\<^sub>R tensor_lmat \<sigma> \<tau> :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat) $$ (I, J)
      = complex_of_real a *
        (unwrap_lm \<sigma> $$ (I div ?P, J div ?P)
         * unwrap_lm \<tau> $$ (I mod ?P, J mod ?P))"
    using rhs_entry tensor_entry by (simp add: scaleR_conv_of_real)
  show "unwrap_lm (tensor_lmat (a *\<^sub>R \<sigma>) \<tau>
                     :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat) $$ (I, J)
      = unwrap_lm (a *\<^sub>R tensor_lmat \<sigma> \<tau>
                     :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat) $$ (I, J)"
    using lhs_simp rhs_simp by simp
qed

lemma tensor_lmat_scaleR_right:
  fixes a :: real
    and \<sigma> :: "(complex, 'm :: finite, 'm) lmat"
    and \<tau> :: "(complex, 'p :: finite, 'p) lmat"
  shows "(tensor_lmat \<sigma> (a *\<^sub>R \<tau>)
            :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat)
       = a *\<^sub>R tensor_lmat \<sigma> \<tau>"
proof (subst lmat_eq_iff_entries, intro allI impI)
  fix I J :: nat
  assume IJ: "I < CARD('m \<times> 'p)" "J < CARD('m \<times> 'p)"
  let ?M = "CARD('m)"
  let ?P = "CARD('p)"
  have card_eq: "CARD('m \<times> 'p) = ?M * ?P" by simp
  have m_pos: "0 < ?M" by simp
  have p_pos: "0 < ?P" by simp
  have I_lt: "I < ?M * ?P" using IJ(1) card_eq by simp
  have J_lt: "J < ?M * ?P" using IJ(2) card_eq by simp
  have I_div: "I div ?P < ?M" using I_lt p_pos
    by (metis div_less_iff_less_mult mult.commute)
  have J_div: "J div ?P < ?M" using J_lt p_pos
    by (metis div_less_iff_less_mult mult.commute)
  have I_mod: "I mod ?P < ?P" using p_pos by simp
  have J_mod: "J mod ?P < ?P" using p_pos by simp
  have rA: "dim_row (unwrap_lm \<sigma>) = ?M" "dim_col (unwrap_lm \<sigma>) = ?M" by simp_all
  have rB: "dim_row (unwrap_lm \<tau>) = ?P" "dim_col (unwrap_lm \<tau>) = ?P" by simp_all
  have rB': "dim_row (unwrap_lm (a *\<^sub>R \<tau>)) = ?P" "dim_col (unwrap_lm (a *\<^sub>R \<tau>)) = ?P"
    by simp_all
  have lhs_entry:
    "unwrap_lm (tensor_lmat \<sigma> (a *\<^sub>R \<tau>) :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat) $$ (I, J)
      = unwrap_lm \<sigma> $$ (I div ?P, J div ?P)
        * unwrap_lm (a *\<^sub>R \<tau>) $$ (I mod ?P, J mod ?P)"
  proof -
    have "unwrap_lm (tensor_lmat \<sigma> (a *\<^sub>R \<tau>)
                       :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat) $$ (I, J)
        = (unwrap_lm \<sigma> \<Otimes> unwrap_lm (a *\<^sub>R \<tau>)) $$ (I, J)" by simp
    also have "\<dots> = unwrap_lm \<sigma> $$ (I div ?P, J div ?P)
                    * unwrap_lm (a *\<^sub>R \<tau>) $$ (I mod ?P, J mod ?P)"
      using index_tensor_mat [OF rA(1) rA(2) rB'(1) rB'(2) I_lt J_lt m_pos p_pos] .
    finally show ?thesis .
  qed
  have rhs_entry:
    "unwrap_lm (a *\<^sub>R tensor_lmat \<sigma> \<tau> :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat) $$ (I, J)
      = a *\<^sub>R (unwrap_lm (tensor_lmat \<sigma> \<tau> :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat) $$ (I, J))"
    using IJ unwrap_lm_scaleR_index by simp
  have tensor_entry:
    "unwrap_lm (tensor_lmat \<sigma> \<tau> :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat) $$ (I, J)
      = unwrap_lm \<sigma> $$ (I div ?P, J div ?P)
        * unwrap_lm \<tau> $$ (I mod ?P, J mod ?P)"
  proof -
    have "unwrap_lm (tensor_lmat \<sigma> \<tau> :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat) $$ (I, J)
        = (unwrap_lm \<sigma> \<Otimes> unwrap_lm \<tau>) $$ (I, J)" by simp
    also have "\<dots> = unwrap_lm \<sigma> $$ (I div ?P, J div ?P)
                    * unwrap_lm \<tau> $$ (I mod ?P, J mod ?P)"
      using index_tensor_mat [OF rA(1) rA(2) rB(1) rB(2) I_lt J_lt m_pos p_pos] .
    finally show ?thesis .
  qed
  have tau_scaled:
    "unwrap_lm (a *\<^sub>R \<tau>) $$ (I mod ?P, J mod ?P)
      = complex_of_real a * (unwrap_lm \<tau> $$ (I mod ?P, J mod ?P))"
    using I_mod J_mod by (simp add: scaleR_conv_of_real)
  have lhs_simp:
    "unwrap_lm (tensor_lmat \<sigma> (a *\<^sub>R \<tau>) :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat) $$ (I, J)
      = complex_of_real a *
        (unwrap_lm \<sigma> $$ (I div ?P, J div ?P)
         * unwrap_lm \<tau> $$ (I mod ?P, J mod ?P))"
    using lhs_entry tau_scaled by (simp add: scaleR_conv_of_real)
  have rhs_simp:
    "unwrap_lm (a *\<^sub>R tensor_lmat \<sigma> \<tau> :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat) $$ (I, J)
      = complex_of_real a *
        (unwrap_lm \<sigma> $$ (I div ?P, J div ?P)
         * unwrap_lm \<tau> $$ (I mod ?P, J mod ?P))"
    using rhs_entry tensor_entry by (simp add: scaleR_conv_of_real)
  show "unwrap_lm (tensor_lmat \<sigma> (a *\<^sub>R \<tau>)
                     :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat) $$ (I, J)
      = unwrap_lm (a *\<^sub>R tensor_lmat \<sigma> \<tau>
                     :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat) $$ (I, J)"
    using lhs_simp rhs_simp by simp
qed

lemma tensor_lmat_zero_left:
  fixes \<tau> :: "(complex, 'p :: finite, 'p) lmat"
  shows "(tensor_lmat (0 :: (complex, 'm :: finite, 'm) lmat) \<tau>
            :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat) = 0"
  by (metis real_vector.scale_zero_left tensor_lmat_scaleR_left)

lemma tensor_lmat_zero_right:
  fixes \<sigma> :: "(complex, 'm :: finite, 'm) lmat"
  shows "(tensor_lmat \<sigma> (0 :: (complex, 'p :: finite, 'p) lmat)
            :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat) = 0"
  by (metis real_vector.scale_zero_left tensor_lmat_scaleR_right)

lemma convex_cone_hull_separable_eq_Sprime:
  "(convex_cone hull
      (separable_lmat_gen
         :: (complex, 'm :: finite \<times> 'p :: finite, 'm \<times> 'p) lmat set))
   = convex_cone hull Sprime"
proof
  show "convex_cone hull Sprime
        \<subseteq> convex_cone hull (separable_lmat_gen
                              :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat set)"
    by (rule hull_mono [OF Sprime_subset_separable_lmat_gen])
next
  show "convex_cone hull (separable_lmat_gen
                            :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat set)
        \<subseteq> convex_cone hull Sprime"
  proof (rule hull_minimal)
    show "separable_lmat_gen
          \<subseteq> convex_cone hull (Sprime
                                  :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat set)"
    proof
      fix x :: "(complex, 'm \<times> 'p, 'm \<times> 'p) lmat"
      assume "x \<in> separable_lmat_gen"
      then obtain \<sigma> \<tau>
        where x_eq: "x = tensor_lmat \<sigma> \<tau>"
          and \<sigma>_psd: "psd_lmat (\<sigma> :: (complex, 'm, 'm) lmat)"
          and \<tau>_psd: "psd_lmat (\<tau> :: (complex, 'p, 'p) lmat)"
        unfolding separable_lmat_gen_def by auto
      have \<sigma>_im: "Im (Tr_lmat \<sigma>) = 0" and \<sigma>_re_nn: "0 \<le> Re (Tr_lmat \<sigma>)"
        using psd_lmat_Tr_real_nonneg [OF \<sigma>_psd] by simp_all
      have \<tau>_im: "Im (Tr_lmat \<tau>) = 0" and \<tau>_re_nn: "0 \<le> Re (Tr_lmat \<tau>)"
        using psd_lmat_Tr_real_nonneg [OF \<tau>_psd] by simp_all
      define \<alpha> where "\<alpha> = Re (Tr_lmat \<sigma>)"
      define \<beta> where "\<beta> = Re (Tr_lmat \<tau>)"
      have \<sigma>_tr: "Tr_lmat \<sigma> = complex_of_real \<alpha>"
        unfolding \<alpha>_def using \<sigma>_im by (simp add: complex_eq_iff)
      have \<tau>_tr: "Tr_lmat \<tau> = complex_of_real \<beta>"
        unfolding \<beta>_def using \<tau>_im by (simp add: complex_eq_iff)
      have \<alpha>_nn: "0 \<le> \<alpha>" unfolding \<alpha>_def using \<sigma>_re_nn .
      have \<beta>_nn: "0 \<le> \<beta>" unfolding \<beta>_def using \<tau>_re_nn .
      show "x \<in> convex_cone hull Sprime"
      proof (cases "\<alpha> = 0 \<or> \<beta> = 0")
        case True
        have x_zero: "x = 0"
        proof (cases "\<alpha> = 0")
          case True
          with \<sigma>_tr have "Tr_lmat \<sigma> = 0" by simp
          with \<sigma>_psd have "\<sigma> = 0"
            by (rule psd_lmat_zero_trace_zero)
          thus ?thesis
            using x_eq tensor_lmat_zero_left by simp
        next
          case False
          with True have b0: "\<beta> = 0" by simp
          with \<tau>_tr have "Tr_lmat \<tau> = 0" by simp
          with \<tau>_psd have "\<tau> = 0"
            by (rule psd_lmat_zero_trace_zero)
          thus ?thesis
            using x_eq tensor_lmat_zero_right by simp
        qed
        show ?thesis
          using x_zero convex_cone_hull_contains_0 by simp
      next
        case False
        hence \<alpha>_pos: "0 < \<alpha>" and \<beta>_pos: "0 < \<beta>"
          using \<alpha>_nn \<beta>_nn by auto
        have \<alpha>_nz: "\<alpha> \<noteq> 0" using \<alpha>_pos by simp
        have \<beta>_nz: "\<beta> \<noteq> 0" using \<beta>_pos by simp
        define \<sigma>' :: "(complex, 'm, 'm) lmat"
          where "\<sigma>' = (1/\<alpha>) *\<^sub>R \<sigma>"
        define \<tau>' :: "(complex, 'p, 'p) lmat"
          where "\<tau>' = (1/\<beta>) *\<^sub>R \<tau>"
        have \<sigma>'_psd: "psd_lmat \<sigma>'"
          unfolding \<sigma>'_def using \<sigma>_psd \<alpha>_pos
          by (intro psd_lmat_scaleR_nonneg) auto
        have \<tau>'_psd: "psd_lmat \<tau>'"
          unfolding \<tau>'_def using \<tau>_psd \<beta>_pos
          by (intro psd_lmat_scaleR_nonneg) auto
        have \<sigma>'_tr: "Tr_lmat \<sigma>' = 1"
        proof -
          have "Tr_lmat \<sigma>' = (1/\<alpha>) *\<^sub>R Tr_lmat \<sigma>"
            unfolding \<sigma>'_def by (rule Tr_lmat_scaleR)
          also have "\<dots> = (1/\<alpha>) *\<^sub>R complex_of_real \<alpha>"
            using \<sigma>_tr by simp
          also have "\<dots> = complex_of_real ((1/\<alpha>) * \<alpha>)"
            by (simp add: scaleR_conv_of_real)
          also have "\<dots> = 1" using \<alpha>_nz by simp
          finally show ?thesis .
        qed
        have \<tau>'_tr: "Tr_lmat \<tau>' = 1"
        proof -
          have "Tr_lmat \<tau>' = (1/\<beta>) *\<^sub>R Tr_lmat \<tau>"
            unfolding \<tau>'_def by (rule Tr_lmat_scaleR)
          also have "\<dots> = (1/\<beta>) *\<^sub>R complex_of_real \<beta>"
            using \<tau>_tr by simp
          also have "\<dots> = complex_of_real ((1/\<beta>) * \<beta>)"
            by (simp add: scaleR_conv_of_real)
          also have "\<dots> = 1" using \<beta>_nz by simp
          finally show ?thesis .
        qed
        have \<sigma>_recon: "\<alpha> *\<^sub>R \<sigma>' = \<sigma>"
          unfolding \<sigma>'_def using \<alpha>_nz by (simp add: scaleR_scaleR)
        have \<tau>_recon: "\<beta> *\<^sub>R \<tau>' = \<tau>"
          unfolding \<tau>'_def using \<beta>_nz by (simp add: scaleR_scaleR)
        have x_resc:
          "x = (\<alpha> * \<beta>) *\<^sub>R (tensor_lmat \<sigma>' \<tau>'
                              :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat)"
        proof -
          have "x = tensor_lmat (\<alpha> *\<^sub>R \<sigma>') (\<beta> *\<^sub>R \<tau>')"
            using x_eq \<sigma>_recon \<tau>_recon by simp
          also have "\<dots> = \<alpha> *\<^sub>R (tensor_lmat \<sigma>' (\<beta> *\<^sub>R \<tau>')
                                  :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat)"
            by (rule tensor_lmat_scaleR_left)
          also have "\<dots> = \<alpha> *\<^sub>R (\<beta> *\<^sub>R (tensor_lmat \<sigma>' \<tau>'
                                          :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat))"
            by (subst tensor_lmat_scaleR_right) (rule refl)
          also have "\<dots> = (\<alpha> * \<beta>) *\<^sub>R (tensor_lmat \<sigma>' \<tau>'
                                          :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat)"
            by (rule scaleR_scaleR)
          finally show ?thesis .
        qed
        have base: "(tensor_lmat \<sigma>' \<tau>'
                       :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat) \<in> Sprime"
        proof -
          have "\<exists>\<sigma>'' \<tau>''. (tensor_lmat \<sigma>' \<tau>'
                            :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat)
                          = tensor_lmat \<sigma>'' \<tau>''
                       \<and> psd_lmat \<sigma>'' \<and> Tr_lmat \<sigma>'' = 1
                       \<and> psd_lmat \<tau>'' \<and> Tr_lmat \<tau>'' = 1"
            using \<sigma>'_psd \<tau>'_psd \<sigma>'_tr \<tau>'_tr by blast
          thus ?thesis unfolding Sprime_def by simp
        qed
        have base_in_hull: "(tensor_lmat \<sigma>' \<tau>'
                              :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat)
                              \<in> convex_cone hull Sprime"
          using base by (rule hull_inc)
        have hull_cone:
          "convex_cone (convex_cone hull
                          (Sprime :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat set))"
          by (rule convex_cone_convex_cone_hull)
        have \<alpha>\<beta>_nn: "0 \<le> \<alpha> * \<beta>" using \<alpha>_pos \<beta>_pos by simp
        have scaled_in_hull:
          "(\<alpha> * \<beta>) *\<^sub>R (tensor_lmat \<sigma>' \<tau>'
                          :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat)
              \<in> convex_cone hull Sprime"
          by (rule convex_cone_scaleR [OF hull_cone \<alpha>\<beta>_nn base_in_hull])
        show ?thesis using x_resc scaled_in_hull by simp
      qed
    qed
  next
    show "convex_cone (convex_cone hull
                         (Sprime :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat set))"
      by (rule convex_cone_convex_cone_hull)
  qed
qed

theorem separable_cone_lmat_closed:
  "closed (separable_cone_lmat
            :: (complex, 'm :: finite \<times> 'p :: finite, 'm \<times> 'p) lmat set)"
proof -
  let ?S' = "Sprime :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat set"
  have hull_eq:
    "separable_cone_lmat
       = insert 0 (conic hull (convex hull ?S'))"
  proof -
    have "separable_cone_lmat
        = convex_cone hull (separable_lmat_gen
                              :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat set)"
      unfolding separable_cone_lmat_def ..
    also have "\<dots> = convex_cone hull ?S'"
      using convex_cone_hull_separable_eq_Sprime .
    also have "\<dots> = insert 0 (conic hull (convex hull ?S'))"
      by (rule convex_cone_hull_separate)
    finally show ?thesis .
  qed
  have compact_convhull: "compact (convex hull ?S')"
    using compact_Sprime by (rule compact_convex_hull)
  have Tr_Sprime: "\<And>s :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat. s \<in> ?S' \<Longrightarrow> Tr_lmat s = 1"
  proof -
    fix s :: "(complex, 'm \<times> 'p, 'm \<times> 'p) lmat"
    assume "s \<in> ?S'"
    then obtain \<sigma> \<tau> where s_eq: "s = tensor_lmat \<sigma> \<tau>"
                  and tr_s: "Tr_lmat (\<sigma> :: (complex, 'm, 'm) lmat) = 1"
                  and tr_t: "Tr_lmat (\<tau> :: (complex, 'p, 'p) lmat) = 1"
      unfolding Sprime_def by auto
    have "Tr_lmat s = Tr_lmat (tensor_lmat \<sigma> \<tau>
                                 :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat)"
      using s_eq by simp
    also have "\<dots> = Tr_lmat \<sigma> * Tr_lmat \<tau>" by (rule Tr_lmat_tensor)
    also have "\<dots> = 1" using tr_s tr_t by simp
    finally show "Tr_lmat s = 1" .
  qed
  have zero_not_in: "0 \<notin> convex hull ?S'"
  proof
    assume "0 \<in> convex hull ?S'"
    then obtain T u where Tfin: "finite T" and Tsub: "T \<subseteq> ?S'"
                    and unn: "\<forall>t \<in> T. 0 \<le> u t"
                    and usum: "sum u T = 1"
                    and sum_eq:
                      "(\<Sum>t \<in> T. u t *\<^sub>R t) = (0 :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat)"
      unfolding convex_hull_explicit by auto
    have tr_zero: "Tr_lmat ((\<Sum>t \<in> T. u t *\<^sub>R t)
                              :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat) = 0"
      using sum_eq by simp
    have tr_one: "Tr_lmat ((\<Sum>t \<in> T. u t *\<^sub>R t)
                             :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat) = 1"
    proof -
      have "Tr_lmat ((\<Sum>t \<in> T. u t *\<^sub>R t)
                       :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat)
          = (\<Sum>t \<in> T. u t *\<^sub>R Tr_lmat t)"
        using Tfin by (rule Tr_lmat_sum_scaleR)
      also have "\<dots> = (\<Sum>t \<in> T. u t *\<^sub>R 1)"
        using Tsub Tr_Sprime by (intro sum.cong) auto
      also have "\<dots> = (\<Sum>t \<in> T. complex_of_real (u t))"
        by (intro sum.cong) (simp_all add: scaleR_conv_of_real)
      also have "\<dots> = complex_of_real (\<Sum>t \<in> T. u t)"
        by simp
      also have "\<dots> = 1" using usum by simp
      finally show ?thesis .
    qed
    from tr_zero tr_one show False by simp
  qed
  have closed_inner: "closed (conic hull (convex hull ?S'))"
    by (rule closed_conic_hull) (use compact_convhull zero_not_in in blast)
  have closed_zero: "closed ({0 :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat})"
    by simp
  have closed_union: "closed ({0} \<union> conic hull (convex hull ?S'))"
    using closed_zero closed_inner by (rule closed_Un)
  show ?thesis
    unfolding hull_eq
    using closed_union by simp
qed


section \<open>The lmat inner product as a real-trace inner product\<close>

text \<open>The real inner product on \<open>(complex, 'm, 'n) lmat\<close> is the real
part of the JNF Hilbert-Schmidt inner product on the underlying
matrices.  For square matrices it is also \<open>Re (Tr (M\<^sup>\<dagger> * N))\<close>.\<close>

lemma inner_lmat_eq_re_hs_inner_prod:
  fixes M N :: "(complex, 'm :: finite, 'n :: finite) lmat"
  shows "inner M N = Re \<langle>\<langle> unwrap_lm M | unwrap_lm N \<rangle>\<rangle>"
proof -
  let ?S = "{0..<CARD('m)} \<times> {0..<CARD('n)}"
  have "inner M N
      = (\<Sum>(i, j) \<in> ?S. inner (unwrap_lm M $$ (i, j)) (unwrap_lm N $$ (i, j)))"
    unfolding inner_lmat_def by simp
  also have "\<dots> = (\<Sum>(i, j) \<in> ?S.
                    Re (cnj (unwrap_lm M $$ (i, j)) * unwrap_lm N $$ (i, j)))"
    by (intro sum.cong refl) (auto simp: inner_complex_def split: prod.split)
  also have "\<dots> = Re (\<Sum>(i, j) \<in> ?S.
                       cnj (unwrap_lm M $$ (i, j)) * unwrap_lm N $$ (i, j))"
    by (subst Re_sum) (simp split: prod.split)
  also have "\<dots> = Re (\<Sum>i = 0..<CARD('m). \<Sum>j = 0..<CARD('n).
                       cnj (unwrap_lm M $$ (i, j)) * unwrap_lm N $$ (i, j))"
    by (subst sum.cartesian_product [symmetric]) (simp split: prod.split)
  also have "\<dots> = Re \<langle>\<langle> unwrap_lm M | unwrap_lm N \<rangle>\<rangle>"
    unfolding hs_inner_prod_def by simp
  finally show ?thesis .
qed

lemma inner_lmat_eq_re_tr_dagger:
  fixes M N :: "(complex, 'k :: finite, 'k) lmat"
  shows "inner M N = Re (Tr ((unwrap_lm M)\<^sup>\<dagger> * unwrap_lm N))"
proof -
  have "inner M N = Re \<langle>\<langle> unwrap_lm M | unwrap_lm N \<rangle>\<rangle>"
    by (rule inner_lmat_eq_re_hs_inner_prod)
  also have "\<langle>\<langle> unwrap_lm M | unwrap_lm N \<rangle>\<rangle>
           = Tr ((unwrap_lm M)\<^sup>\<dagger> * unwrap_lm N)"
    by (rule hs_inner_prod_as_trace) simp_all
  finally show ?thesis .
qed


section \<open>Separating hyperplane for non-separable states\<close>

text \<open>The closedness of the separable cone, combined with HOL-Analysis
\<open>separating_hyperplane_closed_point\<close>, yields the geometric Hahn-Banach
witness:  for every \<open>\<rho>\<close> outside the separable cone there is a linear
functional (an HS inner product against some matrix \<open>a\<close>) that is strictly
negative on \<open>\<rho>\<close> and nonneg on every separable element.  Because the
separable set is a CONE, the strict inequality \<open>inner a x > b\<close> on the
cone forces \<open>b < 0\<close> and \<open>inner a x \<ge> 0\<close> on the cone.\<close>

theorem separable_cone_lmat_separating_hyperplane:
  fixes \<rho> :: "(complex, 'm :: finite \<times> 'p :: finite, 'm \<times> 'p) lmat"
  assumes notin: "\<rho> \<notin> separable_cone_lmat"
  shows "\<exists>a :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat.
           inner a \<rho> < 0
         \<and> (\<forall>\<sigma> \<in> separable_cone_lmat. 0 \<le> inner a \<sigma>)"
proof -
  let ?S = "separable_cone_lmat
              :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat set"
  have cone_S: "convex_cone ?S" by (rule separable_cone_lmat_convex_cone)
  have conv_S: "convex ?S" using cone_S unfolding convex_cone_def by simp
  have closed_S: "closed ?S" by (rule separable_cone_lmat_closed)
  obtain a b
    where ineq_z: "inner a \<rho> < b"
      and ineq_S: "\<forall>x \<in> ?S. inner a x > b"
    using separating_hyperplane_closed_point [OF conv_S closed_S notin] by blast
  have zero_in: "(0 :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat) \<in> ?S"
    by (rule zero_in_separable_cone_lmat)
  have b_neg: "b < 0"
    using ineq_S zero_in by force
  have inner_\<rho>_neg: "inner a \<rho> < 0"
    using ineq_z b_neg by simp
  have inner_\<sigma>_nn: "\<forall>\<sigma> \<in> ?S. 0 \<le> inner a \<sigma>"
  proof
    fix \<sigma> :: "(complex, 'm \<times> 'p, 'm \<times> 'p) lmat"
    assume \<sigma>_in: "\<sigma> \<in> ?S"
    show "0 \<le> inner a \<sigma>"
    proof (rule ccontr)
      assume "\<not> 0 \<le> inner a \<sigma>"
      hence neg: "inner a \<sigma> < 0" by simp
      define t :: real where "t = 2 * b / inner a \<sigma>"
      have t_pos: "0 < t"
        unfolding t_def using b_neg neg
        by (simp add: divide_neg_neg)
      have t_inner: "t * inner a \<sigma> = 2 * b"
        unfolding t_def using neg by simp
      have t_lt_b: "t * inner a \<sigma> < b"
        using t_inner b_neg by simp
      have ts_in: "t *\<^sub>R \<sigma> \<in> ?S"
        using cone_S t_pos \<sigma>_in by (intro convex_cone_scaleR) auto
      hence "inner a (t *\<^sub>R \<sigma>) > b" using ineq_S by blast
      hence "t * inner a \<sigma> > b" by simp
      thus False using t_lt_b by simp
    qed
  qed
  show ?thesis using inner_\<rho>_neg inner_\<sigma>_nn by blast
qed


section \<open>Entanglement witness in real-trace form\<close>

text \<open>Reformulating the separating hyperplane via the
\<open>inner = Re Tr\<close> identity gives a JNF matrix \<open>W\<close> whose adjoint
times \<open>\<rho>\<close> has strictly negative real trace, while \<open>W\<^sup>\<dagger> * \<sigma>\<close>
has nonneg real trace for every \<open>\<sigma>\<close> in the separable cone.\<close>

theorem entanglement_witness_re_tr:
  fixes \<rho> :: "(complex, 'm :: finite \<times> 'p :: finite, 'm \<times> 'p) lmat"
  assumes notin: "\<rho> \<notin> separable_cone_lmat"
  shows "\<exists>W :: complex Matrix.mat.
           W \<in> carrier_mat (CARD('m \<times> 'p)) (CARD('m \<times> 'p))
         \<and> Re (Tr (W * unwrap_lm \<rho>)) < 0
         \<and> (\<forall>\<sigma> :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat.
              \<sigma> \<in> separable_cone_lmat
                \<longrightarrow> 0 \<le> Re (Tr (W * unwrap_lm \<sigma>)))"
proof -
  obtain a :: "(complex, 'm \<times> 'p, 'm \<times> 'p) lmat"
    where ineq_\<rho>: "inner a \<rho> < 0"
      and ineq_S: "\<forall>\<sigma> \<in> separable_cone_lmat. 0 \<le> inner a \<sigma>"
    using separable_cone_lmat_separating_hyperplane [OF notin] by blast
  let ?W = "(unwrap_lm a)\<^sup>\<dagger>"
  have W_carr: "?W \<in> carrier_mat (CARD('m \<times> 'p)) (CARD('m \<times> 'p))"
    by (rule carrier_matI) (auto simp: dim_row_of_dagger dim_col_of_dagger)
  have re_tr_\<rho>:
    "Re (Tr (?W * unwrap_lm \<rho>)) = inner a \<rho>"
  proof -
    have "inner a \<rho> = Re (Tr ((unwrap_lm a)\<^sup>\<dagger> * unwrap_lm \<rho>))"
      by (rule inner_lmat_eq_re_tr_dagger)
    thus ?thesis by simp
  qed
  have re_tr_\<sigma>:
    "\<And>\<sigma> :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat.
       \<sigma> \<in> separable_cone_lmat
         \<Longrightarrow> Re (Tr (?W * unwrap_lm \<sigma>)) = inner a \<sigma>"
  proof -
    fix \<sigma> :: "(complex, 'm \<times> 'p, 'm \<times> 'p) lmat"
    assume \<sigma>_in: "\<sigma> \<in> separable_cone_lmat"
    have "inner a \<sigma> = Re (Tr ((unwrap_lm a)\<^sup>\<dagger> * unwrap_lm \<sigma>))"
      by (rule inner_lmat_eq_re_tr_dagger)
    thus "Re (Tr (?W * unwrap_lm \<sigma>)) = inner a \<sigma>" by simp
  qed
  have neg_\<rho>: "Re (Tr (?W * unwrap_lm \<rho>)) < 0"
    using re_tr_\<rho> ineq_\<rho> by simp
  have nn_\<sigma>:
    "\<forall>\<sigma> :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat.
       \<sigma> \<in> separable_cone_lmat
         \<longrightarrow> 0 \<le> Re (Tr (?W * unwrap_lm \<sigma>))"
    using re_tr_\<sigma> ineq_S by auto
  show ?thesis using W_carr neg_\<rho> nn_\<sigma> by blast
qed


section \<open>Hermitian entanglement witness\<close>

text \<open>For \<open>\<rho>\<close> outside the separable cone with hermitian unwrap, the
witness can be chosen hermitian.  Direct entrywise construction of
\<open>W = (A + A\<^sup>\<dagger>)/2\<close> using \<open>Matrix.mat\<close>; we avoid lemmas about
\<open>dagger\<close> distributing over sums or scalar multiplication.\<close>

theorem entanglement_witness_hermitian:
  fixes \<rho> :: "(complex, 'm :: finite \<times> 'p :: finite, 'm \<times> 'p) lmat"
  assumes notin: "\<rho> \<notin> separable_cone_lmat"
      and \<rho>_herm: "hermitian (unwrap_lm \<rho>)"
  shows "\<exists>W :: complex Matrix.mat.
           W \<in> carrier_mat (CARD('m \<times> 'p)) (CARD('m \<times> 'p))
         \<and> hermitian W
         \<and> Re (Tr (W * unwrap_lm \<rho>)) < 0
         \<and> (\<forall>\<sigma> :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat.
              \<sigma> \<in> separable_cone_lmat
              \<and> hermitian (unwrap_lm \<sigma>)
                \<longrightarrow> 0 \<le> Re (Tr (W * unwrap_lm \<sigma>)))"
proof -
  let ?n = "CARD('m \<times> 'p)"
  obtain a :: "(complex, 'm \<times> 'p, 'm \<times> 'p) lmat"
    where ineq_\<rho>: "inner a \<rho> < 0"
      and ineq_S: "\<forall>\<sigma> \<in> separable_cone_lmat. 0 \<le> inner a \<sigma>"
    using separable_cone_lmat_separating_hyperplane [OF notin] by blast
  let ?A = "unwrap_lm a"
  have A_car: "?A \<in> carrier_mat ?n ?n"
    by (rule carrier_matI) auto
  define W :: "complex Matrix.mat"
    where "W = Matrix.mat ?n ?n
                 (\<lambda>(i, j). (1/2 :: complex) *
                            (?A $$ (i, j) + cnj (?A $$ (j, i))))"
  have W_car: "W \<in> carrier_mat ?n ?n"
    unfolding W_def by (intro carrier_matI) auto
  have W_dr: "dim_row W = ?n" using W_car by simp
  have W_dc: "dim_col W = ?n" using W_car by simp
  have W_entry:
    "\<And>i j. i < ?n \<Longrightarrow> j < ?n \<Longrightarrow>
      W $$ (i, j) = (1/2 :: complex) *
                    (?A $$ (i, j) + cnj (?A $$ (j, i)))"
    unfolding W_def by simp

  text \<open>Hermitian: \<open>W\<^sup>\<dagger> = W\<close> entrywise.\<close>
  have W_herm: "hermitian W"
  proof -
    have "W\<^sup>\<dagger> = W"
    proof (rule eq_matI)
      show "dim_row (W\<^sup>\<dagger>) = dim_row W"
        using W_dr W_dc by (simp add: dim_row_of_dagger)
      show "dim_col (W\<^sup>\<dagger>) = dim_col W"
        using W_dr W_dc by (simp add: dim_col_of_dagger)
    next
      fix i j
      assume i: "i < dim_row W" and j: "j < dim_col W"
      hence ij: "i < ?n" "j < ?n" using W_dr W_dc by simp_all
      have Wji_eq: "W $$ (j, i) = (1/2 :: complex) *
                                    (?A $$ (j, i) + cnj (?A $$ (i, j)))"
        using W_entry [OF ij(2) ij(1)] .
      have Wij_eq: "W $$ (i, j) = (1/2 :: complex) *
                                    (?A $$ (i, j) + cnj (?A $$ (j, i)))"
        using W_entry [OF ij(1) ij(2)] .
      have "W\<^sup>\<dagger> $$ (i, j) = cnj (W $$ (j, i))"
        unfolding dagger_def using ij W_dr W_dc by simp
      also have "\<dots> = cnj ((1/2 :: complex) *
                            (?A $$ (j, i) + cnj (?A $$ (i, j))))"
        by (rule arg_cong [where f = cnj]) (rule Wji_eq)
      also have "\<dots> = (1/2 :: complex) *
                       (cnj (?A $$ (j, i)) + ?A $$ (i, j))"
        by simp
      also have "\<dots> = (1/2 :: complex) *
                       (?A $$ (i, j) + cnj (?A $$ (j, i)))"
        by (simp add: add.commute)
      also have "\<dots> = W $$ (i, j)" using Wij_eq by simp
      finally show "W\<^sup>\<dagger> $$ (i, j) = W $$ (i, j)" .
    qed
    thus ?thesis by (simp add: hermitian_def)
  qed

  text \<open>Key identity: for hermitian \<open>M\<close>, \<open>Re Tr (W M) = Re \<langle>\<langle>A | M\<rangle>\<rangle>\<close>.\<close>
  have re_tr_eq_inner:
    "\<And>M :: complex Matrix.mat.
       M \<in> carrier_mat ?n ?n \<Longrightarrow> hermitian M
        \<Longrightarrow> Re (Tr (W * M)) = Re \<langle>\<langle> ?A | M \<rangle>\<rangle>"
  proof -
    fix M :: "complex Matrix.mat"
    assume Mcar: "M \<in> carrier_mat ?n ?n" and Mherm: "hermitian M"
    have M_dr: "dim_row M = ?n" using Mcar by simp
    have M_dc: "dim_col M = ?n" using Mcar by simp
    have M_herm_entry:
      "\<And>i j. i < ?n \<Longrightarrow> j < ?n \<Longrightarrow> M $$ (j, i) = cnj (M $$ (i, j))"
    proof -
      fix i j assume i_lt: "i < ?n" and j_lt: "j < ?n"
      have "(M\<^sup>\<dagger>) $$ (i, j) = cnj (M $$ (j, i))"
        unfolding dagger_def using i_lt j_lt M_dr M_dc by simp
      hence "M $$ (i, j) = cnj (M $$ (j, i))"
        using Mherm by (simp add: hermitian_def)
      thus "M $$ (j, i) = cnj (M $$ (i, j))"
        by (metis complex_cnj_cnj)
    qed
    have WM_car: "W * M \<in> carrier_mat ?n ?n" using W_car Mcar by simp
    have WM_dr: "dim_row (W * M) = ?n" using WM_car carrier_matD by blast
    have WM_dc: "dim_col (W * M) = ?n" using WM_car carrier_matD by blast
    have Tr_WM:
      "Tr (W * M)
         = (\<Sum>i = 0..<?n. \<Sum>j = 0..<?n. W $$ (i, j) * M $$ (j, i))"
    proof -
      have "Tr (W * M)
          = (\<Sum>r < dim_row (W * M).
              if r < dim_col (W * M) then (W * M) $$ (r, r) else 0)"
        unfolding Tr_def by simp
      also have "\<dots>
          = (\<Sum>r < ?n. if r < ?n then (W * M) $$ (r, r) else 0)"
        using WM_dr WM_dc by simp
      also have "\<dots> = (\<Sum>r < ?n. (W * M) $$ (r, r))"
        by (intro sum.cong refl) auto
      also have "\<dots> = (\<Sum>i = 0..<?n. (W * M) $$ (i, i))"
        by (simp add: atLeast0LessThan)
      also have "\<dots> = (\<Sum>i = 0..<?n. \<Sum>j = 0..<?n.
                          W $$ (i, j) * M $$ (j, i))"
      proof (intro sum.cong refl)
        fix i assume "i \<in> {0..<?n}"
        hence i_lt: "i < ?n" by simp
        show "(W * M) $$ (i, i)
            = (\<Sum>j = 0..<?n. W $$ (i, j) * M $$ (j, i))"
          using W_car Mcar i_lt
          by (simp add: scalar_prod_def Matrix.row_def Matrix.col_def
                          lessThan_atLeast0)
      qed
      finally show ?thesis .
    qed
    have HS:
      "\<langle>\<langle> ?A | M \<rangle>\<rangle>
         = (\<Sum>i = 0..<?n. \<Sum>j = 0..<?n.
              cnj (?A $$ (i, j)) * M $$ (i, j))"
      unfolding hs_inner_prod_def using M_dr M_dc by simp
    have rewrite_entry:
      "\<And>i j. i < ?n \<Longrightarrow> j < ?n
        \<Longrightarrow> W $$ (i, j) * M $$ (j, i)
            = (1/2 :: complex) *
              (?A $$ (i, j) * cnj (M $$ (i, j))
               + cnj (?A $$ (j, i)) * cnj (M $$ (i, j)))"
    proof -
      fix i j assume i: "i < ?n" and j: "j < ?n"
      have Mji: "M $$ (j, i) = cnj (M $$ (i, j))"
        using M_herm_entry [OF i j] .
      have Wij: "W $$ (i, j) = (1/2 :: complex) *
                                (?A $$ (i, j) + cnj (?A $$ (j, i)))"
        using W_entry [OF i j] .
      show "W $$ (i, j) * M $$ (j, i)
          = (1/2 :: complex) *
            (?A $$ (i, j) * cnj (M $$ (i, j))
             + cnj (?A $$ (j, i)) * cnj (M $$ (i, j)))"
        using Mji Wij by (simp add: ring_distribs)
    qed
    have sum_eq_half_split:
      "(\<Sum>i = 0..<?n. \<Sum>j = 0..<?n. W $$ (i, j) * M $$ (j, i))
       = (1/2 :: complex) *
         ((\<Sum>i = 0..<?n. \<Sum>j = 0..<?n. ?A $$ (i, j) * cnj (M $$ (i, j)))
        + (\<Sum>i = 0..<?n. \<Sum>j = 0..<?n. cnj (?A $$ (j, i)) * cnj (M $$ (i, j))))"
    proof -
      have step1:
        "(\<Sum>i = 0..<?n. \<Sum>j = 0..<?n. W $$ (i, j) * M $$ (j, i))
       = (\<Sum>i = 0..<?n. \<Sum>j = 0..<?n.
            (1/2 :: complex) *
              (?A $$ (i, j) * cnj (M $$ (i, j))
               + cnj (?A $$ (j, i)) * cnj (M $$ (i, j))))"
      proof (intro sum.cong refl)
        fix i j assume "i \<in> {0..<?n}" "j \<in> {0..<?n}"
        hence "i < ?n" "j < ?n" by simp_all
        thus "W $$ (i, j) * M $$ (j, i)
            = (1/2 :: complex) *
              (?A $$ (i, j) * cnj (M $$ (i, j))
               + cnj (?A $$ (j, i)) * cnj (M $$ (i, j)))"
          by (rule rewrite_entry)
      qed
      also have "\<dots>
        = (1/2 :: complex) *
          (\<Sum>i = 0..<?n. \<Sum>j = 0..<?n.
            ?A $$ (i, j) * cnj (M $$ (i, j))
            + cnj (?A $$ (j, i)) * cnj (M $$ (i, j)))"
        by (simp only: sum_distrib_left)
      also have "\<dots>
        = (1/2 :: complex) *
          ((\<Sum>i = 0..<?n. \<Sum>j = 0..<?n. ?A $$ (i, j) * cnj (M $$ (i, j)))
         + (\<Sum>i = 0..<?n. \<Sum>j = 0..<?n. cnj (?A $$ (j, i)) * cnj (M $$ (i, j))))"
        by (simp only: sum.distrib)
      finally show ?thesis .
    qed
    have second_swap:
      "(\<Sum>i = 0..<?n. \<Sum>j = 0..<?n. cnj (?A $$ (j, i)) * cnj (M $$ (i, j)))
       = (\<Sum>i = 0..<?n. \<Sum>j = 0..<?n. cnj (?A $$ (i, j)) * M $$ (i, j))"
    proof -
      have "(\<Sum>i = 0..<?n. \<Sum>j = 0..<?n. cnj (?A $$ (j, i)) * cnj (M $$ (i, j)))
          = (\<Sum>j = 0..<?n. \<Sum>i = 0..<?n. cnj (?A $$ (j, i)) * cnj (M $$ (i, j)))"
        by (rule sum.swap)
      also have "\<dots>
          = (\<Sum>i = 0..<?n. \<Sum>j = 0..<?n. cnj (?A $$ (i, j)) * M $$ (i, j))"
      proof (intro sum.cong refl)
        fix i j assume i_in: "i \<in> {0..<?n}" and j_in: "j \<in> {0..<?n}"
        hence i_lt: "i < ?n" and j_lt: "j < ?n" by simp_all
        have "cnj (M $$ (j, i)) = M $$ (i, j)"
          using M_herm_entry [OF i_lt j_lt] by (metis complex_cnj_cnj)
        thus "cnj (?A $$ (i, j)) * cnj (M $$ (j, i))
            = cnj (?A $$ (i, j)) * M $$ (i, j)"
          by simp
      qed
      finally show ?thesis .
    qed
    have Tr_WM_split:
      "Tr (W * M)
       = (1/2 :: complex) *
         ((\<Sum>i = 0..<?n. \<Sum>j = 0..<?n. ?A $$ (i, j) * cnj (M $$ (i, j)))
        + (\<Sum>i = 0..<?n. \<Sum>j = 0..<?n. cnj (?A $$ (i, j)) * M $$ (i, j)))"
      using Tr_WM sum_eq_half_split second_swap by simp
    have re_first_eq_second:
      "Re (\<Sum>i = 0..<?n. \<Sum>j = 0..<?n. ?A $$ (i, j) * cnj (M $$ (i, j)))
       = Re (\<Sum>i = 0..<?n. \<Sum>j = 0..<?n. cnj (?A $$ (i, j)) * M $$ (i, j))"
    proof -
      have "(\<Sum>i = 0..<?n. \<Sum>j = 0..<?n. ?A $$ (i, j) * cnj (M $$ (i, j)))
          = cnj (\<Sum>i = 0..<?n. \<Sum>j = 0..<?n. cnj (?A $$ (i, j)) * M $$ (i, j))"
        by (simp add: cnj_sum)
      thus ?thesis by simp
    qed
    define S1 :: complex where
      "S1 = (\<Sum>i = 0..<?n. \<Sum>j = 0..<?n. ?A $$ (i, j) * cnj (M $$ (i, j)))"
    define S2 :: complex where
      "S2 = (\<Sum>i = 0..<?n. \<Sum>j = 0..<?n. cnj (?A $$ (i, j)) * M $$ (i, j))"
    have Tr_WM_S: "Tr (W * M) = (1/2 :: complex) * (S1 + S2)"
      using Tr_WM_split unfolding S1_def S2_def by simp
    have Re_S_eq: "Re (Tr (W * M)) = (1/2) * (Re S1 + Re S2)"
    proof -
      have eq1: "Tr (W * M) = (S1 + S2) / 2"
        using Tr_WM_S by simp
      have "Re (Tr (W * M)) = Re ((S1 + S2) / 2)"
        by (subst eq1) (rule refl)
      also have "\<dots> = Re (S1 + S2) / 2"
        by (rule Re_divide_numeral)
      also have "\<dots> = (Re S1 + Re S2) / 2" by simp
      also have "\<dots> = (1/2) * (Re S1 + Re S2)" by simp
      finally show ?thesis .
    qed
    have Re_S1_eq_Re_S2: "Re S1 = Re S2"
      using re_first_eq_second unfolding S1_def S2_def by simp
    have Re_S2_eq_HS: "Re S2 = Re \<langle>\<langle> ?A | M \<rangle>\<rangle>"
      using HS unfolding S2_def by simp
    have "Re (Tr (W * M)) = (1/2) * (Re S1 + Re S2)" by (rule Re_S_eq)
    also have "\<dots> = Re S2" using Re_S1_eq_Re_S2 by simp
    also have "\<dots> = Re \<langle>\<langle> ?A | M \<rangle>\<rangle>" by (rule Re_S2_eq_HS)
    finally show "Re (Tr (W * M)) = Re \<langle>\<langle> ?A | M \<rangle>\<rangle>" .
  qed

  have \<rho>_car: "unwrap_lm \<rho> \<in> carrier_mat ?n ?n"
    by (rule carrier_matI) auto
  have re_tr_\<rho>: "Re (Tr (W * unwrap_lm \<rho>)) = inner a \<rho>"
  proof -
    have "Re (Tr (W * unwrap_lm \<rho>)) = Re \<langle>\<langle> ?A | unwrap_lm \<rho> \<rangle>\<rangle>"
      by (rule re_tr_eq_inner [OF \<rho>_car \<rho>_herm])
    also have "\<dots> = inner a \<rho>"
      using inner_lmat_eq_re_hs_inner_prod [of a \<rho>] by simp
    finally show ?thesis .
  qed
  have re_tr_\<sigma>:
    "\<And>\<sigma>. \<sigma> \<in> separable_cone_lmat \<Longrightarrow> hermitian (unwrap_lm \<sigma>)
        \<Longrightarrow> Re (Tr (W * unwrap_lm \<sigma>)) = inner a \<sigma>"
  proof -
    fix \<sigma> :: "(complex, 'm \<times> 'p, 'm \<times> 'p) lmat"
    assume "\<sigma> \<in> separable_cone_lmat" "hermitian (unwrap_lm \<sigma>)"
    hence \<sigma>_herm: "hermitian (unwrap_lm \<sigma>)" by simp
    have \<sigma>_car: "unwrap_lm \<sigma> \<in> carrier_mat ?n ?n"
      by (rule carrier_matI) auto
    have "Re (Tr (W * unwrap_lm \<sigma>)) = Re \<langle>\<langle> ?A | unwrap_lm \<sigma> \<rangle>\<rangle>"
      by (rule re_tr_eq_inner [OF \<sigma>_car \<sigma>_herm])
    also have "\<dots> = inner a \<sigma>"
      using inner_lmat_eq_re_hs_inner_prod [of a \<sigma>] by simp
    finally show "Re (Tr (W * unwrap_lm \<sigma>)) = inner a \<sigma>" .
  qed
  show ?thesis
  proof (intro exI conjI allI impI)
    show "W \<in> carrier_mat ?n ?n" by (rule W_car)
    show "hermitian W" by (rule W_herm)
    show "Re (Tr (W * unwrap_lm \<rho>)) < 0"
      using re_tr_\<rho> ineq_\<rho> by simp
    fix \<sigma> :: "(complex, 'm \<times> 'p, 'm \<times> 'p) lmat"
    assume hyp: "\<sigma> \<in> separable_cone_lmat \<and> hermitian (unwrap_lm \<sigma>)"
    have "Re (Tr (W * unwrap_lm \<sigma>)) = inner a \<sigma>"
      using re_tr_\<sigma> hyp by simp
    moreover have "0 \<le> inner a \<sigma>" using hyp ineq_S by simp
    ultimately show "0 \<le> Re (Tr (W * unwrap_lm \<sigma>))" by simp
  qed
qed


section \<open>Hermitian closure of the separable cone\<close>

text \<open>Every element of \<open>separable_cone_lmat\<close> has hermitian unwrap.
Generators \<open>tensor_lmat \<sigma> \<tau>\<close> with \<open>\<sigma>, \<tau>\<close> PSD are hermitian, and the
hermitian set is closed under \<open>+\<close> and nonneg real scaling.\<close>

lemma hermitian_zero_mat:
  "hermitian (0\<^sub>m n n :: complex Matrix.mat)"
proof -
  have "(0\<^sub>m n n :: complex Matrix.mat)\<^sup>\<dagger> = 0\<^sub>m n n"
    by (rule eq_matI) (auto simp: dagger_def)
  thus ?thesis by (simp add: hermitian_def)
qed

lemma hermitian_add_mat:
  fixes P Q :: "complex Matrix.mat"
  assumes Pcar: "P \<in> carrier_mat n n" and Qcar: "Q \<in> carrier_mat n n"
      and Pherm: "hermitian P" and Qherm: "hermitian Q"
  shows "hermitian (P + Q)"
proof -
  have PQcar: "P + Q \<in> carrier_mat n n" using Pcar Qcar by simp
  have Pdag: "P\<^sup>\<dagger> = P" using Pherm by (simp add: hermitian_def)
  have Qdag: "Q\<^sup>\<dagger> = Q" using Qherm by (simp add: hermitian_def)
  have "(P + Q)\<^sup>\<dagger> = P + Q"
  proof (rule eq_matI)
    show "dim_row ((P + Q)\<^sup>\<dagger>) = dim_row (P + Q)"
      using PQcar Qcar by (simp add: dim_row_of_dagger)
    show "dim_col ((P + Q)\<^sup>\<dagger>) = dim_col (P + Q)"
      using PQcar Qcar by (simp add: dim_col_of_dagger)
  next
    fix i j
    assume i: "i < dim_row (P + Q)" and j: "j < dim_col (P + Q)"
    hence ij: "i < n" "j < n" using PQcar Qcar by simp_all
    have eq1: "(P + Q)\<^sup>\<dagger> $$ (i, j) = cnj ((P + Q) $$ (j, i))"
      unfolding dagger_def using ij PQcar Qcar by simp
    have eq2: "(P + Q) $$ (j, i) = P $$ (j, i) + Q $$ (j, i)"
      using ij Qcar by simp
    have eq3: "cnj (P $$ (j, i)) = P\<^sup>\<dagger> $$ (i, j)"
      unfolding dagger_def using ij Pcar by simp
    have eq4: "cnj (Q $$ (j, i)) = Q\<^sup>\<dagger> $$ (i, j)"
      unfolding dagger_def using ij Qcar by simp
    have "(P + Q)\<^sup>\<dagger> $$ (i, j)
        = cnj (P $$ (j, i)) + cnj (Q $$ (j, i))"
      using eq1 eq2 by simp
    also have "\<dots> = P\<^sup>\<dagger> $$ (i, j) + Q\<^sup>\<dagger> $$ (i, j)"
      using eq3 eq4 by simp
    also have "\<dots> = P $$ (i, j) + Q $$ (i, j)"
      using Pdag Qdag by simp
    also have "\<dots> = (P + Q) $$ (i, j)"
      using ij Qcar by simp
    finally show "(P + Q)\<^sup>\<dagger> $$ (i, j) = (P + Q) $$ (i, j)" .
  qed
  thus ?thesis by (simp add: hermitian_def)
qed

lemma hermitian_smult_real_mat:
  fixes M :: "complex Matrix.mat" and c :: real
  assumes Mcar: "M \<in> carrier_mat n n" and Mherm: "hermitian M"
  shows "hermitian (complex_of_real c \<cdot>\<^sub>m M)"
proof -
  let ?cM = "complex_of_real c \<cdot>\<^sub>m M"
  have cM_car: "?cM \<in> carrier_mat n n" using Mcar by simp
  have Mdag: "M\<^sup>\<dagger> = M" using Mherm by (simp add: hermitian_def)
  have "?cM\<^sup>\<dagger> = ?cM"
  proof (rule eq_matI)
    show "dim_row (?cM\<^sup>\<dagger>) = dim_row ?cM"
      using cM_car Mcar by (simp add: dim_row_of_dagger)
    show "dim_col (?cM\<^sup>\<dagger>) = dim_col ?cM"
      using cM_car Mcar by (simp add: dim_col_of_dagger)
  next
    fix i j
    assume i: "i < dim_row ?cM" and j: "j < dim_col ?cM"
    hence ij: "i < n" "j < n" using cM_car Mcar by simp_all
    have eq1: "?cM\<^sup>\<dagger> $$ (i, j) = cnj (?cM $$ (j, i))"
      unfolding dagger_def using ij cM_car Mcar by simp
    have eq2: "?cM $$ (j, i) = complex_of_real c * M $$ (j, i)"
      using ij Mcar by simp
    have eq3: "cnj (M $$ (j, i)) = M\<^sup>\<dagger> $$ (i, j)"
      unfolding dagger_def using ij Mcar by simp
    have "?cM\<^sup>\<dagger> $$ (i, j) = cnj (complex_of_real c) * cnj (M $$ (j, i))"
      using eq1 eq2 by simp
    also have "\<dots> = complex_of_real c * cnj (M $$ (j, i))" by simp
    also have "\<dots> = complex_of_real c * (M\<^sup>\<dagger>) $$ (i, j)" using eq3 by simp
    also have "\<dots> = complex_of_real c * M $$ (i, j)" using Mdag by simp
    also have "\<dots> = ?cM $$ (i, j)" using ij Mcar by simp
    finally show "?cM\<^sup>\<dagger> $$ (i, j) = ?cM $$ (i, j)" .
  qed
  thus ?thesis by (simp add: hermitian_def)
qed

text \<open>Tensor product of hermitians is hermitian (entrywise via
\<open>index_tensor_mat\<close>).\<close>

lemma hermitian_tensor_mat:
  fixes P Q :: "complex Matrix.mat"
  assumes Pcar: "P \<in> carrier_mat m m" and Qcar: "Q \<in> carrier_mat p p"
      and m_pos: "0 < m" and p_pos: "0 < p"
      and Pherm: "hermitian P" and Qherm: "hermitian Q"
  shows "hermitian (P \<Otimes> Q)"
proof -
  let ?T = "P \<Otimes> Q"
  have T_dr: "dim_row ?T = m * p" using Pcar Qcar by simp
  have T_dc: "dim_col ?T = m * p" using Pcar Qcar by simp
  have T_car: "?T \<in> carrier_mat (m * p) (m * p)"
    using T_dr T_dc by (intro carrier_matI) auto
  have Pdag: "P\<^sup>\<dagger> = P" using Pherm by (simp add: hermitian_def)
  have Qdag: "Q\<^sup>\<dagger> = Q" using Qherm by (simp add: hermitian_def)
  have P_dr: "dim_row P = m" using Pcar by simp
  have P_dc: "dim_col P = m" using Pcar by simp
  have Q_dr: "dim_row Q = p" using Qcar by simp
  have Q_dc: "dim_col Q = p" using Qcar by simp
  have "?T\<^sup>\<dagger> = ?T"
  proof (rule eq_matI)
    show "dim_row (?T\<^sup>\<dagger>) = dim_row ?T"
      using T_dr T_dc Pcar Qcar by (simp add: dim_row_of_dagger)
    show "dim_col (?T\<^sup>\<dagger>) = dim_col ?T"
      using T_dr T_dc Pcar Qcar by (simp add: dim_col_of_dagger)
  next
    fix i j
    assume i: "i < dim_row ?T" and j: "j < dim_col ?T"
    hence ij_lt: "i < m * p" "j < m * p"
      using T_dr T_dc Pcar Qcar by simp_all
    have iP_lt: "i div p < m" using ij_lt(1) p_pos
      by (metis div_less_iff_less_mult mult.commute)
    have jP_lt: "j div p < m" using ij_lt(2) p_pos
      by (metis div_less_iff_less_mult mult.commute)
    have iQ_lt: "i mod p < p" using p_pos by simp
    have jQ_lt: "j mod p < p" using p_pos by simp
    have T_entry: "?T $$ (i, j)
        = P $$ (i div p, j div p) * Q $$ (i mod p, j mod p)"
      using index_tensor_mat [OF P_dr P_dc Q_dr Q_dc ij_lt(1) ij_lt(2)
                                m_pos p_pos] .
    have Tji_entry: "?T $$ (j, i)
        = P $$ (j div p, i div p) * Q $$ (j mod p, i mod p)"
      using index_tensor_mat [OF P_dr P_dc Q_dr Q_dc ij_lt(2) ij_lt(1)
                                m_pos p_pos] .
    have P_herm_entry: "P $$ (j div p, i div p)
                      = cnj (P $$ (i div p, j div p))"
    proof -
      have "P\<^sup>\<dagger> $$ (i div p, j div p) = cnj (P $$ (j div p, i div p))"
        unfolding dagger_def using iP_lt jP_lt P_dr P_dc by simp
      hence "P $$ (i div p, j div p) = cnj (P $$ (j div p, i div p))"
        using Pdag by simp
      thus ?thesis by (metis complex_cnj_cnj)
    qed
    have Q_herm_entry: "Q $$ (j mod p, i mod p)
                      = cnj (Q $$ (i mod p, j mod p))"
    proof -
      have "Q\<^sup>\<dagger> $$ (i mod p, j mod p) = cnj (Q $$ (j mod p, i mod p))"
        unfolding dagger_def using iQ_lt jQ_lt Q_dr Q_dc by simp
      hence "Q $$ (i mod p, j mod p) = cnj (Q $$ (j mod p, i mod p))"
        using Qdag by simp
      thus ?thesis by (metis complex_cnj_cnj)
    qed
    have "?T\<^sup>\<dagger> $$ (i, j) = cnj (?T $$ (j, i))"
      unfolding dagger_def using ij_lt T_dr T_dc Pcar Qcar by simp
    also have "\<dots> = cnj (P $$ (j div p, i div p) * Q $$ (j mod p, i mod p))"
      using Tji_entry by simp
    also have "\<dots> = cnj (P $$ (j div p, i div p))
                  * cnj (Q $$ (j mod p, i mod p))" by simp
    also have "\<dots> = P $$ (i div p, j div p) * Q $$ (i mod p, j mod p)"
      using P_herm_entry Q_herm_entry by (metis complex_cnj_cnj)
    also have "\<dots> = ?T $$ (i, j)" using T_entry by simp
    finally show "?T\<^sup>\<dagger> $$ (i, j) = ?T $$ (i, j)" .
  qed
  thus ?thesis by (simp add: hermitian_def)
qed

text \<open>Generators of \<open>separable_cone_lmat\<close> have hermitian unwrap.\<close>

lemma separable_lmat_gen_hermitian:
  fixes \<sigma> :: "(complex, 'm :: finite \<times> 'p :: finite, 'm \<times> 'p) lmat"
  assumes "\<sigma> \<in> separable_lmat_gen"
  shows "hermitian (unwrap_lm \<sigma>)"
proof -
  from assms obtain a b
    where \<sigma>_eq: "\<sigma> = tensor_lmat a b"
      and a_psd: "psd_lmat (a :: (complex, 'm, 'm) lmat)"
      and b_psd: "psd_lmat (b :: (complex, 'p, 'p) lmat)"
    unfolding separable_lmat_gen_def by auto
  have a_herm: "hermitian (unwrap_lm a)" using a_psd by (simp add: psd_def)
  have b_herm: "hermitian (unwrap_lm b)" using b_psd by (simp add: psd_def)
  have a_car: "unwrap_lm a \<in> carrier_mat (CARD('m)) (CARD('m))"
    by (rule carrier_matI) auto
  have b_car: "unwrap_lm b \<in> carrier_mat (CARD('p)) (CARD('p))"
    by (rule carrier_matI) auto
  have m_pos: "0 < CARD('m)" by simp
  have p_pos: "0 < CARD('p)" by simp
  have "hermitian (unwrap_lm a \<Otimes> unwrap_lm b)"
    using hermitian_tensor_mat [OF a_car b_car m_pos p_pos a_herm b_herm] .
  thus ?thesis using \<sigma>_eq by simp
qed

text \<open>The hermitian set in lmat is a convex cone, hence contains the
hull of the generators.\<close>

lemma hermitian_lmat_set_convex_cone:
  "convex_cone {M :: (complex, 'k :: finite, 'k) lmat.
                  hermitian (unwrap_lm M)}"
proof -
  let ?H = "{M :: (complex, 'k, 'k) lmat. hermitian (unwrap_lm M)}"
  have zero_in: "(0 :: (complex, 'k, 'k) lmat) \<in> ?H"
    using hermitian_zero_mat by simp
  have add_closed:
    "\<And>M N. M \<in> ?H \<Longrightarrow> N \<in> ?H \<Longrightarrow> M + N \<in> ?H"
  proof -
    fix M N :: "(complex, 'k, 'k) lmat"
    assume Mh: "M \<in> ?H" and Nh: "N \<in> ?H"
    have Mherm: "hermitian (unwrap_lm M)" using Mh by simp
    have Nherm: "hermitian (unwrap_lm N)" using Nh by simp
    have Mcar: "unwrap_lm M \<in> carrier_mat (CARD('k)) (CARD('k))"
      by (rule carrier_matI) auto
    have Ncar: "unwrap_lm N \<in> carrier_mat (CARD('k)) (CARD('k))"
      by (rule carrier_matI) auto
    have MN_eq: "unwrap_lm (M + N) = unwrap_lm M + unwrap_lm N"
    proof (rule eq_matI)
      fix i j
      assume "i < dim_row (unwrap_lm M + unwrap_lm N)"
             "j < dim_col (unwrap_lm M + unwrap_lm N)"
      hence ij: "i < CARD('k)" "j < CARD('k)" using Mcar Ncar by simp_all
      show "unwrap_lm (M + N) $$ (i, j)
          = (unwrap_lm M + unwrap_lm N) $$ (i, j)"
        using ij Mcar Ncar by (simp add: index_add_mat)
    qed (use Mcar Ncar in auto)
    have "hermitian (unwrap_lm M + unwrap_lm N)"
      using hermitian_add_mat [OF Mcar Ncar Mherm Nherm] .
    hence "hermitian (unwrap_lm (M + N))" using MN_eq by simp
    thus "M + N \<in> ?H" by simp
  qed
  have scaleR_closed:
    "\<And>M c. M \<in> ?H \<Longrightarrow> 0 \<le> c \<Longrightarrow> c *\<^sub>R M \<in> ?H"
  proof -
    fix M :: "(complex, 'k, 'k) lmat" and c :: real
    assume Mh: "M \<in> ?H" and c_nn: "0 \<le> c"
    have Mherm: "hermitian (unwrap_lm M)" using Mh by simp
    have Mcar: "unwrap_lm M \<in> carrier_mat (CARD('k)) (CARD('k))"
      by (rule carrier_matI) auto
    have unwrap_eq:
      "unwrap_lm (c *\<^sub>R M) = complex_of_real c \<cdot>\<^sub>m unwrap_lm M"
      by (rule unwrap_lm_scaleR_eq)
    have "hermitian (complex_of_real c \<cdot>\<^sub>m unwrap_lm M)"
      using hermitian_smult_real_mat [OF Mcar Mherm] .
    hence "hermitian (unwrap_lm (c *\<^sub>R M))" using unwrap_eq by simp
    thus "c *\<^sub>R M \<in> ?H" by simp
  qed
  show ?thesis
    using zero_in add_closed scaleR_closed
    by (subst convex_cone_iff) blast
qed

theorem separable_cone_lmat_hermitian:
  fixes \<sigma> :: "(complex, 'm :: finite \<times> 'p :: finite, 'm \<times> 'p) lmat"
  assumes "\<sigma> \<in> separable_cone_lmat"
  shows "hermitian (unwrap_lm \<sigma>)"
proof -
  let ?H = "{M :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat.
              hermitian (unwrap_lm M)}"
  have gen_sub: "separable_lmat_gen \<subseteq> ?H"
    using separable_lmat_gen_hermitian by blast
  have H_cone: "convex_cone ?H"
    by (rule hermitian_lmat_set_convex_cone)
  have "convex_cone hull
          (separable_lmat_gen :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat set)
         \<subseteq> ?H"
    using gen_sub H_cone by (rule hull_minimal)
  hence "separable_cone_lmat \<subseteq> ?H"
    unfolding separable_cone_lmat_def .
  thus ?thesis using assms by blast
qed

text \<open>Final form of the entanglement witness theorem: the side
condition ``\<open>\<sigma>\<close> has hermitian unwrap'' is automatic for elements
of the separable cone.\<close>

theorem entanglement_witness_hermitian':
  fixes \<rho> :: "(complex, 'm :: finite \<times> 'p :: finite, 'm \<times> 'p) lmat"
  assumes notin: "\<rho> \<notin> separable_cone_lmat"
      and \<rho>_herm: "hermitian (unwrap_lm \<rho>)"
  shows "\<exists>W :: complex Matrix.mat.
           W \<in> carrier_mat (CARD('m \<times> 'p)) (CARD('m \<times> 'p))
         \<and> hermitian W
         \<and> Re (Tr (W * unwrap_lm \<rho>)) < 0
         \<and> (\<forall>\<sigma> :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat.
              \<sigma> \<in> separable_cone_lmat
                \<longrightarrow> 0 \<le> Re (Tr (W * unwrap_lm \<sigma>)))"
proof -
  obtain W where W_car: "W \<in> carrier_mat (CARD('m \<times> 'p)) (CARD('m \<times> 'p))"
            and W_herm: "hermitian W"
            and W_\<rho>: "Re (Tr (W * unwrap_lm \<rho>)) < 0"
            and W_\<sigma>: "\<forall>\<sigma> :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat.
                       \<sigma> \<in> separable_cone_lmat
                       \<and> hermitian (unwrap_lm \<sigma>)
                         \<longrightarrow> 0 \<le> Re (Tr (W * unwrap_lm \<sigma>))"
    using entanglement_witness_hermitian [OF notin \<rho>_herm] by blast
  have W_\<sigma>': "\<forall>\<sigma> :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat.
                \<sigma> \<in> separable_cone_lmat
                  \<longrightarrow> 0 \<le> Re (Tr (W * unwrap_lm \<sigma>))"
  proof (intro allI impI)
    fix \<sigma> :: "(complex, 'm \<times> 'p, 'm \<times> 'p) lmat"
    assume \<sigma>_in: "\<sigma> \<in> separable_cone_lmat"
    hence \<sigma>_herm: "hermitian (unwrap_lm \<sigma>)"
      by (rule separable_cone_lmat_hermitian)
    show "0 \<le> Re (Tr (W * unwrap_lm \<sigma>))"
      using W_\<sigma> \<sigma>_in \<sigma>_herm by blast
  qed
  show ?thesis using W_car W_herm W_\<rho> W_\<sigma>' by blast
qed


section \<open>Main separability characterisation\<close>

text \<open>The Horodecki-style witness characterisation: for hermitian
\<open>\<rho>\<close>, membership in the separable cone is equivalent to the
nonneg-real-trace property holding against every hermitian witness
that is itself nonneg-real-trace on the cone.\<close>

theorem separable_iff_witness:
  fixes \<rho> :: "(complex, 'm :: finite \<times> 'p :: finite, 'm \<times> 'p) lmat"
  assumes \<rho>_herm: "hermitian (unwrap_lm \<rho>)"
  shows "\<rho> \<in> separable_cone_lmat
       \<longleftrightarrow>
        (\<forall>W :: complex Matrix.mat.
           W \<in> carrier_mat (CARD('m \<times> 'p)) (CARD('m \<times> 'p))
           \<and> hermitian W
           \<and> (\<forall>\<sigma> :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat.
                \<sigma> \<in> separable_cone_lmat
                  \<longrightarrow> 0 \<le> Re (Tr (W * unwrap_lm \<sigma>)))
             \<longrightarrow> 0 \<le> Re (Tr (W * unwrap_lm \<rho>)))"
proof
  assume \<rho>_in: "\<rho> \<in> separable_cone_lmat"
  show "\<forall>W :: complex Matrix.mat.
          W \<in> carrier_mat (CARD('m \<times> 'p)) (CARD('m \<times> 'p))
          \<and> hermitian W
          \<and> (\<forall>\<sigma> :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat.
               \<sigma> \<in> separable_cone_lmat
                 \<longrightarrow> 0 \<le> Re (Tr (W * unwrap_lm \<sigma>)))
            \<longrightarrow> 0 \<le> Re (Tr (W * unwrap_lm \<rho>))"
    using \<rho>_in by blast
next
  assume rhs:
    "\<forall>W :: complex Matrix.mat.
       W \<in> carrier_mat (CARD('m \<times> 'p)) (CARD('m \<times> 'p))
       \<and> hermitian W
       \<and> (\<forall>\<sigma> :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat.
            \<sigma> \<in> separable_cone_lmat
              \<longrightarrow> 0 \<le> Re (Tr (W * unwrap_lm \<sigma>)))
         \<longrightarrow> 0 \<le> Re (Tr (W * unwrap_lm \<rho>))"
  show "\<rho> \<in> separable_cone_lmat"
  proof (rule ccontr)
    assume not_in: "\<rho> \<notin> separable_cone_lmat"
    obtain W :: "complex Matrix.mat"
      where W_car: "W \<in> carrier_mat (CARD('m \<times> 'p)) (CARD('m \<times> 'p))"
        and W_herm: "hermitian W"
        and W_\<rho>: "Re (Tr (W * unwrap_lm \<rho>)) < 0"
        and W_\<sigma>:
              "\<forall>\<sigma> :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat.
                \<sigma> \<in> separable_cone_lmat
                  \<longrightarrow> 0 \<le> Re (Tr (W * unwrap_lm \<sigma>))"
      using entanglement_witness_hermitian' [OF not_in \<rho>_herm] by blast
    have "0 \<le> Re (Tr (W * unwrap_lm \<rho>))"
      using rhs W_car W_herm W_\<sigma> by blast
    thus False using W_\<rho> by simp
  qed
qed


section \<open>Density-matrix specialisation\<close>

text \<open>For an actual quantum density matrix \<open>\<rho>\<close> (PSD with unit trace),
the conditions \<open>psd_lmat \<rho>\<close> and \<open>Tr_lmat \<rho> = 1\<close> imply
\<open>hermitian (unwrap_lm \<rho>)\<close>, so the witness theorem and the
characterisation specialise cleanly.\<close>

theorem entanglement_witness_for_density:
  fixes \<rho> :: "(complex, 'm :: finite \<times> 'p :: finite, 'm \<times> 'p) lmat"
  assumes \<rho>_psd: "psd_lmat \<rho>"
      and \<rho>_tr: "Tr_lmat \<rho> = 1"
      and \<rho>_not_sep: "\<rho> \<notin> separable_cone_lmat"
  shows "\<exists>W :: complex Matrix.mat.
           W \<in> carrier_mat (CARD('m \<times> 'p)) (CARD('m \<times> 'p))
         \<and> hermitian W
         \<and> Re (Tr (W * unwrap_lm \<rho>)) < 0
         \<and> (\<forall>\<sigma> :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat.
              \<sigma> \<in> separable_cone_lmat
                \<longrightarrow> 0 \<le> Re (Tr (W * unwrap_lm \<sigma>)))"
proof -
  have \<rho>_herm: "hermitian (unwrap_lm \<rho>)"
    using \<rho>_psd by (simp add: psd_def)
  show ?thesis
    using entanglement_witness_hermitian' [OF \<rho>_not_sep \<rho>_herm] .
qed

text \<open>The witness is also nonneg on every separable density matrix
(\<open>Sprime\<close>) since \<open>Sprime \<subseteq> separable_cone_lmat\<close>.\<close>

theorem entanglement_witness_for_density_on_Sprime:
  fixes \<rho> :: "(complex, 'm :: finite \<times> 'p :: finite, 'm \<times> 'p) lmat"
  assumes \<rho>_psd: "psd_lmat \<rho>"
      and \<rho>_tr: "Tr_lmat \<rho> = 1"
      and \<rho>_not_sep: "\<rho> \<notin> separable_cone_lmat"
  shows "\<exists>W :: complex Matrix.mat.
           W \<in> carrier_mat (CARD('m \<times> 'p)) (CARD('m \<times> 'p))
         \<and> hermitian W
         \<and> Re (Tr (W * unwrap_lm \<rho>)) < 0
         \<and> (\<forall>\<sigma> :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat.
              \<sigma> \<in> Sprime \<longrightarrow> 0 \<le> Re (Tr (W * unwrap_lm \<sigma>)))"
proof -
  obtain W where W_car: "W \<in> carrier_mat (CARD('m \<times> 'p)) (CARD('m \<times> 'p))"
            and W_herm: "hermitian W"
            and W_\<rho>: "Re (Tr (W * unwrap_lm \<rho>)) < 0"
            and W_cone: "\<forall>\<sigma> :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat.
                          \<sigma> \<in> separable_cone_lmat
                            \<longrightarrow> 0 \<le> Re (Tr (W * unwrap_lm \<sigma>))"
    using entanglement_witness_for_density [OF \<rho>_psd \<rho>_tr \<rho>_not_sep] by blast
  have Sprime_sub:
    "(Sprime :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat set)
       \<subseteq> separable_cone_lmat"
  proof -
    have step1: "Sprime \<subseteq> (separable_lmat_gen
                              :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat set)"
      by (rule Sprime_subset_separable_lmat_gen)
    have step2: "(separable_lmat_gen :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat set)
                  \<subseteq> separable_cone_lmat"
      unfolding separable_cone_lmat_def by (rule hull_subset)
    show ?thesis using step1 step2 by (rule subset_trans)
  qed
  have W_Sprime:
    "\<forall>\<sigma> :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat.
       \<sigma> \<in> Sprime \<longrightarrow> 0 \<le> Re (Tr (W * unwrap_lm \<sigma>))"
    using W_cone Sprime_sub by blast
  show ?thesis using W_car W_herm W_\<rho> W_Sprime by blast
qed

text \<open>The full Horodecki characterisation, specialised to density
matrices.\<close>

theorem separable_density_iff_witness:
  fixes \<rho> :: "(complex, 'm :: finite \<times> 'p :: finite, 'm \<times> 'p) lmat"
  assumes \<rho>_psd: "psd_lmat \<rho>"
      and \<rho>_tr: "Tr_lmat \<rho> = 1"
  shows "\<rho> \<in> separable_cone_lmat
       \<longleftrightarrow>
        (\<forall>W :: complex Matrix.mat.
           W \<in> carrier_mat (CARD('m \<times> 'p)) (CARD('m \<times> 'p))
           \<and> hermitian W
           \<and> (\<forall>\<sigma> :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat.
                \<sigma> \<in> separable_cone_lmat
                  \<longrightarrow> 0 \<le> Re (Tr (W * unwrap_lm \<sigma>)))
             \<longrightarrow> 0 \<le> Re (Tr (W * unwrap_lm \<rho>)))"
proof -
  have \<rho>_herm: "hermitian (unwrap_lm \<rho>)"
    using \<rho>_psd by (simp add: psd_def)
  show ?thesis using separable_iff_witness [OF \<rho>_herm] .
qed


text \<open>The trace is identically \<open>1\<close> on the convex hull of \<open>Sprime\<close>.\<close>

lemma Tr_lmat_convex_hull_Sprime_eq_one:
  fixes \<rho> :: "(complex, 'm :: finite \<times> 'p :: finite, 'm \<times> 'p) lmat"
  assumes "\<rho> \<in> convex hull Sprime"
  shows "Tr_lmat \<rho> = 1"
proof -
  from assms obtain T u
    where Tfin: "finite T"
      and Tsub: "T \<subseteq> (Sprime :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat set)"
      and unn: "\<forall>t \<in> T. 0 \<le> u t"
      and usum: "sum u T = 1"
      and sum_eq:
        "(\<Sum>t \<in> T. u t *\<^sub>R t) = \<rho>"
    unfolding convex_hull_explicit by auto
  have Tr_Sprime:
    "\<And>s :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat. s \<in> Sprime \<Longrightarrow> Tr_lmat s = 1"
  proof -
    fix s :: "(complex, 'm \<times> 'p, 'm \<times> 'p) lmat"
    assume "s \<in> Sprime"
    then obtain \<sigma>\<^sub>0 \<tau>\<^sub>0
      where s_eq: "s = tensor_lmat \<sigma>\<^sub>0 \<tau>\<^sub>0"
        and tr_s: "Tr_lmat (\<sigma>\<^sub>0 :: (complex, 'm, 'm) lmat) = 1"
        and tr_t: "Tr_lmat (\<tau>\<^sub>0 :: (complex, 'p, 'p) lmat) = 1"
      unfolding Sprime_def by auto
    have "Tr_lmat s = Tr_lmat (tensor_lmat \<sigma>\<^sub>0 \<tau>\<^sub>0
                                 :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat)"
      using s_eq by simp
    also have "\<dots> = Tr_lmat \<sigma>\<^sub>0 * Tr_lmat \<tau>\<^sub>0" by (rule Tr_lmat_tensor)
    also have "\<dots> = 1" using tr_s tr_t by simp
    finally show "Tr_lmat s = 1" .
  qed
  have "Tr_lmat \<rho> = Tr_lmat ((\<Sum>t \<in> T. u t *\<^sub>R t)
                              :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat)"
    using sum_eq by simp
  also have "\<dots> = (\<Sum>t \<in> T. u t *\<^sub>R Tr_lmat t)"
    using Tfin by (rule Tr_lmat_sum_scaleR)
  also have "\<dots> = (\<Sum>t \<in> T. u t *\<^sub>R 1)"
    using Tsub Tr_Sprime by (intro sum.cong) auto
  also have "\<dots> = (\<Sum>t \<in> T. complex_of_real (u t))"
    by (intro sum.cong) (simp_all add: scaleR_conv_of_real)
  also have "\<dots> = complex_of_real (\<Sum>t \<in> T. u t)" by simp
  also have "\<dots> = 1" using usum by simp
  finally show ?thesis .
qed

text \<open>A density matrix is separable iff it is a convex combination of
separable pure-product states.  This is the standard textbook
definition of separability for mixed states.\<close>

theorem separable_density_iff_in_convex_hull_Sprime:
  fixes \<rho> :: "(complex, 'm :: finite \<times> 'p :: finite, 'm \<times> 'p) lmat"
  assumes \<rho>_psd: "psd_lmat \<rho>"
      and \<rho>_tr: "Tr_lmat \<rho> = 1"
  shows "\<rho> \<in> separable_cone_lmat \<longleftrightarrow> \<rho> \<in> convex hull Sprime"
proof
  assume rho_in_hull: "\<rho> \<in> convex hull Sprime"
  text \<open>(Easy direction.)  \<open>convex hull Sprime \<subseteq> separable_cone_lmat\<close>.\<close>
  have Sprime_sub:
    "(Sprime :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat set)
       \<subseteq> separable_cone_lmat"
  proof -
    have s1: "Sprime \<subseteq> (separable_lmat_gen
                          :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat set)"
      by (rule Sprime_subset_separable_lmat_gen)
    have s2: "(separable_lmat_gen :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat set)
                \<subseteq> separable_cone_lmat"
      unfolding separable_cone_lmat_def by (rule hull_subset)
    show ?thesis using s1 s2 by (rule subset_trans)
  qed
  have cone_convex:
    "convex (separable_cone_lmat
              :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat set)"
    using separable_cone_lmat_convex_cone
    unfolding convex_cone_def by blast
  have hull_in_cone:
    "convex hull (Sprime :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat set)
        \<subseteq> separable_cone_lmat"
    using Sprime_sub cone_convex by (rule hull_minimal)
  thus "\<rho> \<in> separable_cone_lmat" using rho_in_hull by blast
next
  assume rho_in_cone: "\<rho> \<in> separable_cone_lmat"
  text \<open>(Hard direction.)  Use \<open>convex_cone_hull_separable_eq_Sprime\<close>
  + \<open>convex_cone_hull_separate\<close> to identify the cone with
  \<open>insert 0 (conic hull (convex hull Sprime))\<close>, then exploit that
  \<open>\<rho>\<close> has unit trace.\<close>
  let ?S' = "Sprime :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat set"
  have hull_eq:
    "separable_cone_lmat
       = insert 0 (conic hull (convex hull ?S'))"
  proof -
    have "separable_cone_lmat
        = convex_cone hull (separable_lmat_gen
                              :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat set)"
      unfolding separable_cone_lmat_def ..
    also have "\<dots> = convex_cone hull ?S'"
      using convex_cone_hull_separable_eq_Sprime .
    also have "\<dots> = insert 0 (conic hull (convex hull ?S'))"
      by (rule convex_cone_hull_separate)
    finally show ?thesis .
  qed
  have rho_nonzero: "\<rho> \<noteq> 0"
  proof
    assume "\<rho> = 0"
    hence "Tr_lmat \<rho> = 0" by simp
    thus False using \<rho>_tr by simp
  qed
  from hull_eq rho_in_cone
  have rho_in_conic: "\<rho> \<in> conic hull (convex hull ?S')"
    using rho_nonzero by auto
  then obtain c x where rho_eq: "\<rho> = c *\<^sub>R x"
                    and c_nn: "0 \<le> c"
                    and x_in: "x \<in> convex hull ?S'"
    unfolding conic_hull_explicit by auto
  have Tr_x_one: "Tr_lmat x = 1"
    using x_in by (rule Tr_lmat_convex_hull_Sprime_eq_one)
  have "Tr_lmat \<rho> = c *\<^sub>R Tr_lmat x"
    using rho_eq Tr_lmat_scaleR by simp
  also have "\<dots> = c *\<^sub>R (1 :: complex)" using Tr_x_one by simp
  also have "\<dots> = complex_of_real c"
    by (simp add: scaleR_conv_of_real)
  finally have c_eq: "(complex_of_real c :: complex) = 1"
    using \<rho>_tr by simp
  have c_one: "c = 1"
    using c_eq by (metis Re_complex_of_real one_complex.simps(1))
  have "\<rho> = 1 *\<^sub>R x" using rho_eq c_one by simp
  hence "\<rho> = x" by simp
  thus "\<rho> \<in> convex hull Sprime" using x_in by simp
qed


end

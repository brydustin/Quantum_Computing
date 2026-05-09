(*
  Title:    Lmat/Separable_Cone.thy
  Purpose:  Define the separable-state cone in the typed lmat space and
            prove it is closed in the Hilbert-Schmidt topology, using
            the HOL-Analysis machinery exposed by Lmat_Euclidean.
*)

theory Separable_Cone
  imports
    Lmat_Euclidean
    Vern_Paulsen_QC_3_10.Quantum_Computing_3_10
    Isabelle_Marries_Dirac.Tensor
    "HOL-Analysis.Convex"
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

theorem separable_cone_lmat_closed:
  "closed (separable_cone_lmat
            :: (complex, 'm :: finite \<times> 'p :: finite, 'm \<times> 'p) lmat set)"
  sorry


end

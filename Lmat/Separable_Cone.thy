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


section \<open>Closedness\<close>

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

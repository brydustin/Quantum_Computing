(*  Title:   Day26_Separable_Cone.thy
    Author:  Dustin Bryant.  Days 26-28 of Paulsen's lectures: the separable cone is closed,
             separating hyperplanes, entanglement witnesses, the Horodecki characterisation.
*)

theory Day26_Separable_Cone
  imports
    Day22_UCP_Compact
    Day26_Arveson_Extension
    "HOL-Analysis.Convex"
    "HOL-Analysis.Convex_Euclidean_Space"
    "HOL-Analysis.Polytope"
    "HOL-Analysis.Starlike"
begin

text \<open>HOL-Hahn\_Banach defines a locale also called \<open>continuous\<close>.
Hide its short name so that, in the proofs below, \<open>continuous\<close>
resolves to the topological-space predicate from
\<^theory>\<open>HOL.Topological_Spaces\<close>.\<close>

hide_const (open) Function_Norm.continuous

section \<open>Separability and entanglement witnesses: the proofs (Days 26--28)\<close>

text \<open>This theory proves the results restated lecture by lecture in theory
Day26\_Separability.  The notes argue in the real vector space of Hermitian matrices with a
closed-cone separation theorem; formally we work in the typed matrix space
\<open>(complex, 'm \<times> 'p, 'm \<times> 'p) lmat\<close>, a real inner-product space (Lmat\_Euclidean), and use
HOL-Analysis' \<open>separating_hyperplane_closed_point\<close>.  Steps: the positive matrices form a
closed set; the unit-trace positive matrices form a compact set; the tensor product is
continuous, so the product density matrices \<open>Sprime\<close> form a compact set; its convex hull is
compact and does not contain $0$, and the separable cone is the cone over it, hence closed.  Separation
then yields a real functional, which is converted into a Hermitian witness $W$ with
$\Re\Tr(W\rho)<0\le\Re\Tr(W\sigma)$ on the cone.\<close>

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

text \<open>Why the separable cone is closed.  Let $S'=\{\sigma\otimes\tau:\ \sigma,\tau\ge0,\ \Tr\sigma=\Tr\tau=1\}$.
\begin{enumerate}
\item $S'$ is compact: the positive matrices of trace $1$ form a closed and bounded set
  ($\norm\sigma_{HS}\le\Tr\sigma=1$), and $\otimes$ is continuous.
\item Its convex hull $K$ is compact, and $0\notin K$ since every element of $K$ has trace $1$.
\item For $\sigma,\tau\ge0$, $\sigma\otimes\tau=\Tr\sigma\,\Tr\tau\cdot\frac{\sigma}{\Tr\sigma}\otimes\frac{\tau}{\Tr\tau}$ if both traces are
  positive, and $\sigma\otimes\tau=0$ otherwise (a positive matrix of trace $0$ is $0$).
\item So the separable cone is $\{t\,k:\ t\ge0,\ k\in K\}$, and the cone over a compact convex set
  not containing $0$ is closed.
\end{enumerate}\<close>

text \<open>The convex cone hulls of \<open>separable_lmat_gen\<close> and \<open>Sprime\<close>
coincide: every \<open>tensor_lmat \<sigma> \<tau>\<close> with \<open>\<sigma>, \<tau>\<close> PSD can be rescaled
into \<open>Sprime\<close> by dividing by traces (when nonzero) or replaced by
0 when a trace is zero.\<close>

text \<open>The hard inclusion uses step 3 above: positivity is preserved by non-negative scaling, a
positive matrix of trace $0$ is $0$, and $\otimes$ is bilinear.\<close>

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
    by (rule psd_smult_nonneg [OF a_nn M_jnf_psd M_jnf_carr])
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

text \<open>Separation.  The separable cone $C$ is closed and convex, so a point $\rho\notin C$ is strictly
separated from it by a linear functional $x\mapsto\langle a,x\rangle$ and a constant $b$:
$\langle a,\rho\rangle<b<\langle a,x\rangle$ for $x\in C$.  Since $C$ is a cone, $b<0$ and
$\langle a,x\rangle\ge0$ on $C$.\<close>

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

text \<open>Since $\langle a,x\rangle=\mathrm{Re}\Tr(a^*x)$, the separating functional is a matrix $W$ with
$\mathrm{Re}\Tr(W^*\rho)<0\le\mathrm{Re}\Tr(W^*\sigma)$ for every separable $\sigma$.\<close>

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

text \<open>If $\rho$ is Hermitian the witness can be taken Hermitian: replace $W$ by $\tfrac12(W+W^*)$,
which leaves $\mathrm{Re}\Tr(W^*\sigma)$ unchanged for Hermitian $\sigma$.\<close>

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


text \<open>Topology of the separable density-matrix set.\<close>

lemma compact_convex_hull_Sprime:
  "compact (convex hull
              (Sprime :: (complex, 'm :: finite \<times> 'p :: finite, 'm \<times> 'p) lmat set))"
  using compact_Sprime by (rule compact_convex_hull)

lemma closed_convex_hull_Sprime:
  "closed (convex hull
              (Sprime :: (complex, 'm :: finite \<times> 'p :: finite, 'm \<times> 'p) lmat set))"
  using compact_convex_hull_Sprime by (rule compact_imp_closed)

lemma bounded_convex_hull_Sprime:
  "bounded (convex hull
              (Sprime :: (complex, 'm :: finite \<times> 'p :: finite, 'm \<times> 'p) lmat set))"
  using compact_convex_hull_Sprime by (rule compact_imp_bounded)


text \<open>Strict separation in the inner-product form: by closedness of
\<open>convex hull Sprime\<close> we get a strictly negative-inner-product
hyperplane.  The Re-trace strict-form is then an immediate corollary
once the hermitian witness construction is replayed.\<close>

lemma separable_density_separating_hyperplane:
  fixes \<rho> :: "(complex, 'm :: finite \<times> 'p :: finite, 'm \<times> 'p) lmat"
  assumes \<rho>_psd: "psd_lmat \<rho>"
      and \<rho>_tr: "Tr_lmat \<rho> = 1"
      and \<rho>_not_sep: "\<rho> \<notin> separable_cone_lmat"
  shows "\<exists>a b.
           inner a \<rho> < b
         \<and> (\<forall>\<sigma> :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat.
              \<sigma> \<in> convex hull Sprime \<longrightarrow> b < inner a \<sigma>)"
proof -
  have \<rho>_not_in_hull: "\<rho> \<notin> convex hull Sprime"
    using \<rho>_not_sep separable_density_iff_in_convex_hull_Sprime [OF \<rho>_psd \<rho>_tr]
    by blast
  have hull_closed: "closed (convex hull
                                (Sprime :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat set))"
    by (rule closed_convex_hull_Sprime)
  have hull_convex: "convex (convex hull
                                (Sprime :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat set))"
    by (rule convex_convex_hull)
  show ?thesis
    using separating_hyperplane_closed_point
            [OF hull_convex hull_closed \<rho>_not_in_hull] by blast
qed


text \<open>The strict Re-trace form of the entanglement witness.\<close>

theorem entanglement_witness_strict:
  fixes \<rho> :: "(complex, 'm :: finite \<times> 'p :: finite, 'm \<times> 'p) lmat"
  assumes \<rho>_psd: "psd_lmat \<rho>"
      and \<rho>_tr: "Tr_lmat \<rho> = 1"
      and \<rho>_not_sep: "\<rho> \<notin> separable_cone_lmat"
  shows "\<exists>(W :: complex Matrix.mat) c.
           W \<in> carrier_mat (CARD('m \<times> 'p)) (CARD('m \<times> 'p))
         \<and> hermitian W
         \<and> Re (Tr (W * unwrap_lm \<rho>)) < c
         \<and> (\<forall>\<sigma> :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat.
              \<sigma> \<in> convex hull Sprime
                \<longrightarrow> c < Re (Tr (W * unwrap_lm \<sigma>)))"
proof -
  obtain a c
    where ineq_\<rho>: "inner a \<rho> < c"
      and ineq_S: "\<forall>\<sigma> :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat.
                      \<sigma> \<in> convex hull Sprime \<longrightarrow> c < inner a \<sigma>"
    using separable_density_separating_hyperplane [OF \<rho>_psd \<rho>_tr \<rho>_not_sep]
    by blast
  obtain W :: "complex Matrix.mat"
    where W_car: "W \<in> carrier_mat (CARD('m \<times> 'p)) (CARD('m \<times> 'p))"
      and W_herm: "hermitian W"
      and W_eq: "\<forall>M :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat.
                   hermitian (unwrap_lm M)
                     \<longrightarrow> Re (Tr (W * unwrap_lm M)) = inner a M"
    using hermitian_witness_from_lmat [where 'k = "'m \<times> 'p" and a = a]
    by blast
  have \<rho>_herm: "hermitian (unwrap_lm \<rho>)"
    using \<rho>_psd by (simp add: psd_def)
  have re_tr_\<rho>: "Re (Tr (W * unwrap_lm \<rho>)) = inner a \<rho>"
    using W_eq \<rho>_herm by blast
  have re_tr_\<sigma>:
    "\<And>\<sigma> :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat.
       \<sigma> \<in> convex hull Sprime
        \<Longrightarrow> Re (Tr (W * unwrap_lm \<sigma>)) = inner a \<sigma>"
  proof -
    fix \<sigma> :: "(complex, 'm \<times> 'p, 'm \<times> 'p) lmat"
    assume \<sigma>_in: "\<sigma> \<in> convex hull Sprime"
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
      using separable_cone_lmat_convex_cone unfolding convex_cone_def by blast
    have hull_in_cone:
      "convex hull (Sprime :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat set)
         \<subseteq> separable_cone_lmat"
      using Sprime_sub cone_convex by (rule hull_minimal)
    hence \<sigma>_in_cone: "\<sigma> \<in> separable_cone_lmat" using \<sigma>_in by blast
    hence \<sigma>_herm: "hermitian (unwrap_lm \<sigma>)"
      by (rule separable_cone_lmat_hermitian)
    show "Re (Tr (W * unwrap_lm \<sigma>)) = inner a \<sigma>"
      using W_eq \<sigma>_herm by blast
  qed
  show ?thesis
  proof (intro exI conjI allI impI)
    show "W \<in> carrier_mat (CARD('m \<times> 'p)) (CARD('m \<times> 'p))" by (rule W_car)
    show "hermitian W" by (rule W_herm)
    show "Re (Tr (W * unwrap_lm \<rho>)) < c"
      using re_tr_\<rho> ineq_\<rho> by simp
    fix \<sigma> :: "(complex, 'm \<times> 'p, 'm \<times> 'p) lmat"
    assume \<sigma>_in: "\<sigma> \<in> convex hull Sprime"
    have "Re (Tr (W * unwrap_lm \<sigma>)) = inner a \<sigma>"
      using re_tr_\<sigma> \<sigma>_in by simp
    moreover have "c < inner a \<sigma>" using ineq_S \<sigma>_in by blast
    ultimately show "c < Re (Tr (W * unwrap_lm \<sigma>))" by simp
  qed
qed


end

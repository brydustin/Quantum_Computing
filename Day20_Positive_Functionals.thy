(*  Title:   Day20_Positive_Functionals.thy
    Author:  Dustin Bryant, after Vern Paulsen's lecture of 12 October 2011 (Day 20)
*)

theory Day20_Positive_Functionals
  imports Day19_Choi_Theorem
begin

section \<open>Day 20 (12 October 2011): positive functionals, adjoints, Choi rank\<close>

text \<open>\begin{notesprop}
For linear $\phi:M_n\to\C$: $\phi$ positive $\Leftrightarrow$ $\phi$ completely positive
$\Leftrightarrow$ $(\phi(E_{ij}))\in M_n^+$.
\end{notesprop}
\begin{notesprop}
Let $\Phi:M_n\to M_d$ with Hilbert--Schmidt adjoint $\Phi^*:M_d\to M_n$ ($\langle Y|X\rangle=\tr(Y^*X)$).
(1) If $\Phi(X)=\sum_iA_iXA_i^*$ then $\Phi^*(Y)=\sum_iA_i^*YA_i$.
(2) $\Phi$ is completely positive iff $\Phi^*$ is.
(3) $\Phi$ is unital and completely positive iff $\Phi^*$ is completely positive and trace
preserving.
\end{notesprop}
\begin{notesdef}
The \emph{Choi rank} of a completely positive $\Phi$ is
$\crk(\Phi)=\min\{L:\Phi(X)=\sum_{l=1}^LB_lXB_l^*\}$.
\end{notesdef}
\begin{notestheorem}[Choi]
$\crk(\Phi)=\rank(P_\Phi)$.
\end{notestheorem}
The functional proposition, the adjoint proposition (for Kraus maps) and the definition of
the Choi rank are formalised below; the rank theorem is \<open>choi_rank_eq_rank\<close>, proved on Day 22 from the linear independence
of minimal Kraus representations (its lemma $\rank((E_{ij}))=1$ is not needed), and the bound
$\crk(\Phi)\le nd$ is below.\<close>

subsection \<open>The adjoint of a Kraus map\<close>

text \<open>For $\Phi(X)=\sum_iA_iXA_i^\dagger$ with $A_i\in M_{d,n}$, the adjoint is
$\Phi^*(Y)=\sum_iA_i^\dagger YA_i$ (\<open>kraus_adjoint_dim n As\<close>; the output dimension $n$ is
kept explicit for the empty list).\<close>

definition kraus_adjoint_dim ::
  "nat \<Rightarrow> complex Matrix.mat list \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "kraus_adjoint_dim n As y \<equiv>
     foldr (\<lambda>A acc. (A\<^sup>\<dagger>) * y * A + acc) As (0\<^sub>m n n)"

lemma kraus_adjoint_dim_Nil [simp]:
  fixes Y :: "complex Matrix.mat"
  shows "kraus_adjoint_dim n [] Y = 0\<^sub>m n n"
  by (simp add: kraus_adjoint_dim_def)

lemma kraus_adjoint_dim_Cons [simp]:
  fixes Y :: "complex Matrix.mat"
  shows "kraus_adjoint_dim n (A # As) Y =
           (A\<^sup>\<dagger>) * Y * A + kraus_adjoint_dim n As Y"
  by (simp add: kraus_adjoint_dim_def)

lemma kraus_adjoint_dim_carrier:
  fixes Y :: "complex Matrix.mat"
  assumes As_c: "\<forall>A \<in> set As. A \<in> carrier_mat d n"
      and Y_c: "Y \<in> carrier_mat d d"
  shows "kraus_adjoint_dim n As Y \<in> carrier_mat n n"
  using As_c
proof (induction As)
  case Nil
  show ?case by simp
next
  case (Cons A As)
  hence A_c: "A \<in> carrier_mat d n"
    and As_c': "\<forall>X \<in> set As. X \<in> carrier_mat d n"
    by auto
  have Adag_c: "A\<^sup>\<dagger> \<in> carrier_mat n d"
    using A_c by (rule dagger_carrier)
  have term_c: "(A\<^sup>\<dagger>) * Y * A \<in> carrier_mat n n"
    using Adag_c Y_c A_c by (intro mult_carrier_mat) auto
  have rec_c: "kraus_adjoint_dim n As Y \<in> carrier_mat n n"
    using Cons.IH As_c' by blast
  show ?case
    using term_c rec_c by simp
qed

lemma kraus_adjoint_dim_as_kraus_map_dim:
  fixes Y :: "complex Matrix.mat"
  assumes As_c: "\<forall>A \<in> set As. A \<in> carrier_mat d n"
      and Y_c: "Y \<in> carrier_mat d d"
  shows "kraus_adjoint_dim n As Y =
           kraus_map_dim n (map (\<lambda>A. (A\<^sup>\<dagger>)) As) Y"
  using As_c
proof (induction As)
  case Nil
  show ?case by simp
next
  case (Cons A As)
  hence A_c: "A \<in> carrier_mat d n"
    and As_c': "\<forall>X \<in> set As. X \<in> carrier_mat d n"
    by auto
  have dd_eq: "(A\<^sup>\<dagger>)\<^sup>\<dagger> = A"
    using A_c by (simp add: dagger_of_dagger_is_id)
  have IH: "kraus_adjoint_dim n As Y
              = kraus_map_dim n (map (\<lambda>A. (A\<^sup>\<dagger>)) As) Y"
    using Cons.IH As_c' by blast
  show "kraus_adjoint_dim n (A # As) Y  
      = kraus_map_dim n (map (\<lambda>A. (A\<^sup>\<dagger>)) (A # As)) Y"
    using dd_eq IH by simp
qed

text \<open>The adjoint identity $\langle Y|\Phi(X)\rangle=\langle\Phi^*(Y)|X\rangle$, by induction on
the Kraus list and cyclicity of the trace.\<close>

lemma hs_inner_prod_right_zero:
  "\<langle>\<langle> y | 0\<^sub>m m n \<rangle>\<rangle> = 0"
proof -
  have "\<langle>\<langle> y | 0\<^sub>m m n \<rangle>\<rangle>
          = (\<Sum>i\<in>{0..<m}. \<Sum>j\<in>{0..<n}.
                cnj (y $$ (i, j)) * (0\<^sub>m m n) $$ (i, j))"
    by (simp add: hs_inner_prod_def)
  also have "\<dots> = (\<Sum>i\<in>{0..<m}. \<Sum>j\<in>{0..<n}. (0 :: complex))"
    by (intro sum.cong refl) simp
  also have "\<dots> = 0" by simp
  finally show ?thesis.
qed

lemma hs_inner_prod_kraus_term:
  fixes A X Y :: "complex Matrix.mat"
  assumes A_c: "A \<in> carrier_mat d n"
      and X_c: "X \<in> carrier_mat n n"
      and Y_c: "Y \<in> carrier_mat d d"
  shows "\<langle>\<langle> Y | A * X * (A\<^sup>\<dagger>) \<rangle>\<rangle> = \<langle>\<langle> (A\<^sup>\<dagger>) * Y * A | X \<rangle>\<rangle>"
proof -
  have Adag_c: "A\<^sup>\<dagger> \<in> carrier_mat n d" using A_c by (rule dagger_carrier)
  have Ydag_c: "Y\<^sup>\<dagger> \<in> carrier_mat d d" using Y_c by (rule dagger_carrier)
  have AX_c: "A * X \<in> carrier_mat d n"
    using A_c X_c by (rule mult_carrier_mat)
  have AXAd_c: "A * X * (A\<^sup>\<dagger>) \<in> carrier_mat d d"
    using AX_c Adag_c by (rule mult_carrier_mat)
  have YdA_c: "Y\<^sup>\<dagger> * A \<in> carrier_mat d n"
    using Ydag_c A_c by (rule mult_carrier_mat)
  have YdAX_c: "Y\<^sup>\<dagger> * A * X \<in> carrier_mat d n"
    using YdA_c X_c by (rule mult_carrier_mat)
  have AdY_c: "A\<^sup>\<dagger> * Y \<in> carrier_mat n d"
    using Adag_c Y_c by (rule mult_carrier_mat)
  have AdYA_c: "A\<^sup>\<dagger> * Y * A \<in> carrier_mat n n"
    using AdY_c A_c by (rule mult_carrier_mat)
  have AdYd_c: "(A\<^sup>\<dagger>) * (Y\<^sup>\<dagger>) \<in> carrier_mat n d"
    using Adag_c Ydag_c by (rule mult_carrier_mat)
  have AdYdA_c: "(A\<^sup>\<dagger>) * (Y\<^sup>\<dagger>) * A \<in> carrier_mat n n"
    using AdYd_c A_c by (rule mult_carrier_mat)

  have lhs: "\<langle>\<langle> Y | A * X * (A\<^sup>\<dagger>) \<rangle>\<rangle> = Tr (Y\<^sup>\<dagger> * (A * X * (A\<^sup>\<dagger>)))"
    using Y_c AXAd_c by (intro hs_inner_prod_as_trace) auto

  have assoc1: "Y\<^sup>\<dagger> * (A * X * (A\<^sup>\<dagger>)) = (Y\<^sup>\<dagger> * A * X) * (A\<^sup>\<dagger>)"
    using Ydag_c A_c X_c Adag_c
    by (smt (verit) AX_c assoc_mult_mat mult_carrier_mat)

  have cyc: "Tr ((Y\<^sup>\<dagger> * A * X) * (A\<^sup>\<dagger>)) = Tr ((A\<^sup>\<dagger>) * (Y\<^sup>\<dagger> * A * X))"
    using YdAX_c Adag_c by (intro Tr_cyclic, blast+)
    

  have assoc2: "(A\<^sup>\<dagger>) * ((Y\<^sup>\<dagger>) * A * X) = ((A\<^sup>\<dagger>) * (Y\<^sup>\<dagger>) * A) * X"
    using Adag_c Ydag_c A_c X_c
    by (smt (verit) YdA_c assoc_mult_mat mult_carrier_mat)

  have dim1: "dim_col ((A\<^sup>\<dagger>) * Y) = dim_row A"
    using AdY_c A_c by (metis carrier_matD)
  have dim2: "dim_col (A\<^sup>\<dagger>) = dim_row Y"
    using Adag_c Y_c by (metis carrier_matD)
  have dag_eq: "((A\<^sup>\<dagger>) * Y * A)\<^sup>\<dagger> = (A\<^sup>\<dagger>) * (Y\<^sup>\<dagger>) * A"
  proof -
    have step1: "((A\<^sup>\<dagger>) * Y * A)\<^sup>\<dagger> = (A\<^sup>\<dagger>) * (((A\<^sup>\<dagger>) * Y)\<^sup>\<dagger>)"
      using dim1 by (rule dagger_of_prod)
    have step2: "((A\<^sup>\<dagger>) * Y)\<^sup>\<dagger> = (Y\<^sup>\<dagger>) * ((A\<^sup>\<dagger>)\<^sup>\<dagger>)"
      using dim2 by (rule dagger_of_prod)
    have step3: "(A\<^sup>\<dagger>)\<^sup>\<dagger> = A"
      using A_c by (simp add: dagger_of_dagger_is_id)
    have step4: "(A\<^sup>\<dagger>) * ((Y\<^sup>\<dagger>) * A) = (A\<^sup>\<dagger>) * (Y\<^sup>\<dagger>) * A"
      using Adag_c Ydag_c A_c by simp
    show ?thesis
      using step1 step2 step3 step4 by simp
  qed

  have rhs: "\<langle>\<langle> (A\<^sup>\<dagger>) * Y * A | X \<rangle>\<rangle> = Tr (((A\<^sup>\<dagger>) * Y * A)\<^sup>\<dagger> * X)"
    using AdYA_c X_c by (intro hs_inner_prod_as_trace) auto

  show ?thesis
    using lhs assoc1 cyc assoc2 dag_eq rhs by simp
qed

theorem kraus_adjoint_correct:
  fixes As :: "complex Matrix.mat list"
    and X :: "complex Matrix.mat"
    and Y :: "complex Matrix.mat"
  assumes As_c: "\<forall>A \<in> set As. A \<in> carrier_mat d n"
      and X_c: "X \<in> carrier_mat n n"
      and Y_c: "Y \<in> carrier_mat d d"
  shows "\<langle>\<langle> Y | kraus_map_dim d As X \<rangle>\<rangle>
         = \<langle>\<langle> kraus_adjoint_dim n As Y | X \<rangle>\<rangle>"
  using As_c
proof (induction As)
  case Nil
  have lhs0: "\<langle>\<langle> Y | kraus_map_dim d [] X \<rangle>\<rangle> = 0"
    by (simp add: hs_inner_prod_right_zero)
  have rhs0: "\<langle>\<langle> kraus_adjoint_dim n [] Y | X \<rangle>\<rangle> = 0"
    using X_c hs_inner_prod_as_trace kraus_adjoint_dim_def by force
  show "\<langle>\<langle> Y | kraus_map_dim d [] X \<rangle>\<rangle> = \<langle>\<langle> kraus_adjoint_dim n [] Y | X \<rangle>\<rangle>" using lhs0 rhs0 by simp
next
  case (Cons A As)
  hence A_c: "A \<in> carrier_mat d n"
    and As_c': "\<forall>B \<in> set As. B \<in> carrier_mat d n"
    by auto
  have Adag_c: "A\<^sup>\<dagger> \<in> carrier_mat n d" using A_c by (rule dagger_carrier)
  have AX_c: "A * X \<in> carrier_mat d n" using A_c X_c by (rule mult_carrier_mat)
  have AXAd_c: "A * X * (A\<^sup>\<dagger>) \<in> carrier_mat d d"
    using AX_c Adag_c by (rule mult_carrier_mat)
  have AdY_c: "A\<^sup>\<dagger> * Y \<in> carrier_mat n d"
    using Adag_c Y_c by (rule mult_carrier_mat)
  have AdYA_c: "A\<^sup>\<dagger> * Y * A \<in> carrier_mat n n"
    using AdY_c A_c by (rule mult_carrier_mat)
  have km_c: "kraus_map_dim d As X \<in> carrier_mat d d"
    using kraus_map_dim_carrier[OF As_c' X_c] .
  have ka_c: "kraus_adjoint_dim n As Y \<in> carrier_mat n n"
    using kraus_adjoint_dim_carrier[OF As_c' Y_c] .

  have IH: "\<langle>\<langle> Y | kraus_map_dim d As X \<rangle>\<rangle>
         = \<langle>\<langle> kraus_adjoint_dim n As Y | X \<rangle>\<rangle>"
    using Cons.IH As_c' by blast

  have left_add: "\<langle>\<langle> A\<^sup>\<dagger> * Y * A + kraus_adjoint_dim n As Y | X \<rangle>\<rangle>
                  = \<langle>\<langle> A\<^sup>\<dagger> * Y * A | X \<rangle>\<rangle>
                    + \<langle>\<langle> kraus_adjoint_dim n As Y | X \<rangle>\<rangle>"
    using AdYA_c ka_c X_c
    by (metis carrier_matD(1,2) complex_cnj_add hs_inner_prod_cnj hs_inner_prod_right_add index_add_mat(2,3))

  have "\<langle>\<langle> Y | kraus_map_dim d (A # As) X \<rangle>\<rangle>
        = \<langle>\<langle> Y | A * X * (A\<^sup>\<dagger>) + kraus_map_dim d As X \<rangle>\<rangle>"
    by simp
  also have "\<dots> = \<langle>\<langle> Y | A * X * (A\<^sup>\<dagger>) \<rangle>\<rangle>
                  + \<langle>\<langle> Y | kraus_map_dim d As X \<rangle>\<rangle>"
    using Y_c AXAd_c km_c by (intro hs_inner_prod_right_add) auto
  also have "\<dots> = \<langle>\<langle> A\<^sup>\<dagger> * Y * A | X \<rangle>\<rangle>
                  + \<langle>\<langle> kraus_adjoint_dim n As Y | X \<rangle>\<rangle>"
    using hs_inner_prod_kraus_term[OF A_c X_c Y_c] IH by simp
  also have "\<dots> = \<langle>\<langle> A\<^sup>\<dagger> * Y * A + kraus_adjoint_dim n As Y | X \<rangle>\<rangle>"
    using left_add by simp
  also have "\<dots> = \<langle>\<langle> kraus_adjoint_dim n (A # As) Y | X \<rangle>\<rangle>"
    by simp
  finally show ?case.
qed

subsection \<open>Complete positivity and the UCP/CPTP duality\<close>

text \<open>$\Phi^*$ is the Kraus map of the adjoint operators, hence completely positive, and
$\Phi$ is unital iff $\Phi^*$ is trace preserving: $\sum_iA_iA_i^*=I$ in both cases, using that
$\tr(BY)=\tr(Y)$ for all $Y$ forces $B=I$.\<close>

theorem adjoint_cp_from_kraus:
  assumes As_c: "\<forall>A \<in> set As. A \<in> carrier_mat d n"
      and npos: "0 < n"
      and dpos: "0 < d"
  shows "completely_positive d n (kraus_adjoint_dim n As)"
proof -
  define Bs where "Bs = map (\<lambda>A. (A\<^sup>\<dagger>)) As"
  have Bs_c: "\<forall>B \<in> set Bs. B \<in> carrier_mat n d"
    using As_c by (auto simp: Bs_def dagger_carrier)

  show ?thesis
  proof (unfold completely_positive_def p_positive_def, intro allI impI)
    fix p :: nat and X :: "complex Matrix.mat"
    assume ppos: "0 < p"
       and X_c: "X \<in> carrier_mat (p*d) (p*d)"
       and X_psd: "psd X"

    have amp_eq:
      "amplification d n p (kraus_adjoint_dim n As) X =
       amplification d n p (kraus_map_dim n Bs) X"
    proof (rule eq_matI)
      show "dim_row (amplification d n p (kraus_adjoint_dim n As) X) =
            dim_row (amplification d n p (kraus_map_dim n Bs) X)"
        by (simp add: amplification_def)
      show "dim_col (amplification d n p (kraus_adjoint_dim n As) X) =
            dim_col (amplification d n p (kraus_map_dim n Bs) X)"
        by (simp add: amplification_def)
    next
      fix i j
      assume i: "i < dim_row (amplification d n p (kraus_map_dim n Bs) X)"
         and j: "j < dim_col (amplification d n p (kraus_map_dim n Bs) X)"
      hence ipn: "i < p*n" and jpn: "j < p*n"
        by (auto simp: amplification_def)
      have B_c: "block_of_mat d X (i div n) (j div n) \<in> carrier_mat d d"
        by (simp add: block_of_mat_def)
      have eq:
        "kraus_adjoint_dim n As (block_of_mat d X (i div n) (j div n)) =
         kraus_map_dim n Bs (block_of_mat d X (i div n) (j div n))"
        unfolding Bs_def
        using kraus_adjoint_dim_as_kraus_map_dim[OF As_c B_c].
      have lhs_index:
        "amplification d n p (kraus_adjoint_dim n As) X $$ (i,j)
           = (kraus_adjoint_dim n As)
                (block_of_mat d X (i div n) (j div n)) $$
             (i mod n, j mod n)"
        using ipn jpn by (simp add: amplification_def)
      have rhs_index:
        "amplification d n p (kraus_map_dim n Bs) X $$ (i,j)
           = (kraus_map_dim n Bs)
                (block_of_mat d X (i div n) (j div n)) $$
             (i mod n, j mod n)"
        using ipn jpn by (simp add: amplification_def)
      show "amplification d n p (kraus_adjoint_dim n As) X $$ (i,j) =
            amplification d n p (kraus_map_dim n Bs) X $$ (i,j)"
        using lhs_index rhs_index eq by simp
    qed

    have lifted_c:
      "\<forall>L \<in> set (map (\<lambda>B. 1\<^sub>m p \<Otimes> B) Bs). L \<in> carrier_mat (p*n) (p*d)"
      using tensor_id_kraus_list_carrier[OF Bs_c].
    have amp_kr:
      "amplification d n p (kraus_map_dim n Bs) X =
         kraus_map_dim (p*n) (map (\<lambda>B. 1\<^sub>m p \<Otimes> B) Bs) X"
      using amplification_kraus_map_dim[OF Bs_c X_c npos dpos].
    have psd_kr:
      "psd (kraus_map_dim (p*n) (map (\<lambda>B. 1\<^sub>m p \<Otimes> B) Bs) X)"
      using kraus_map_dim_psd[OF lifted_c X_c X_psd].
    show "psd (amplification d n p (kraus_adjoint_dim n As) X)"
      using amp_eq amp_kr psd_kr by simp
  qed
qed

lemma kraus_map_dim_one_eq_sum_wdag_w_dagger:
  fixes As :: "complex Matrix.mat list"
  assumes As_c: "\<forall>A \<in> set As. A \<in> carrier_mat d n"
  shows "kraus_map_dim d As (1\<^sub>m n)
         = sum_wdag_w d (map (\<lambda>A. (A\<^sup>\<dagger>)) As)"
  using As_c
proof (induction As)
  case Nil
  show ?case by (simp add: sum_wdag_w_def)
next
  case (Cons A As)
  hence A_c: "A \<in> carrier_mat d n"
    and As_c': "\<forall>B \<in> set As. B \<in> carrier_mat d n" by auto
  have Adag_c: "A\<^sup>\<dagger> \<in> carrier_mat n d" using A_c by (rule dagger_carrier)
  have A_one: "A * 1\<^sub>m n = A" using A_c by simp
  have ddag: "(A\<^sup>\<dagger>)\<^sup>\<dagger> = A"
    using A_c by (simp add: dagger_of_dagger_is_id)
  have IH: "kraus_map_dim d As (1\<^sub>m n)
              = sum_wdag_w d (map (\<lambda>A. (A\<^sup>\<dagger>)) As)"
    using Cons.IH As_c' .
  have "kraus_map_dim d (A # As) (1\<^sub>m n)
          = A * 1\<^sub>m n * (A\<^sup>\<dagger>) + kraus_map_dim d As (1\<^sub>m n)"
    by simp
  also have "\<dots> = A * (A\<^sup>\<dagger>) + sum_wdag_w d (map (\<lambda>A. (A\<^sup>\<dagger>)) As)"
    using A_one IH by simp
  also have "\<dots> = ((A\<^sup>\<dagger>)\<^sup>\<dagger>) * (A\<^sup>\<dagger>)
                  + sum_wdag_w d (map (\<lambda>A. (A\<^sup>\<dagger>)) As)"
    using ddag by simp
  also have "\<dots> = sum_wdag_w d ((A\<^sup>\<dagger>) # map (\<lambda>A. (A\<^sup>\<dagger>)) As)"
    by (simp add: sum_wdag_w_Cons)
  also have "\<dots> = sum_wdag_w d (map (\<lambda>A. (A\<^sup>\<dagger>)) (A # As))"
    by simp
  finally show ?case.
qed

theorem cp_unital_iff_adjoint_tp:
  assumes As_c: "\<forall>A \<in> set As. A \<in> carrier_mat d n"
      and npos: "0 < n"
      and dpos: "0 < d"
  shows "unital_map n d (kraus_map_dim d As)
         \<longleftrightarrow> trace_preserving d (kraus_adjoint_dim n As)"
proof -
  define Bs where "Bs = map (\<lambda>A. (A\<^sup>\<dagger>)) As"
  have Bs_c: "\<forall>B \<in> set Bs. B \<in> carrier_mat n d"
    using As_c by (auto simp: Bs_def dagger_carrier)
  let ?M = "sum_wdag_w d Bs"
  have M_c: "?M \<in> carrier_mat d d"
    using sum_wdag_w_carrier[OF Bs_c].

  have unital_iff:
    "unital_map n d (kraus_map_dim d As) \<longleftrightarrow> ?M = 1\<^sub>m d"
  proof -
    have eq: "kraus_map_dim d As (1\<^sub>m n) = ?M"
      unfolding Bs_def
      using kraus_map_dim_one_eq_sum_wdag_w_dagger[OF As_c].
    show ?thesis unfolding unital_map_def using eq by simp
  qed

  have Tr_adj:
    "\<And>Y. Y \<in> carrier_mat d d
       \<Longrightarrow> Tr (kraus_adjoint_dim n As Y) = Tr (?M * Y)"
  proof -
    fix Y :: "complex Matrix.mat"
    assume Y_c: "Y \<in> carrier_mat d d"
    have step1: "kraus_adjoint_dim n As Y = kraus_map_dim n Bs Y"
      unfolding Bs_def
      using kraus_adjoint_dim_as_kraus_map_dim[OF As_c Y_c].
    have step2: "Tr (kraus_map_dim n Bs Y) = Tr (?M * Y)"
      using Tr_kraus_map_dim_as_wdagw[OF Bs_c Y_c] .
    show "Tr (kraus_adjoint_dim n As Y) = Tr (?M * Y)"
      using step1 step2 by simp
  qed

  have tp_iff:
    "trace_preserving d (kraus_adjoint_dim n As) \<longleftrightarrow> ?M = 1\<^sub>m d"
  proof
    assume tp: "trace_preserving d (kraus_adjoint_dim n As)"
    have Tr_eq: "\<And>Y. Y \<in> carrier_mat d d \<Longrightarrow> Tr (?M * Y) = Tr Y"
    proof -
      fix Y :: "complex Matrix.mat"
      assume Y_c: "Y \<in> carrier_mat d d"
      have "Tr (kraus_adjoint_dim n As Y) = Tr Y"
        using tp Y_c by (simp add: trace_preserving_def)
      thus "Tr (?M * Y) = Tr Y" using Tr_adj[OF Y_c] by simp
    qed
    show "?M = 1\<^sub>m d"
    proof (rule eq_matI)
      show "dim_row ?M = dim_row (1\<^sub>m d)" using M_c by simp
      show "dim_col ?M = dim_col (1\<^sub>m d)" using M_c by simp
    next
      fix i j
      assume i: "i < dim_row (1\<^sub>m d)" and j: "j < dim_col (1\<^sub>m d)"
      hence id: "i < d" and jd: "j < d" by simp_all
      let ?E = "mat_unit j i d d"
      have E_c: "?E \<in> carrier_mat d d"
        by (simp add: mat_unit_def)
      have Tr_ME: "Tr (?M * ?E) = ?M $$ (i, j)"
        using Tr_mat_unit_mult[OF M_c id jd] .
      have Tr_E: "Tr ?E = (if j = i then 1 else 0)"
        using Tr_mat_unit[OF jd id].
      have eq: "Tr (?M * ?E) = Tr ?E"
        using Tr_eq[OF E_c].
      have M_ij: "?M $$ (i, j) = (if j = i then 1 else 0)"
        using Tr_ME Tr_E eq by simp
      have one_ij: "(1\<^sub>m d) $$ (i, j) = (if i = j then 1 else 0)"
        using id jd by simp
      show "?M $$ (i, j) = (1\<^sub>m d) $$ (i, j)"
        using M_ij one_ij by (cases "i = j") auto
    qed
  next
    assume M_id: "?M = 1\<^sub>m d"
    show "trace_preserving d (kraus_adjoint_dim n As)"
    proof (unfold trace_preserving_def, intro allI impI)
      fix Y :: "complex Matrix.mat"
      assume Y_c: "Y \<in> carrier_mat d d"
      have "Tr (kraus_adjoint_dim n As Y) = Tr (?M * Y)"
        using Tr_adj[OF Y_c] .
      also have "\<dots> = Tr ((1\<^sub>m d) * Y)" using M_id by simp
      also have "\<dots> = Tr Y" using Y_c by simp
      finally show "Tr (kraus_adjoint_dim n As Y) = Tr Y" .
    qed
  qed

  show ?thesis using unital_iff tp_iff by simp
qed

subsection \<open>Positive functionals are completely positive\<close>

text \<open>The case $d=1$ of Choi's theorem: for $P=(P_{ij})\in M_r(M_n)^+$ and $v=(\alpha_i)\in\C^r$,
$\braket v{(\phi(P_{ij}))v}=\phi(\sum_{ij}\overline{\alpha_i}\alpha_jP_{ij})=\phi(Y^*PY)\ge0$ with
$Y$ the block column $(\alpha_iI)_i$.\<close>

theorem positive_scalar_is_cp:
  fixes \<phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes linear: "\<And>A B. A \<in> carrier_mat n n \<Longrightarrow> B \<in> carrier_mat n n
                      \<Longrightarrow> \<phi> (A + B) = \<phi> A + \<phi> B"
      and smult:  "\<And>c A. A \<in> carrier_mat n n \<Longrightarrow> \<phi> (c \<cdot>\<^sub>m A) = c \<cdot>\<^sub>m \<phi> A"
      and range:  "\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<phi> A \<in> carrier_mat 1 1"
      and pos:    "positive_map n 1 \<phi>"
      and npos:   "0 < n"
  shows "completely_positive n 1 \<phi>"
proof -
  define P where "P = choi_matrix n 1 \<phi>"
  have Pc: "P \<in> carrier_mat n n" using choi_matrix_carrier[of n 1 \<phi>] by (simp add: P_def)
  have Pe: "P $$ (i, j) = \<phi> (E\<lbrakk>i,j ; n,n\<rbrakk>) $$ (0, 0)" if "i < n" "j < n" for i j
    using that by (simp add: P_def choi_matrix_def)
  have L: "lin_on n 1 (carrier_mat n n) \<phi>" unfolding lin_on_def using linear smult range by auto
  have rangeE: "\<phi> (E\<lbrakk>i,j ; n,n\<rbrakk>) \<in> carrier_mat 1 1" for i j using range by simp
  have quad: "\<langle>x | P *\<^sub>v x\<rangle> = \<phi> (outer_sum n [Matrix.vec n (\<lambda>i. cnj (x $ i))]) $$ (0, 0)"
    if x: "dim_vec x = n" for x
  proof -
    let ?X = "outer_sum n [Matrix.vec n (\<lambda>i. cnj (x $ i))]"
    have Xc: "?X \<in> carrier_mat n n" by auto
    have Xe: "?X $$ (i, j) = cnj (x $ i) * x $ j" if "i < n" "j < n" for i j
      using outer_sum_entry_sum_list[of "[Matrix.vec n (\<lambda>i. cnj (x $ i))]" n i j] that by simp
    have carr: "\<forall>y \<in> set (List.product [0..<n] [0..<n]).
                  (\<lambda>(i, j). ?X $$ (i, j) \<cdot>\<^sub>m \<phi> (E\<lbrakk>i,j ; n,n\<rbrakk>)) y \<in> carrier_mat 1 1"
      using rangeE by (auto simp: case_prod_beta)
    have "\<langle>x | P *\<^sub>v x\<rangle> = (\<Sum>i<n. \<Sum>j<n. cnj (x $ i) * (P $$ (i, j) * x $ j))"
      unfolding inner_prod_sum[OF x dim_mult_mat_vec[of P x, unfolded carrier_matD(1)[OF Pc]]] atLeast0LessThan
      by (rule sum.cong[OF refl])
         (simp add: mult_mat_vec_index[OF Pc carrier_vecI[OF x]] atLeast0LessThan sum_distrib_left)
    also have "\<dots> = (\<Sum>i<n. \<Sum>j<n. (?X $$ (i, j) \<cdot>\<^sub>m \<phi> (E\<lbrakk>i,j ; n,n\<rbrakk>)) $$ (0, 0))"
      by (intro sum.cong refl) (simp add: Pe Xe carrier_matD[OF rangeE] mult_ac)
    also have "\<dots> = \<phi> ?X $$ (0, 0)"
      unfolding lin_expansion[OF L Xc] using carr by (simp add: msum_index sum_list_product_upt case_prod_beta)
    finally show ?thesis .
  qed
  have rn: "\<langle>x | P *\<^sub>v x\<rangle> \<in> \<real> \<and> 0 \<le> Re \<langle>x | P *\<^sub>v x\<rangle>" if x: "dim_vec x = n" for x
  proof -
    let ?X = "outer_sum n [Matrix.vec n (\<lambda>i. cnj (x $ i))]"
    have Xpsd: "psd ?X"
      using outer_sum_psd[where vs = "[Matrix.vec n (\<lambda>i. cnj (x $ i))]" and k = 1 and n = n] by simp
    have Xc: "?X \<in> carrier_mat n n" by auto
    have phiXc: "\<phi> ?X \<in> carrier_mat 1 1" using range Xc by blast
    have "psd (\<phi> ?X)" by (rule pos[unfolded positive_map_def, THEN conjunct2, rule_format, OF Xc Xpsd])
    thus ?thesis unfolding quad[OF x] using psd_one_by_one[OF phiXc] by simp
  qed
  have "psd P"
    unfolding psd_def hermitian_iff_real_quad_form[OF Pc] using rn carrier_matD(1)[OF Pc] by blast
  moreover have "(0::nat) < 1" by simp
  ultimately show ?thesis using choi_theorem[OF linear smult range npos] by (simp add: P_def)
qed

subsection \<open>Choi rank\<close>

text \<open>\<open>choi_rank n d \<Phi>\<close> is the least length of a Kraus list representing $\Phi$ on the
carrier.  The theorem $\crk(\Phi)=\rank(P_\Phi)$ is \<open>choi_rank_eq_rank\<close>
(Day 22); the bound $\crk(\Phi)\le nd$ follows from the Kraus-rank bound of Day 21.\<close>

definition choi_rank ::
  "nat \<Rightarrow> nat \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow> nat" where
  "choi_rank n d \<Phi> \<equiv>
     Inf { length As | As :: complex Matrix.mat list.
             (\<forall>A \<in> set As. A \<in> carrier_mat d n)
             \<and> (\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi> X = kraus_map_dim d As X) }"

end

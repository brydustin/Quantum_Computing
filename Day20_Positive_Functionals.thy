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

  (* LHS as trace *)
  have lhs: "\<langle>\<langle> Y | A * X * (A\<^sup>\<dagger>) \<rangle>\<rangle> = Tr (Y\<^sup>\<dagger> * (A * X * (A\<^sup>\<dagger>)))"
    using Y_c AXAd_c by (intro hs_inner_prod_as_trace) auto

  (* Re-bracket: Y\<^sup>\<dagger> * (A X * A\<^sup>\<dagger>) = (Y\<^sup>\<dagger> * A * X) * A\<^sup>\<dagger> *)
  have assoc1: "Y\<^sup>\<dagger> * (A * X * (A\<^sup>\<dagger>)) = (Y\<^sup>\<dagger> * A * X) * (A\<^sup>\<dagger>)"
    using Ydag_c A_c X_c Adag_c
    by (smt (verit) AX_c assoc_mult_mat mult_carrier_mat)

  (* Trace cyclicity: Tr ((Y\<^sup>\<dagger> A X) A\<^sup>\<dagger>) = Tr (A\<^sup>\<dagger> (Y\<^sup>\<dagger> A X)) *)
  have cyc: "Tr ((Y\<^sup>\<dagger> * A * X) * (A\<^sup>\<dagger>)) = Tr ((A\<^sup>\<dagger>) * (Y\<^sup>\<dagger> * A * X))"
    using YdAX_c Adag_c by (intro Tr_cyclic, blast+)
    

  (* Re-bracket: A\<^sup>\<dagger> * (Y\<^sup>\<dagger> * A * X) = (A\<^sup>\<dagger> * Y\<^sup>\<dagger> * A) * X *)
  have assoc2: "(A\<^sup>\<dagger>) * ((Y\<^sup>\<dagger>) * A * X) = ((A\<^sup>\<dagger>) * (Y\<^sup>\<dagger>) * A) * X"
    using Adag_c Ydag_c A_c X_c
    by (smt (verit) YdA_c assoc_mult_mat mult_carrier_mat)

  (* Dagger identity: (A\<^sup>\<dagger> * Y * A)\<^sup>\<dagger> = A\<^sup>\<dagger> * Y\<^sup>\<dagger> * A *)
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

  (* RHS as trace *)
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

    (* Amplification of kraus_adjoint_dim n As agrees with that of
       kraus_map_dim n Bs because the two functions agree on M_{d,d}
       (kraus_adjoint_dim_as_kraus_map_dim). *)
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

    (* Reduce to PSD-ness of an amplified Kraus map (no TP needed). *)
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

  (* Unital: \<Phi>(I_n) = \<Sum> A A\<^sup>\<dagger> = ?M, so unital iff ?M = I_d *)
  have unital_iff:
    "unital_map n d (kraus_map_dim d As) \<longleftrightarrow> ?M = 1\<^sub>m d"
  proof -
    have eq: "kraus_map_dim d As (1\<^sub>m n) = ?M"
      unfolding Bs_def
      using kraus_map_dim_one_eq_sum_wdag_w_dagger[OF As_c].
    show ?thesis unfolding unital_map_def using eq by simp
  qed

  (* TP: Tr(\<Phi>\<^sup>*(Y)) = Tr(?M * Y), so TP iff \<forall>Y. Tr(?M * Y) = Tr Y *)
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
        using Tr_mult_mat_unit[OF M_c jd id].
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

lemma phi_entry_double_sum:
  fixes \<phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes f_add: "\<And>X Y. X \<in> carrier_mat n n \<Longrightarrow> Y \<in> carrier_mat n n
                    \<Longrightarrow> \<phi> (X + Y) = \<phi> X + \<phi> Y"
      and f_smult: "\<And>c X. X \<in> carrier_mat n n \<Longrightarrow> \<phi> (c \<cdot>\<^sub>m X) = c \<cdot>\<^sub>m \<phi> X"
      and f_car: "\<And>X. X \<in> carrier_mat n n \<Longrightarrow> \<phi> X \<in> carrier_mat d d"
      and M_c: "M \<in> carrier_mat n n"
      and r_lt: "r < d" and c_lt: "c < d"
      and npos: "0 < n" and dpos: "0 < d"
  shows "\<phi> M $$ (r, c) =
         (\<Sum>i<n. \<Sum>j<n. M $$ (i, j) * \<phi> (mat_unit i j n n) $$ (r, c))"
proof -
  have ps_valid: "\<forall>p \<in> set (mat_unit_pairs n). fst p < n \<and> snd p < n"
    using mat_unit_pairs_set by auto
  have phi_pc: "\<phi> M = pair_comb \<phi> M n d (mat_unit_pairs n)"
    using linear_eq_pair_comb[OF f_add f_smult f_car M_c npos dpos] .
  have fE_car: "\<And>a b. a < n \<Longrightarrow> b < n
                  \<Longrightarrow> \<phi> (mat_unit a b n n) \<in> carrier_mat d d"
  proof -
    fix a b :: nat
    assume "a < n" "b < n"
    have "mat_unit a b n n \<in> carrier_mat n n"
      by (simp add: mat_unit_def)
    thus "\<phi> (mat_unit a b n n) \<in> carrier_mat d d"
      using f_car by blast
  qed

  let ?term = "\<lambda>p. M $$ p * \<phi> (mat_unit (fst p) (snd p) n n) $$ (r, c)"
  have entry_eq:
    "\<phi> M $$ (r, c) = (\<Sum>p \<leftarrow> mat_unit_pairs n. ?term p)"
  proof -
    have pc_entry:
      "pair_comb \<phi> M n d (mat_unit_pairs n) $$ (r, c)
         = (\<Sum>p \<leftarrow> mat_unit_pairs n. ?term p)"
    proof (rule pair_comb_entry)
      fix a b :: nat
      assume "a < n" "b < n"
      thus "\<phi> (mat_unit a b n n) \<in> carrier_mat d d"
        using fE_car by blast
    qed (use ps_valid r_lt c_lt in auto)
    show ?thesis using pc_entry phi_pc by simp
  qed
  also have "\<dots> = (\<Sum>p \<in> set (mat_unit_pairs n). ?term p)"
    using mat_unit_pairs_distinct
    by (rule sum_list_distinct_conv_sum_set)
  also have "\<dots> = (\<Sum>p \<in> {0..<n} \<times> {0..<n}. ?term p)"
    using mat_unit_pairs_set
    by (intro sum.cong) (auto)
  also have "\<dots> = (\<Sum>i \<in> {0..<n}. \<Sum>j \<in> {0..<n}. ?term (i, j))"
    by (simp add: sum.cartesian_product')
  also have "\<dots> = (\<Sum>i<n. \<Sum>j<n.
                    M $$ (i, j) * \<phi> (mat_unit i j n n) $$ (r, c))"
    by (simp add: atLeast0LessThan)
  finally show ?thesis.
qed

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
  let ?P = "choi_matrix n 1 \<phi>"
  have one_pos: "(0 :: nat) < 1" by simp
  have P_n: "?P \<in> carrier_mat n n"
    by (simp add: choi_matrix_def)
  have P_entry: "\<And>a b. a < n \<Longrightarrow> b < n
                    \<Longrightarrow> ?P $$ (a, b) = \<phi> (mat_unit a b n n) $$ (0, 0)"
    by (simp add: choi_matrix_def)
  have range': "\<And>A. A \<in> carrier_mat n n \<Longrightarrow> \<phi> A \<in> carrier_mat 1 1"
    using range by blast

  (* For arbitrary x \<in> \<complex>\<^sup>n, express \<langle>x | P x\<rangle> as \<phi>(\<rho>\<^sub>x) $$ (0,0)
     where \<rho>\<^sub>x is rank-one psd. *)
  have quad_real_nonneg:
    "\<And>x :: complex Matrix.vec. dim_vec x = n \<Longrightarrow>
       \<langle>x | ?P *\<^sub>v x\<rangle> \<in> \<real> \<and> Re (\<langle>x | ?P *\<^sub>v x\<rangle>) \<ge> 0"
  proof -
    fix x :: "complex Matrix.vec"
    assume xdim: "dim_vec x = n"
    let ?cx = "Matrix.vec n (\<lambda>i. cnj (x $ i))"
    let ?Xx = "outer_sum n [?cx]"
    have cx_dim: "dim_vec ?cx = n" by simp
    have cx_set: "\<forall>v \<in> set [?cx]. dim_vec v = n" by simp
    have Xx_c: "?Xx \<in> carrier_mat n n" by auto
    have Xx_psd: "psd ?Xx"
      using outer_sum_psd[where vs="[?cx]" and k=1 and n=n] cx_set by simp
    have Xx_entry: "\<And>a b. a < n \<Longrightarrow> b < n
                       \<Longrightarrow> ?Xx $$ (a, b) = cnj (x $ a) * x $ b"
    proof -
      fix a b assume a: "a < n" and b: "b < n"
      have "?Xx $$ (a, b)
              = sum_list (map (\<lambda>v. v $ a * cnj (v $ b)) [?cx])"
        using outer_sum_entry_sum_list[OF cx_set a b] .
      also have "\<dots> = ?cx $ a * cnj (?cx $ b)" by simp
      also have "\<dots> = cnj (x $ a) * cnj (cnj (x $ b))"
        using a b by simp
      also have "\<dots> = cnj (x $ a) * x $ b" by simp
      finally show "?Xx $$ (a, b) = cnj (x $ a) * x $ b" .
    qed

    have phiXx_c: "\<phi> ?Xx \<in> carrier_mat 1 1" using range' Xx_c by blast
    have phiXx_psd: "psd (\<phi> ?Xx)"
      using pos Xx_psd Xx_c by (auto simp: positive_map_def)

    (* psd in M\<^sub>1: hermitian gives realness of (0,0) entry *)
    have phiXx_real: "\<phi> ?Xx $$ (0, 0) \<in> \<real>"
    proof -
      have herm: "(\<phi> ?Xx)\<^sup>\<dagger> = \<phi> ?Xx"
        using phiXx_psd by (simp add: psd_def hermitian_def)
      have "(\<phi> ?Xx)\<^sup>\<dagger> $$ (0, 0) = cnj (\<phi> ?Xx $$ (0, 0))"
        using phiXx_c by (simp add: dagger_def)
      hence "cnj (\<phi> ?Xx $$ (0, 0)) = \<phi> ?Xx $$ (0, 0)" using herm by simp
      thus ?thesis using Reals_cnj_iff by metis
    qed

    (* psd: \<langle>(1) | (\<phi> X\<^sub>x) (1)\<rangle> \<ge> 0 gives Re of (0,0) entry \<ge> 0 *)
    have phiXx_nonneg: "Re (\<phi> ?Xx $$ (0, 0)) \<ge> 0"
    proof -
      let ?one = "Matrix.vec 1 (\<lambda>i. (1 :: complex))"
      have one_dim: "dim_vec ?one = 1" by simp
      have one_eq_dr: "dim_vec ?one = dim_row (\<phi> ?Xx)"
        using phiXx_c by simp
      have nn_quad: "Re (\<langle>?one | (\<phi> ?Xx) *\<^sub>v ?one\<rangle>) \<ge> 0"
        using phiXx_psd one_eq_dr by (auto simp: psd_def)

      (* \<langle>?one | M *_v ?one\<rangle> = M $$ (0,0) for M \<in> M\<^sub>1 *)
      have prod_dim: "dim_vec ((\<phi> ?Xx) *\<^sub>v ?one) = 1"
        using phiXx_c by simp
      have prod_entry: "((\<phi> ?Xx) *\<^sub>v ?one) $ 0 = \<phi> ?Xx $$ (0, 0)"
      proof -
        have "((\<phi> ?Xx) *\<^sub>v ?one) $ 0
                = (\<Sum>k<dim_col (\<phi> ?Xx). \<phi> ?Xx $$ (0, k) * ?one $ k)"
          using phiXx_c
          by (simp add: scalar_prod_def atLeast0LessThan)
        also have "\<dots> = (\<Sum>k<1. \<phi> ?Xx $$ (0, k) * ?one $ k)"
          using phiXx_c by simp
        also have "\<dots> = \<phi> ?Xx $$ (0, 0) * ?one $ 0"
          by simp
        also have "\<dots> = \<phi> ?Xx $$ (0, 0)" by simp
        finally show ?thesis .
      qed
      have inner_eq: "\<langle>?one | (\<phi> ?Xx) *\<^sub>v ?one\<rangle> = \<phi> ?Xx $$ (0, 0)"
      proof -
        have "\<langle>?one | (\<phi> ?Xx) *\<^sub>v ?one\<rangle>
                = (\<Sum>i<dim_vec ((\<phi> ?Xx) *\<^sub>v ?one).
                    cnj (?one $ i) * ((\<phi> ?Xx) *\<^sub>v ?one) $ i)"
          by (simp add: inner_prod_def atLeast0LessThan)
        also have "\<dots> = (\<Sum>i<1. cnj (?one $ i) * ((\<phi> ?Xx) *\<^sub>v ?one) $ i)"
          using prod_dim by simp
        also have "\<dots> = cnj (?one $ 0) * ((\<phi> ?Xx) *\<^sub>v ?one) $ 0" by simp
        also have "\<dots> = \<phi> ?Xx $$ (0, 0)" using prod_entry by simp
        finally show ?thesis .
      qed
      show ?thesis using nn_quad inner_eq by simp
    qed

    (* \<langle>x | P *\<^sub>v x\<rangle> equals \<phi>(\<rho>\<^sub>x) $$ (0,0) by linearity over the
       matrix-unit basis. *)
    have inner_lhs:
      "\<langle>x | ?P *\<^sub>v x\<rangle>
         = (\<Sum>i<n. \<Sum>j<n. cnj (x $ i) * x $ j * ?P $$ (i, j))"
    proof -
      have prod_dim: "dim_vec (?P *\<^sub>v x) = n" using P_n by simp
      have "\<langle>x | ?P *\<^sub>v x\<rangle>
              = (\<Sum>i<dim_vec (?P *\<^sub>v x).
                   cnj (x $ i) * (?P *\<^sub>v x) $ i)"
        by (simp add: inner_prod_def atLeast0LessThan)
      also have "\<dots> = (\<Sum>i<n. cnj (x $ i) * (?P *\<^sub>v x) $ i)"
        using prod_dim by simp
      also have "\<dots> = (\<Sum>i<n. cnj (x $ i) *
                          (\<Sum>j<n. ?P $$ (i, j) * x $ j))"
      proof (intro sum.cong refl)
        fix i assume i_in: "i \<in> {..<n}"
        hence i_lt: "i < n" by simp
        have "(?P *\<^sub>v x) $ i
                = (\<Sum>j<dim_col ?P. ?P $$ (i, j) * x $ j)"
          using i_lt P_n xdim
          by (simp add: scalar_prod_def atLeast0LessThan)
        also have "\<dots> = (\<Sum>j<n. ?P $$ (i, j) * x $ j)"
          using P_n by simp
        finally show "cnj (x $ i) * (?P *\<^sub>v x) $ i =
                      cnj (x $ i) * (\<Sum>j<n. ?P $$ (i, j) * x $ j)" by simp
      qed
      also have "\<dots> = (\<Sum>i<n. \<Sum>j<n.
                        cnj (x $ i) * x $ j * ?P $$ (i, j))"
      proof (intro sum.cong refl)
        fix i assume "i \<in> {..<n}"
        have "cnj (x $ i) * (\<Sum>j<n. ?P $$ (i, j) * x $ j)
                = (\<Sum>j<n. cnj (x $ i) * (?P $$ (i, j) * x $ j))"
          by (simp add: sum_distrib_left)
        also have "\<dots> = (\<Sum>j<n. cnj (x $ i) * x $ j * ?P $$ (i, j))"
          by (metis (mono_tags, opaque_lifting) mult.commute mult.left_commute)
        finally show "cnj (x $ i) * (\<Sum>j<n. ?P $$ (i, j) * x $ j)
                       = (\<Sum>j<n. cnj (x $ i) * x $ j * ?P $$ (i, j))" .
      qed
      finally show ?thesis.
    qed

    have quad_eq: "\<langle>x | ?P *\<^sub>v x\<rangle> = \<phi> ?Xx $$ (0, 0)"
    proof -
      have phi_Xx_eq:
        "\<phi> ?Xx $$ (0, 0) =
           (\<Sum>i<n. \<Sum>j<n. ?Xx $$ (i, j) * \<phi> (mat_unit i j n n) $$ (0, 0))"
        using phi_entry_double_sum[OF linear smult range' Xx_c
                                       _ _ npos one_pos] by simp
      have step:
        "(\<Sum>i<n. \<Sum>j<n. cnj (x $ i) * x $ j * ?P $$ (i, j))
         = (\<Sum>i<n. \<Sum>j<n. ?Xx $$ (i, j) * \<phi> (mat_unit i j n n) $$ (0, 0))"
        using P_entry Xx_entry by (intro sum.cong refl, auto)        
      show ?thesis using inner_lhs phi_Xx_eq step by simp
    qed

    show "\<langle>x | ?P *\<^sub>v x\<rangle> \<in> \<real> \<and> Re (\<langle>x | ?P *\<^sub>v x\<rangle>) \<ge> 0"
      using quad_eq phiXx_real phiXx_nonneg by simp
  qed

  have psd_choi: "psd ?P"
  proof -
    have herm: "hermitian ?P"
    proof -
      have "\<forall>x :: complex Matrix.vec. dim_vec x = n
              \<longrightarrow> \<langle>x | ?P *\<^sub>v x\<rangle> \<in> \<real>"
        using quad_real_nonneg by blast
      thus ?thesis
        using P_n hermitian_iff_real_quad_form by metis
    qed
    have nonneg:
      "\<forall>x :: complex Matrix.vec. dim_vec x = dim_row ?P
         \<longrightarrow> Re (\<langle>x | ?P *\<^sub>v x\<rangle>) \<ge> 0"
    proof (intro allI impI)
      fix x :: "complex Matrix.vec"
      assume "dim_vec x = dim_row ?P"
      hence "dim_vec x = n" using P_n by simp
      thus "Re (\<langle>x | ?P *\<^sub>v x\<rangle>) \<ge> 0"
        using quad_real_nonneg by blast
    qed
    show ?thesis unfolding psd_def using herm nonneg P_n by simp
  qed

  show "completely_positive n 1 \<phi>"
    using choi_theorem[OF linear smult range npos one_pos] psd_choi by simp
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

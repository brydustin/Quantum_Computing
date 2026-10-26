(*  Title:   Day18_CP_Maps.thy
    Author:  Dustin Bryant, after Vern Paulsen's lecture of 7 October 2011 (Day 18)
*)

theory Day18_CP_Maps
  imports Day17_Quantum_Noise
begin

section \<open>Day 18 (7 October 2011): the theory of completely positive maps\<close>

text \<open>\begin{notesprop}
Every $X\in M_n$ is $X=(P_1-P_2)+i(P_3-P_4)$ with $P_i\ge0$: $\operatorname{span}(M_n^+)=M_n$.
\end{notesprop}
(Write $X=H+iK$ with $H,K$ Hermitian and split each spectral decomposition into its
non-negative and negative eigenvalues.)
\begin{notesdef}
A linear $\Phi:M_n\to M_d$ is \emph{positive} if $P\ge0$ implies $\Phi(P)\ge0$; it is
\emph{$p$-positive} if $\Phi^{(p)}:M_p(M_n)\to M_p(M_d)$, $(X_{ij})\mapsto(\Phi(X_{ij}))$, is
positive, and \emph{completely positive} if it is $p$-positive for every $p$.
\end{notesdef}
\begin{notesprop}
A linear $\Phi:M_n\to M_d$ maps density matrices to density matrices iff it is positive and
trace preserving.
\end{notesprop}
Example (notes): the transpose $\Phi(A)=A^t$ on $M_2$ is positive but not $2$-positive, since
$\Phi^{(2)}$ sends the positive matrix $(E_{ij})_{i,j}$ to a matrix of determinant $-1$.  The
decomposition into positives is formalised below; the proposition is
\<open>density_preserving_iff_positive_tp\<close> and the example \<open>transpose_not_2_positive\<close>, both in
\<open>Day18_Positive_Maps\<close>.\<close>

lemma diag_mat_of_real_hermitian:
  "((diag_mat_of_real D)\<^sup>\<dagger>) = diag_mat_of_real D"
proof (rule eq_matI)
  show "dim_row ((diag_mat_of_real D)\<^sup>\<dagger>) = dim_row (diag_mat_of_real D)"
    by simp
  show "dim_col ((diag_mat_of_real D)\<^sup>\<dagger>) = dim_col (diag_mat_of_real D)"
    by simp
next
  fix i j
  assume ij: "i < dim_row (diag_mat_of_real D)"
             "j < dim_col (diag_mat_of_real D)"
  hence iln: "i < length D" and jln: "j < length D" by simp_all
  have "(diag_mat_of_real D)\<^sup>\<dagger> $$ (i,j) = cnj (diag_mat_of_real D $$ (j,i))"
    using iln jln by (simp add: dagger_def)
  also have "\<dots> = (if i = j then cnj (of_real (D ! i)) else 0)"
    using iln jln by auto
  also have "\<dots> = (if i = j then of_real (D ! i) else 0)"
    by simp
  also have "\<dots> = diag_mat_of_real D $$ (i,j)"
    using iln jln by auto
  finally show "(diag_mat_of_real D)\<^sup>\<dagger> $$ (i,j) = diag_mat_of_real D $$ (i,j)".
qed

lemma hermitian_decomp_psd:
  fixes H :: "complex Matrix.mat"
  assumes sq: "H \<in> carrier_mat n n"
      and herm: "hermitian H"
  shows "\<exists>P1 P2 :: complex Matrix.mat.
         P1 \<in> carrier_mat n n \<and> P2 \<in> carrier_mat n n \<and>
         psd P1 \<and> psd P2 \<and>
         H = P1 - P2"
proof -
  (* Spectral decomp: H = U D (U\<^sup>\<dagger>), D real diagonal.  Split D into D+ (\<lambda>i \<ge> 0)
     and D- (-\<lambda>i for \<lambda>i < 0).  Then P1 = U D+ (U\<^sup>\<dagger>), P2 = U D- (U\<^sup>\<dagger>). *)
  obtain U D where Uc: "U \<in> carrier_mat n n" and UU: "unitary U"
    and Dlen: "length D = n"
    and spec: "(U\<^sup>\<dagger>) * H * U = diag_mat_of_real D"
    using hermitian_spectral_decomp[OF sq herm] by blast
  let ?Dpos = "map (\<lambda>x. max x 0) D"
  let ?Dneg = "map (\<lambda>x. max (- x) 0) D"
  let ?P1 = "U * diag_mat_of_real ?Dpos * (U\<^sup>\<dagger>)"
  let ?P2 = "U * diag_mat_of_real ?Dneg * (U\<^sup>\<dagger>)"
  have Udag: "(U\<^sup>\<dagger>) \<in> carrier_mat n n"
    using Uc by (rule dagger_carrier)
  have Dpos_len: "length ?Dpos = n" using Dlen by simp
  have Dneg_len: "length ?Dneg = n" using Dlen by simp
  have c1: "?P1 \<in> carrier_mat n n"
    using Uc Udag Dpos_len by auto
  have c2: "?P2 \<in> carrier_mat n n"
    using Uc Udag Dneg_len by auto

  have Dpos_nn: "\<And>i. i < n \<Longrightarrow> 0 \<le> ?Dpos ! i"
    using Dlen by simp
  have Dneg_nn: "\<And>i. i < n \<Longrightarrow> 0 \<le> ?Dneg ! i"
    using Dlen by simp
  have p1: "psd ?P1"
    using psd_U_diag_Udag[OF Uc Dpos_len Dpos_nn].
  have p2: "psd ?P2"
    using psd_U_diag_Udag[OF Uc Dneg_len Dneg_nn].

  (* H = U * diag D * U\<^sup>\<dagger> *)
  have UdagU: "(U\<^sup>\<dagger>) * U = 1\<^sub>m n" using Uc UU unfolding unitary_def by auto
  have UUdag: "U * (U\<^sup>\<dagger>) = 1\<^sub>m n" using Uc UU unfolding unitary_def by auto
  have D_c: "diag_mat_of_real D \<in> carrier_mat n n"
    using Dlen diag_mat_of_real_carrier by metis
  have H_eq: "H = U * diag_mat_of_real D * (U\<^sup>\<dagger>)"
  proof -
    have "U * diag_mat_of_real D * (U\<^sup>\<dagger>) = U * ((U\<^sup>\<dagger>) * H * U) * (U\<^sup>\<dagger>)"
      using spec by simp
    also have "\<dots> = (U * (U\<^sup>\<dagger>)) * H * (U * (U\<^sup>\<dagger>))"
      using Uc Udag sq
      by (smt (verit, ccfv_SIG) assoc_mult_mat carrier_mat_triv mult_carrier_mat)
    also have "\<dots> = 1\<^sub>m n * H * 1\<^sub>m n" using UUdag by simp
    also have "\<dots> = H" using sq by simp
    finally show ?thesis by simp
  qed

  (* diag_mat_of_real D = diag ?Dpos - diag ?Dneg *)
  have diag_split: "diag_mat_of_real D
                  = diag_mat_of_real ?Dpos - diag_mat_of_real ?Dneg"
  proof (rule eq_matI)
    show "dim_row (diag_mat_of_real D)
        = dim_row (diag_mat_of_real ?Dpos - diag_mat_of_real ?Dneg)"
      using Dpos_len Dneg_len Dlen by simp
    show "dim_col (diag_mat_of_real D)
        = dim_col (diag_mat_of_real ?Dpos - diag_mat_of_real ?Dneg)"
      using Dpos_len Dneg_len Dlen by simp
  next
    fix i j
    assume "i < dim_row (diag_mat_of_real ?Dpos - diag_mat_of_real ?Dneg)"
           "j < dim_col (diag_mat_of_real ?Dpos - diag_mat_of_real ?Dneg)"
    hence iln: "i < n" and jln: "j < n"
      using Dpos_len Dneg_len by auto
    have iD: "i < length D" and jD: "j < length D"
      using iln jln Dlen by auto
    have iDp: "i < length ?Dpos" and jDp: "j < length ?Dpos"
      using iln jln Dpos_len by auto
    have iDn: "i < length ?Dneg" and jDn: "j < length ?Dneg"
      using iln jln Dneg_len by auto
    have rhs_entry:
      "(diag_mat_of_real ?Dpos - diag_mat_of_real ?Dneg) $$ (i,j)
       = diag_mat_of_real ?Dpos $$ (i,j) - diag_mat_of_real ?Dneg $$ (i,j)"
      using iDp jDp by simp
    show "diag_mat_of_real D $$ (i,j)
        = (diag_mat_of_real ?Dpos - diag_mat_of_real ?Dneg) $$ (i,j)"
    proof (cases "i = j")
      case True
      have lhs_val: "diag_mat_of_real D $$ (i,j) = of_real (D ! i)"
        using True iD by simp
      have p_val: "diag_mat_of_real ?Dpos $$ (i,j) = of_real (max (D ! i) 0)"
        using True iDp Dlen by simp
      have n_val: "diag_mat_of_real ?Dneg $$ (i,j) = of_real (max (- (D ! i)) 0)"
        using True iDn Dlen by simp
      have real_split: "(D ! i) = max (D ! i) 0 - max (- (D ! i)) 0"
        by linarith
      have of_real_split:
        "(of_real (D ! i) :: complex)
         = of_real (max (D ! i) 0) - of_real (max (- (D ! i)) 0)"
        using real_split by (metis of_real_diff)
      show ?thesis
        using lhs_val p_val n_val rhs_entry of_real_split by simp
    next
      case False
      have lhs0: "diag_mat_of_real D $$ (i,j) = 0" using iD jD False by simp
      have p0: "diag_mat_of_real ?Dpos $$ (i,j) = 0"
        using iDp jDp False by simp
      have n0: "diag_mat_of_real ?Dneg $$ (i,j) = 0"
        using iDn jDn False by simp
      show ?thesis using lhs0 p0 n0 rhs_entry by simp
    qed
  qed

  have Dp_c: "diag_mat_of_real ?Dpos \<in> carrier_mat n n"
    using Dpos_len diag_mat_of_real_carrier by metis
  have Dn_c: "diag_mat_of_real ?Dneg \<in> carrier_mat n n"
    using Dneg_len diag_mat_of_real_carrier by metis
  have UDp_c: "U * diag_mat_of_real ?Dpos \<in> carrier_mat n n"
    using Uc Dp_c by (intro mult_carrier_mat) auto
  have UDn_c: "U * diag_mat_of_real ?Dneg \<in> carrier_mat n n"
    using Uc Dn_c by (intro mult_carrier_mat) auto

  have eq: "H = ?P1 - ?P2"
  proof -
    have "H = U * diag_mat_of_real D * (U\<^sup>\<dagger>)" using H_eq .
    also have "\<dots> = U * (diag_mat_of_real ?Dpos - diag_mat_of_real ?Dneg) * (U\<^sup>\<dagger>)"
      using diag_split by simp
    also have "\<dots> = (U * diag_mat_of_real ?Dpos - U * diag_mat_of_real ?Dneg) * (U\<^sup>\<dagger>)"
      using Uc Dp_c Dn_c by (simp add: mult_minus_distrib_mat)
    also have "\<dots> = U * diag_mat_of_real ?Dpos * (U\<^sup>\<dagger>)
                  - U * diag_mat_of_real ?Dneg * (U\<^sup>\<dagger>)"
      using UDp_c UDn_c Udag by (simp add: minus_mult_distrib_mat)
    finally show ?thesis .
  qed

  show ?thesis using c1 c2 p1 p2 eq by blast
qed


lemma matrix_decomp_psd:
  fixes X :: "complex Matrix.mat"
  assumes sq: "X \<in> carrier_mat n n"
  shows "\<exists>P1 P2 P3 P4 :: complex Matrix.mat.
         (\<forall>i \<in> {0..3}. [P1,P2,P3,P4] ! i \<in> carrier_mat n n \<and> psd ([P1,P2,P3,P4] ! i)) \<and>
         X = (P1 - P2) + \<i> \<cdot>\<^sub>m (P3 - P4)"
proof -
  let ?Hr = "(((1/2) :: complex) \<cdot>\<^sub>m (X + (X\<^sup>\<dagger>)))"
  let ?Hi = "(((1 / (2 * \<i>)) :: complex) \<cdot>\<^sub>m (X - (X\<^sup>\<dagger>)))"

  have Hr_carrier: "?Hr \<in> carrier_mat n n"
    using sq by auto
  have Hi_carrier: "?Hi \<in> carrier_mat n n"
    using sq by auto

  have Hr_herm: "hermitian ?Hr"
  proof -
    have "((?Hr)\<^sup>\<dagger>) = ?Hr"
    proof (rule eq_matI)
      show "dim_row ((?Hr)\<^sup>\<dagger>) = dim_row ?Hr"
        using Hr_carrier sq by (simp add: dagger_def)
      show "dim_col ((?Hr)\<^sup>\<dagger>) = dim_col ?Hr"
        using Hr_carrier sq by (simp add: dagger_def)
    next
      fix i j
      assume "i < dim_row ?Hr" "j < dim_col ?Hr"
      hence iln: "i < n" and jln: "j < n" using Hr_carrier by auto
      have hr_ji: "?Hr $$ (j,i) = (1/2) * (X $$ (j,i) + cnj (X $$ (i,j)))"
        using iln jln sq by (simp add: dagger_def)
      have hr_ij: "?Hr $$ (i,j) = (1/2) * (X $$ (i,j) + cnj (X $$ (j,i)))"
        using iln jln sq by (simp add: dagger_def)
      have d_eval: "(?Hr)\<^sup>\<dagger> $$ (i,j) = cnj (?Hr $$ (j,i))"
        using iln jln Hr_carrier sq by (simp add: dagger_def)
      have d_val: "(?Hr)\<^sup>\<dagger> $$ (i,j)
                 = (1/2) * (cnj (X $$ (j,i)) + X $$ (i,j))"
        using d_eval hr_ji by simp
      have "(?Hr)\<^sup>\<dagger> $$ (i,j)
            = (1/2) * (cnj (X $$ (j,i)) + X $$ (i,j))" using d_val.
      also have "\<dots> = (1/2) * (X $$ (i,j) + cnj (X $$ (j,i)))"
        by (simp add: add.commute)
      also have "\<dots> = ?Hr $$ (i,j)" using hr_ij[symmetric].
      finally show "(?Hr)\<^sup>\<dagger> $$ (i,j) = ?Hr $$ (i,j)".
    qed
    thus ?thesis by (simp add: hermitian_def)
  qed

  have Hi_herm: "hermitian ?Hi"
  proof -
    have "((?Hi)\<^sup>\<dagger>) = ?Hi"
    proof (rule eq_matI)
      show "dim_row ((?Hi)\<^sup>\<dagger>) = dim_row ?Hi"
        using Hi_carrier sq by (simp add: dagger_def)
      show "dim_col ((?Hi)\<^sup>\<dagger>) = dim_col ?Hi"
        using Hi_carrier sq by (simp add: dagger_def)
    next
      fix i j
      assume "i < dim_row ?Hi" "j < dim_col ?Hi"
      hence iln: "i < n" and jln: "j < n" using Hi_carrier by auto
      have hi_ji: "?Hi $$ (j,i) = (1 / (2 * \<i>)) * (X $$ (j,i) - cnj (X $$ (i,j)))"
        using iln jln sq by (simp add: dagger_def)
      have hi_ij: "?Hi $$ (i,j) = (1 / (2 * \<i>)) * (X $$ (i,j) - cnj (X $$ (j,i)))"
        using iln jln sq by (simp add: dagger_def)
      have d_eval: "(?Hi)\<^sup>\<dagger> $$ (i,j) = cnj (?Hi $$ (j,i))"
        using iln jln Hi_carrier sq by (simp add: dagger_def)
      have cnj_coef: "cnj (1 / (2 * \<i>) :: complex) = - (1 / (2 * \<i>))"
        by (simp add: complex_eq_iff)
      have "(?Hi)\<^sup>\<dagger> $$ (i,j) = cnj (?Hi $$ (j,i))" using d_eval .
      also have "\<dots> = cnj ((1 / (2 * \<i>)) * (X $$ (j,i) - cnj (X $$ (i,j))))"
        using hi_ji by simp
      also have "\<dots> = cnj (1 / (2 * \<i>)) * cnj (X $$ (j,i) - cnj (X $$ (i,j)))"
        by simp
      also have "\<dots> = (- (1 / (2 * \<i>))) * (cnj (X $$ (j,i)) - X $$ (i,j))"
        using cnj_coef by simp
      also have "\<dots> = (1 / (2 * \<i>)) * (X $$ (i,j) - cnj (X $$ (j,i)))"
        by (simp add: field_simps)
      also have "\<dots> = ?Hi $$ (i,j)" using hi_ij[symmetric].
      finally show "(?Hi)\<^sup>\<dagger> $$ (i,j) = ?Hi $$ (i,j)".
    qed
    thus ?thesis by (simp add: hermitian_def)
  qed

  obtain A B :: "complex Matrix.mat"
    where A_car: "A \<in> carrier_mat n n"
      and B_car: "B \<in> carrier_mat n n"
      and A_psd: "psd A"
      and B_psd: "psd B"
      and Hr_decomp: "?Hr = A - B"
    using hermitian_decomp_psd[OF Hr_carrier Hr_herm] by blast

  obtain C D :: "complex Matrix.mat"
    where C_car: "C \<in> carrier_mat n n"
      and D_car: "D \<in> carrier_mat n n"
      and C_psd: "psd C"
      and D_psd: "psd D"
      and Hi_decomp: "?Hi = C - D"
    using hermitian_decomp_psd[OF Hi_carrier Hi_herm] by blast

  have X_split: "X = ?Hr + (\<i> \<cdot>\<^sub>m ?Hi)"
  proof (rule eq_matI)
    show "dim_row X = dim_row (?Hr + (\<i> \<cdot>\<^sub>m ?Hi))"
      using sq Hr_carrier Hi_carrier by simp
    show "dim_col X = dim_col (?Hr + (\<i> \<cdot>\<^sub>m ?Hi))"
      using sq Hr_carrier Hi_carrier by simp
  next
    fix i j
    assume "i < dim_row (?Hr + (\<i> \<cdot>\<^sub>m ?Hi))"
           "j < dim_col (?Hr + (\<i> \<cdot>\<^sub>m ?Hi))"
    hence iln: "i < n" and jln: "j < n" using Hr_carrier Hi_carrier by auto
    have hr_at: "?Hr $$ (i,j) = (1/2) * (X $$ (i,j) + cnj (X $$ (j,i)))"
      using iln jln sq by (simp add: dagger_def)
    have hi_at: "?Hi $$ (i,j)
                 = (1 / (2 * \<i>)) * (X $$ (i,j) - cnj (X $$ (j,i)))"
      using iln jln sq by (simp add: dagger_def)
    have iHi_c: "\<i> \<cdot>\<^sub>m ?Hi \<in> carrier_mat n n"
      using Hi_carrier by simp
    have Hi_dim_row: "dim_row ?Hi = n" using Hi_carrier by auto
    have Hi_dim_col: "dim_col ?Hi = n" using Hi_carrier by auto
    have iHi_at: "(\<i> \<cdot>\<^sub>m ?Hi) $$ (i,j) = \<i> * ?Hi $$ (i,j)"
      using iln jln Hi_dim_row Hi_dim_col index_smult_mat(1) by metis
    have Hr_dim_row: "dim_row ?Hr = n" using Hr_carrier by auto
    have Hr_dim_col: "dim_col ?Hr = n" using Hr_carrier by auto
    have iHi_dim_row: "dim_row (\<i> \<cdot>\<^sub>m ?Hi) = n" using iHi_c by auto
    have iHi_dim_col: "dim_col (\<i> \<cdot>\<^sub>m ?Hi) = n" using iHi_c by auto
    have add_at: "(?Hr + (\<i> \<cdot>\<^sub>m ?Hi)) $$ (i,j)
                = ?Hr $$ (i,j) + (\<i> \<cdot>\<^sub>m ?Hi) $$ (i,j)"
      using iln jln Hr_dim_row Hr_dim_col iHi_dim_row iHi_dim_col index_add_mat(1)
      by metis
    have sum_at: "(?Hr + (\<i> \<cdot>\<^sub>m ?Hi)) $$ (i,j)
                = ?Hr $$ (i,j) + \<i> * ?Hi $$ (i,j)"
      using add_at iHi_at by simp
    have arith:
      "(1/2 :: complex) * (X $$ (i,j) + cnj (X $$ (j,i)))
       + \<i> * ((1 / (2 * \<i>)) * (X $$ (i,j) - cnj (X $$ (j,i))))
       = X $$ (i,j)"
      by (simp add: field_simps)
    show "X $$ (i,j) = (?Hr + (\<i> \<cdot>\<^sub>m ?Hi)) $$ (i,j)"
      using sum_at hr_at hi_at arith by simp
  qed

  have X_decomp: "X = (A - B) + \<i> \<cdot>\<^sub>m (C - D)"
    using X_split Hr_decomp Hi_decomp by simp

  have list_cond:
    "\<forall>i \<in> {0..3}. [A,B,C,D] ! i \<in> carrier_mat n n \<and> psd ([A,B,C,D] ! i)"
  proof clarify
    fix i :: nat
    assume i: "i \<in> {0..3}"
    then have i_cases: "i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3"
      by auto
    then show "[A,B,C,D] ! i \<in> carrier_mat n n \<and> psd ([A,B,C,D] ! i)"
    proof
      assume "i = 0"
      then show ?thesis using A_car A_psd by simp
    next
      assume "i = 1 \<or> i = 2 \<or> i = 3"
      then show "[A,B,C,D] ! i \<in> carrier_mat n n \<and> psd ([A,B,C,D] ! i)"
      proof -
        assume "i = 1 \<or> i = 2 \<or> i = 3"
        then show ?thesis
        proof
          assume "i = 1"
          then show ?thesis using B_car B_psd by simp
        next
          assume "i = 2 \<or> i = 3"
          then show ?thesis
          proof -
            assume "i = 2 \<or> i = 3"
            then show ?thesis
            proof
              assume "i = 2"
              then show ?thesis using C_car C_psd by simp
            next
              assume "i = 3"
              then show ?thesis using D_car D_psd by auto
            qed
          qed
        qed
      qed
    qed
  qed
  show ?thesis
    using list_cond X_decomp by blast
qed

end

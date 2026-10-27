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
\<open>density_preserving_iff_positive_tp\<close> and the example \<open>transpose_not_2_positive\<close>, both
below.\<close>

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

definition choi_seed :: "nat \<Rightarrow> complex Matrix.mat" where
  "choi_seed n \<equiv>
     Matrix.mat (n*n) (n*n)
       (\<lambda>(r,c). mat_unit (r div n) (c div n) n n $$ (r mod n, c mod n))"

lemma choi_seed_carrier [simp]:
  "choi_seed n \<in> carrier_mat (n*n) (n*n)"
  by (simp add: choi_seed_def)

subsection \<open>Densities to densities iff positive and trace-preserving (D17-4, D18-2)\<close>

theorem density_preserving_iff_positive_tp:
  fixes \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes linear: "\<And>A B. A \<in> carrier_mat n n \<Longrightarrow> B \<in> carrier_mat n n \<Longrightarrow>
                   \<Phi> (A + B) = \<Phi> A + \<Phi> B"
      and smult:  "\<And>c A. A \<in> carrier_mat n n \<Longrightarrow> \<Phi> (c \<cdot>\<^sub>m A) = c \<cdot>\<^sub>m \<Phi> A"
      and range:  "\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A \<in> carrier_mat d d"
      and npos: "0 < n"
  shows "(\<forall>\<rho>. density_matrix n \<rho> \<longrightarrow> density_matrix d (\<Phi> \<rho>)) \<longleftrightarrow>
         (positive_map n d \<Phi> \<and> trace_preserving n \<Phi>)"
proof
  assume H: "positive_map n d \<Phi> \<and> trace_preserving n \<Phi>"
  show "\<forall>\<rho>. density_matrix n \<rho> \<longrightarrow> density_matrix d (\<Phi> \<rho>)"
  proof (intro allI impI)
    fix \<rho> assume "density_matrix n \<rho>"
    hence \<rho>c: "\<rho> \<in> carrier_mat n n" and \<rho>p: "psd \<rho>" and \<rho>t: "Tr \<rho> = 1"
      by (auto simp: density_matrix_def)
    have "\<Phi> \<rho> \<in> carrier_mat d d" using range \<rho>c by blast
    moreover have "psd (\<Phi> \<rho>)" using H \<rho>c \<rho>p by (auto simp: positive_map_def)
    moreover have "Tr (\<Phi> \<rho>) = 1" using H \<rho>c \<rho>t by (auto simp: trace_preserving_def)
    ultimately show "density_matrix d (\<Phi> \<rho>)" by (simp add: density_matrix_def)
  qed
next
  assume H: "\<forall>\<rho>. density_matrix n \<rho> \<longrightarrow> density_matrix d (\<Phi> \<rho>)"
  have Phi0: "\<Phi> (0\<^sub>m n n) = 0\<^sub>m d d"
  proof -
    have z: "(0::complex) \<cdot>\<^sub>m (0\<^sub>m n n) = (0\<^sub>m n n :: complex Matrix.mat)"
      by (rule zero_smult_mat_carrier) simp
    have "\<Phi> (0\<^sub>m n n) = \<Phi> (0 \<cdot>\<^sub>m (0\<^sub>m n n))" using z by simp
    also have "\<dots> = 0 \<cdot>\<^sub>m \<Phi> (0\<^sub>m n n)" by (rule smult) simp
    also have "\<dots> = 0\<^sub>m d d" using range by (intro zero_smult_mat_carrier) simp
    finally show ?thesis .
  qed
  \<comment> \<open>The key scaling argument: for $P\ge0$ with $c=\Tr P>0$, $\rho=P/c$ is a density matrix.\<close>
  have key: "\<And>P. P \<in> carrier_mat n n \<Longrightarrow> psd P \<Longrightarrow> psd (\<Phi> P) \<and> Tr (\<Phi> P) = Tr P"
  proof -
    fix P :: "complex Matrix.mat" assume Pc: "P \<in> carrier_mat n n" and Pp: "psd P"
    define c where "c = Re (Tr P)"
    have c_nn: "0 \<le> c" unfolding c_def using Tr_psd_Re_nonneg[OF Pp Pc] .
    have TrP: "Tr P = complex_of_real c"
      unfolding c_def using Tr_hermitian_real[OF Pc psd_hermitian[OF Pp]] .
    have PhiPc: "\<Phi> P \<in> carrier_mat d d" using range Pc by blast
    show "psd (\<Phi> P) \<and> Tr (\<Phi> P) = Tr P"
    proof (cases "c = 0")
      case True
      hence "Tr P = 0" using TrP by simp
      hence "P = 0\<^sub>m n n" using psd_Tr_zero_imp_zero[OF Pc Pp] by simp
      thus ?thesis using Phi0 True TrP by simp
    next
      case False
      hence cpos: "0 < c" using c_nn by simp
      define \<rho> where "\<rho> = complex_of_real (1 / c) \<cdot>\<^sub>m P"
      have \<rho>c: "\<rho> \<in> carrier_mat n n" unfolding \<rho>_def using Pc by simp
      have \<rho>p: "psd \<rho>" unfolding \<rho>_def
        using psd_smult_nonneg[OF _ Pp Pc, of "1 / c"] cpos by simp
      have \<rho>t: "Tr \<rho> = 1" unfolding \<rho>_def using Tr_smult TrP cpos by simp
      have dens: "density_matrix n \<rho>" using \<rho>c \<rho>p \<rho>t by (simp add: density_matrix_def)
      hence d\<rho>: "density_matrix d (\<Phi> \<rho>)" using H by blast
      have cc: "complex_of_real c * complex_of_real (1 / c) = 1"
        using cpos[THEN less_imp_neq, THEN not_sym] by (simp flip: of_real_mult)
      have P_eq: "P = complex_of_real c \<cdot>\<^sub>m \<rho>"
        unfolding \<rho>_def smult_smult_mat cc by (rule eq_matI) auto
      have PhiP: "\<Phi> P = complex_of_real c \<cdot>\<^sub>m \<Phi> \<rho>"
        using P_eq smult[OF \<rho>c] by simp
      have "psd (\<Phi> P)" unfolding PhiP
        using d\<rho> c_nn by (intro psd_smult_nonneg) (auto simp: density_matrix_def)
      moreover have "Tr (\<Phi> P) = Tr P"
        unfolding PhiP Tr_smult using d\<rho> TrP by (simp add: density_matrix_def)
      ultimately show ?thesis by simp
    qed
  qed
  have pos: "positive_map n d \<Phi>"
    unfolding positive_map_def using range key by blast
  have Phi_minus: "\<And>A B. A \<in> carrier_mat n n \<Longrightarrow> B \<in> carrier_mat n n \<Longrightarrow>
                     \<Phi> (A - B) = \<Phi> A - \<Phi> B"
  proof -
    fix A B :: "complex Matrix.mat" assume Ac: "A \<in> carrier_mat n n" and Bc: "B \<in> carrier_mat n n"
    have AB: "A - B = A + (-1) \<cdot>\<^sub>m B" using Ac Bc by (intro eq_matI) auto
    have PA: "\<Phi> A \<in> carrier_mat d d" and PB: "\<Phi> B \<in> carrier_mat d d" using range Ac Bc by auto
    have "\<Phi> (A - B) = \<Phi> A + \<Phi> ((-1) \<cdot>\<^sub>m B)"
      unfolding AB using linear[OF Ac, of "(-1) \<cdot>\<^sub>m B"] Bc by simp
    also have "\<dots> = \<Phi> A + (-1) \<cdot>\<^sub>m \<Phi> B" using smult[OF Bc] by simp
    also have "\<dots> = \<Phi> A - \<Phi> B" using PA PB by (intro eq_matI) auto
    finally show "\<Phi> (A - B) = \<Phi> A - \<Phi> B" .
  qed
  have tp: "trace_preserving n \<Phi>"
  proof (unfold trace_preserving_def, intro allI impI)
    fix X :: "complex Matrix.mat" assume Xc: "X \<in> carrier_mat n n"
    obtain P1 P2 P3 P4 :: "complex Matrix.mat"
      where Ps: "\<forall>i \<in> {0..3}. [P1,P2,P3,P4] ! i \<in> carrier_mat n n \<and> psd ([P1,P2,P3,P4] ! i)"
        and Xd: "X = (P1 - P2) + \<i> \<cdot>\<^sub>m (P3 - P4)"
      using matrix_decomp_psd[OF Xc] by blast
    have P1: "P1 \<in> carrier_mat n n \<and> psd P1" using Ps[rule_format, of 0] by simp
    have P2: "P2 \<in> carrier_mat n n \<and> psd P2" using Ps[rule_format, of 1] by simp
    have P3: "P3 \<in> carrier_mat n n \<and> psd P3" using Ps[rule_format, of 2] by simp
    have P4: "P4 \<in> carrier_mat n n \<and> psd P4" using Ps[rule_format, of 3] by simp
    have T1: "Tr (\<Phi> P1) = Tr P1" and T2: "Tr (\<Phi> P2) = Tr P2"
      and T3: "Tr (\<Phi> P3) = Tr P3" and T4: "Tr (\<Phi> P4) = Tr P4"
      using key P1 P2 P3 P4 by blast+
    have c12: "P1 - P2 \<in> carrier_mat n n" and c34: "P3 - P4 \<in> carrier_mat n n"
      using P1 P2 P3 P4 by auto
    have "\<Phi> X = \<Phi> (P1 - P2) + \<Phi> (\<i> \<cdot>\<^sub>m (P3 - P4))"
      unfolding Xd using linear[OF c12] c34 by simp
    also have "\<dots> = (\<Phi> P1 - \<Phi> P2) + \<i> \<cdot>\<^sub>m (\<Phi> P3 - \<Phi> P4)"
      using smult[OF c34] Phi_minus P1 P2 P3 P4 by simp
    finally have PhiX: "\<Phi> X = (\<Phi> P1 - \<Phi> P2) + \<i> \<cdot>\<^sub>m (\<Phi> P3 - \<Phi> P4)" .
    have dP1: "\<Phi> P1 \<in> carrier_mat d d" and dP2: "\<Phi> P2 \<in> carrier_mat d d"
      and dP3: "\<Phi> P3 \<in> carrier_mat d d" and dP4: "\<Phi> P4 \<in> carrier_mat d d"
      using range P1 P2 P3 P4 by blast+
    have TP12: "Tr (\<Phi> P1 - \<Phi> P2) = Tr (\<Phi> P1) - Tr (\<Phi> P2)"
      using dP1 dP2 by (intro Tr_diff) (auto simp: carrier_matD)
    have TP34: "Tr (\<Phi> P3 - \<Phi> P4) = Tr (\<Phi> P3) - Tr (\<Phi> P4)"
      using dP3 dP4 by (intro Tr_diff) (auto simp: carrier_matD)
    have T12: "Tr (P1 - P2) = Tr P1 - Tr P2" using P1 P2 by (intro Tr_diff) (auto simp: carrier_matD)
    have T34: "Tr (P3 - P4) = Tr P3 - Tr P4" using P3 P4 by (intro Tr_diff) (auto simp: carrier_matD)
    have "Tr (\<Phi> X) = Tr (\<Phi> P1 - \<Phi> P2) + Tr (\<i> \<cdot>\<^sub>m (\<Phi> P3 - \<Phi> P4))"
      unfolding PhiX using dP1 dP2 dP3 dP4 by (intro Tr_add) (auto simp: carrier_matD)
    also have "\<dots> = (Tr P1 - Tr P2) + \<i> * (Tr P3 - Tr P4)"
      unfolding Tr_smult TP12 TP34 T1 T2 T3 T4 ..
    also have "\<dots> = Tr (P1 - P2) + Tr (\<i> \<cdot>\<^sub>m (P3 - P4))" unfolding Tr_smult T12 T34 ..
    also have "\<dots> = Tr X" unfolding Xd using c12 c34 P1 P2 P3 P4 by (intro Tr_add[symmetric]) (auto simp: carrier_matD)
    finally show "Tr (\<Phi> X) = Tr X" .
  qed
  show "positive_map n d \<Phi> \<and> trace_preserving n \<Phi>" using pos tp by simp
qed



subsection \<open>The transpose is positive but not 2-positive (D18-4)\<close>

lemma transpose_positive_map: "positive_map n n (transpose_mat :: complex Matrix.mat \<Rightarrow> complex Matrix.mat)"
proof (unfold positive_map_def, intro conjI allI impI)
  fix A :: "complex Matrix.mat" assume "A \<in> carrier_mat n n"
  thus "transpose_mat A \<in> carrier_mat n n" by simp
next
  fix P :: "complex Matrix.mat" assume Pc: "P \<in> carrier_mat n n" and pos: "psd P"
  have Ph: "P\<^sup>\<dagger> = P" using pos by (simp add: psd_def hermitian_def)
  have dr: "dim_row P = n" and dc: "dim_col P = n" using Pc by auto
  have herm: "hermitian (transpose_mat P)"
  proof (unfold hermitian_def, rule eq_matI)
    fix i j assume i: "i < dim_row (transpose_mat P)" and j: "j < dim_col (transpose_mat P)"
    hence i': "i < n" and j': "j < n" using dr dc by simp_all
    have "(transpose_mat P)\<^sup>\<dagger> $$ (i,j) = cnj (P $$ (i,j))" using i' j' dr dc by (simp add: dagger_def)
    also have "\<dots> = cnj ((P\<^sup>\<dagger>) $$ (i,j))" using Ph by simp
    also have "\<dots> = P $$ (j,i)" using i' j' dr dc by (simp add: dagger_def)
    also have "\<dots> = transpose_mat P $$ (i,j)" using i j by simp
    finally show "(transpose_mat P)\<^sup>\<dagger> $$ (i,j) = transpose_mat P $$ (i,j)" .
  qed (simp_all add: dagger_def dr dc)
  have quad: "\<And>x :: complex Matrix.vec. dim_vec x = n \<Longrightarrow> 0 \<le> Re (\<langle>x | transpose_mat P *\<^sub>v x\<rangle>)"
  proof -
    fix x :: "complex Matrix.vec" assume xd: "dim_vec x = n"
    define cx where "cx = Matrix.vec n (\<lambda>i. cnj (x $ i))"
    have cxd: "dim_vec cx = n" by (simp add: cx_def)
    have "\<langle>x | transpose_mat P *\<^sub>v x\<rangle> =
          (\<Sum>i = 0..<n. cnj (x $ i) * (\<Sum>j = 0..<n. P $$ (j,i) * x $ j))"
      unfolding inner_prod_def using Pc xd
      by (simp add: scalar_prod_def)
    also have "\<dots> = (\<Sum>i = 0..<n. \<Sum>j = 0..<n. cnj (x $ i) * (P $$ (j,i) * x $ j))"
      by (simp add: sum_distrib_left)
    also have "\<dots> = (\<Sum>j = 0..<n. \<Sum>i = 0..<n. cnj (x $ i) * (P $$ (j,i) * x $ j))"
      by (rule sum.swap)
    also have "\<dots> = (\<Sum>j = 0..<n. cnj (cx $ j) * (\<Sum>i = 0..<n. P $$ (j,i) * cx $ i))"
      unfolding cx_def by (simp add: sum_distrib_left algebra_simps)
    also have "\<dots> = \<langle>cx | P *\<^sub>v cx\<rangle>"
      unfolding inner_prod_def using Pc cxd by (simp add: scalar_prod_def)
    finally have "\<langle>x | transpose_mat P *\<^sub>v x\<rangle> = \<langle>cx | P *\<^sub>v cx\<rangle>" .
    moreover have "0 \<le> Re (\<langle>cx | P *\<^sub>v cx\<rangle>)" using pos Pc cxd by (simp add: psd_def)
    ultimately show "0 \<le> Re (\<langle>x | transpose_mat P *\<^sub>v x\<rangle>)" by simp
  qed
  show "psd (transpose_mat P)"
    unfolding psd_def using herm quad Pc by simp
qed

text \<open>The notes' witness: $X=(E_{ij})\in M_2(M_2)$ is positive (it is $|w\rangle\langle w|$ for
$w=e_0\otimes e_0+e_1\otimes e_1$) while $\Phi^{(2)}(X)$ has the eigenvector $(0,1,-1,0)$ with
eigenvalue $-1$ (the notes compute $\det\Phi^{(2)}(X)=-1$ instead).\<close>

lemma choi_seed_2_outer: "choi_seed 2 = outer_sum 4 [Matrix.vec 4 (\<lambda>i. if i = 0 \<or> i = 3 then 1 else 0)]"
proof (rule eq_matI)
  let ?w = "Matrix.vec 4 (\<lambda>i. if i = 0 \<or> i = 3 then (1::complex) else 0)"
  fix i j assume i: "i < dim_row (outer_sum 4 [?w])" and j: "j < dim_col (outer_sum 4 [?w])"
  hence i4: "i < 4" and j4: "j < 4" by simp_all
  have "outer_sum 4 [?w] $$ (i,j) = ?w $ i * cnj (?w $ j)"
    using outer_sum_singleton_index[OF i4 j4] .
  also have "\<dots> = choi_seed 2 $$ (i,j)"
    using i4 j4 by (auto simp: choi_seed_def mat_unit_def dest!: set_4_disj)
  finally show "choi_seed 2 $$ (i,j) = outer_sum 4 [?w] $$ (i,j)" ..
qed (simp_all add: choi_seed_def)

lemma choi_seed_2_psd: "psd (choi_seed 2)"
  unfolding choi_seed_2_outer by (rule outer_sum_psd) simp_all

lemma transpose_not_2_positive:
  "\<not> p_positive 2 2 2 (transpose_mat :: complex Matrix.mat \<Rightarrow> complex Matrix.mat)"
proof
  assume pp: "p_positive 2 2 2 (transpose_mat :: complex Matrix.mat \<Rightarrow> complex Matrix.mat)"
  let ?X = "choi_seed 2"
  let ?Y = "amplification 2 2 2 (transpose_mat :: complex Matrix.mat \<Rightarrow> complex Matrix.mat) ?X"
  have Xc: "?X \<in> carrier_mat (2*2) (2*2)" using choi_seed_carrier[of 2] by simp
  have Ypsd: "psd ?Y" using pp Xc choi_seed_2_psd by (simp add: p_positive_def)
  have Yc: "?Y \<in> carrier_mat 4 4" by (simp add: amplification_def)
  define v :: "complex Matrix.vec" where
    "v = Matrix.vec 4 (\<lambda>i. if i = 1 then 1 else if i = 2 then -1 else 0)"
  have vd: "dim_vec v = 4" by (simp add: v_def)
  have Yent: "\<And>i j :: nat. i < 4 \<Longrightarrow> j < 4 \<Longrightarrow>
      ?Y $$ (i,j) = ?X $$ ((i div 2) * 2 + j mod 2, (j div 2) * 2 + i mod 2)"
  proof -
    fix i j :: nat assume i: "i < 4" and j: "j < 4"
    have "?Y $$ (i,j) = transpose_mat (block_of_mat 2 ?X (i div 2) (j div 2)) $$ (i mod 2, j mod 2)"
      using i j by (simp add: amplification_def)
    also have "\<dots> = block_of_mat 2 ?X (i div 2) (j div 2) $$ (j mod 2, i mod 2)"
      by (simp add: block_of_mat_def)
    also have "\<dots> = ?X $$ ((i div 2) * 2 + j mod 2, (j div 2) * 2 + i mod 2)"
      by (simp add: block_of_mat_def)
    finally show "?Y $$ (i,j) = ?X $$ ((i div 2) * 2 + j mod 2, (j div 2) * 2 + i mod 2)" .
  qed
  have Y11: "?Y $$ (1,1) = 0" using Yent[of 1 1] by (simp add: choi_seed_def mat_unit_def)
  have Y12: "?Y $$ (1,2) = 1" using Yent[of 1 2] by (simp add: choi_seed_def mat_unit_def)
  have Y21: "?Y $$ (2,1) = 1" using Yent[of 2 1] by (simp add: choi_seed_def mat_unit_def)
  have Y22: "?Y $$ (2,2) = 0" using Yent[of 2 2] by (simp add: choi_seed_def mat_unit_def)
  have s4: "{0..<(4::nat)} = {0,1,2,3}" by auto
  have Yv: "\<And>i :: nat. i < 4 \<Longrightarrow> (?Y *\<^sub>v v) $ i = ?Y $$ (i,1) - ?Y $$ (i,2)"
  proof -
    fix i :: nat assume i: "i < 4"
    have "(?Y *\<^sub>v v) $ i = (\<Sum>j = 0..<4. ?Y $$ (i,j) * v $ j)"
      using i Yc vd carrier_matD[OF Yc] by (simp add: scalar_prod_def)
    also have "\<dots> = ?Y $$ (i,1) - ?Y $$ (i,2)"
      unfolding s4 by (simp add: v_def)
    finally show "(?Y *\<^sub>v v) $ i = ?Y $$ (i,1) - ?Y $$ (i,2)" .
  qed
  have "\<langle>v | ?Y *\<^sub>v v\<rangle> = (\<Sum>i = 0..<4. cnj (v $ i) * (?Y *\<^sub>v v) $ i)"
    using inner_prod_sum[of v 4 "?Y *\<^sub>v v"] vd Yc carrier_matD[OF Yc] by simp
  also have "\<dots> = (?Y *\<^sub>v v) $ 1 - (?Y *\<^sub>v v) $ 2"
    unfolding s4 by (simp add: v_def)
  also have "\<dots> = (?Y $$ (1,1) - ?Y $$ (1,2)) - (?Y $$ (2,1) - ?Y $$ (2,2))"
    using Yv[of 1] Yv[of 2] by simp
  also have "\<dots> = -2" unfolding Y11 Y12 Y21 Y22 by simp
  finally have "Re (\<langle>v | ?Y *\<^sub>v v\<rangle>) = -2" by simp
  moreover have "0 \<le> Re (\<langle>v | ?Y *\<^sub>v v\<rangle>)" using Ypsd Yc vd by (simp add: psd_def)
  ultimately show False by simp
qed

corollary transpose_not_completely_positive:
  "\<not> completely_positive 2 2 (transpose_mat :: complex Matrix.mat \<Rightarrow> complex Matrix.mat)"
proof
  assume "completely_positive 2 2 (transpose_mat :: complex Matrix.mat \<Rightarrow> complex Matrix.mat)"
  hence "p_positive 2 2 2 (transpose_mat :: complex Matrix.mat \<Rightarrow> complex Matrix.mat)"
    by (simp add: completely_positive_def)
  thus False using transpose_not_2_positive by simp
qed

end

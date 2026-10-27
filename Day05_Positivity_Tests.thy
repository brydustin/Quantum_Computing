(*  Title:   Day05_Positivity_Tests.thy
    Author:  Dustin Bryant, after Vern Paulsen's lecture of 7 September 2011 (Day 5)
*)

theory Day05_Positivity_Tests
  imports Day04_Hermitian_Matrices
begin

section \<open>Day 5 (7 September 2011): tests for positivity; direct sums and partitioned matrices\<close>

subsection \<open>Practical tests for positivity\<close>

text \<open>Given $P=P^*$, how does one decide whether $P\ge 0$ or $P>0$?  The notes give two
tests.  (1) Sylvester's criterion, in terms of the leading principal submatrices
$P_k=(p_{ij})_{1\le i,j\le k}$ (the upper left $k\times k$ corners):
\begin{notestheorem}[Sylvester's criterion]
Let $P=P^*\in M_n$.  Then $P>0$ if and only if $\det P_k>0$ for $k=1,\dots,n$.
\end{notestheorem}
Each $\det P_k$ is real, as $P_k$ is Hermitian.  The same test with $\ge 0$ does \emph{not}
characterise $P\ge 0$: $\begin{pmatrix}0&0\\0&-1\end{pmatrix}$ has leading minors $0$ and $0$
but is not positive.  For $n=2$ the criterion says
$\begin{pmatrix}a&b\\\bar b&c\end{pmatrix}>0$ iff $a>0$ and $ac-|b|^2>0$.  The notes state it
without proof.  It is not reproved in this development: it is imported from the AFP entry
\emph{Two Hermitian Results} and restated for \<^const>\<open>pd\<close> and \<^const>\<open>hermitian\<close> as
\texttt{pd\_iff\_leading\_minors\_pos} (for $P\in M_n$ Hermitian, \<^term>\<open>pd P\<close> iff
$\det P_k>0$ for all $k\le n$) in the next section, the theory
\texttt{Day05\_Sylvester\_Criterion}.  (2) Cholesky's algorithm:
\begin{notestheorem}
If $P=(p_{ij})$ is $n\times n$ with $P=P^*$, then $P\ge 0$ if and only if
$P-\bigl(\tfrac{p_{i1}p_{1j}}{p_{11}}\bigr)_{ij}\ge 0$.
\end{notestheorem}
The subtracted matrix agrees with $P$ in the first row and column, so the difference is
really an $(n-1)\times(n-1)$ matrix and the test can be repeated; when $P\ge 0$ the
algorithm also writes $P$ as a sum of rank-one matrices.  The formal theorem adds the
hypothesis $p_{11}>0$, which the notes leave implicit (for $p_{11}=0$ the quotient is
undefined).\<close>

theorem cholesky_reduction:
  fixes P :: "complex Matrix.mat"
  assumes sq: "P \<in> carrier_mat n n"
      and herm: "hermitian P"
      and n_pos: "0 < n"
      and p11_pos: "P $$ (0,0) > 0"
  shows "psd P \<longleftrightarrow>
         psd (Matrix.mat (n-1) (n-1)
              (\<lambda>(i,j). P $$ (i+1, j+1) -
                       P $$ (i+1, 0) * cnj (P $$ (j+1, 0)) / P $$ (0,0)))"
proof -
  let ?S = "Matrix.mat (n-1) (n-1)
              (\<lambda>(i,j). P $$ (i+1, j+1) -
                       P $$ (i+1, 0) * cnj (P $$ (j+1, 0)) / P $$ (0,0))"
  let ?tail = "\<lambda>x :: complex Matrix.vec. Matrix.vec (n-1) (\<lambda>i. x $ (i+1))"
  let ?lift = "\<lambda>z y. Matrix.vec n (\<lambda>i. if i = 0 then z else y $ (i-1))"
  let ?cross = "\<lambda>y :: complex Matrix.vec. \<Sum>i = 0..<(n-1). cnj (P $$ (i+1, 0)) * y $ i"

  have S_car: "?S \<in> carrier_mat (n-1) (n-1)"
    by simp
  have P00_nonzero: "P $$ (0,0) \<noteq> 0"
    using p11_pos by auto
  have P00_real: "P $$ (0,0) \<in> \<real>"
    using herm sq n_pos
    by (simp add: nonnegative_complex_is_real order_less_imp_le p11_pos) 
  have P00_Re_pos: "0 < Re (P $$ (0,0))"
    using p11_pos P00_real
    by (simp add: less_complex_def)

  have S_herm: "hermitian ?S"
  proof -
    have S_dagger_entries:
      "\<And>i j. i < n-1 \<Longrightarrow> j < n-1 \<Longrightarrow>
        (?S\<^sup>\<dagger>) $$ (i,j) = ?S $$ (i,j)"
    proof -
      fix i j
      assume i: "i < n-1" and j: "j < n-1"
      have ip: "i + 1 < n" and jp: "j + 1 < n"
        using i j by linarith+
      have irow: "i + 1 < dim_row P" and icol: "i + 1 < dim_col P"
        using sq ip by simp_all
      have jrow: "j + 1 < dim_row P" and jcol: "j + 1 < dim_col P"
        using sq jp by simp_all
      have zrow: "0 < dim_row P" and zcol: "0 < dim_col P"
        using sq n_pos by simp_all
      have Pji: "P $$ (j+1, i+1) = cnj (P $$ (i+1, j+1))"
        using hermitian_index[OF herm jrow icol] by simp
      have Pj0: "P $$ (j+1, 0) = cnj (P $$ (0, j+1))"
        using hermitian_index[OF herm jrow zcol] by simp
      have Pi0: "P $$ (i+1, 0) = cnj (P $$ (0, i+1))"
        using hermitian_index[OF herm irow zcol] by simp
      have cnj_P00: "cnj (P $$ (0,0)) = P $$ (0,0)"
        using P00_real by (simp add: Reals_cnj_iff)
      have "(?S\<^sup>\<dagger>) $$ (i,j) = cnj (?S $$ (j,i))"
        using i j by (simp add: dagger_def)
      also have "\<dots> = ?S $$ (i,j)"
        using i j Pji Pj0 Pi0 cnj_P00 P00_nonzero
        by (simp add: field_simps)
      finally show "(?S\<^sup>\<dagger>) $$ (i,j) = ?S $$ (i,j)" .
    qed
    show ?thesis
      unfolding hermitian_def
      using S_dagger_entries by (intro eq_matI, auto)
  qed

  have lift_dim: "\<And>z y. dim_vec y = n-1 \<Longrightarrow> dim_vec (?lift z y) = n"
    by simp
  have tail_dim: "\<And>x. dim_vec x = n \<Longrightarrow> dim_vec (?tail x) = n-1"
    by simp
  have lift_tail_head: "\<And>x. dim_vec x = n \<Longrightarrow> ?lift (x $ 0) (?tail x) = x"
  proof -
    fix x :: "complex Matrix.vec"
    assume xdim: "dim_vec x = n"
    show "?lift (x $ 0) (?tail x) = x"
    proof (rule eq_vecI)
      show "dim_vec (?lift (x $ 0) (?tail x)) = dim_vec x"
        using xdim by simp
    next
      fix i
      assume i: "i < dim_vec x"
      show "(?lift (x $ 0) (?tail x)) $ i = x $ i"
        using xdim i n_pos by (cases i) simp_all
    qed
  qed

  have Schur_quadratic_lift:
    "\<And>z y. dim_vec y = n-1 \<Longrightarrow>
      \<langle>?lift z y | P *\<^sub>v (?lift z y)\<rangle> =
        cnj (z + ?cross y / P $$ (0,0)) * (P $$ (0,0)) * (z + ?cross y / P $$ (0,0)) +
        \<langle>y | ?S *\<^sub>v y\<rangle>"
  proof -
    fix z :: complex and y :: "complex Matrix.vec"
    assume ydim: "dim_vec y = n-1"
    let ?x = "?lift z y"
    let ?a = "P $$ (0,0)"
    let ?c = "?cross y"
    let ?tail_quad = "(\<Sum>i = 0..<(n-1). \<Sum>j = 0..<(n-1).
                         cnj (y $ i) * P $$ (i+1,j+1) * y $ j)"

    have xdim: "dim_vec ?x = n"
      using ydim by simp
    have x0: "?x $ 0 = z"
      using n_pos by simp
    have xSuc: "\<And>i. i < n-1 \<Longrightarrow> ?x $ (i+1) = y $ i"
      by simp
    have cnj_a: "cnj ?a = ?a"
      using P00_real by (simp add: Reals_cnj_iff)
    have P0_suc:
      "\<And>i. i < n-1 \<Longrightarrow> P $$ (0, i+1) = cnj (P $$ (i+1, 0))"
    proof -
      fix i
      assume i: "i < n-1"
      then have ip: "i + 1 < n"
        by linarith
      have zrow: "0 < dim_row P"
        using sq n_pos by simp
      have ipcol: "i + 1 < dim_col P"
        using sq ip by simp
      show "P $$ (0, i+1) = cnj (P $$ (i+1, 0))"
        using hermitian_index[OF herm zrow ipcol] by simp
    qed
    have c_alt: "?c = (\<Sum>i = 0..<(n-1). P $$ (0, i+1) * y $ i)"
      using P0_suc by (intro sum.cong refl) simp
    have cnj_c: "cnj ?c = (\<Sum>i = 0..<(n-1). cnj (y $ i) * P $$ (i+1, 0))"
    proof -
      have "cnj ?c = (\<Sum>i = 0..<(n-1). cnj (cnj (P $$ (i+1, 0)) * y $ i))"
        by simp
      also have "\<dots> = (\<Sum>i = 0..<(n-1). cnj (cnj (P $$ (i+1, 0))) * cnj (y $ i))"
        by (intro sum.cong refl) simp
      also have "\<dots> = (\<Sum>i = 0..<(n-1). P $$ (i+1, 0) * cnj (y $ i))"
        by (intro sum.cong refl) simp
      also have "\<dots> = (\<Sum>i = 0..<(n-1). cnj (y $ i) * P $$ (i+1, 0))"
        by (intro sum.cong refl) (simp add: mult.commute)
      finally show ?thesis .
    qed

    have Px0:
      "(P *\<^sub>v ?x) $ 0 = ?a * z + ?c"
    proof -
      have zrow: "0 < dim_row P"
        using sq n_pos by simp
      have colP: "dim_col P = n"
        using sq by simp
      have step1: "(P *\<^sub>v ?x) $ 0 = (\<Sum>j = 0..<n. P $$ (0,j) * ?x $ j)"
      proof -
        have "(P *\<^sub>v ?x) $ 0 = Matrix.row P 0 \<bullet> ?x"
          using zrow by simp
        also have "\<dots> = (\<Sum>j = 0..<dim_vec ?x. (Matrix.row P 0) $ j * ?x $ j)"
          unfolding scalar_prod_def by simp
        also have "\<dots> = (\<Sum>j = 0..<n. (Matrix.row P 0) $ j * ?x $ j)"
          using xdim by simp
        also have "\<dots> = (\<Sum>j = 0..<n. P $$ (0,j) * ?x $ j)"
        proof (intro sum.cong refl)
          fix j
          assume "j \<in> {0..<n}"
          then have jlt: "j < n" by simp
          have jcol: "j < dim_col P" using colP jlt by simp
          show "(Matrix.row P 0) $ j * ?x $ j = P $$ (0,j) * ?x $ j"
            using zrow jcol by simp
        qed
        finally show ?thesis .
      qed
      have reindex: "(\<Sum>j = Suc 0..<n. P $$ (0,j) * ?x $ j)
                   = (\<Sum>j = 0..<n-1. P $$ (0, j+1) * ?x $ (j+1))"
      proof -
        have Sucn: "Suc (n-1) = n" using n_pos by simp
        have "(\<Sum>j = Suc 0..<Suc (n-1). P $$ (0,j) * ?x $ j)
            = (\<Sum>j = 0..<n-1. P $$ (0, Suc j) * ?x $ (Suc j))"
          by (rule sum.shift_bounds_Suc_ivl)
        then show ?thesis using Sucn by simp
      qed
      have step2: "(\<Sum>j = 0..<n. P $$ (0,j) * ?x $ j)
                 = P $$ (0,0) * z + (\<Sum>j = 0..<(n-1). P $$ (0,j+1) * y $ j)"
      proof -
        have "(\<Sum>j = 0..<n. P $$ (0,j) * ?x $ j)
            = P $$ (0,0) * ?x $ 0 + (\<Sum>j = Suc 0..<n. P $$ (0,j) * ?x $ j)"
          using n_pos by (simp add: sum.atLeast_Suc_lessThan)
        also have "\<dots> = P $$ (0,0) * z + (\<Sum>j = Suc 0..<n. P $$ (0,j) * ?x $ j)"
          using x0 by simp
        also have "\<dots> = P $$ (0,0) * z + (\<Sum>j = 0..<n-1. P $$ (0, j+1) * ?x $ (j+1))"
          using reindex by simp
        also have "\<dots> = P $$ (0,0) * z + (\<Sum>j = 0..<(n-1). P $$ (0, j+1) * y $ j)"
          by (intro arg_cong2[where f="(+)"] refl sum.cong refl, simp add: xSuc)
        finally show ?thesis .
      qed
      from step1 step2 show ?thesis
        using c_alt by simp
    qed

    have PxSuc:
      "\<And>i. i < n-1 \<Longrightarrow>
        (P *\<^sub>v ?x) $ (i+1) =
          P $$ (i+1,0) * z + (\<Sum>j = 0..<(n-1). P $$ (i+1,j+1) * y $ j)"
    proof -
      fix i
      assume i: "i < n-1"
      then have ip: "i + 1 < n"
        by linarith
      have iprow: "i + 1 < dim_row P"
        using sq ip by simp
      have colP: "dim_col P = n"
        using sq by simp
      have step1: "(P *\<^sub>v ?x) $ (i+1) = (\<Sum>j = 0..<n. P $$ (i+1,j) * ?x $ j)"
      proof -
        have "(P *\<^sub>v ?x) $ (i+1) = Matrix.row P (i+1) \<bullet> ?x"
          using iprow by simp
        also have "\<dots> = (\<Sum>j = 0..<dim_vec ?x. (Matrix.row P (i+1)) $ j * ?x $ j)"
          unfolding scalar_prod_def by simp
        also have "\<dots> = (\<Sum>j = 0..<n. (Matrix.row P (i+1)) $ j * ?x $ j)"
          using xdim by simp
        also have "\<dots> = (\<Sum>j = 0..<n. P $$ (i+1,j) * ?x $ j)"
        proof (intro sum.cong refl)
          fix j
          assume "j \<in> {0..<n}"
          then have jlt: "j < n" by simp
          have jcol: "j < dim_col P" using colP jlt by simp
          show "(Matrix.row P (i+1)) $ j * ?x $ j = P $$ (i+1,j) * ?x $ j"
            using iprow jcol by simp
        qed
        finally show ?thesis .
      qed
      have reindex: "(\<Sum>j = Suc 0..<n. P $$ (i+1,j) * ?x $ j)
                   = (\<Sum>j = 0..<n-1. P $$ (i+1, j+1) * ?x $ (j+1))"
      proof -
        have Sucn: "Suc (n-1) = n" using n_pos by simp
        have "(\<Sum>j = Suc 0..<Suc (n-1). P $$ (i+1,j) * ?x $ j)
            = (\<Sum>j = 0..<n-1. P $$ (i+1, Suc j) * ?x $ (Suc j))"
          by (rule sum.shift_bounds_Suc_ivl)
        then show ?thesis using Sucn by simp
      qed
      have step2: "(\<Sum>j = 0..<n. P $$ (i+1,j) * ?x $ j)
                 = P $$ (i+1,0) * z + (\<Sum>j = 0..<(n-1). P $$ (i+1,j+1) * y $ j)"
      proof -
        have "(\<Sum>j = 0..<n. P $$ (i+1,j) * ?x $ j)
            = P $$ (i+1,0) * ?x $ 0 + (\<Sum>j = Suc 0..<n. P $$ (i+1,j) * ?x $ j)"
          using n_pos by (simp add: sum.atLeast_Suc_lessThan)
        also have "\<dots> = P $$ (i+1,0) * z + (\<Sum>j = Suc 0..<n. P $$ (i+1,j) * ?x $ j)"
          using x0 by simp
        also have "\<dots> = P $$ (i+1,0) * z + (\<Sum>j = 0..<n-1. P $$ (i+1, j+1) * ?x $ (j+1))"
          using reindex by simp
        also have "\<dots> = P $$ (i+1,0) * z + (\<Sum>j = 0..<(n-1). P $$ (i+1, j+1) * y $ j)"
          by (intro arg_cong2[where f="(+)"] refl sum.cong refl, simp add: xSuc)
        finally show ?thesis .
      qed
      from step1 step2 show "(P *\<^sub>v ?x) $ (i+1) =
          P $$ (i+1,0) * z + (\<Sum>j = 0..<(n-1). P $$ (i+1,j+1) * y $ j)"
        by simp
    qed

    have full_quad:
      "\<langle>?x | P *\<^sub>v ?x\<rangle> =
        cnj z * ?a * z + cnj z * ?c + cnj ?c * z + ?tail_quad"
    proof -
      have Pxdim: "dim_vec (P *\<^sub>v ?x) = n"
        using sq xdim by simp
      have "\<langle>?x | P *\<^sub>v ?x\<rangle> =
          (\<Sum>i = 0..<n. cnj (?x $ i) * (P *\<^sub>v ?x) $ i)"
      using xdim Pxdim by (simp add: inner_prod_def)
          also have "\<dots> = cnj z * (P *\<^sub>v ?x) $ 0 +
        (\<Sum>i = 0..<(n - 1). cnj (y $ i) * (P *\<^sub>v ?x) $ (i + 1))"
      proof -
        have "(\<Sum>i = 0..<n. cnj (?x $ i) * (P *\<^sub>v ?x) $ i)
            = cnj (?x $ 0) * (P *\<^sub>v ?x) $ 0
            + (\<Sum>i = Suc 0..<n. cnj (?x $ i) * (P *\<^sub>v ?x) $ i)"
          using xdim n_pos sum.atLeast_Suc_lessThan by blast
        also have "\<dots> =
            cnj z * (P *\<^sub>v ?x) $ 0
            + (\<Sum>i = 0..<(n - 1). cnj (?x $ (i + 1)) * (P *\<^sub>v ?x) $ (i + 1))"
        proof -
          have Sucn: "Suc (n-1) = n" using n_pos by simp
          have "(\<Sum>i = Suc 0..<Suc (n-1). cnj (?x $ i) * (P *\<^sub>v ?x) $ i)
              = (\<Sum>i = 0..<n-1. cnj (?x $ (Suc i)) * (P *\<^sub>v ?x) $ (Suc i))"
            by (rule sum.shift_bounds_Suc_ivl)
          then have reindex:
            "(\<Sum>i = Suc 0..<n. cnj (?x $ i) * (P *\<^sub>v ?x) $ i)
           = (\<Sum>i = 0..<(n - 1). cnj (?x $ (i + 1)) * (P *\<^sub>v ?x) $ (i + 1))"
            using Sucn by simp
          show "cnj (?x $ 0) * (P *\<^sub>v ?x) $ 0
                + (\<Sum>i = Suc 0..<n. cnj (?x $ i) * (P *\<^sub>v ?x) $ i)
              = cnj z * (P *\<^sub>v ?x) $ 0
                + (\<Sum>i = 0..<(n - 1). cnj (?x $ (i + 1)) * (P *\<^sub>v ?x) $ (i + 1))"
            using reindex x0 by simp
        qed
        also have "\<dots> =
            cnj z * (P *\<^sub>v ?x) $ 0
            + (\<Sum>i = 0..<(n - 1). cnj (y $ i) * (P *\<^sub>v ?x) $ (i + 1))"
          by simp
        finally show ?thesis.
      qed
      also have "\<dots> =
          cnj z * (?a * z + ?c) +
          (\<Sum>i = 0..<(n-1).
             cnj (y $ i) * (P $$ (i+1,0) * z +
               (\<Sum>j = 0..<(n-1). P $$ (i+1,j+1) * y $ j)))"
        using Px0 PxSuc by (intro arg_cong2[where f="(+)"] refl sum.cong, simp_all)
      also have "\<dots> =
          cnj z * ?a * z + cnj z * ?c +
          (\<Sum>i = 0..<(n-1). cnj (y $ i) * P $$ (i+1,0)) * z +
          ?tail_quad"
        by (simp add: algebra_simps sum_distrib_left sum_distrib_right sum.distrib)
      also have "\<dots> = cnj z * ?a * z + cnj z * ?c + cnj ?c * z + ?tail_quad"
        using cnj_c by simp
      finally show ?thesis.
    qed

    have Schur_quad:
      "\<langle>y | ?S *\<^sub>v y\<rangle> = ?tail_quad - cnj ?c * ?c / ?a"
    proof -
      have Sydim: "dim_vec (?S *\<^sub>v y) = n-1"
        using ydim by simp
      have "\<langle>y | ?S *\<^sub>v y\<rangle> =
          (\<Sum>i = 0..<(n-1). cnj (y $ i) * (?S *\<^sub>v y) $ i)"
        using ydim Sydim by (simp add: inner_prod_def)
      also have "\<dots> =
          (\<Sum>i = 0..<(n-1). cnj (y $ i) *
            (\<Sum>j = 0..<(n-1).
              (P $$ (i+1,j+1) - P $$ (i+1,0) * cnj (P $$ (j+1,0)) / ?a) * y $ j))"
      proof (intro sum.cong refl)
        fix i
        assume "i \<in> {0..<n-1}"
        then have ilt: "i < n-1" by simp
        have irow: "i < dim_row ?S" using ilt by simp
        have colS: "dim_col ?S = n-1" by simp
        have "(?S *\<^sub>v y) $ i = Matrix.row ?S i \<bullet> y"
          using irow by simp
        also have "\<dots> = (\<Sum>j = 0..<dim_vec y. (Matrix.row ?S i) $ j * y $ j)"
          unfolding scalar_prod_def by simp
        also have "\<dots> = (\<Sum>j = 0..<n-1. (Matrix.row ?S i) $ j * y $ j)"
          using ydim by simp
        also have "\<dots> = (\<Sum>j = 0..<n-1. ?S $$ (i,j) * y $ j)"
        proof (intro sum.cong refl)
          fix j
          assume "j \<in> {0..<n-1}"
          then have jlt: "j < n-1" by simp
          have jcol: "j < dim_col ?S" using colS jlt by simp
          show "(Matrix.row ?S i) $ j * y $ j = ?S $$ (i,j) * y $ j"
            using irow jcol by simp
        qed
        also have "\<dots> = (\<Sum>j = 0..<n-1.
                  (P $$ (i+1,j+1) - P $$ (i+1,0) * cnj (P $$ (j+1,0)) / ?a) * y $ j)"
        proof (intro sum.cong refl)
          fix j
          assume "j \<in> {0..<n-1}"
          then have jlt: "j < n-1" by simp
          have Sij: "?S $$ (i,j) =
              P $$ (i+1,j+1) - P $$ (i+1,0) * cnj (P $$ (j+1,0)) / ?a"
            using ilt jlt by simp
          show "?S $$ (i,j) * y $ j =
              (P $$ (i+1,j+1) - P $$ (i+1,0) * cnj (P $$ (j+1,0)) / ?a) * y $ j"
            using Sij by simp
        qed
        finally have Sy_i:
          "(?S *\<^sub>v y) $ i = (\<Sum>j = 0..<n-1.
              (P $$ (i+1,j+1) - P $$ (i+1,0) * cnj (P $$ (j+1,0)) / ?a) * y $ j)" .
        show "cnj (y $ i) * (?S *\<^sub>v y) $ i =
            cnj (y $ i) * (\<Sum>j = 0..<(n-1).
              (P $$ (i+1,j+1) - P $$ (i+1,0) * cnj (P $$ (j+1,0)) / ?a) * y $ j)"
          using Sy_i by simp
      qed
      also have "\<dots> =
          ?tail_quad -
          ((\<Sum>i = 0..<(n-1). cnj (y $ i) * P $$ (i+1,0)) *
           (\<Sum>j = 0..<(n-1). cnj (P $$ (j+1,0)) * y $ j)) / ?a"
        by (simp add: algebra_simps sum_distrib_left sum_distrib_right sum_subtractf sum_divide_distrib)
      also have "\<dots> = ?tail_quad - cnj ?c * ?c / ?a"
        using cnj_c by simp
      finally show ?thesis .
    qed

    have square_expand:
      "cnj (z + ?c / ?a) * ?a * (z + ?c / ?a) =
       cnj z * ?a * z + cnj z * ?c + cnj ?c * z + cnj ?c * ?c / ?a"
      using P00_nonzero cnj_a by (simp add: algebra_simps)

    show "\<langle>?lift z y | P *\<^sub>v (?lift z y)\<rangle> =
        cnj (z + ?cross y / P $$ (0,0)) * (P $$ (0,0)) * (z + ?cross y / P $$ (0,0)) + \<langle>y | ?S *\<^sub>v y\<rangle>"
      using full_quad Schur_quad square_expand by simp
  qed

  have Schur_quadratic_tail:
    "\<And>x. dim_vec x = n \<Longrightarrow>
      \<langle>x | P *\<^sub>v x\<rangle> =
        cnj (x $ 0 + ?cross (?tail x) / P $$ (0,0)) * (P $$ (0,0)) *
          (x $ 0 + ?cross (?tail x) / P $$ (0,0)) +
        \<langle>?tail x | ?S *\<^sub>v (?tail x)\<rangle>"
  proof -
    fix x :: "complex Matrix.vec"
    assume xdim: "dim_vec x = n"
    have "\<langle>x | P *\<^sub>v x\<rangle> = \<langle>?lift (x $ 0) (?tail x) | P *\<^sub>v (?lift (x $ 0) (?tail x))\<rangle>"
      using lift_tail_head[OF xdim] by simp
    also have "\<dots> =
        cnj (x $ 0 + ?cross (?tail x) / P $$ (0,0)) * (P $$ (0,0)) *
          (x $ 0 + ?cross (?tail x) / P $$ (0,0)) +
        \<langle>?tail x | ?S *\<^sub>v (?tail x)\<rangle>"
      using Schur_quadratic_lift[OF tail_dim[OF xdim], of "x $ 0"] .
    finally show "\<langle>x | P *\<^sub>v x\<rangle> =
        cnj (x $ 0 + ?cross (?tail x) / P $$ (0,0)) * (P $$ (0,0)) *
          (x $ 0 + ?cross (?tail x) / P $$ (0,0)) +
        \<langle>?tail x | ?S *\<^sub>v (?tail x)\<rangle>".
  qed

  have completed_square_nonneg: "\<And>w. 0 \<le> Re (cnj w * (P $$ (0,0)) * w)"
    using P00_Re_pos P00_real
    by (metis Re_complex_div_gt_0 mult.left_commute mult.right_neutral mult_zero_right 
        nonzero_mult_div_cancel_right order_le_less times_complex.simps(1) zero_complex.simps(1)) 
  have completed_square_zero_choice:
    "\<And>y. cnj ((- ?cross y / P $$ (0,0)) + ?cross y / P $$ (0,0)) *
          (P $$ (0,0)) *
          ((- ?cross y / P $$ (0,0)) + ?cross y / P $$ (0,0)) = 0"
    using P00_nonzero by simp

  have forward: "psd P \<Longrightarrow> psd ?S"
  proof -
    assume P_psd: "psd P"
    have S_nonneg: "\<forall>y :: complex Matrix.vec. dim_vec y = dim_row ?S \<longrightarrow> 0 \<le> Re \<langle>y | ?S *\<^sub>v y\<rangle>"
    proof (intro allI impI)
      fix y :: "complex Matrix.vec"
      assume ydimS: "dim_vec y = dim_row ?S"
      then have ydim: "dim_vec y = n-1"
        by simp
      let ?z = "- ?cross y / P $$ (0,0)"
      let ?x = "?lift ?z y"
      have xdim: "dim_vec ?x = n"
        using ydim by simp
      have P_nonneg: "0 \<le> Re \<langle>?x | P *\<^sub>v ?x\<rangle>"
        using P_psd xdim sq unfolding psd_def by auto
      have q_eq: "\<langle>?x | P *\<^sub>v ?x\<rangle> = \<langle>y | ?S *\<^sub>v y\<rangle>"
        using Schur_quadratic_lift[OF ydim] completed_square_zero_choice[of y] by simp
      show "0 \<le> Re \<langle>y | ?S *\<^sub>v y\<rangle>"
        using P_nonneg q_eq by simp
    qed
    show "psd ?S"
      unfolding psd_def using S_herm S_nonneg by simp
  qed

  have backward: "psd ?S \<Longrightarrow> psd P"
  proof -
    assume S_psd: "psd ?S"
    have P_nonneg:
      "\<forall>x :: complex Matrix.vec. dim_vec x = dim_row P \<longrightarrow>
        0 \<le> Re \<langle>x | P *\<^sub>v x\<rangle>"
    proof (intro allI impI)
      fix x :: "complex Matrix.vec"
      assume xdimP: "dim_vec x = dim_row P"
      then have xdim: "dim_vec x = n"
        using sq by simp
      have taildim: "dim_vec (?tail x) = n-1"
        using xdim by simp
      have S_nonneg: "0 \<le> Re \<langle>?tail x | ?S *\<^sub>v (?tail x)\<rangle>"
        using S_psd taildim unfolding psd_def by simp
      have square_nonneg:
        "0 \<le> Re (cnj (x $ 0 + ?cross (?tail x) / P $$ (0,0)) * (P $$ (0,0)) *
          (x $ 0 + ?cross (?tail x) / P $$ (0,0)))"
        using completed_square_nonneg by blast
      have q_decomp: "\<langle>x | P *\<^sub>v x\<rangle> =
        cnj (x $ 0 + ?cross (?tail x) / P $$ (0,0)) * (P $$ (0,0)) *
          (x $ 0 + ?cross (?tail x) / P $$ (0,0)) +
        \<langle>?tail x | ?S *\<^sub>v (?tail x)\<rangle>"
        using Schur_quadratic_tail[OF xdim].
      show "0 \<le> Re \<langle>x | P *\<^sub>v x\<rangle>"
        using square_nonneg S_nonneg q_decomp by simp
    qed
    show "psd P"
      unfolding psd_def using herm P_nonneg by simp
  qed
  show ?thesis
    using forward backward by blast
qed

subsection \<open>Cholesky's algorithm on the notes' two examples (D5-3)\<close>

subsubsection \<open>One step of Cholesky's algorithm\<close>

text \<open>For $P=(p_{ij})$ with $p_{11}\ne0$ the notes subtract
$R=\bigl(\tfrac{p_{i1}p_{1j}}{p_{11}}\bigr)_{ij}$; $P-R$ vanishes in the first row and column, and
what remains is the $(n-1)\times(n-1)$ matrix \<open>chol_next P\<close>.\<close>

definition chol_R :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "chol_R P = Matrix.mat (dim_row P) (dim_row P) (\<lambda>(i, j). P $$ (i, 0) * P $$ (0, j) / P $$ (0, 0))"

definition chol_next :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "chol_next P = Matrix.mat (dim_row P - 1) (dim_row P - 1) (\<lambda>(i, j). (P - chol_R P) $$ (i + 1, j + 1))"

lemma hermitian_entry:
  assumes "hermitian P" "P \<in> carrier_mat n n" "i < n" "j < n"
  shows "P $$ (i, j) = cnj (P $$ (j, i))"
proof -
  have "P $$ (i, j) = P\<^sup>\<dagger> $$ (i, j)" using assms(1) by (simp add: hermitian_def)
  also have "\<dots> = cnj (P $$ (j, i))" using assms(2-4) by (simp add: dagger_def)
  finally show ?thesis .
qed

text \<open>The test: for $P=P^*$ with $p_{11}>0$, $P\ge0$ iff the next matrix is $\ge0$
(from @{thm [source] cholesky_reduction}).\<close>

lemma chol_test:
  assumes P: "P \<in> carrier_mat n n" and h: "hermitian P" and n: "0 < n" and p: "P $$ (0, 0) > 0"
  shows "psd P \<longleftrightarrow> psd (chol_next P)"
proof -
  have "chol_next P = Matrix.mat (n - 1) (n - 1)
          (\<lambda>(i, j). P $$ (i + 1, j + 1) - P $$ (i + 1, 0) * cnj (P $$ (j + 1, 0)) / P $$ (0, 0))"
  proof (rule eq_matI)
    fix i j assume "i < dim_row (Matrix.mat (n - 1) (n - 1)
          (\<lambda>(i, j). P $$ (i + 1, j + 1) - P $$ (i + 1, 0) * cnj (P $$ (j + 1, 0)) / P $$ (0, 0)))"
      "j < dim_col (Matrix.mat (n - 1) (n - 1)
          (\<lambda>(i, j). P $$ (i + 1, j + 1) - P $$ (i + 1, 0) * cnj (P $$ (j + 1, 0)) / P $$ (0, 0)))"
    hence i: "i + 1 < n" and j: "j + 1 < n" by simp_all
    have "P $$ (0, j + 1) = cnj (P $$ (j + 1, 0))" by (rule hermitian_entry[OF h P n j])
    thus "chol_next P $$ (i, j) = Matrix.mat (n - 1) (n - 1)
          (\<lambda>(i, j). P $$ (i + 1, j + 1) - P $$ (i + 1, 0) * cnj (P $$ (j + 1, 0)) / P $$ (0, 0)) $$ (i, j)"
      using i j P by (simp add: chol_next_def chol_R_def)
  qed (use P in \<open>simp_all add: chol_next_def\<close>)
  thus ?thesis using cholesky_reduction[OF P h n p] by simp
qed

subsubsection \<open>Small matrices entry by entry\<close>

lemma mat3_eqI:
  assumes "A \<in> carrier_mat 3 3" "B \<in> carrier_mat 3 3"
      and "\<And>i j. i \<in> {0, 1, 2} \<Longrightarrow> j \<in> {0, 1, 2} \<Longrightarrow> A $$ (i, j) = B $$ (i, j)"
  shows "A = B"
proof (rule eq_matI)
  fix i j assume "i < dim_row B" "j < dim_col B"
  hence "i \<in> {0, 1, 2}" "j \<in> {0, 1, 2}" using assms(2) by auto
  thus "A $$ (i, j) = B $$ (i, j)" by (rule assms(3))
qed (use assms(1,2) in auto)

lemma mat2_eqI:
  assumes "A \<in> carrier_mat 2 2" "B \<in> carrier_mat 2 2"
      and "\<And>i j. i \<in> {0, 1} \<Longrightarrow> j \<in> {0, 1} \<Longrightarrow> A $$ (i, j) = B $$ (i, j)"
  shows "A = B"
proof (rule eq_matI)
  fix i j assume "i < dim_row B" "j < dim_col B"
  hence "i \<in> {0, 1}" "j \<in> {0, 1}" using assms(2) by auto
  thus "A $$ (i, j) = B $$ (i, j)" by (rule assms(3))
qed (use assms(1,2) in auto)

subsubsection \<open>Example 1: a matrix that is not positive\<close>

text \<open>The notes: for $P=\begin{pmatrix}1&2&3\\2&4&5\\3&5&7\end{pmatrix}$,
$R=\begin{pmatrix}1&2&3\\2&4&6\\3&6&9\end{pmatrix}$ and
$P-R=\begin{pmatrix}0&0&0\\0&0&-1\\0&-1&-2\end{pmatrix}$, so $P\not\ge0$.  Each matrix is checked
below; the last step is the test vector $(1,1)$ for the remaining $2\times2$ block.\<close>

definition notes_P1 :: "complex Matrix.mat" where
  "notes_P1 = mat_of_rows_list 3 [[1, 2, 3], [2, 4, 5], [3, 5, 7]]"

lemma notes_P1_carrier: "notes_P1 \<in> carrier_mat 3 3"
  by (simp add: notes_P1_def mat_of_rows_list_def eval_nat_numeral)

lemma notes_P1_hermitian: "hermitian notes_P1"
  unfolding hermitian_def
  by (rule mat3_eqI) (auto simp: notes_P1_def mat_of_rows_list_def dagger_def)

lemma notes_P1_R: "chol_R notes_P1 = mat_of_rows_list 3 [[1, 2, 3], [2, 4, 6], [3, 6, 9]]"
  by (rule mat3_eqI) (auto simp: chol_R_def notes_P1_def mat_of_rows_list_def)

lemma notes_P1_diff: "notes_P1 - chol_R notes_P1 = mat_of_rows_list 3 [[0, 0, 0], [0, 0, -1], [0, -1, -2]]"
  by (rule mat3_eqI) (auto simp: chol_R_def notes_P1_def mat_of_rows_list_def)

lemma notes_P1_next: "chol_next notes_P1 = mat_of_rows_list 2 [[0, -1], [-1, -2]]"
  by (rule mat2_eqI) (auto simp: chol_next_def chol_R_def notes_P1_def mat_of_rows_list_def)

lemma not_psd_witness:
  assumes A: "A \<in> carrier_mat n n" and x: "dim_vec x = n" and neg: "Re (Quantum.inner_prod x (A *\<^sub>v x)) < 0"
  shows "\<not> psd A"
proof
  assume "psd A"
  hence "\<forall>y. dim_vec y = dim_row A \<longrightarrow> 0 \<le> Re (Quantum.inner_prod y (A *\<^sub>v y))" unfolding psd_def by blast
  thus False using x neg carrier_matD(1)[OF A] by force
qed

text \<open>$\begin{pmatrix}0&-1\\-1&-2\end{pmatrix}$ has the value $-4$ at $(1,1)$, so it is not positive.\<close>

lemma notes_P1_next_not_psd: "\<not> psd (mat_of_rows_list 2 [[0, -1], [-1, -2]])"
proof (rule not_psd_witness)
  show "mat_of_rows_list 2 [[0, -1], [-1, -2]] \<in> carrier_mat 2 2"
    by (simp add: mat_of_rows_list_def eval_nat_numeral)
  show "dim_vec (Matrix.vec 2 (\<lambda>_. 1)) = 2" by simp
  show "Re (Quantum.inner_prod (Matrix.vec 2 (\<lambda>_. 1)) (mat_of_rows_list 2 [[0, -1], [-1, -2]] *\<^sub>v Matrix.vec 2 (\<lambda>_. 1))) < 0"
    by (simp add: Quantum.inner_prod_def scalar_prod_def mat_of_rows_list_def eval_nat_numeral)
qed

theorem notes_example_1: "hermitian notes_P1 \<and> \<not> psd notes_P1"
proof
  show "hermitian notes_P1" by (rule notes_P1_hermitian)
  have p: "notes_P1 $$ (0, 0) > 0" by (simp add: notes_P1_def mat_of_rows_list_def less_complex_def)
  show "\<not> psd notes_P1"
    using chol_test[OF notes_P1_carrier notes_P1_hermitian _ p] notes_P1_next notes_P1_next_not_psd by simp
qed

subsubsection \<open>Example 2: a positive matrix, in two steps\<close>

text \<open>The notes: for $P=\begin{pmatrix}4&2&3\\2&5&6\\3&6&8\end{pmatrix}$,
$R=\tfrac14\begin{pmatrix}16&8&12\\8&4&6\\12&6&9\end{pmatrix}$ and
$P-R=\begin{pmatrix}0&0&0\\0&4&\frac92\\0&\frac92&\frac{23}4\end{pmatrix}$.  Repeating on
$Q=\begin{pmatrix}4&\frac92\\\frac92&\frac{23}4\end{pmatrix}$:
$Q-\tfrac14\begin{pmatrix}4\\\frac92\end{pmatrix}\begin{pmatrix}4&\frac92\end{pmatrix}
=\begin{pmatrix}0&0\\0&\frac{11}{16}\end{pmatrix}$, so $P\ge0$.\<close>

definition notes_P2 :: "complex Matrix.mat" where
  "notes_P2 = mat_of_rows_list 3 [[4, 2, 3], [2, 5, 6], [3, 6, 8]]"

lemma notes_P2_carrier: "notes_P2 \<in> carrier_mat 3 3"
  by (simp add: notes_P2_def mat_of_rows_list_def eval_nat_numeral)

lemma notes_P2_hermitian: "hermitian notes_P2"
  unfolding hermitian_def
  by (rule mat3_eqI) (auto simp: notes_P2_def mat_of_rows_list_def dagger_def)

text \<open>First step: the first column is $c=(4,2,3)^t$ and $p_{11}=4$, and subtracting $\tfrac14cc^t$
clears the first row and column:
\[ P_2-\frac14\begin{pmatrix}4\\2\\3\end{pmatrix}\begin{pmatrix}4&2&3\end{pmatrix}
   =\begin{pmatrix}0&0&0\\0&4&9/2\\0&9/2&23/4\end{pmatrix}. \]\<close>

lemma notes_P2_R: "chol_R notes_P2 = (1/4) \<cdot>\<^sub>m mat_of_rows_list 3 [[16, 8, 12], [8, 4, 6], [12, 6, 9]]"
  by (rule mat3_eqI) (auto simp: chol_R_def notes_P2_def mat_of_rows_list_def)

lemma notes_P2_diff: "notes_P2 - chol_R notes_P2 = mat_of_rows_list 3 [[0, 0, 0], [0, 4, 9/2], [0, 9/2, 23/4]]"
  by (rule mat3_eqI) (auto simp: chol_R_def notes_P2_def mat_of_rows_list_def)

definition notes_Q2 :: "complex Matrix.mat" where
  "notes_Q2 = mat_of_rows_list 2 [[4, 9/2], [9/2, 23/4]]"

lemma notes_P2_next: "chol_next notes_P2 = notes_Q2"
  by (rule mat2_eqI) (auto simp: chol_next_def chol_R_def notes_P2_def notes_Q2_def mat_of_rows_list_def)

lemma notes_Q2_carrier: "notes_Q2 \<in> carrier_mat 2 2"
  by (simp add: notes_Q2_def mat_of_rows_list_def eval_nat_numeral)

lemma notes_Q2_hermitian: "hermitian notes_Q2"
  unfolding hermitian_def
  by (rule mat2_eqI) (auto simp: notes_Q2_def mat_of_rows_list_def dagger_def)

text \<open>Second step, on the remaining block $Q_2$:
\[ Q_2-\frac14\begin{pmatrix}4\\9/2\end{pmatrix}\begin{pmatrix}4&9/2\end{pmatrix}
   =\begin{pmatrix}0&0\\0&11/16\end{pmatrix}, \]
and the last pivot $11/16$ is positive.\<close>

lemma notes_Q2_R: "chol_R notes_Q2 = (1/4) \<cdot>\<^sub>m mat_of_rows_list 2 [[16, 18], [18, 81/4]]"
  by (rule mat2_eqI) (auto simp: chol_R_def notes_Q2_def mat_of_rows_list_def)

lemma notes_Q2_diff: "notes_Q2 - chol_R notes_Q2 = mat_of_rows_list 2 [[0, 0], [0, 11/16]]"
  by (rule mat2_eqI) (auto simp: chol_R_def notes_Q2_def mat_of_rows_list_def)

text \<open>The last matrix is $(\tfrac{11}{16})=\tfrac{11}{16}\,|e\rangle\langle e|$, which is positive.\<close>

lemma notes_Q2_next: "chol_next notes_Q2 = complex_of_real (11/16) \<cdot>\<^sub>m (Matrix.vec 1 (\<lambda>_. 1) \<oslash> Matrix.vec 1 (\<lambda>_. 1))"
proof (rule eq_matI)
  have oc: "Matrix.vec 1 (\<lambda>_. 1) \<oslash> Matrix.vec 1 (\<lambda>_. (1::complex)) \<in> carrier_mat 1 1"
    by (rule outer_prod_carrier) simp_all
  fix i j assume "i < dim_row (complex_of_real (11/16) \<cdot>\<^sub>m (Matrix.vec 1 (\<lambda>_. 1) \<oslash> Matrix.vec 1 (\<lambda>_. (1::complex))))"
    "j < dim_col (complex_of_real (11/16) \<cdot>\<^sub>m (Matrix.vec 1 (\<lambda>_. 1) \<oslash> Matrix.vec 1 (\<lambda>_. (1::complex))))"
  hence ij: "i = 0" "j = 0" using carrier_matD[OF oc] by auto
  show "chol_next notes_Q2 $$ (i, j) = (complex_of_real (11/16) \<cdot>\<^sub>m (Matrix.vec 1 (\<lambda>_. 1) \<oslash> Matrix.vec 1 (\<lambda>_. 1))) $$ (i, j)"
    using ij carrier_matD[OF oc] outer_prod_index[of 0 "Matrix.vec 1 (\<lambda>_. (1::complex))" 0 "Matrix.vec 1 (\<lambda>_. 1)"]
    by (simp add: chol_next_def chol_R_def notes_Q2_def mat_of_rows_list_def)
qed (use carrier_matD[OF outer_prod_carrier[of "Matrix.vec 1 (\<lambda>_. (1::complex))" 1 "Matrix.vec 1 (\<lambda>_. 1)" 1]]
     in \<open>simp_all add: chol_next_def notes_Q2_def mat_of_rows_list_def\<close>)

lemma notes_Q2_next_psd: "psd (chol_next notes_Q2)"
  unfolding notes_Q2_next
  by (rule psd_smult_nonneg[OF _ outer_prod_self_psd outer_prod_carrier]) simp_all

theorem notes_example_2: "hermitian notes_P2 \<and> psd notes_P2"
proof
  show "hermitian notes_P2" by (rule notes_P2_hermitian)
  have q: "notes_Q2 $$ (0, 0) > 0" by (simp add: notes_Q2_def mat_of_rows_list_def less_complex_def)
  have "psd notes_Q2"
    using chol_test[OF notes_Q2_carrier notes_Q2_hermitian _ q] notes_Q2_next_psd by simp
  moreover have p: "notes_P2 $$ (0, 0) > 0" by (simp add: notes_P2_def mat_of_rows_list_def less_complex_def)
  ultimately show "psd notes_P2"
    using chol_test[OF notes_P2_carrier notes_P2_hermitian _ p] notes_P2_next by simp
qed

text \<open>The notes' remark: the algorithm writes $P$ as a sum of rank-one matrices,
$P=\tfrac14|v_1\rangle\langle v_1|+\tfrac14|v_2\rangle\langle v_2|+\tfrac{11}{16}|e_3\rangle\langle e_3|$ with
$v_1=(4,2,3)$, $v_2=(0,4,\tfrac92)$, $e_3=(0,0,1)$ (the first columns of $P$, of $P-R$ and of the
last step).\<close>

lemma outer_prod_of_list:
  "vec_of_list l \<oslash> vec_of_list l = Matrix.mat (length l) (length l) (\<lambda>(i, j). l ! i * cnj (l ! j))"
proof -
  have d: "dim_vec (vec_of_list l) = length l" by simp
  have c: "vec_of_list l \<oslash> vec_of_list l \<in> carrier_mat (length l) (length l)" by (rule outer_prod_carrier[OF d d])
  show ?thesis
  proof (rule eq_matI)
    fix i j assume "i < dim_row (Matrix.mat (length l) (length l) (\<lambda>(i, j). l ! i * cnj (l ! j)))"
      "j < dim_col (Matrix.mat (length l) (length l) (\<lambda>(i, j). l ! i * cnj (l ! j)))"
    hence i: "i < length l" and j: "j < length l" by simp_all
    have "(vec_of_list l \<oslash> vec_of_list l) $$ (i, j) = vec_of_list l $ i * cnj (vec_of_list l $ j)"
      by (rule outer_prod_index) (use i j in simp_all)
    thus "(vec_of_list l \<oslash> vec_of_list l) $$ (i, j) = Matrix.mat (length l) (length l) (\<lambda>(i, j). l ! i * cnj (l ! j)) $$ (i, j)"
      using i j by (simp add: vec_of_list_index)
  qed (use carrier_matD[OF c] in simp_all)
qed

lemma notes_P2_rank_one_sum:
  "notes_P2 = complex_of_real (1/4) \<cdot>\<^sub>m (vec_of_list [4, 2, 3] \<oslash> vec_of_list [4, 2, 3])
            + complex_of_real (1/4) \<cdot>\<^sub>m (vec_of_list [0, 4, 9/2] \<oslash> vec_of_list [0, 4, 9/2])
            + complex_of_real (11/16) \<cdot>\<^sub>m (vec_of_list [0, 0, 1] \<oslash> vec_of_list [0, 0, 1])"
  unfolding outer_prod_of_list
  by (rule mat3_eqI[OF notes_P2_carrier]) (auto simp: notes_P2_def mat_of_rows_list_def eval_nat_numeral)

subsection \<open>Direct sums of vector spaces and partitioned matrices\<close>

text \<open>\begin{notesdef}
The \emph{direct sum} of vector spaces $V,W$ is $V\oplus W=\{(v,w): v\in V, w\in W\}$ with
componentwise operations and inner product
$\langle(v_1,w_1)|(v_2,w_2)\rangle=\braket{v_1}{v_2}_V+\braket{w_1}{w_2}_W$.
\end{notesdef}
\begin{notesprop}
If $v_1,\dots,v_n$ is a basis of $V$ and $w_1,\dots,w_k$ a basis of $W$, then
$(v_1,0),\dots,(v_n,0),(0,w_1),\dots,(0,w_k)$ is a basis of $V\oplus W$; hence
$\dim(V\oplus W)=\dim V+\dim W$.
\end{notesprop}
Key examples: $\C^{n+k}=\C^n\oplus\C^k$, and a linear map
$T:\C^{n_1+k_1}\to\C^{n_2+k_2}$ has the block form
$T=\begin{pmatrix}T_{11}&T_{12}\\T_{21}&T_{22}\end{pmatrix}$ with
$T\binom{v}{w}=\binom{T_{11}v+T_{12}w}{T_{21}v+T_{22}w}$.
Formally the direct sum of vectors is the concatenation \<open>v \<oplus>\<^sub>v w\<close>, and block
matrices are the library's \<open>four_block_mat\<close>.\<close>

text \<open>The direct sum of vectors is JNF's concatenation \<open>@\<^sub>v\<close>.\<close>

abbreviation direct_sum_vec :: "complex Matrix.vec \<Rightarrow> complex Matrix.vec \<Rightarrow> complex Matrix.vec" (infixr "\<oplus>\<^sub>v" 65) where
  "v \<oplus>\<^sub>v w \<equiv> v @\<^sub>v w"

lemma direct_sum_vec_right [simp]:
  "i < dim_vec w \<Longrightarrow> (v \<oplus>\<^sub>v w) $ (dim_vec v + i) = w $ i"
  by (simp add: append_vec_def Let_def)

lemma direct_sum_inner_prod:
  assumes vd1: "dim_vec v1 = m" and vd2: "dim_vec v2 = m"
      and wd1: "dim_vec w1 = p" and wd2: "dim_vec w2 = p"
  shows "\<langle>v1 \<oplus>\<^sub>v w1 | v2 \<oplus>\<^sub>v w2\<rangle> = \<langle>v1 | v2\<rangle> + \<langle>w1 | w2\<rangle>"
proof -
  (* Split at i = m using sum.atLeastLessThan_concat:
       (\<Sum>i = 0..<m+p. f i) = (\<Sum>i = 0..<m. f i) + (\<Sum>i = m..<m+p. f i),
     then reindex i \<mapsto> m + j to match the second range. *)
  have "\<langle>v1 \<oplus>\<^sub>v w1 | v2 \<oplus>\<^sub>v w2\<rangle> =
        (\<Sum>i = 0..<m+p. cnj ((v1 \<oplus>\<^sub>v w1) $ i) * (v2 \<oplus>\<^sub>v w2) $ i)"
    using assms by (simp add: inner_prod_def)
  also have "\<dots> = (\<Sum>i = 0..<m. cnj ((v1 \<oplus>\<^sub>v w1) $ i) * (v2 \<oplus>\<^sub>v w2) $ i)
                + (\<Sum>i = m..<m+p. cnj ((v1 \<oplus>\<^sub>v w1) $ i) * (v2 \<oplus>\<^sub>v w2) $ i)"
    by (simp add: sum.atLeastLessThan_concat)

  also have "(\<Sum>i = 0..<m. cnj ((v1 \<oplus>\<^sub>v w1) $ i) * (v2 \<oplus>\<^sub>v w2) $ i) =
             (\<Sum>i = 0..<m. cnj (v1 $ i) * v2 $ i)"
    using vd1 vd2 by (intro sum.cong refl, simp)
  also have "(\<Sum>i = m..<m+p. cnj ((v1 \<oplus>\<^sub>v w1) $ i) * (v2 \<oplus>\<^sub>v w2) $ i) =
             (\<Sum>j = 0..<p. cnj (w1 $ j) * w2 $ j)"
  proof -
    have "(\<Sum>i = m..<m+p. cnj ((v1 \<oplus>\<^sub>v w1) $ i) * (v2 \<oplus>\<^sub>v w2) $ i) =
          (\<Sum>j = 0..<p. cnj ((v1 \<oplus>\<^sub>v w1) $ (j + m)) * (v2 \<oplus>\<^sub>v w2) $ (j + m))"
      using sum.shift_bounds_nat_ivl[of _ 0 m p]
      by (simp add: add.commute)
    also have "\<dots> = (\<Sum>j = 0..<p. cnj (w1 $ j) * w2 $ j)"
    proof (intro sum.cong refl)
      fix j assume "j \<in> {0..<p}"
      hence jp: "j < p" by simp
      have e1: "(v1 \<oplus>\<^sub>v w1) $ (j + m) = w1 $ j"
        using jp vd1 wd1 direct_sum_vec_right[of j w1 v1]
        by (simp add: add.commute)
      have e2: "(v2 \<oplus>\<^sub>v w2) $ (j + m) = w2 $ j"
        using jp vd2 wd2 direct_sum_vec_right[of j w2 v2]
        by (simp add: add.commute)
      show "cnj ((v1 \<oplus>\<^sub>v w1) $ (j + m)) * (v2 \<oplus>\<^sub>v w2) $ (j + m) =
            cnj (w1 $ j) * w2 $ j"
        using e1 e2 by simp
    qed
    finally show ?thesis.
  qed
  finally show ?thesis
    using vd1 vd2 wd1 wd2 by (simp add: inner_prod_def)
qed

lemma block_mat_apply:
  assumes "dim_vec v = k1" and "dim_vec w = k2"
      and "T11 \<in> carrier_mat n1 k1" and "T12 \<in> carrier_mat n1 k2"
      and "T21 \<in> carrier_mat n2 k1" and "T22 \<in> carrier_mat n2 k2"
  shows "four_block_mat T11 T12 T21 T22 *\<^sub>v (v \<oplus>\<^sub>v w) =
         (T11 *\<^sub>v v + T12 *\<^sub>v w) \<oplus>\<^sub>v (T21 *\<^sub>v v + T22 *\<^sub>v w)"
proof -
  have v_carrier: "v \<in> carrier_vec k1"
    using assms(1) by (rule carrier_vecI)
  have w_carrier: "w \<in> carrier_vec k2"
    using assms(2) by (rule carrier_vecI)
  have vw_append: "v \<oplus>\<^sub>v w = v @\<^sub>v w"
    by (rule refl)

  have left_dim:
    "dim_vec (four_block_mat T11 T12 T21 T22 *\<^sub>v (v \<oplus>\<^sub>v w)) = n1 + n2"
    using assms by simp
  have right_dim:
    "dim_vec ((T11 *\<^sub>v v + T12 *\<^sub>v w) \<oplus>\<^sub>v (T21 *\<^sub>v v + T22 *\<^sub>v w)) = n1 + n2"
    using assms by simp

  show ?thesis
  proof
    show "dim_vec (four_block_mat T11 T12 T21 T22 *\<^sub>v (v \<oplus>\<^sub>v w)) =
          dim_vec ((T11 *\<^sub>v v + T12 *\<^sub>v w) \<oplus>\<^sub>v (T21 *\<^sub>v v + T22 *\<^sub>v w))"
      using left_dim right_dim by simp
  next
    fix i
    assume i: "i < dim_vec ((T11 *\<^sub>v v + T12 *\<^sub>v w) \<oplus>\<^sub>v
                             (T21 *\<^sub>v v + T22 *\<^sub>v w))"
    then have i_bound: "i < n1 + n2"
      using right_dim by simp
    show "(four_block_mat T11 T12 T21 T22 *\<^sub>v (v \<oplus>\<^sub>v w)) $ i =
          ((T11 *\<^sub>v v + T12 *\<^sub>v w) \<oplus>\<^sub>v (T21 *\<^sub>v v + T22 *\<^sub>v w)) $ i"
    proof (cases "i < n1")
      case True
      have row_top:
        "Matrix.row (four_block_mat T11 T12 T21 T22) i = Matrix.row T11 i @\<^sub>v Matrix.row T12 i"
        using assms True row_four_block_mat[of T11 n1 k1 T12 k2 T21 n2 T22 i]
        by simp
      have lhs_i:
        "(four_block_mat T11 T12 T21 T22 *\<^sub>v (v \<oplus>\<^sub>v w)) $ i =
         Matrix.row T11 i \<bullet> v + Matrix.row T12 i \<bullet> w"
        using assms True v_carrier w_carrier vw_append row_top
        by (metis dim_mult_mat_vec i_bound index_mult_mat_vec
            left_dim row_carrier_vec scalar_prod_append)
      have rhs_i:
        "((T11 *\<^sub>v v + T12 *\<^sub>v w) \<oplus>\<^sub>v (T21 *\<^sub>v v + T22 *\<^sub>v w)) $ i =
         Matrix.row T11 i \<bullet> v + Matrix.row T12 i \<bullet> w"
        using assms True
        by simp
      show ?thesis
        using lhs_i rhs_i by simp
    next
      case False
      let ?j = "i - n1"
      have j_bound: "?j < n2"
        using False i_bound by simp
      have row_bottom:
        "Matrix.row (four_block_mat T11 T12 T21 T22) i = Matrix.row T21 ?j @\<^sub>v Matrix.row T22 ?j"
        using assms False i_bound row_four_block_mat[of T11 n1 k1 T12 k2 T21 n2 T22 i]
        by simp
      have lhs_i:
        "(four_block_mat T11 T12 T21 T22 *\<^sub>v (v \<oplus>\<^sub>v w)) $ i =
         Matrix.row T21 ?j \<bullet> v + Matrix.row T22 ?j \<bullet> w"
        using assms False i_bound v_carrier w_carrier vw_append row_bottom
        by (metis dim_mult_mat_vec index_mult_mat_vec j_bound left_dim row_carrier_vec scalar_prod_append)
      have rhs_i:
        "((T11 *\<^sub>v v + T12 *\<^sub>v w) \<oplus>\<^sub>v (T21 *\<^sub>v v + T22 *\<^sub>v w)) $ i =
         Matrix.row T21 ?j \<bullet> v + Matrix.row T22 ?j \<bullet> w"
        using assms False j_bound
        by (simp add: append_vec_def Let_def)
      show ?thesis
        using lhs_i rhs_i by simp
    qed
  qed
qed

subsection \<open>A basis of $V\oplus W$ (D5-5)\<close>

text \<open>A basis of $\C^n$ is a list of $n$ vectors whose column matrix is invertible.  The notes: if $v_1,\dots,v_n$ and $w_1,\dots,w_k$ are bases of
$V$ and $W$ then $(v_i,0)$, $(0,w_j)$ is a basis of $V\oplus W$, so
$\dim(V\oplus W)=\dim V+\dim W$.  The column matrix is block diagonal.\<close>

definition direct_sum_basis :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.vec list \<Rightarrow> complex Matrix.vec list \<Rightarrow> complex Matrix.vec list" where
  "direct_sum_basis n k vs ws = map (\<lambda>v. v \<oplus>\<^sub>v 0\<^sub>v k) vs @ map (\<lambda>w. 0\<^sub>v n \<oplus>\<^sub>v w) ws"

lemma direct_sum_basis_block:
  assumes vs: "\<forall>v \<in> set vs. dim_vec v = n" "length vs = n" and ws: "\<forall>w \<in> set ws. dim_vec w = k" "length ws = k"
  shows "mat_of_cols (n + k) (direct_sum_basis n k vs ws)
         = four_block_mat (mat_of_cols n vs) (0\<^sub>m n k) (0\<^sub>m k n) (mat_of_cols k ws)"
proof (rule eq_matI)
  fix i j assume "i < dim_row (four_block_mat (mat_of_cols n vs) (0\<^sub>m n k) (0\<^sub>m k n) (mat_of_cols k ws))"
    "j < dim_col (four_block_mat (mat_of_cols n vs) (0\<^sub>m n k) (0\<^sub>m k n) (mat_of_cols k ws))"
  hence i: "i < n + k" and j: "j < n + k" using vs ws by simp_all
  show "mat_of_cols (n + k) (direct_sum_basis n k vs ws) $$ (i, j)
        = four_block_mat (mat_of_cols n vs) (0\<^sub>m n k) (0\<^sub>m k n) (mat_of_cols k ws) $$ (i, j)"
  proof (cases "j < n")
    case True
    have vj: "dim_vec (vs ! j) = n" using vs True by simp
    show ?thesis using i j True vs ws vj
      by (auto simp: mat_of_cols_def direct_sum_basis_def nth_append append_vec_def Let_def)
  next
    case False
    have wj: "dim_vec (ws ! (j - n)) = k" using ws j False by simp
    show ?thesis using i j False vs ws wj
      by (auto simp: mat_of_cols_def direct_sum_basis_def nth_append append_vec_def Let_def)
  qed
qed (use vs ws in \<open>simp_all add: direct_sum_basis_def\<close>)

lemma basis_inverse:
  fixes fs :: "complex Matrix.vec list"
  assumes fd: "\<forall>f \<in> set fs. dim_vec f = m" "length fs = m" and inv: "invertible_mat (mat_of_cols m fs)"
  obtains G where "G \<in> carrier_mat m m" "G * mat_of_cols m fs = 1\<^sub>m m" "mat_of_cols m fs * G = 1\<^sub>m m"
proof -
  let ?F = "mat_of_cols m fs"
  obtain G where FG: "?F * G = 1\<^sub>m m" and GF: "G * ?F = 1\<^sub>m (dim_row G)"
    using inv unfolding invertible_mat_def inverts_mat_def by auto
  have c: "dim_col G = m" using arg_cong[OF FG, of dim_col] by simp
  have r: "dim_row G = m" using arg_cong[OF GF, of dim_col] fd by simp
  show thesis by (rule that) (use c r FG GF in \<open>auto intro: carrier_matI\<close>)
qed

theorem direct_sum_basis_is_basis:
  assumes vs: "\<forall>v \<in> set vs. dim_vec v = n" "length vs = n" and iv: "invertible_mat (mat_of_cols n vs)"
      and ws: "\<forall>w \<in> set ws. dim_vec w = k" "length ws = k" and iw: "invertible_mat (mat_of_cols k ws)"
  shows "\<forall>u \<in> set (direct_sum_basis n k vs ws). dim_vec u = n + k"
    and "length (direct_sum_basis n k vs ws) = n + k"
    and "invertible_mat (mat_of_cols (n + k) (direct_sum_basis n k vs ws))"
proof -
  show "\<forall>u \<in> set (direct_sum_basis n k vs ws). dim_vec u = n + k"
    using vs ws by (auto simp: direct_sum_basis_def)
  show "length (direct_sum_basis n k vs ws) = n + k" using vs ws by (simp add: direct_sum_basis_def)
  obtain G where G: "G \<in> carrier_mat n n" and GV: "G * mat_of_cols n vs = 1\<^sub>m n" and VG: "mat_of_cols n vs * G = 1\<^sub>m n"
    by (rule basis_inverse[OF vs iv])
  obtain H where H: "H \<in> carrier_mat k k" and HW: "H * mat_of_cols k ws = 1\<^sub>m k" and WH: "mat_of_cols k ws * H = 1\<^sub>m k"
    by (rule basis_inverse[OF ws iw])
  have V: "mat_of_cols n vs \<in> carrier_mat n n" using mat_of_cols_carrier(1)[of n vs] vs(2) by simp
  have W: "mat_of_cols k ws \<in> carrier_mat k k" using mat_of_cols_carrier(1)[of k ws] ws(2) by simp
  let ?M = "four_block_mat (mat_of_cols n vs) (0\<^sub>m n k) (0\<^sub>m k n) (mat_of_cols k ws)"
  let ?N = "four_block_mat G (0\<^sub>m n k) (0\<^sub>m k n) H"
  have MN: "?M * ?N = 1\<^sub>m (n + k)"
    using mult_four_block_mat[OF V zero_carrier_mat zero_carrier_mat W G zero_carrier_mat zero_carrier_mat H]
    using V W G H VG WH right_mult_zero_mat[OF V, of k] right_mult_zero_mat[OF W, of n] by simp
  have NM: "?N * ?M = 1\<^sub>m (n + k)"
    using mult_four_block_mat[OF G zero_carrier_mat zero_carrier_mat H V zero_carrier_mat zero_carrier_mat W]
    using V W G H GV HW right_mult_zero_mat[OF G, of k] right_mult_zero_mat[OF H, of n] vs(2) ws(2) by simp
  have Mc: "?M \<in> carrier_mat (n + k) (n + k)" using V W by simp
  have Nc: "?N \<in> carrier_mat (n + k) (n + k)" using G H by simp
  have "invertible_mat ?M"
  proof -
    have "inverts_mat ?M ?N" unfolding inverts_mat_def using MN carrier_matD[OF Mc] by simp
    moreover have "inverts_mat ?N ?M" unfolding inverts_mat_def using NM carrier_matD[OF Nc] by simp
    moreover have "square_mat ?M" using carrier_matD[OF Mc] by simp
    ultimately show ?thesis unfolding invertible_mat_def by blast
  qed
  thus "invertible_mat (mat_of_cols (n + k) (direct_sum_basis n k vs ws))"
    unfolding direct_sum_basis_block[OF vs ws] .
qed

end

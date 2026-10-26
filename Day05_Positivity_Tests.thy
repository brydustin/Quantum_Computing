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

lemma direct_sum_vec_left [simp]:
  "i < dim_vec v \<Longrightarrow> (v \<oplus>\<^sub>v w) $ i = v $ i"
  by (simp add: append_vec_def Let_def)

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

end

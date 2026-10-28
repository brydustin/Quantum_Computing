(*  Title:   Day02_Trace_Projections.thy
    Author:  Dustin Bryant, after Vern Paulsen's lecture of 24 August 2011 (Day 2)
*)

theory Day02_Trace_Projections
  imports Day01_Inner_Product
begin

section \<open>Day 2 (24 August 2011): bases, matrix units, trace, projections\<close>

text \<open>\begin{notesdef}[Examples]
$\C^n$ has the orthonormal basis $e_1,\dots,e_n$ and every $x$ satisfies
$x=\sum_i x_i e_i=\sum_i\braket{e_i}{x}e_i$.  The \emph{matrix units} $E_{ij}$ (entry $1$ in
position $(i,j)$, $0$ elsewhere) form an orthonormal basis of $M_{n,m}$, and
\[ X=\sum_{i,j}X_{ij}E_{ij}=\sum_{i,j}\langle E_{ij}|X\rangle E_{ij}. \]
\end{notesdef}
Formally \<open>E\<lbrakk>i,j ; m,n\<rbrakk>\<close> is the $m\times n$ matrix unit (indices first,
dimensions second).  The notes also recall the conjugate $\overline X$, the transpose
$X^t$, the adjoint $X^*=\overline{X}^{\,t}$ (written $X^\dagger$ by physicists, formally
\<^term>\<open>X\<^sup>\<dagger>\<close>) and the row-times-column rule for matrix products; these are library
notions.\<close>

definition mat_unit :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
  "mat_unit i j m n = Matrix.mat m n (\<lambda>(r,c). if r = i \<and> c = j then 1 else 0)"

notation mat_unit ("E\<lbrakk>_,_ ; _,_\<rbrakk>" [1000, 1000, 1000, 1000] 999)

text \<open>Entrywise, $(E_{ij})_{rc}=\delta_{ri}\,\delta_{cj}$.\<close>

lemma mat_unit_carrier [simp]: "E\<lbrakk>i,j ; m,n\<rbrakk> \<in> carrier_mat m n"
  by (simp add: mat_unit_def)

lemma mat_unit_dim_row [simp]:
  fixes i j m n :: nat
  shows "dim_row (E\<lbrakk>i,j ; m,n\<rbrakk>) = m"
  by (simp add: mat_unit_def)

lemma mat_unit_dim_col [simp]:
  fixes i j m n :: nat
  shows "dim_col (E\<lbrakk>i,j ; m,n\<rbrakk>) = n"
  by (simp add: mat_unit_def)

lemma mat_unit_index [simp]:
  assumes "r < m" and "c < n"
  shows "(E\<lbrakk>i,j ; m,n\<rbrakk>) $$ (r,c) = (if r = i \<and> c = j then 1 else 0)"
  using assms by (simp add: mat_unit_def)

text \<open>Pairing with $E_{ij}$ extracts the $(i,j)$ entry: the matrix analogue of
$\braket{e_i}{v}=v_i$.\<close>

lemma hs_inner_prod_mat_unit_left:
  assumes "i < dim_row x" and "j < dim_col x"
  shows "\<langle>\<langle> E\<lbrakk>i,j ; (dim_row x), (dim_col x)\<rbrakk> | x \<rangle>\<rangle> = x $$ (i,j)"
proof -
  let ?m = "dim_row x"
  let ?n = "dim_col x"

  have "\<langle>\<langle> E\<lbrakk>i,j ; ?m,?n\<rbrakk> | x \<rangle>\<rangle> =
        (\<Sum>r \<in> {0..<?m}. \<Sum>c \<in> {0..<?n}.
          cnj (E\<lbrakk>i,j ; ?m,?n\<rbrakk> $$ (r,c)) * x $$ (r,c))"
    by (simp add: hs_inner_prod_def)
  also have "\<dots> = (\<Sum>r \<in> {0..<?m}. \<Sum>c \<in> {0..<?n}.
          cnj (if r = i \<and> c = j then 1 else 0) * x $$ (r,c))"
    by (intro sum.cong refl) auto
  also have "\<dots> = (\<Sum>r \<in> {0..<?m}. \<Sum>c \<in> {0..<?n}.
          (if r = i \<and> c = j then x $$ (r,c) else 0))"
    by (intro sum.cong refl) simp
  also have "\<dots> = (\<Sum>r \<in> {0..<?m}. if r = i then x $$ (i,j) else 0)"
  proof (intro sum.cong refl)
    fix r
    assume hr: "r \<in> {0..<?m}"
    show "(\<Sum>c \<in> {0..<?n}. if r = i \<and> c = j then x $$ (r,c) else 0) =
          (if r = i then x $$ (i,j) else 0)"
    proof (cases "r = i")
      case True
      then have "(\<Sum>c \<in> {0..<?n}. if r = i \<and> c = j then x $$ (r,c) else 0) =
                 (\<Sum>c \<in> {0..<?n}. if c = j then x $$ (i,j) else 0)"
        by (intro sum.cong) auto
      also have "\<dots> = x $$ (i,j)"
      proof -
        have "(\<Sum>c \<in> {0..<?n}. if c = j then x $$ (i,j) else 0) =
              (\<Sum>c \<in> {0..<?n}. (if c = j then 1 else 0) * x $$ (i,j))"
          by (intro sum.cong) auto
        also have "\<dots> = (\<Sum>c \<in> {0..<?n}. if c = j then 1 else 0) * x $$ (i,j)"
          by (metis sum_distrib_right)
        also have "(\<Sum>c \<in> {0..<?n}. if c = j then 1 else (0::complex)) = 1"
          using assms(2) by simp
        finally show ?thesis by simp
      qed
      finally show ?thesis
        using True by simp
    next
      case False
      then show ?thesis by simp
    qed
  qed
  also have "\<dots> = x $$ (i,j)"
  proof -
    have "(\<Sum>r \<in> {0..<?m}. if r = i then x $$ (i,j) else 0) =
          (\<Sum>r \<in> {0..<?m}. (if r = i then 1 else 0) * x $$ (i,j))"
      by (intro sum.cong) auto
    also have "\<dots> = (\<Sum>r \<in> {0..<?m}. if r = i then 1 else 0) * x $$ (i,j)"
      by (metis sum_distrib_right)
    also have "(\<Sum>r \<in> {0..<?m}. if r = i then 1 else (0::complex)) = 1"
      using assms(1) by simp
    finally show ?thesis by simp
  qed
  finally show ?thesis.
qed

lemma mat_unit_orthonormal:
  assumes i_lt: "i < m"
      and j_lt: "j < n"
      and k_lt: "k < m"
      and l_lt: "l < n"
  shows "\<langle>\<langle> E\<lbrakk>i,j ; m,n\<rbrakk> | E\<lbrakk>k,l ; m,n\<rbrakk> \<rangle>\<rangle> =
         (if i = k \<and> j = l then 1 else 0)"
  by (metis hs_inner_prod_mat_unit_left i_lt j_lt mat_unit_dim_col mat_unit_dim_row mat_unit_index)

text \<open>Expansion in the basis $\{E_{ij}\}$, stated entrywise because matrices of
different dimensions cannot be added in the library.\<close>

lemma mat_unit_expansion:
  assumes "r < dim_row x" and "c < dim_col x"
  shows "x $$ (r,c) =
         (\<Sum>i \<in> {0..<dim_row x}. \<Sum>j \<in> {0..<dim_col x}.
            x $$ (i,j) * (mat_unit i j (dim_row x) (dim_col x)) $$ (r,c))"
proof -
  let ?m = "dim_row x"
  let ?n = "dim_col x"

  have "(\<Sum>i \<in> {0..<?m}. \<Sum>j \<in> {0..<?n}.
          x $$ (i,j) * (E\<lbrakk>i,j ; ?m,?n\<rbrakk>) $$ (r,c)) =
        (\<Sum>i \<in> {0..<?m}. \<Sum>j \<in> {0..<?n}.
          x $$ (i,j) * (if i = r \<and> j = c then 1 else 0))"
    using assms by (intro sum.cong refl) simp
  also have "\<dots> = (\<Sum>i \<in> {0..<?m}. \<Sum>j \<in> {0..<?n}.
                    (if i = r \<and> j = c then x $$ (i,j) else 0))"
    by (intro sum.cong refl) auto
  also have "\<dots> = (\<Sum>i \<in> {0..<?m}. if i = r then x $$ (r,c) else 0)"
  proof (intro sum.cong refl)
    fix i
    assume hi: "i \<in> {0..<?m}"
    show "(\<Sum>j \<in> {0..<?n}. if i = r \<and> j = c then x $$ (i,j) else 0) =
          (if i = r then x $$ (r,c) else 0)"
    proof (cases "i = r")
      case True
      then have "(\<Sum>j \<in> {0..<?n}. if i = r \<and> j = c then x $$ (i,j) else 0) =
                 (\<Sum>j \<in> {0..<?n}. if j = c then x $$ (r,j) else 0)"
        by (intro sum.cong) auto
      also have "\<dots> = x $$ (r,c)"
      proof -
        have "(\<Sum>j \<in> {0..<?n}. if j = c then x $$ (r,j) else 0) =
              (\<Sum>j \<in> {0..<?n}. (if j = c then 1 else 0) * x $$ (r,c))"
          by (intro sum.cong) auto
        also have "\<dots> = (\<Sum>j \<in> {0..<?n}. if j = c then 1 else 0) * x $$ (r,c)"
          by (metis sum_distrib_right)
        also have "(\<Sum>j \<in> {0..<?n}. if j = c then 1 else (0::complex)) = 1"
          using assms(2) by simp
        finally show ?thesis by simp
      qed
      finally show ?thesis
        using True by simp
    next
      case False
      then show ?thesis by simp
    qed
  qed
  also have "\<dots> = x $$ (r,c)"
  proof -
    have "(\<Sum>i \<in> {0..<?m}. if i = r then x $$ (r,c) else 0) =
          (\<Sum>i \<in> {0..<?m}. (if i = r then 1 else 0) * x $$ (r,c))"
      by (intro sum.cong) auto
    also have "\<dots> = (\<Sum>i \<in> {0..<?m}. if i = r then 1 else 0) * x $$ (r,c)"
      by (metis sum_distrib_right)
    also have "(\<Sum>i \<in> {0..<?m}. if i = r then 1 else (0::complex)) = 1"
      using assms(1) by simp
    finally show ?thesis by simp
  qed
  finally show ?thesis by simp
qed

lemma mat_unit_hs_expansion:
  assumes "r < dim_row x" and "c < dim_col x"
  shows "x $$ (r,c) =
         (\<Sum>i \<in> {0..<dim_row x}. \<Sum>j \<in> {0..<dim_col x}.
            \<langle>\<langle> mat_unit i j (dim_row x) (dim_col x) | x \<rangle>\<rangle> *
            (mat_unit i j (dim_row x) (dim_col x)) $$ (r,c))"
proof -
  let ?m = "dim_row x"
  let ?n = "dim_col x"

  have "(\<Sum>i \<in> {0..<?m}. \<Sum>j \<in> {0..<?n}.
          \<langle>\<langle> E\<lbrakk>i,j ; ?m,?n\<rbrakk> | x \<rangle>\<rangle> * (E\<lbrakk>i,j ; ?m,?n\<rbrakk>) $$ (r,c)) =
        (\<Sum>i \<in> {0..<?m}. \<Sum>j \<in> {0..<?n}.
          x $$ (i,j) * (E\<lbrakk>i,j ; ?m,?n\<rbrakk>) $$ (r,c))"
  proof (intro sum.cong refl)
    fix i
    assume hi: "i \<in> {0..<?m}"
    fix j
    assume hj: "j \<in> {0..<?n}"
    have "\<langle>\<langle> E\<lbrakk>i,j ; ?m,?n\<rbrakk> | x \<rangle>\<rangle> = x $$ (i,j)"
      using hi hj
      by (simp add: hs_inner_prod_mat_unit_left)
    then show "\<langle>\<langle> E\<lbrakk>i,j ; ?m,?n\<rbrakk> | x \<rangle>\<rangle> * (E\<lbrakk>i,j ; ?m,?n\<rbrakk>) $$ (r,c) =
               x $$ (i,j) * (E\<lbrakk>i,j ; ?m,?n\<rbrakk>) $$ (r,c)"
      by simp
  qed
  also have "\<dots> = x $$ (r,c)"
    using mat_unit_expansion[OF assms] by simp
  finally show ?thesis by simp
qed

subsection \<open>The trace\<close>

text \<open>\begin{notesdef}
$\Tr:M_{n,n}\to\C$, $\Tr(X)=\sum_{i=1}^n x_{ii}$; we sometimes write $\Tr_n$.
\end{notesdef}
The formal \<open>Tr\<close> sums the diagonal of any matrix.  On matrix units, $\Tr(E_{ii})=1$
and $\Tr(E_{ij})=0$ for $i\neq j$, so the trace is the sum of the diagonal
Hilbert--Schmidt coefficients.\<close>

definition Tr :: "complex Matrix.mat \<Rightarrow> complex" where
  "Tr x = (\<Sum>r < dim_row x. if r < dim_col x then x $$ (r,r) else 0)"

lemma Tr_mat_unit:
  assumes i_lt: "i < m"
      and j_lt: "j < n"
  shows "Tr (E\<lbrakk>i,j ; m,n\<rbrakk>) = (if i = j then 1 else 0)"
proof (cases "i = j")
  case True
  have "Tr (E\<lbrakk>i,j ; m,n\<rbrakk>) =
        (\<Sum>r<m. if r < n then (E\<lbrakk>i,j ; m,n\<rbrakk>) $$ (r,r) else 0)"
    by (simp add: Tr_def)
  also have "... =
        (\<Sum>r<m. if r < n then (if r = i \<and> r = j then 1 else 0) else 0)"
    by (intro sum.cong refl) simp
  also have "... = (\<Sum>r<m. if r = i then 1 else 0)"
    by (metis True j_lt)  
  also have "... = 1"
    using i_lt by simp
  finally show ?thesis
    using True by simp
next
  case False
  have "Tr (E\<lbrakk>i,j ; m,n\<rbrakk>) =
        (\<Sum>r<m. if r < n then (E\<lbrakk>i,j ; m,n\<rbrakk>) $$ (r,r) else 0)"
    by (simp add: Tr_def)
  also have "... =
        (\<Sum>r<m. if r < n then (if r = i \<and> r = j then 1 else 0) else 0)"
    by (intro sum.cong refl) simp
  also have "... = 0"
    by (simp add: False sum.neutral)
  finally show ?thesis
    using False by simp
qed

text \<open>So $\Tr E_{ij}=\delta_{ij}$, and since $\langle E_{rr}|X\rangle=x_{rr}$,
\[ \Tr X=\sum_r x_{rr}=\sum_r\langle E_{rr}|X\rangle. \]\<close>

corollary Tr_mat_unit_diag:
  assumes "i < n"
  shows "Tr (E\<lbrakk>i,i ; n,n\<rbrakk>) = 1"
  using assms by (simp add: Tr_mat_unit)

corollary Tr_mat_unit_offdiag:
  assumes "i < m" and "j < n" and "i \<noteq> j"
  shows "Tr (E\<lbrakk>i,j ; m,n\<rbrakk>) = 0"
  by (simp add: Tr_mat_unit assms)

lemma Tr_hs_diagonal_sum:
  shows "Tr x =
         (\<Sum>r < dim_row x.
            if r < dim_col x
            then \<langle>\<langle> E\<lbrakk>r,r ; (dim_row x), (dim_col x)\<rbrakk> | x \<rangle>\<rangle>
            else 0)"
  by (smt (verit, ccfv_threshold) Tr_def hs_inner_prod_mat_unit_left lessThan_iff sum.cong)

corollary Tr_hs_diagonal_sum_square:
  assumes rows: "dim_row x = n"
      and cols: "dim_col x = n"
  shows "Tr x = (\<Sum>r<n. \<langle>\<langle> E\<lbrakk>r,r ; n,n\<rbrakk> | x \<rangle>\<rangle>)"
proof -
  have "Tr x = (\<Sum>r<n. x $$ (r,r))"
    using rows cols by (simp add: Tr_def)
  also have "... = (\<Sum>r<n. \<langle>\<langle> E\<lbrakk>r,r ; n,n\<rbrakk> | x \<rangle>\<rangle>)"
    by (intro sum.cong refl, metis cols hs_inner_prod_mat_unit_left lessThan_iff rows)
  finally show ?thesis.
qed

text \<open>The trace is linear.\<close>

lemma Tr_add:
  assumes rows: "dim_row x = dim_row y"
      and cols: "dim_col x = dim_col y"
  shows "Tr (x + y) = Tr x + Tr y"
proof -
  have "Tr (x + y) =
        (\<Sum>r < dim_row x. if r < dim_col x then (x + y) $$ (r,r) else 0)"
    using rows cols by (simp add: Tr_def)
  also have "... =
        (\<Sum>r < dim_row x.
           (if r < dim_col x then x $$ (r,r) else 0) +
           (if r < dim_col x then y $$ (r,r) else 0))"
    by (intro sum.cong refl, simp add: cols rows)
  also have "... =
        (\<Sum>r < dim_row x. if r < dim_col x then x $$ (r,r) else 0) +
        (\<Sum>r < dim_row x. if r < dim_col x then y $$ (r,r) else 0)"
    by (simp add: sum.distrib)
  also have "... = Tr x + Tr y"
    using rows cols by (simp add: Tr_def)
  finally show ?thesis.
qed

lemma Tr_smult: "Tr (a \<cdot>\<^sub>m x) = a * Tr x"
proof -
  have "Tr (a \<cdot>\<^sub>m x) =
        (\<Sum>r < dim_row x. if r < dim_col x then (a \<cdot>\<^sub>m x) $$ (r,r) else 0)"
    by (simp add: Tr_def)
  also have "... =
        (\<Sum>r < dim_row x. a * (if r < dim_col x then x $$ (r,r) else 0))"
    by (intro sum.cong refl) simp
  also have "... =
        a * (\<Sum>r < dim_row x. if r < dim_col x then x $$ (r,r) else 0)"
    by (simp add: sum_distrib_left)
  also have "... = a * Tr x"
    by (simp add: Tr_def)
  finally show ?thesis.
qed

corollary Tr_uminus: "Tr (- x) = - Tr x"
  by (smt (verit, ccfv_threshold) Tr_add add_cancel_right_right add_eq_0_iff carrier_mat_triv 
      index_uminus_mat(2,3) index_zero_mat(2,3)
      right_add_zero_mat uminus_l_inv_mat uminus_uminus_mat)

corollary Tr_diff:
  assumes rows: "dim_row x = dim_row y"
      and cols: "dim_col x = dim_col y"
  shows "Tr (x - y) = Tr x - Tr y"
proof -
  have "Tr (x - y) = Tr (x + (- y))"
    by (metis carrier_mat_triv cols minus_add_uminus_mat rows)
  also have "... = Tr x + Tr (- y)"
    using rows cols by (intro Tr_add) simp_all
  also have "... = Tr x - Tr y"
    by (simp add: Tr_uminus)
  finally show ?thesis.
qed

lemma Tr_zero_mat [simp]:
  shows "Tr (Matrix.mat m n (\<lambda>(r,c). 0)) = 0"
  by (simp add: Tr_def, simp add: sum.neutral)

lemma Tr_dagger:
  fixes M :: "complex Matrix.mat"
  assumes M_c: "M \<in> carrier_mat n n"
  shows "Tr (M\<^sup>\<dagger>) = cnj (Tr M)"
proof -
  have dr: "dim_row M = n" and dc: "dim_col M = n" using M_c by auto
  have d_dr: "dim_row (M\<^sup>\<dagger>) = n" using dc by simp
  have d_dc: "dim_col (M\<^sup>\<dagger>) = n" using dr by simp
  have "Tr (M\<^sup>\<dagger>) = (\<Sum>r<n. (M\<^sup>\<dagger>) $$ (r,r))"
    unfolding Tr_def using d_dr d_dc by simp
  also have "\<dots> = (\<Sum>r<n. cnj (M $$ (r,r)))"
    using dr dc unfolding dagger_def by simp
  also have "\<dots> = cnj (\<Sum>r<n. M $$ (r,r))" by simp
  also have "\<dots> = cnj (Tr M)"
    unfolding Tr_def using dr dc by simp
  finally show ?thesis .
qed

subsection \<open>Matrix-unit algebra and cyclicity of the trace\<close>

text \<open>$E_{ij}^*=E_{ji}$, $E_{ij}E_{kl}=\delta_{jk}E_{il}$, $\Tr(AB)=\Tr(BA)$,
$\Tr(U^*AU)=\Tr(A)$ for unitary $U$, and $\langle A|B\rangle=\Tr(A^*B)$: the facts about the
trace that the notes use from Day 3 onwards.\<close>

lemma mat_unit_dagger:
  shows "(E\<lbrakk>i,j ; m,n\<rbrakk>)\<^sup>\<dagger> = E\<lbrakk>j,i ; n,m\<rbrakk>"
  by (rule eq_matI, simp_all, simp add: dagger_def)

text \<open>Multiplying by a matrix unit selects a row or a column.\<close>

lemma unit_mult_left_entry:
  assumes Bm: "Bm \<in> carrier_mat n m" and r: "r < p" and k: "k < m" and j: "j < n"
  shows "(E\<lbrakk>i,j ; p,n\<rbrakk> * Bm) $$ (r,k) = (if r = i then Bm $$ (j,k) else 0)"
proof -
  have "(E\<lbrakk>i,j ; p,n\<rbrakk> * Bm) $$ (r,k) = (\<Sum>l<n. (if r = i \<and> l = j then 1 else 0) * Bm $$ (l,k))"
    using Bm r k by (simp add: scalar_prod_def mat_unit_def atLeast0LessThan)
  also have "\<dots> = (\<Sum>l<n. if l = j then (if r = i then Bm $$ (l,k) else 0) else 0)"
    by (rule sum.cong) auto
  finally show ?thesis using j by simp
qed

lemma unit_mult_right_entry:
  assumes Cm: "Cm \<in> carrier_mat p n" and r: "r < p" and s: "s < m" and i: "i < n"
  shows "(Cm * E\<lbrakk>i,j ; n,m\<rbrakk>) $$ (r,s) = (if s = j then Cm $$ (r,i) else 0)"
proof -
  have "(Cm * E\<lbrakk>i,j ; n,m\<rbrakk>) $$ (r,s) = (\<Sum>l<n. Cm $$ (r,l) * (if l = i \<and> s = j then 1 else 0))"
    using Cm r s by (simp add: scalar_prod_def mat_unit_def atLeast0LessThan)
  also have "\<dots> = (\<Sum>l<n. if l = i then (if s = j then Cm $$ (r,l) else 0) else 0)"
    by (rule sum.cong) auto
  finally show ?thesis using i by simp
qed

lemma mat_unit_mult_entry:
  assumes r_lt: "r < m" and c_lt: "c < p" and j_lt: "j < n"
  shows "(E\<lbrakk>i,j ; m,n\<rbrakk> * E\<lbrakk>k,l ; n,p\<rbrakk>) $$ (r,c) = (if j = k \<and> r = i \<and> c = l then 1 else 0)"
  using unit_mult_left_entry[OF mat_unit_carrier r_lt c_lt j_lt, of i k l] j_lt c_lt by simp

lemma sandwich_mat_unit_entry:
  assumes V: "V \<in> carrier_mat d n" and W: "W \<in> carrier_mat d n"
      and a: "a < n" and b: "b < n" and i: "i < d" and j: "j < d"
  shows "(V * mat_unit a b n n * (W\<^sup>\<dagger>)) $$ (i, j) = V $$ (i, a) * cnj (W $$ (j, b))"
proof -
  have VE: "(V * mat_unit a b n n) $$ (i, s) = (if s = b then V $$ (i, a) else 0)" if "s < n" for s
    using unit_mult_right_entry[OF V i that a] by simp
  have "(V * mat_unit a b n n * (W\<^sup>\<dagger>)) $$ (i, j)
      = (\<Sum>s<n. (V * mat_unit a b n n) $$ (i, s) * (W\<^sup>\<dagger>) $$ (s, j))"
    using V W i j by (intro mat_mult_entry) (auto simp: mat_unit_def)
  also have "\<dots> = (\<Sum>s<n. if s = b then V $$ (i, a) * cnj (W $$ (j, b)) else 0)"
    using W j by (intro sum.cong refl) (auto simp: VE dagger_def)
  also have "\<dots> = V $$ (i, a) * cnj (W $$ (j, b))" using b by simp
  finally show ?thesis .
qed

text \<open>Writing $A=\sum_{i,j}a_{ij}E_{ij}$ and $B=\sum_{k,l}b_{kl}E_{kl}$, the product rule for matrix
units gives $\Tr(AB)=\sum_{i,j}a_{ij}b_{ji}$, which is symmetric in $A$ and $B$:\<close>

lemma Tr_cyclic:
  assumes AB: "dim_col A = dim_row B"
      and BA: "dim_row A = dim_col B"
  shows "Tr (A * B) = Tr (B * A)"
proof -
  let ?m = "dim_row A"
  let ?n = "dim_col A"

  have "Tr (A * B) = (\<Sum>i<?m. (A * B) $$ (i,i))"
    using AB BA by (simp add: Tr_def)
  also have "... = (\<Sum>i<?m. \<Sum>k<?n. A $$ (i,k) * B $$ (k,i))"
    using AB BA by (intro sum.cong refl, simp)
  also have "... = (\<Sum>k<?n. \<Sum>i<?m. A $$ (i,k) * B $$ (k,i))"
    by (rule sum.swap)
  also have "... = (\<Sum>k<?n. \<Sum>i<?m. B $$ (k,i) * A $$ (i,k))"
  proof (rule sum.cong[OF refl])
    fix k
    assume "k \<in> {..<dim_col A}"
    then have k_lt: "k < ?n"
      by (metis lessThan_iff)

    show "(\<Sum>i<?m. A $$ (i,k) * B $$ (k,i)) =
          (\<Sum>i<?m. B $$ (k,i) * A $$ (i,k))"
      by (metis mult.commute)
  qed
  also have "... = (\<Sum>k<?n. (B * A) $$ (k,k))"
    using AB BA by (intro sum.cong refl, simp add:  mult.commute)
  also have "... = Tr (B * A)"
    using AB BA by (simp add: Tr_def)
  finally show ?thesis.
qed

text \<open>Hence the trace is invariant under unitary conjugation,
$\Tr(U^*AU)=\Tr(AUU^*)=\Tr A$, and the Hilbert--Schmidt inner product is a trace:
$\langle A|B\rangle=\sum_{i,j}\overline{a_{ij}}\,b_{ij}=\Tr(A^*B)$.\<close>

lemma Tr_unitary_conjugation:
  assumes Uu: "unitary U"
      and Arow: "dim_row A = dim_row U"
      and Acol: "dim_col A = dim_row U"
  shows "Tr ((U\<^sup>\<dagger>) * A * U) = Tr(A)"
proof -
  have "Tr ((U\<^sup>\<dagger>) * A * U) = Tr (U * ((U\<^sup>\<dagger>) * A))"
    by (metis Acol Tr_cyclic dim_row_of_dagger index_mult_mat(2,3))
  also have "... = Tr (((1\<^sub>m (dim_row U)) * A))"
    by (smt (verit, ccfv_SIG) Arow Uu assoc_mult_mat carrier_mat_triv dagger_of_dagger_is_id dim_row_of_dagger unitary_def)
  finally show ?thesis
    by (metis Arow left_mult_one_mat')
qed

lemma hs_inner_prod_as_trace:
  assumes rows: "dim_row A = dim_row B"
      and cols: "dim_col A = dim_col B"
  shows "\<langle>\<langle> A | B \<rangle>\<rangle> = Tr ((A\<^sup>\<dagger>) * B)"
proof -
  let ?m = "dim_row A" and ?n = "dim_col A"
  have "\<langle>\<langle> A | B \<rangle>\<rangle> = (\<Sum>i<?m. \<Sum>j<?n. cnj (A $$ (i,j)) * B $$ (i,j))"
    using rows cols by (simp add: hs_inner_prod_def atLeast0LessThan)
  also have "\<dots> = (\<Sum>j<?n. \<Sum>i<?m. cnj (A $$ (i,j)) * B $$ (i,j))"
    by (rule sum.swap)
  also have "\<dots> = (\<Sum>j<?n. (A\<^sup>\<dagger> * B) $$ (j,j))"
  proof (intro sum.cong refl)
    fix j 
    assume "j \<in> {..<?n}"
    then have j_lt: "j < ?n" by simp
    have "(A\<^sup>\<dagger> * B) $$ (j,j) = (\<Sum>i<?m. (A\<^sup>\<dagger>) $$ (j,i) * B $$ (i,j))"
      using j_lt rows cols by simp
    also have "\<dots> = (\<Sum>i<?m. cnj (A $$ (i,j)) * B $$ (i,j))"
      by (intro sum.cong refl, metis dagger_def index_mat(1) j_lt lessThan_iff old.prod.case)
    finally show "(\<Sum>i<?m. cnj (A $$ (i,j)) * B $$ (i,j)) = (A\<^sup>\<dagger> * B) $$ (j,j)"
      by simp
  qed
  also have "\<dots> = Tr (A\<^sup>\<dagger> * B)"
    using rows cols by (simp add: Tr_def)
  finally show ?thesis.
qed

corollary hs_inner_prod_self_as_trace:
  shows "\<langle>\<langle> A | A \<rangle>\<rangle> = Tr ((A\<^sup>\<dagger>) * A)"
  by (rule hs_inner_prod_as_trace) simp_all

text \<open>The trace pairing is non-degenerate: $\Tr(ME_{sr})=m_{rs}$, so if
$\Tr(M\rho)=\Tr(N\rho)$ for every $\rho\in M_n$ then $M=N$.\<close>

lemma Tr_mat_unit_mult:
  fixes M :: "complex Matrix.mat"
  assumes M_c: "M \<in> carrier_mat n n"
      and r_lt: "r < n" and s_lt: "s < n"
  shows "Tr (M * mat_unit s r n n) = M $$ (r, s)"
proof -
  let ?E = "mat_unit s r n n"
  have E_c: "?E \<in> carrier_mat n n" by (simp add: mat_unit_def)
  have ME_c: "M * ?E \<in> carrier_mat n n" using M_c E_c by auto
  \<comment> \<open>Per-entry: \<open>(M * E)$$(i, j) = M$$(i, s)\<close> if \<open>j = r\<close>, else \<open>0\<close>.\<close>
  have ME_idx: "\<And>i j. i < n \<Longrightarrow> j < n \<Longrightarrow>
                    (M * ?E) $$ (i, j) = (if j = r then M $$ (i, s) else 0)"
  proof -
    fix i j assume i_lt: "i < n" and j_lt: "j < n"
    have "(M * ?E) $$ (i, j) = (\<Sum>k = 0..<n. M $$ (i, k) * ?E $$ (k, j))"
      by (rule mat_mult_index_sum[OF M_c E_c i_lt j_lt])
    also have "\<dots> = (\<Sum>k = 0..<n.
                       M $$ (i, k) * (if k = s \<and> j = r then 1 else 0))"
    proof (rule sum.cong[OF refl])
      fix k assume "k \<in> {0..<n}" hence k_lt: "k < n" by simp
      show "M $$ (i, k) * ?E $$ (k, j)
              = M $$ (i, k) * (if k = s \<and> j = r then 1 else 0)"
        using mat_unit_index[OF k_lt j_lt, of s r] by simp
    qed
    also have "\<dots> = (if j = r then M $$ (i, s) else 0)"
    proof (cases "j = r")
      case True
      have "(\<Sum>k = 0..<n.
              M $$ (i, k) * (if k = s \<and> j = r then 1 else 0))
              = (\<Sum>k = 0..<n. if k = s then M $$ (i, k) else 0)"
        using True by (intro sum.cong refl) (auto)
      also have "\<dots> = (if s \<in> {0..<n} then M $$ (i, s) else 0)"
        by (rule sum.delta) simp
      also have "\<dots> = M $$ (i, s)" using s_lt by simp
      finally show ?thesis using True by simp
    next
      case False
      have "(\<Sum>k = 0..<n.
              M $$ (i, k) * (if k = s \<and> j = r then 1 else 0))
              = (\<Sum>k = 0..<n. (0::complex))"
        using False by (intro sum.cong refl) (auto)
      thus ?thesis using False by simp
    qed
    finally show "(M * ?E) $$ (i, j) = (if j = r then M $$ (i, s) else 0)" .
  qed
  \<comment> \<open>\<open>Tr (M * E) = \<Sum>\<^sub>i (M * E)[i, i] = M[r, s]\<close>.\<close>
  have ME_dr: "dim_row (M * ?E) = n" using ME_c by auto
  have ME_dc: "dim_col (M * ?E) = n" using ME_c by auto
  have "Tr (M * ?E) = (\<Sum>i < n. if i < n then (M * ?E) $$ (i, i) else 0)"
    unfolding Tr_def using ME_dr ME_dc by simp
  also have "\<dots> = (\<Sum>i = 0..<n. (M * ?E) $$ (i, i))"
    by (simp add: lessThan_atLeast0)
  also have "\<dots> = (\<Sum>i = 0..<n. if i = r then M $$ (i, s) else 0)"
    by (rule sum.cong[OF refl]) (auto simp: ME_idx)
  also have "\<dots> = (if r \<in> {0..<n} then M $$ (r, s) else 0)"
    by (rule sum.delta) simp
  also have "\<dots> = M $$ (r, s)" using r_lt by simp
  finally show ?thesis .
qed

lemma mat_trace_pairing_unique:
  fixes M N :: "complex Matrix.mat"
  assumes M_c: "M \<in> carrier_mat n n"
      and N_c: "N \<in> carrier_mat n n"
      and pair_eq: "\<And>rho. rho \<in> carrier_mat n n \<Longrightarrow> Tr (M * rho) = Tr (N * rho)"
  shows "M = N"
proof (rule eq_matI)
  show "dim_row M = dim_row N" using M_c N_c by auto
  show "dim_col M = dim_col N" using M_c N_c by auto
  fix r c assume r_a: "r < dim_row N" and c_a: "c < dim_col N"
  hence r_lt: "r < n" and c_lt: "c < n" using N_c by auto
  let ?E = "mat_unit c r n n"
  have E_c: "?E \<in> carrier_mat n n" by (simp add: mat_unit_def)
  have "M $$ (r, c) = Tr (M * ?E)"
    using Tr_mat_unit_mult[OF M_c r_lt c_lt] by simp
  also have "\<dots> = Tr (N * ?E)" using pair_eq[OF E_c] .
  also have "\<dots> = N $$ (r, c)"
    using Tr_mat_unit_mult[OF N_c r_lt c_lt] by simp
  finally show "M $$ (r, c) = N $$ (r, c)" .
qed

subsection \<open>Orthogonal projections and Parseval's identity\<close>

text \<open>\begin{notesdef}[Orthogonal projections]
Let $V\subseteq\C^n$ be a subspace with orthonormal basis $\{v_1,\dots,v_k\}$ and put
$P=\sum_{i=1}^k\ketbra{v_i}{v_i}$.  Then $Px=\sum_i\braket{v_i}{x}v_i\in V$ and
$x-Px\perp V$, so every $x\in\C^n$ is uniquely $x=v+w$ with $v\in V$ and $w\in V^\perp$.
Consequently $P$ does not depend on the orthonormal basis chosen for $V$, $Pv=v$ for
$v\in V$, $P^2=P$ and $P=P^*$: $P$ is \emph{the} orthogonal projection onto $V$.
\end{notesdef}

\begin{notestheorem}[Parseval]
If $\{v_1,\dots,v_k\}$ is an orthonormal basis of $V$ and $v\in V$, then
$\norm{v}^2=\sum_{i=1}^k|\braket{v_i}{v}|^2$.  For $V=\C^n$ this holds for every $v$.
\end{notestheorem}

\begin{notestheorem}
If $P\in M_n$ satisfies $P^2=P$ and $P=P^*$, and $V=\range(P)$, then $P$ is the orthogonal
projection onto $V$.
\end{notestheorem}

Formally, an orthonormal list \<open>vs\<close> of vectors in $\C^n$ is \<^term>\<open>orthonormal_list n vs\<close>,
the matrix with columns $v_1,\dots,v_k$ is \<^term>\<open>mat_of_cols n vs\<close>, and
$P=\sum_i\ketbra{v_i}{v_i}=VV^\dagger$ is \<^term>\<open>outer_sum n vs\<close>.  The results below are the
projection formula, $V^\dagger V=I_k$, the completeness relation $VV^\dagger=I_n$ for a full
basis, $P=P^\dagger$, $P^2=P$, Parseval, the orthogonality of the residual, and the uniqueness
of the decomposition.  Independence of $P$ from the basis is \<open>outer_sum_basis_independent\<close> below; the
characterisation of Hermitian idempotents as orthogonal projections needs Hermitian matrices and
is \<open>projection_annihilates_orthogonal\<close> on Day 4.\<close>

text \<open>The outer product $\ketbra vw=v\,w^*$ of Dirac's notation; the formal text writes it \<open>v \<oslash> w\<close>.\<close>

abbreviation outer_prod :: "complex Matrix.vec \<Rightarrow> complex Matrix.vec \<Rightarrow> complex Matrix.mat"
    (infixr "\<oslash>" 75)
  where "v \<oslash> w \<equiv> |v\<rangle> * bra_vec w"

lemma bra_vec_index_0:
  assumes j: "j < dim_vec w"
  shows "bra_vec w $$ (0,j) = cnj (w $ j)"
  using j by (simp add: bra_vec_def row_vec_def cpx_mat_cnj_def)

text \<open>$\ketbra vw=v\,w^*$ has entries $v_i\overline{w_j}$ and sends every vector to a multiple of
$v$: $\ketbra vw\,x=\braket wx\,v$.\<close>

lemma outer_prod_index:
  fixes v w :: "complex Matrix.vec"
  assumes i: "i < dim_vec v"
      and j: "j < dim_vec w"
  shows "(v \<oslash> w) $$ (i,j) = (v $ i) * cnj (w $ j)"
proof -
  have row_index_0: "Matrix.row (ket_vec v) i $ 0 = v $ i"
    using i by (simp add: Matrix.row_def ket_vec_def)
  have bra_rows: "dim_row (bra_vec w) = 1"
    by (simp add: bra_vec_def row_vec_def cpx_mat_cnj_def)
  have ket_rows: "dim_row (ket_vec v) = dim_vec v"
    by (simp add: ket_vec_def)
  have bra_cols: "dim_col (bra_vec w) = dim_vec w"
    by (simp add: bra_vec_def row_vec_def cpx_mat_cnj_def)
  have col_index_0: "Matrix.col (bra_vec w) j $ 0 = cnj (w $ j)"
    using j bra_rows by (simp add: Matrix.col_def bra_vec_index_0)

  have "(ket_vec v * bra_vec w) $$ (i,j) =
        Matrix.row (ket_vec v) i \<bullet> Matrix.col (bra_vec w) j"
    by (rule index_mult_mat(1)) (use i j ket_rows bra_cols in auto)
  also have "\<dots> = (\<Sum>k<1. Matrix.row (ket_vec v) i $ k * Matrix.col (bra_vec w) j $ k)"
    using bra_rows by (simp add: scalar_prod_def lessThan_atLeast0)
  also have "\<dots> = Matrix.row (ket_vec v) i $ 0 * Matrix.col (bra_vec w) j $ 0"
    by simp
  also have "\<dots> = (v $ i) * cnj (w $ j)"
    using row_index_0 col_index_0 by simp
  finally show ?thesis .
qed

lemma outer_prod_mult_vec_index:
  fixes v w x :: "complex Matrix.vec"
  assumes xdim: "dim_vec x = dim_vec w"
      and i: "i < dim_vec v"
  shows "((v \<oslash> w) *\<^sub>v x) $ i = (v $ i) * \<langle>w | x\<rangle>"
proof -
  have ket_rows: "dim_row (ket_vec v) = dim_vec v"
    by (simp add: ket_vec_def)
  have bra_cols: "dim_col (bra_vec w) = dim_vec w"
    by (simp add: bra_vec_def row_vec_def cpx_mat_cnj_def)
  have prod_rows: "dim_row (ket_vec v * bra_vec w) = dim_vec v"
    using ket_rows by simp

  have "((ket_vec v * bra_vec w) *\<^sub>v x) $ i =
        Matrix.row (ket_vec v * bra_vec w) i \<bullet> x"
    by (rule index_mult_mat_vec) (use i prod_rows in auto)
  also have "\<dots> =
        (\<Sum>j<dim_vec w. (v $ i * cnj (w $ j)) * (x $ j))"
  proof -
    have "\<And>j. j < dim_vec w \<Longrightarrow>
          Matrix.row (ket_vec v * bra_vec w) i $ j = v $ i * cnj (w $ j)"
      using i bra_cols by (simp add: Matrix.row_def outer_prod_index)
    then show ?thesis
      using xdim by (simp add: scalar_prod_def lessThan_atLeast0)
  qed
  also have "\<dots> = (v $ i) * (\<Sum>j<dim_vec w. cnj (w $ j) * (x $ j))"
    by (simp add: sum_distrib_left algebra_simps)
  also have "\<dots> = (v $ i) * \<langle>w | x\<rangle>"
    using xdim by (simp add: inner_prod_def lessThan_atLeast0)
  finally show ?thesis .
qed

lemma outer_prod_mult_vec:
  fixes v w x :: "complex Matrix.vec"
  assumes xdim: "dim_vec x = dim_vec w"
  shows "(v \<oslash> w) *\<^sub>v x = \<langle>w | x\<rangle> \<cdot>\<^sub>v v"
proof (rule eq_vecI)
  show "dim_vec ((v \<oslash> w) *\<^sub>v x) = dim_vec (\<langle>w | x\<rangle> \<cdot>\<^sub>v v)"
    by (simp add: ket_vec_def)
next
  fix i
  assume i: "i < dim_vec (\<langle>w | x\<rangle> \<cdot>\<^sub>v v)"
  then have iv: "i < dim_vec v"
    by simp
  have "((v \<oslash> w) *\<^sub>v x) $ i = (v $ i) * \<langle>w | x\<rangle>"
    using outer_prod_mult_vec_index[OF xdim iv] .
  also have "\<dots> = (\<langle>w | x\<rangle> \<cdot>\<^sub>v v) $ i"
    using iv by (simp add: algebra_simps)
  finally show "((v \<oslash> w) *\<^sub>v x) $ i = (\<langle>w | x\<rangle> \<cdot>\<^sub>v v) $ i" .
qed

lemma outer_prod_carrier:
  fixes v w :: "complex Matrix.vec"
  assumes "dim_vec v = n" and "dim_vec w = m"
  shows "v \<oslash> w \<in> carrier_mat n m"
  using assms by (simp add: ket_vec_def bra_vec_def cpx_mat_cnj_def row_vec_def carrier_matI)

text \<open>$\ketbra ww$ is idempotent for a unit vector $w$: $(ww^*)(ww^*)=w(w^*w)w^*$.\<close>

lemma outer_prod_idempotent:
  fixes w :: "complex Matrix.vec"
  assumes "\<parallel>w\<parallel> = 1"
  shows "(w \<oslash> w) * (w \<oslash> w) = w \<oslash> w"
proof (rule eq_matI)
  let ?n = "dim_vec w"
  have P: "w \<oslash> w \<in> carrier_mat ?n ?n" by (rule outer_prod_carrier) simp_all
  have one: "\<langle>w|w\<rangle> = 1" using assms by (simp flip: cpx_vec_length_inner_prod)
  fix i j assume "i < dim_row (w \<oslash> w)" "j < dim_col (w \<oslash> w)"
  hence i: "i < ?n" and j: "j < ?n" using P by auto
  have "((w \<oslash> w) * (w \<oslash> w)) $$ (i, j) = (\<Sum>k<?n. (w $ i * cnj (w $ j)) * (cnj (w $ k) * w $ k))"
    by (simp only: mat_mult_entry[OF P P i j]) (intro sum.cong refl, simp add: outer_prod_index i j mult_ac)
  also have "\<dots> = w $ i * cnj (w $ j) * (\<Sum>k<?n. cnj (w $ k) * w $ k)" by (simp add: sum_distrib_left)
  also have "(\<Sum>k<?n. cnj (w $ k) * w $ k) = \<langle>w|w\<rangle>"
    by (simp only: inner_prod_sum[OF refl refl] atLeast0LessThan)
  finally show "((w \<oslash> w) * (w \<oslash> w)) $$ (i, j) = (w \<oslash> w) $$ (i, j)"
    using one i j by (simp add: outer_prod_index)
qed (use outer_prod_carrier[of w "dim_vec w" w "dim_vec w"] in auto)

text \<open>Conjugating a rank-one matrix: $W|\varphi\rangle\langle\varphi|W^*=|W\varphi\rangle\langle W\varphi|$.\<close>

lemma conj_outer_prod:
  fixes W :: "complex Matrix.mat" and \<phi> :: "complex Matrix.vec"
  assumes Wc: "W \<in> carrier_mat m n" and \<phi>d: "dim_vec \<phi> = n"
  shows "W * (\<phi> \<oslash> \<phi>) * (W\<^sup>\<dagger>) = (W *\<^sub>v \<phi>) \<oslash> (W *\<^sub>v \<phi>)"
proof -
  define M where "M = \<phi> \<oslash> \<phi>"
  define R where "R = (W *\<^sub>v \<phi>) \<oslash> (W *\<^sub>v \<phi>)"
  have Mc: "M \<in> carrier_mat n n" unfolding M_def by (rule outer_prod_carrier[OF \<phi>d \<phi>d])
  have Me: "\<And>k l. k < n \<Longrightarrow> l < n \<Longrightarrow> M $$ (k,l) = \<phi> $ k * cnj (\<phi> $ l)"
    unfolding M_def using \<phi>d by (intro outer_prod_index) auto
  have Wdc: "W\<^sup>\<dagger> \<in> carrier_mat n m" by (rule dagger_carrier[OF Wc])
  have W\<phi>d: "dim_vec (W *\<^sub>v \<phi>) = m" using Wc by simp
  have Rc: "R \<in> carrier_mat m m" unfolding R_def by (rule outer_prod_carrier[OF W\<phi>d W\<phi>d])
  have Re: "\<And>i j. i < m \<Longrightarrow> j < m \<Longrightarrow> R $$ (i,j) = (W *\<^sub>v \<phi>) $ i * cnj ((W *\<^sub>v \<phi>) $ j)"
    unfolding R_def using W\<phi>d by (intro outer_prod_index) auto
  have WMc: "W * M \<in> carrier_mat m n" using Wc Mc by simp
  have "W * M * (W\<^sup>\<dagger>) = R"
  proof (rule eq_matI)
    fix i j assume "i < dim_row R" "j < dim_col R"
    hence i: "i < m" and j: "j < m" using carrier_matD[OF Rc] by auto
    have inner: "\<And>l. l < n \<Longrightarrow> (W * M) $$ (i,l) = (\<Sum>k<n. W $$ (i,k) * \<phi> $ k) * cnj (\<phi> $ l)"
    proof -
      fix l assume l: "l < n"
      have "(W * M) $$ (i,l) = (\<Sum>k<n. W $$ (i,k) * M $$ (k,l))"
        using i l carrier_matD[OF Wc] carrier_matD[OF Mc] by (simp add: scalar_prod_def atLeast0LessThan)
      also have "\<dots> = (\<Sum>k<n. W $$ (i,k) * (\<phi> $ k * cnj (\<phi> $ l)))"
        using l by (intro sum.cong refl) (simp add: Me)
      also have "\<dots> = (\<Sum>k<n. W $$ (i,k) * \<phi> $ k) * cnj (\<phi> $ l)"
        by (simp add: sum_distrib_right mult_ac(1))
      finally show "(W * M) $$ (i,l) = (\<Sum>k<n. W $$ (i,k) * \<phi> $ k) * cnj (\<phi> $ l)" .
    qed
    have "(W * M * (W\<^sup>\<dagger>)) $$ (i,j) = (\<Sum>l<n. (W * M) $$ (i,l) * cnj (W $$ (j,l)))"
      using i j carrier_matD[OF WMc] carrier_matD[OF Wdc] carrier_matD[OF Wc]
      by (simp add: scalar_prod_def dagger_def atLeast0LessThan)
    also have "\<dots> = (\<Sum>l<n. (\<Sum>k<n. W $$ (i,k) * \<phi> $ k) * (cnj (\<phi> $ l) * cnj (W $$ (j,l))))"
      by (intro sum.cong refl) (simp add: inner mult_ac(1))
    also have "\<dots> = (\<Sum>k<n. W $$ (i,k) * \<phi> $ k) * (\<Sum>l<n. cnj (W $$ (j,l) * \<phi> $ l))"
      by (simp add: sum_distrib_left mult.commute)
    also have "\<dots> = (W *\<^sub>v \<phi>) $ i * cnj ((W *\<^sub>v \<phi>) $ j)"
      using i j carrier_matD[OF Wc] \<phi>d by (simp add: scalar_prod_def atLeast0LessThan)
    also have "\<dots> = R $$ (i,j)" by (rule Re[OF i j, symmetric])
    finally show "(W * M * (W\<^sup>\<dagger>)) $$ (i,j) = R $$ (i,j)" .
  next
    show "dim_row (W * M * (W\<^sup>\<dagger>)) = dim_row R" using carrier_matD[OF Wc] carrier_matD[OF Rc] by simp
    show "dim_col (W * M * (W\<^sup>\<dagger>)) = dim_col R" using carrier_matD[OF Wdc] carrier_matD[OF Rc] by simp
  qed
  thus ?thesis unfolding M_def R_def .
qed

lemma outer_prod_zero_vec: "(0\<^sub>v n :: complex Matrix.vec) \<oslash> (0\<^sub>v n) = 0\<^sub>m n n"
proof (rule eq_matI)
  have c: "(0\<^sub>v n :: complex Matrix.vec) \<oslash> (0\<^sub>v n) \<in> carrier_mat n n" by (rule outer_prod_carrier) simp_all
  fix i j assume "i < dim_row (0\<^sub>m n n :: complex Matrix.mat)" "j < dim_col (0\<^sub>m n n :: complex Matrix.mat)"
  hence "i < n" "j < n" by simp_all
  thus "((0\<^sub>v n :: complex Matrix.vec) \<oslash> (0\<^sub>v n)) $$ (i,j) = (0\<^sub>m n n :: complex Matrix.mat) $$ (i,j)"
    by (simp add: outer_prod_index)
qed (use carrier_matD[OF outer_prod_carrier[of "0\<^sub>v n :: complex Matrix.vec" n "0\<^sub>v n" n]] in auto)

definition orthonormal_list :: "nat \<Rightarrow> complex Matrix.vec list \<Rightarrow> bool" where
  "orthonormal_list n vs \<equiv>
     (\<forall>v \<in> set vs. dim_vec v = n) \<and>
     (\<forall>i < length vs. \<forall>j < length vs.
        \<langle>vs ! i | vs ! j\<rangle> = (if i = j then 1 else 0))"

lemma orthonormal_listD_dim:
  assumes "orthonormal_list n vs" and "i < length vs"
  shows "dim_vec (vs ! i) = n"
  using assms by (simp add: orthonormal_list_def)

lemma orthonormal_listD_inner:
  assumes "orthonormal_list n vs" and "i < length vs" and "j < length vs"
  shows "\<langle>vs ! i | vs ! j\<rangle> = (if i = j then 1 else 0)"
  using assms by (simp add: orthonormal_list_def, force)

lemma orthonormal_listD_carrier:
  assumes "orthonormal_list n vs"
  shows "set vs \<subseteq> carrier_vec n"
  using assms orthonormal_list_def by auto

definition outer_sum :: "nat \<Rightarrow> complex Matrix.vec list \<Rightarrow> complex Matrix.mat" where
  "outer_sum n vs = mat_of_cols n vs * ((mat_of_cols n vs)\<^sup>\<dagger>)"

lemma outer_sum_dim_row [simp]: "dim_row (outer_sum n vs) = n"
  by (simp add: outer_sum_def)

lemma outer_sum_dim_col [simp]: "dim_col (outer_sum n vs) = n"
  by (simp add: outer_sum_def)

text \<open>$P=VV^*$ is Hermitian, and orthonormality of the columns is $V^*V=I_k$, entry by
entry $(V^*V)_{ij}=\braket{v_i}{v_j}=\delta_{ij}$.\<close>

lemma outer_sum_hermitian:
  shows "(outer_sum n vs)\<^sup>\<dagger> = outer_sum n vs"
  unfolding outer_sum_def
  by (simp add: dagger_of_prod dagger_of_dagger_is_id)

lemma cols_mat_dagger_left:
  assumes orth: "orthonormal_list n vs"
  shows "(mat_of_cols n vs)\<^sup>\<dagger> * (mat_of_cols n vs) = 1\<^sub>m (length vs)"
proof (rule eq_matI)
  let ?V = "mat_of_cols n vs"
  let ?k = "length vs"
  show "dim_row (?V\<^sup>\<dagger> * ?V) = dim_row (1\<^sub>m ?k)" by simp
  show "dim_col (?V\<^sup>\<dagger> * ?V) = dim_col (1\<^sub>m ?k)" by simp
  fix l1 l2
  assume "l1 < dim_row (1\<^sub>m ?k)" and "l2 < dim_col (1\<^sub>m ?k)"
  then have l12: "l1 < ?k" "l2 < ?k" by simp_all

  have dim1: "dim_vec (vs ! l1) = n" using orth l12(1) by (simp add: orthonormal_listD_dim)
  have dim2: "dim_vec (vs ! l2) = n" using orth l12(2) by (simp add: orthonormal_listD_dim)

  have "(?V\<^sup>\<dagger> * ?V) $$ (l1,l2) = (\<Sum>i<n. (?V\<^sup>\<dagger>) $$ (l1,i) * ?V $$ (i,l2))"
    using l12 by simp
  also have "\<dots> = (\<Sum>i<n. cnj ((vs ! l1) $ i) * (vs ! l2) $ i)"
    using l12 dim1 dim2 by (intro sum.cong refl)
       (simp add: dagger_def mat_of_cols_def)
  also have "\<dots> = \<langle>vs ! l1 | vs ! l2\<rangle>"
    using dim1 dim2 by (simp add: inner_prod_def atLeast0LessThan)
  also have "\<dots> = (if l1 = l2 then 1 else 0)"
    using orth l12 by (simp add: orthonormal_listD_inner)
  also have "\<dots> = (1\<^sub>m ?k) $$ (l1,l2)"
    using l12 by simp
  finally show "(?V\<^sup>\<dagger> * ?V) $$ (l1,l2) = (1\<^sub>m ?k) $$ (l1,l2)" .
qed

lemma cols_mat_dagger_right:
  assumes orth: "orthonormal_list n vs"
      and full: "length vs = n"
  shows "(mat_of_cols n vs) * ((mat_of_cols n vs)\<^sup>\<dagger>) = 1\<^sub>m n"
proof -
  let ?V = "mat_of_cols n vs"
  have left: "?V\<^sup>\<dagger> * ?V = 1\<^sub>m n"
    using cols_mat_dagger_left[OF orth] full by simp
  then have "inverts_mat (?V\<^sup>\<dagger>) ?V"
    by (simp add: full inverts_mat_def)
  then have "inverts_mat ?V (?V\<^sup>\<dagger>)"
    by (metis dim_col_of_dagger full inverts_mat_sym
        mat_of_cols_carrier(2,3) square_mat.elims(3))
  then show ?thesis
    by (simp add: inverts_mat_def full)
qed

text \<open>For a full basis ($k=n$) $V$ is square, so $V^*V=I$ forces $VV^*=I$ as well.  Entrywise
this is the completeness relation
\[ \sum_{l}(v_l)_i\,\overline{(v_l)_j}=\delta_{ij}. \]\<close>

lemma completeness_relation:
  assumes orth: "orthonormal_list n vs"
      and full: "length vs = n"
      and i_lt: "i < n" and j_lt: "j < n"
  shows "(\<Sum>l<n. (vs ! l) $ i * cnj ((vs ! l) $ j)) = (if i = j then 1 else 0)"
proof -
  let ?V = "mat_of_cols n vs"
  have "(?V * (?V\<^sup>\<dagger>)) $$ (i,j) = (\<Sum>l<n. ?V $$ (i,l) * (?V\<^sup>\<dagger>) $$ (l,j))"
    using i_lt j_lt full by simp
  also have "\<dots> = (\<Sum>l<n. (vs ! l) $ i * cnj ((vs ! l) $ j))"
    using i_lt j_lt full
    by (intro sum.cong refl, simp add: mat_of_cols_def dagger_def orthonormal_listD_dim[OF orth])
  finally have sum_eq: "(\<Sum>l<n. (vs ! l) $ i * cnj ((vs ! l) $ j)) = (?V * (?V\<^sup>\<dagger>)) $$ (i,j)"
    by simp
  also have "(?V * (?V\<^sup>\<dagger>)) $$ (i,j) = (1\<^sub>m n) $$ (i,j)"
    by (simp add: cols_mat_dagger_right full orth)
  also have "\<dots> = (if i = j then 1 else 0)"
    using i_lt j_lt by simp
  finally show ?thesis using sum_eq by simp
qed

lemma outer_sum_index:
  assumes orth: "orthonormal_list n vs"
      and i_lt: "i < n" and j_lt: "j < n"
  shows "(outer_sum n vs) $$ (i,j) = 
         (\<Sum>l < length vs. (vs ! l) $ i * cnj ((vs ! l) $ j))"
proof -
  let ?V = "mat_of_cols n vs"
  let ?k = "length vs"
  have "(outer_sum n vs) $$ (i,j) = (?V * (?V\<^sup>\<dagger>)) $$ (i,j)"
    by (simp add: outer_sum_def)
  also have "\<dots> = (\<Sum>l<?k. ?V $$ (i,l) * (?V\<^sup>\<dagger>) $$ (l,j))"
    using i_lt j_lt by (simp add: outer_sum_def)
  also have "\<dots> = (\<Sum>l<?k. (vs ! l) $ i * cnj ((vs ! l) $ j))"
    using i_lt j_lt
    by (intro sum.cong refl)
       (simp add: mat_of_cols_def dagger_def orthonormal_listD_dim[OF orth])
  finally show ?thesis.
qed

text \<open>$P$ acts by $Px=\sum_l\braket{v_l}{x}\,v_l$, and $P^2=V(V^*V)V^*=VV^*=P$.\<close>

lemma outer_sum_apply:
  assumes orth: "orthonormal_list n vs"
      and xdim: "dim_vec x = n"
      and i_lt: "i < n"
  shows "(outer_sum n vs *\<^sub>v x) $ i =  (\<Sum>l < length vs. \<langle>vs ! l | x\<rangle> * (vs ! l) $ i)"
proof -
  let ?V = "mat_of_cols n vs"
  let ?k = "length vs"
  have "(outer_sum n vs *\<^sub>v x) $ i = Matrix.row (outer_sum n vs) i \<bullet> x"
    using i_lt xdim by simp
  also have "\<dots> = (\<Sum>j<n. (outer_sum n vs) $$ (i,j) * x $ j)"
    using i_lt xdim  lessThan_atLeast0 by (simp add: scalar_prod_def)
  also have "\<dots> = (\<Sum>j<n. (\<Sum>l<?k. (vs ! l) $ i * cnj ((vs ! l) $ j)) * x $ j)"
    by (intro sum.cong refl, simp add: outer_sum_index[OF orth i_lt])
  also have "\<dots> = (\<Sum>j<n. \<Sum>l<?k. (vs ! l) $ i * cnj ((vs ! l) $ j) * x $ j)"
    by (intro sum.cong refl) (simp add: sum_distrib_right)
  also have "\<dots> = (\<Sum>l<?k. \<Sum>j<n. (vs ! l) $ i * cnj ((vs ! l) $ j) * x $ j)"
    by (rule sum.swap)
  also have "\<dots> = (\<Sum>l<?k. (vs ! l) $ i * (\<Sum>j<n. cnj ((vs ! l) $ j) * x $ j))"
    by (intro sum.cong refl, 
        metis (mono_tags, lifting) semigroup_mult_class.mult.assoc sum.cong sum_distrib_left)
  also have "\<dots> = (\<Sum>l<?k. (vs ! l) $ i * \<langle>vs ! l | x\<rangle>)"
    using atLeast0LessThan inner_prod_def xdim by (intro sum.cong refl, presburger)   
  also have "\<dots> = (\<Sum>l<?k. \<langle>vs ! l | x\<rangle> * (vs ! l) $ i)"
    by (intro sum.cong refl) (simp add: mult.commute)
  finally show ?thesis.
qed

lemma outer_sum_idempotent:
  assumes orth: "orthonormal_list n vs"
  shows "outer_sum n vs * outer_sum n vs = outer_sum n vs"
proof -
  let ?V = "mat_of_cols n vs"
  let ?k = "length vs"

  have "outer_sum n vs * outer_sum n vs = (?V * (?V\<^sup>\<dagger>)) * (?V * (?V\<^sup>\<dagger>))"
    by (simp add: outer_sum_def)
  also have "\<dots> = ?V * ((?V\<^sup>\<dagger>) * ?V) * (?V\<^sup>\<dagger>)"
    by (metis (no_types, lifting) assoc_mult_mat carrier_mat_triv dim_col_of_dagger 
        dim_row_of_dagger mat_of_cols_carrier(2) outer_sum_def outer_sum_dim_col)
  also have "\<dots> = ?V * (1\<^sub>m ?k) * (?V\<^sup>\<dagger>)"
    using cols_mat_dagger_left[OF orth] by simp
  also have "\<dots> = ?V * (?V\<^sup>\<dagger>)"
    by simp
  also have "\<dots> = outer_sum n vs"
    by (simp add: outer_sum_def)
  finally show ?thesis .
qed

text \<open>For a full basis $P=I$, so each vector is its own expansion $v=\sum_l\braket{v_l}{v}\,v_l$;
taking $\braket{v}{\cdot}$ gives Parseval, $\norm{v}^2=\sum_l|\braket{v_l}{v}|^2$.\<close>

lemma parseval:
  assumes orth: "orthonormal_list n vs"
      and full: "length vs = n"
      and vdim: "dim_vec v = n"
      and i_lt: "i < n"
  shows "v $ i = (\<Sum>l<n. \<langle>vs ! l | v\<rangle> * (vs ! l) $ i)"
proof -
  have "(\<Sum>l<n. \<langle>vs ! l | v\<rangle> * (vs ! l) $ i) =
        (\<Sum>l<n. (\<Sum>j<n. cnj ((vs ! l) $ j) * v $ j) * (vs ! l) $ i)"
    using atLeast0LessThan inner_prod_def vdim by (intro sum.cong refl, simp)   
  also have "\<dots> = (\<Sum>l<n. \<Sum>j<n. cnj ((vs ! l) $ j) * v $ j * (vs ! l) $ i)"
    by (intro sum.cong refl, simp add: sum_distrib_right)
  also have "\<dots> = (\<Sum>j<n. \<Sum>l<n. cnj ((vs ! l) $ j) * v $ j * (vs ! l) $ i)"
    by (rule sum.swap)
  also have "\<dots> = (\<Sum>j<n. v $ j * (\<Sum>l<n. (vs ! l) $ i * cnj ((vs ! l) $ j)))"
    by (intro sum.cong refl)
       (simp add: sum_distrib_left mult.assoc mult.commute mult.left_commute)
  also have "\<dots> = (\<Sum>j<n. v $ j * (if i = j then 1 else 0))"
    using orth full i_lt by (intro sum.cong refl, simp add: completeness_relation)
  also have "... = (\<Sum>j<n. if j = i then v $ j else 0)"
    by (intro sum.cong refl) auto
  also have "\<dots> = v $ i"
    using i_lt by simp
  finally show ?thesis 
    by simp
qed

corollary parseval_norm:
  assumes orth: "orthonormal_list n vs"
      and full: "length vs = n"
      and vdim: "dim_vec v = n"
  shows "\<parallel>v\<parallel>\<^sup>2 = (\<Sum>l<n. (cmod (\<langle>vs ! l | v\<rangle>))\<^sup>2)"
proof -
  have "\<parallel>v\<parallel>\<^sup>2 = \<langle>v|v\<rangle>"
    using cpx_vec_length_inner_prod by presburger
  also have "\<dots> = (\<Sum>i<n. cnj (v $ i) * v $ i)"
    using vdim by (simp add: inner_prod_def atLeast0LessThan)
  also have "\<dots> = (\<Sum>i<n. cnj (v $ i) * (\<Sum>l<n. \<langle>vs ! l | v\<rangle> * (vs ! l) $ i))"
    using orth full vdim by (intro sum.cong refl arg_cong[where f = "\<lambda>s. cnj (v $ _) * s"], 
        simp add: parseval) 
  also have "\<dots> = (\<Sum>i<n. \<Sum>l<n. cnj (v $ i) * (\<langle>vs ! l | v\<rangle> * (vs ! l) $ i))"
    by (intro sum.cong refl) (simp add: sum_distrib_left)
  also have "\<dots> = (\<Sum>i<n. \<Sum>l<n. \<langle>vs ! l | v\<rangle> * (cnj (v $ i) * (vs ! l) $ i))"
    by (intro sum.cong refl, simp add: mult.assoc mult.commute mult.left_commute)
  also have "\<dots> = (\<Sum>l<n. \<Sum>i<n. \<langle>vs ! l | v\<rangle> * (cnj (v $ i) * (vs ! l) $ i))"
    by (rule sum.swap)
  also have "\<dots> = (\<Sum>l<n. \<langle>vs ! l | v\<rangle> * (\<Sum>i<n. cnj (v $ i) * (vs ! l) $ i))"
    by (intro sum.cong refl) (simp add: sum_distrib_left)
  also have "\<dots> = (\<Sum>l<n. \<langle>vs ! l | v\<rangle> * \<langle>v | vs ! l\<rangle>)"
    using atLeast0LessThan full inner_prod_def orth orthonormal_listD_dim by force
  also have "\<dots> = (\<Sum>l<n. \<langle>vs ! l | v\<rangle> * cnj (\<langle>vs ! l | v\<rangle>))"
    by (simp add: full inner_prod_cnj orth orthonormal_listD_dim vdim)    
  also have "\<dots> = (\<Sum>l<n. (cmod (\<langle>vs ! l | v\<rangle>))\<^sup>2)"
    using complex_norm_square by force
  finally show ?thesis
    by (meson of_real_eq_iff) 
qed

text \<open>The residual $x-Px$ is orthogonal to every $v_l$, because
$\braket{v_l}{Px}=\braket{v_l}{x}$; hence the orthogonal decomposition $x=Px+(x-Px)$.\<close>

lemma inner_prod_outer_sum:
  assumes orth: "orthonormal_list n vs"
      and xdim: "dim_vec x = n"
      and l_lt: "l < length vs"
  shows "\<langle>vs ! l | outer_sum n vs *\<^sub>v x\<rangle> = \<langle>vs ! l | x\<rangle>"
proof -
  let ?k = "length vs"
  have ldim: "dim_vec (vs ! l) = n" 
    using orth l_lt by (simp add: orthonormal_listD_dim)
  have Pdim: "dim_vec (outer_sum n vs *\<^sub>v x) = n" 
    using xdim by simp
  have "\<langle>vs ! l | outer_sum n vs *\<^sub>v x\<rangle> = (\<Sum>i<n. cnj ((vs ! l) $ i) * (outer_sum n vs *\<^sub>v x) $ i)"
    using ldim Pdim by (simp add: inner_prod_def atLeast0LessThan)
  also have "\<dots> = (\<Sum>i<n. cnj ((vs ! l) $ i) * (\<Sum>m<?k. \<langle>vs ! m | x\<rangle> * (vs ! m) $ i))"
    using orth xdim outer_sum_apply 
    by(intro sum.cong refl arg_cong[where f = "\<lambda>s. cnj _ * s"], auto)
  also have "\<dots> = (\<Sum>i<n. \<Sum>m<?k. cnj ((vs ! l) $ i) * (\<langle>vs ! m | x\<rangle> * (vs ! m) $ i))"
    by (intro sum.cong refl) (simp add: sum_distrib_left)
  also have "\<dots> = (\<Sum>i<n. \<Sum>m<?k. \<langle>vs ! m | x\<rangle> * (cnj ((vs ! l) $ i) * (vs ! m) $ i))"
    by (intro sum.cong refl, simp add: mult.assoc mult.commute mult.left_commute)
  also have "\<dots> = (\<Sum>m<?k. \<Sum>i<n. \<langle>vs ! m | x\<rangle> * (cnj ((vs ! l) $ i) * (vs ! m) $ i))"
    by (rule sum.swap)
  also have "\<dots> = (\<Sum>m<?k. \<langle>vs ! m | x\<rangle> * (\<Sum>i<n. cnj ((vs ! l) $ i) * (vs ! m) $ i))"
    by (intro sum.cong refl, simp add: sum_distrib_left)
  also have "\<dots> = (\<Sum>m<?k. \<langle>vs ! m | x\<rangle> * \<langle>vs ! l | vs ! m\<rangle>)"
    using atLeast0LessThan inner_prod_def orth orthonormal_listD_dim by auto    
  also have "\<dots> = (\<Sum>m<?k. \<langle>vs ! m | x\<rangle> * (if l = m then 1 else 0))"
    using orth l_lt by (intro sum.cong refl, simp add: orthonormal_listD_inner)
  also have "\<dots> = (\<Sum>m<?k. if m = l then \<langle>vs ! m | x\<rangle> else 0)"
    by (intro sum.cong refl) auto
  also have "\<dots> = \<langle>vs ! l | x\<rangle>"
    using l_lt by simp
  finally show ?thesis.
qed

lemma residual_orthogonal:
  assumes orth: "orthonormal_list n vs"
      and xdim: "dim_vec x = n"
      and l_lt: "l < length vs"
  shows "\<langle>vs ! l | x - outer_sum n vs *\<^sub>v x\<rangle> = 0"
proof -
  let ?Px = "outer_sum n vs *\<^sub>v x"
  have ldim: "dim_vec (vs ! l) = n" 
    using orth l_lt by (simp add: orthonormal_listD_dim)
  have Pdim: "dim_vec ?Px = n" 
    using xdim by simp
  have diffdim: "dim_vec (x - ?Px) = n" 
    using xdim Pdim by simp
  have "\<langle>vs ! l | x - ?Px\<rangle> = (\<Sum>i<n. cnj ((vs ! l) $ i) * (x - ?Px) $ i)"
    using ldim diffdim by (simp add: inner_prod_def atLeast0LessThan)
  also have "\<dots> = (\<Sum>i<n. cnj ((vs ! l) $ i) * (x $ i - ?Px $ i))"
    using xdim Pdim by (intro sum.cong refl, simp)
  also have "\<dots> = (\<Sum>i<n. cnj ((vs ! l) $ i) * x $ i - cnj ((vs ! l) $ i) * ?Px $ i)"
    by (intro sum.cong refl, simp add: right_diff_distrib)
  also have "\<dots> = (\<Sum>i<n. cnj ((vs ! l) $ i) * x $ i) -
                  (\<Sum>i<n. cnj ((vs ! l) $ i) * ?Px $ i)"
    by (simp add: sum_subtractf)
  also have "\<dots> = \<langle>vs ! l | x\<rangle> - \<langle>vs ! l | ?Px\<rangle>"
    using ldim xdim Pdim by (simp add: inner_prod_def atLeast0LessThan)
  also have "\<dots> = \<langle>vs ! l | x\<rangle> - \<langle>vs ! l | x\<rangle>"
    using inner_prod_outer_sum[OF orth xdim l_lt] by simp
  also have "\<dots> = 0" 
    by simp
  finally show ?thesis.
qed

corollary orthogonal_decomposition:
  assumes xdim: "dim_vec x = n"
  shows "x = outer_sum n vs *\<^sub>v x + (x - outer_sum n vs *\<^sub>v x)"
proof -
  have "dim_vec (outer_sum n vs *\<^sub>v x) = n" 
    using xdim by simp
  then show ?thesis using xdim
    by (intro eq_vecI, auto)
qed

text \<open>Uniqueness: if $x=v+w$ with $Pv=v$ and $w\perp v_l$ for all $l$, then $v=Px$
and $w=x-Px$.\<close>

lemma outer_sum_orthogonal_zero:
  assumes orth: "orthonormal_list n vs"
      and wdim: "dim_vec w = n"
      and ortho: "\<forall>l < length vs. \<langle>vs ! l | w\<rangle> = 0"
  shows "outer_sum n vs *\<^sub>v w = 0\<^sub>v n"
proof (rule eq_vecI)
  show "dim_vec (outer_sum n vs *\<^sub>v w) = dim_vec (0\<^sub>v n)"
    using wdim by simp
next
  fix i assume "i < dim_vec (0\<^sub>v n)"
  then have i_lt: "i < n" by simp
  have "(outer_sum n vs *\<^sub>v w) $ i =
        (\<Sum>l < length vs. \<langle>vs ! l | w\<rangle> * (vs ! l) $ i)"
    using outer_sum_apply[OF orth wdim i_lt] .
  also have "\<dots> = (\<Sum>l < length vs. 0 * (vs ! l) $ i)"
    using ortho by (intro sum.cong refl) simp
  also have "\<dots> = 0" by simp
  finally show "(outer_sum n vs *\<^sub>v w) $ i = (0\<^sub>v n) $ i"
    using i_lt by simp
qed

lemma outer_sum_add:
  assumes vdim: "dim_vec v = n" and wdim: "dim_vec w = n"
  shows "outer_sum n vs *\<^sub>v (v + w) = 
         outer_sum n vs *\<^sub>v v + outer_sum n vs *\<^sub>v w"
proof -
  have "outer_sum n vs \<in> carrier_mat n n"
    by fastforce

  moreover have "v \<in> carrier_vec n" 
    using vdim carrier_vec_dim_vec by blast
  moreover have "w \<in> carrier_vec n" 
    using wdim carrier_vec_dim_vec by blast
  ultimately show ?thesis
    by (simp add: mult_add_distrib_mat_vec)
qed

lemma orthogonal_decomposition_unique:
  assumes orth: "orthonormal_list n vs"
      and xdim: "dim_vec x = n"
      and vdim: "dim_vec v = n"
      and wdim: "dim_vec w = n"
      and decomp: "x = v + w"
      and v_fixed: "outer_sum n vs *\<^sub>v v = v"
      and w_ortho: "\<forall>l < length vs. \<langle>vs ! l | w\<rangle> = 0"
  shows "v = outer_sum n vs *\<^sub>v x" and "w = x - outer_sum n vs *\<^sub>v x"
proof -
  let ?P = "outer_sum n vs"

  have "v = v + 0\<^sub>v n"
    by (simp add: carrier_vecI vdim)
  also have "\<dots> = ?P *\<^sub>v v + ?P *\<^sub>v w"
    using v_fixed outer_sum_orthogonal_zero[OF orth wdim w_ortho] by simp
  also have "\<dots> = ?P *\<^sub>v (v + w)"
    using outer_sum_add[OF vdim wdim] by simp
  also have "\<dots> = ?P *\<^sub>v x"
    using decomp by simp
  finally show Px_eq: "v = ?P *\<^sub>v x".

  have "w = (v + w) - v"
    using vdim wdim by auto
  also have "\<dots> = x - v"
    using decomp by simp
  also have "\<dots> = x - ?P *\<^sub>v x"
    using Px_eq by simp
  finally show "w = x - ?P *\<^sub>v x".
qed

lemma Tr_one_mat:
  "Tr (1\<^sub>m n :: complex Matrix.mat) = of_nat n"
proof -
  have "Tr (1\<^sub>m n :: complex Matrix.mat)
          = (\<Sum>r < n. if r < n then (1\<^sub>m n :: complex Matrix.mat) $$ (r, r)
                       else 0)"
    by (simp add: Tr_def)
  also have "\<dots> = (\<Sum>r < n. (1 :: complex))" by simp
  also have "\<dots> = of_nat n" by simp
  finally show ?thesis.
qed

subsection \<open>The projection does not depend on the orthonormal basis\<close>

definition col_span :: "nat \<Rightarrow> complex Matrix.vec list \<Rightarrow> complex Matrix.vec set" where
  "col_span n vs = {mat_of_cols n vs *\<^sub>v c | c. dim_vec c = length vs}"

lemma outer_sum_fixes_col_span:
  assumes orth: "orthonormal_list n vs" and w: "w \<in> col_span n vs"
  shows "outer_sum n vs *\<^sub>v w = w"
proof -
  let ?k = "length vs" and ?V = "mat_of_cols n vs"
  obtain c where c: "dim_vec c = ?k" and wc: "w = ?V *\<^sub>v c" using w unfolding col_span_def by blast
  have Vc: "?V \<in> carrier_mat n ?k" by simp
  have Vdc: "?V\<^sup>\<dagger> \<in> carrier_mat ?k n" by (rule dagger_carrier[OF Vc])
  have cc: "c \<in> carrier_vec ?k" by (rule carrier_vecI[OF c])
  have VdV: "(?V\<^sup>\<dagger>) * ?V = 1\<^sub>m ?k" by (rule cols_mat_dagger_left[OF orth])
  have "outer_sum n vs *\<^sub>v w = ?V *\<^sub>v ((?V\<^sup>\<dagger>) *\<^sub>v (?V *\<^sub>v c))"
    unfolding outer_sum_def wc by (rule assoc_mult_mat_vec[OF Vc Vdc mult_mat_vec_carrier[OF Vc cc]])
  also have "(?V\<^sup>\<dagger>) *\<^sub>v (?V *\<^sub>v c) = c"
    using assoc_mult_mat_vec[OF Vdc Vc cc] unfolding VdV using cc by simp
  finally show ?thesis unfolding wc .
qed

lemma mem_col_span_self:
  assumes "\<forall>v \<in> set vs. dim_vec v = n" and j: "j < length vs"
  shows "vs ! j \<in> col_span n vs"
proof -
  have Vc: "mat_of_cols n vs \<in> carrier_mat n (length vs)" by simp
  have vj: "vs ! j \<in> carrier_vec n" using assms(1) j by (auto intro!: carrier_vecI)
  have "mat_of_cols n vs *\<^sub>v unit_vec (length vs) j = Matrix.col (mat_of_cols n vs) j"
    by (rule eq_vecI) (use Vc j in auto)
  also have "\<dots> = vs ! j" by (rule col_mat_of_cols[OF j vj])
  finally have "mat_of_cols n vs *\<^sub>v unit_vec (length vs) j = vs ! j" .
  thus ?thesis unfolding col_span_def
    by (intro CollectI exI[of _ "unit_vec (length vs) j"]) simp
qed

lemma outer_sum_absorbs:
  assumes ov: "orthonormal_list n vs" and ow: "orthonormal_list n ws"
      and sub: "set ws \<subseteq> col_span n vs"
  shows "outer_sum n vs * outer_sum n ws = outer_sum n ws"
proof -
  let ?V = "mat_of_cols n vs" and ?W = "mat_of_cols n ws" and ?P = "outer_sum n vs"
  have wd: "\<And>j. j < length ws \<Longrightarrow> ws ! j \<in> carrier_vec n"
    using ow unfolding orthonormal_list_def by (auto intro: carrier_vecI)
  have Pc: "?P \<in> carrier_mat n n" by (simp add: carrier_matI)
  have Wc: "?W \<in> carrier_mat n (length ws)" by simp
  have Wdc: "?W\<^sup>\<dagger> \<in> carrier_mat (length ws) n" by (rule dagger_carrier[OF Wc])
  have PW: "?P * ?W = ?W"
  proof (rule eq_matI)
    fix i j assume i: "i < dim_row ?W" and j': "j < dim_col ?W"
    have j: "j < length ws" using j' by simp
    have "(?P * ?W) $$ (i,j) = (?P *\<^sub>v Matrix.col ?W j) $ i" using i j Pc by (simp add: scalar_prod_def atLeast0LessThan)
    also have "Matrix.col ?W j = ws ! j" by (rule col_mat_of_cols[OF j wd[OF j]])
    also have "?P *\<^sub>v ws ! j = ws ! j" by (rule outer_sum_fixes_col_span[OF ov subsetD[OF sub nth_mem[OF j]]])
    finally show "(?P * ?W) $$ (i,j) = ?W $$ (i,j)" using i j wd[OF j] by (simp add: mat_of_cols_def)
  qed (use Pc in simp_all)
  have "?P * outer_sum n ws = (?P * ?W) * (?W\<^sup>\<dagger>)"
    unfolding outer_sum_def[of n ws] by (rule assoc_mult_mat[OF Pc Wc Wdc, symmetric])
  thus ?thesis unfolding PW outer_sum_def[of n ws] .
qed

text \<open>D2-8: two orthonormal bases of the same subspace give the same projection.\<close>

theorem outer_sum_basis_independent:
  assumes ov: "orthonormal_list n vs" and ow: "orthonormal_list n ws"
      and span: "col_span n vs = col_span n ws"
  shows "outer_sum n vs = outer_sum n ws"
proof -
  let ?P = "outer_sum n vs" and ?Q = "outer_sum n ws"
  have vd: "\<forall>v \<in> set vs. dim_vec v = n" and wd: "\<forall>v \<in> set ws. dim_vec v = n"
    using ov ow unfolding orthonormal_list_def by auto
  have subw: "set ws \<subseteq> col_span n vs"
    using mem_col_span_self[OF wd] span by (auto simp: in_set_conv_nth)
  have subv: "set vs \<subseteq> col_span n ws"
    using mem_col_span_self[OF vd] span by (auto simp: in_set_conv_nth)
  have PQ: "?P * ?Q = ?Q" by (rule outer_sum_absorbs[OF ov ow subw])
  have QP: "?Q * ?P = ?P" by (rule outer_sum_absorbs[OF ow ov subv])
  have Pc: "?P \<in> carrier_mat n n" and Qc: "?Q \<in> carrier_mat n n" by (simp_all add: carrier_matI)
  have "?Q = (?P * ?Q)\<^sup>\<dagger>" unfolding PQ outer_sum_hermitian ..
  also have "\<dots> = (?Q\<^sup>\<dagger>) * (?P\<^sup>\<dagger>)" by (rule dagger_of_prod) (use Pc Qc in simp)
  also have "\<dots> = ?P" unfolding outer_sum_hermitian QP ..
  finally show ?thesis ..
qed

end

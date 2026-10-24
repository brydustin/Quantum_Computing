theory Suzuki_Order
  imports Trotter_Product_Formula Matrix_Sums
begin

section \<open>Order conditions for product formulas\<close>

text \<open>Taylor coefficients of products $e^{tY_1}\cdots e^{tY_m}$ as convolutions of matrix sequences.
A palindromic product has odd error order (\<open>sym_order\<close>), and Suzuki's five-fold recursion
raises the order by two (\<open>scaled_copies\<close>), so $S_{2k+2}$ agrees with $e^{itH}$ up to degree
$2k+2$ (\<open>suzuki_order\<close>).\<close>

text \<open>A sequence $f_0,f_1,\dots$ of $n\times n$ matrices stands for the power series $\sum_pf_pt^p$, and the
product of two series has the coefficients of the Cauchy product
\[ (f\ast g)_p=\sum_{q\le p}f_q\,g_{p-q}. \]\<close>

definition cauchy_prod :: "nat \<Rightarrow> (nat \<Rightarrow> complex Matrix.mat) \<Rightarrow> (nat \<Rightarrow> complex Matrix.mat) \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
  "cauchy_prod n f g p = matrix_sum n (\<lambda>q. f q * g (p - q)) (Suc p)"

text \<open>All terms of the sequence are $n\times n$.\<close>

definition seq_carrier :: "nat \<Rightarrow> (nat \<Rightarrow> complex Matrix.mat) \<Rightarrow> bool" where
  "seq_carrier n f \<longleftrightarrow> (\<forall>p. f p \<in> carrier_mat n n)"

lemma seq_carrier_in [simp]: "seq_carrier n f \<Longrightarrow> f q \<in> carrier_mat n n"
  by (simp add: seq_carrier_def)

lemma seq_carrier_row [simp]: "seq_carrier n f \<Longrightarrow> dim_row (f q) = n"
  by (rule carrier_matD(1)[OF seq_carrier_in])

lemma seq_carrier_col [simp]: "seq_carrier n f \<Longrightarrow> dim_col (f q) = n"
  by (rule carrier_matD(2)[OF seq_carrier_in])

lemma seq_carrier_mult [simp]: "seq_carrier n f \<Longrightarrow> seq_carrier n g \<Longrightarrow> f q * g r \<in> carrier_mat n n"
  by (rule mult_carrier_mat[OF seq_carrier_in seq_carrier_in])

lemma cauchy_prod_carrier: "seq_carrier n f \<Longrightarrow> seq_carrier n g \<Longrightarrow> seq_carrier n (cauchy_prod n f g)"
  unfolding seq_carrier_def cauchy_prod_def by (intro allI matrix_sum_dim, rule mult_carrier_mat) auto

lemma cauchy_prod_index:
  assumes "seq_carrier n f" "seq_carrier n g" "i < n" "j < n"
  shows "cauchy_prod n f g p $$ (i, j) = (\<Sum>q\<le>p. \<Sum>c<n. f q $$ (i, c) * g (p - q) $$ (c, j))"
proof -
  have "cauchy_prod n f g p $$ (i, j) = (\<Sum>q<Suc p. (f q * g (p - q)) $$ (i, j))"
    unfolding cauchy_prod_def by (rule matrix_sum_index) (use assms in simp_all)
  also have "\<dots> = (\<Sum>q\<le>p. \<Sum>c<n. f q $$ (i, c) * g (p - q) $$ (c, j))"
      using assms unfolding lessThan_Suc_atMost
    by (intro sum.cong refl) (auto simp: scalar_prod_def atLeast0LessThan)
  finally show ?thesis .
qed

lemma triple_reindex:
  fixes F :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a::comm_monoid_add"
  shows "(\<Sum>q\<le>p. \<Sum>r\<le>q. F r (q - r) (p - q)) = (\<Sum>r\<le>p. \<Sum>s\<le>p - r. F r s (p - r - s))"
proof -
  have "(\<Sum>q\<le>p. \<Sum>r\<le>q. F r (q - r) (p - q)) = (\<Sum>(q, r)\<in>Sigma {..p} (\<lambda>q. {..q}). F r (q - r) (p - q))"
    by (rule sum.Sigma) auto
  also have "\<dots> = (\<Sum>(r, s)\<in>Sigma {..p} (\<lambda>r. {..p - r}). F r s (p - r - s))"
    by (rule sum.reindex_bij_witness[where i = "\<lambda>(r, s). (r + s, r)" and j = "\<lambda>(q, r). (r, q - r)"]) auto
  also have "\<dots> = (\<Sum>r\<le>p. \<Sum>s\<le>p - r. F r s (p - r - s))"
    by (rule sum.Sigma[symmetric]) auto
  finally show ?thesis .
qed

text \<open>The Cauchy product is associative:\<close>

lemma cauchy_prod_assoc:
  assumes f: "seq_carrier n f" and g: "seq_carrier n g" and h: "seq_carrier n h"
  shows "cauchy_prod n (cauchy_prod n f g) h p = cauchy_prod n f (cauchy_prod n g h) p"
proof (rule eq_matI)
  fix i j assume i: "i < dim_row (cauchy_prod n f (cauchy_prod n g h) p)" and j: "j < dim_col (cauchy_prod n f (cauchy_prod n g h) p)"
  have ij: "i < n" "j < n" using i j cauchy_prod_carrier[OF f cauchy_prod_carrier[OF g h]] by simp_all
  have fg: "seq_carrier n (cauchy_prod n f g)" and gh: "seq_carrier n (cauchy_prod n g h)" using cauchy_prod_carrier f g h by auto
  have sw1: "(\<Sum>c<n. \<Sum>r\<le>q. \<Sum>e<n. T c r e) = (\<Sum>r\<le>q. \<Sum>e<n. \<Sum>c<n. T c r e)" for T :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex" and q
    by (subst sum.swap) (rule sum.cong[OF refl], rule sum.swap)
  have sw2: "(\<Sum>e<n. \<Sum>s\<le>m. \<Sum>c<n. T e s c) = (\<Sum>s\<le>m. \<Sum>e<n. \<Sum>c<n. T e s c)" for T :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex" and m
    by (rule sum.swap)
  have "cauchy_prod n (cauchy_prod n f g) h p $$ (i, j)
      = (\<Sum>q\<le>p. \<Sum>c<n. (\<Sum>r\<le>q. \<Sum>e<n. f r $$ (i, e) * g (q - r) $$ (e, c)) * h (p - q) $$ (c, j))"
    unfolding cauchy_prod_index[OF fg h ij] using cauchy_prod_index[OF f g ij(1)] by (intro sum.cong refl) simp
  also have "\<dots> = (\<Sum>q\<le>p. \<Sum>r\<le>q. \<Sum>e<n. \<Sum>c<n. f r $$ (i, e) * g (q - r) $$ (e, c) * h (p - q) $$ (c, j))"
    by (simp only: sum_distrib_right sw1)
  also have "\<dots> = (\<Sum>r\<le>p. \<Sum>s\<le>p - r. \<Sum>e<n. \<Sum>c<n. f r $$ (i, e) * g s $$ (e, c) * h (p - r - s) $$ (c, j))"
    by (rule triple_reindex)
  also have "\<dots> = (\<Sum>r\<le>p. \<Sum>e<n. f r $$ (i, e) * (\<Sum>s\<le>p - r. \<Sum>c<n. g s $$ (e, c) * h (p - r - s) $$ (c, j)))"
    unfolding sum_distrib_left sw2 by (simp add: mult_ac)
  also have "\<dots> = cauchy_prod n f (cauchy_prod n g h) p $$ (i, j)"
    unfolding cauchy_prod_index[OF f gh ij] using cauchy_prod_index[OF g h _ ij(2)] by (intro sum.cong refl) simp
  finally show "cauchy_prod n (cauchy_prod n f g) h p $$ (i, j) = cauchy_prod n f (cauchy_prod n g h) p $$ (i, j)" .
qed (use cauchy_prod_carrier[OF cauchy_prod_carrier[OF f g] h] cauchy_prod_carrier[OF f cauchy_prod_carrier[OF g h]] in \<open>simp_all add: seq_carrier_def\<close>)


text \<open>The unit series $1,0,0,\dots$; scaling $f_p\mapsto u^pf_p$, which substitutes $ut$ for $t$; and the
coefficients $X^p/p!$ of $e^{tX}$.\<close>

definition seq_one :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
  "seq_one n p = (if p = 0 then 1\<^sub>m n else 0\<^sub>m n n)"

definition seq_scale :: "complex \<Rightarrow> (nat \<Rightarrow> complex Matrix.mat) \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
  "seq_scale u f p = (u ^ p) \<cdot>\<^sub>m f p"

definition exp_coeff :: "complex Matrix.mat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
  "exp_coeff X p = complex_of_real (1 / fact p) \<cdot>\<^sub>m X ^\<^sub>m p"

lemma seq_one_carrier [simp]: "seq_carrier n (seq_one n)"
  by (simp add: seq_carrier_def seq_one_def)

lemma seq_scale_carrier [simp]: "seq_carrier n f \<Longrightarrow> seq_carrier n (seq_scale u f)"
  by (simp add: seq_carrier_def seq_scale_def)

lemma exp_coeff_carrier [simp]: "X \<in> carrier_mat n n \<Longrightarrow> seq_carrier n (exp_coeff X)"
  by (simp add: seq_carrier_def exp_coeff_def)

text \<open>The unit is neutral and scaling commutes with products:\<close>

lemma cauchy_prod_unit_left: "seq_carrier n f \<Longrightarrow> cauchy_prod n (seq_one n) f p = f p"
proof (induction p)
  case 0
  thus ?case by (simp add: cauchy_prod_def seq_one_def)
next
  case (Suc p)
  have "matrix_sum n (\<lambda>q. seq_one n q * f (Suc p - q)) (Suc p) = matrix_sum n (\<lambda>q. if q = 0 then f (Suc p) else 0\<^sub>m n n) (Suc p)"
    by (rule matrix_sum_cong) (use Suc.prems in \<open>auto simp: seq_one_def\<close>)
  also have "\<dots> = f (Suc p)"
  proof -
    have z: "matrix_sum n (\<lambda>q. if q = 0 then f (Suc p) else 0\<^sub>m n n) m = f (Suc p)" if "0 < m" for m
      using that by (induction m) (use Suc.prems in \<open>auto simp: gr0_conv_Suc\<close>)
    show ?thesis by (rule z) simp
  qed
  finally show ?case using Suc.prems by (simp add: cauchy_prod_def seq_one_def)
qed

lemma cauchy_prod_unit_right: "seq_carrier n f \<Longrightarrow> cauchy_prod n f (seq_one n) p = f p"
proof (rule eq_matI)
  fix i j assume f: "seq_carrier n f" and i: "i < dim_row (f p)" and j: "j < dim_col (f p)"
  have ij: "i < n" "j < n" using i j f by simp_all
  have "cauchy_prod n f (seq_one n) p $$ (i, j) = (\<Sum>q\<le>p. \<Sum>c<n. f q $$ (i, c) * seq_one n (p - q) $$ (c, j))"
    by (rule cauchy_prod_index[OF f seq_one_carrier ij])
  also have "\<dots> = (\<Sum>q\<le>p. if q = p then f p $$ (i, j) else 0)"
  proof (rule sum.cong[OF refl])
    fix q assume q: "q \<in> {..p}"
    show "(\<Sum>c<n. f q $$ (i, c) * seq_one n (p - q) $$ (c, j)) = (if q = p then f p $$ (i, j) else 0)"
    proof (cases "q = p")
      case True
      have "(\<Sum>c<n. f p $$ (i, c) * (if c = j then 1 else 0)) = (\<Sum>c<n. if c = j then f p $$ (i, c) else 0)"
        by (intro sum.cong) auto
      also have "\<dots> = f p $$ (i, j)" using ij by simp
      finally have "(\<Sum>c<n. f p $$ (i, c) * (if c = j then 1 else 0)) = f p $$ (i, j)" .
      thus ?thesis using True ij by (simp add: seq_one_def one_mat_def)
    qed (use q ij in \<open>auto simp: seq_one_def\<close>)
  qed
  also have "\<dots> = f p $$ (i, j)" by simp
  finally show "cauchy_prod n f (seq_one n) p $$ (i, j) = f p $$ (i, j)" .
qed (simp_all add: cauchy_prod_carrier[THEN seq_carrier_row] cauchy_prod_carrier[THEN seq_carrier_col])

lemma seq_scale_cauchy_prod: "seq_carrier n f \<Longrightarrow> seq_carrier n g \<Longrightarrow> cauchy_prod n (seq_scale u f) (seq_scale u g) p = seq_scale u (cauchy_prod n f g) p"
proof (rule eq_matI)
  fix i j assume f: "seq_carrier n f" and g: "seq_carrier n g" and i: "i < dim_row (seq_scale u (cauchy_prod n f g) p)"
    and j: "j < dim_col (seq_scale u (cauchy_prod n f g) p)"
  have ij: "i < n" "j < n" using i j cauchy_prod_carrier[OF f g] by (simp_all add: seq_scale_def)
  have "cauchy_prod n (seq_scale u f) (seq_scale u g) p $$ (i, j) = (\<Sum>q\<le>p. \<Sum>c<n. (u ^ q * f q $$ (i, c)) * (u ^ (p - q) * g (p - q) $$ (c, j)))"
    unfolding cauchy_prod_index[OF seq_scale_carrier[OF f] seq_scale_carrier[OF g] ij] using ij f g by (intro sum.cong refl) (simp add: seq_scale_def)
  also have "\<dots> = (\<Sum>q\<le>p. \<Sum>c<n. u ^ p * (f q $$ (i, c) * g (p - q) $$ (c, j)))"
    by (intro sum.cong refl) (simp add: mult_ac power_add[symmetric])
  also have "\<dots> = seq_scale u (cauchy_prod n f g) p $$ (i, j)"
    unfolding seq_scale_def using ij cauchy_prod_index[OF f g ij] cauchy_prod_carrier[OF f g] by (simp add: sum_distrib_left)
  finally show "cauchy_prod n (seq_scale u f) (seq_scale u g) p $$ (i, j) = seq_scale u (cauchy_prod n f g) p $$ (i, j)" .
qed (simp_all add: seq_scale_def cauchy_prod_carrier[THEN seq_carrier_row] cauchy_prod_carrier[THEN seq_carrier_col])

lemma smult_pow_mat: "X \<in> carrier_mat n n \<Longrightarrow> (u \<cdot>\<^sub>m X) ^\<^sub>m p = (u ^ p) \<cdot>\<^sub>m (X ^\<^sub>m p)"
  for X :: "complex Matrix.mat"
proof (induction p)
  case 0
  thus ?case by simp (intro eq_matI, auto)
next
  case (Suc p)
  have Xp: "X ^\<^sub>m p \<in> carrier_mat n n" using Suc.prems by simp
  have "(u \<cdot>\<^sub>m X) ^\<^sub>m Suc p = (u ^ p \<cdot>\<^sub>m X ^\<^sub>m p) * (u \<cdot>\<^sub>m X)" using Suc by simp
  also have "\<dots> = u ^ p \<cdot>\<^sub>m (X ^\<^sub>m p * (u \<cdot>\<^sub>m X))"
    by (rule mult_smult_assoc_mat[where nr = n and n = n and nc = n]) (use Xp Suc.prems in simp_all)
  also have "X ^\<^sub>m p * (u \<cdot>\<^sub>m X) = u \<cdot>\<^sub>m (X ^\<^sub>m p * X)"
    by (rule mult_smult_distrib[where nr = n and n = n and nc = n]) (use Xp Suc.prems in simp_all)
  also have "u ^ p \<cdot>\<^sub>m (u \<cdot>\<^sub>m (X ^\<^sub>m p * X)) = (u ^ Suc p) \<cdot>\<^sub>m (X ^\<^sub>m p * X)"
    by (rule eq_matI) (auto simp: mult_ac)
  finally show ?case by simp
qed

lemma smult_mult_smult:
  fixes A B :: "complex Matrix.mat"
  assumes "A \<in> carrier_mat n n" "B \<in> carrier_mat n n"
  shows "(c \<cdot>\<^sub>m A) * (d \<cdot>\<^sub>m B) = (c * d) \<cdot>\<^sub>m (A * B)"
proof -
  have "(c \<cdot>\<^sub>m A) * (d \<cdot>\<^sub>m B) = c \<cdot>\<^sub>m (A * (d \<cdot>\<^sub>m B))"
    by (rule mult_smult_assoc_mat[where nr = n and n = n and nc = n]) (use assms in simp_all)
  also have "A * (d \<cdot>\<^sub>m B) = d \<cdot>\<^sub>m (A * B)"
    by (rule mult_smult_distrib[where nr = n and n = n and nc = n]) (use assms in simp_all)
  also have "c \<cdot>\<^sub>m (d \<cdot>\<^sub>m (A * B)) = (c * d) \<cdot>\<^sub>m (A * B)" by (rule eq_matI) auto
  finally show ?thesis .
qed

lemma exp_coeff_smult: "X \<in> carrier_mat n n \<Longrightarrow> exp_coeff (u \<cdot>\<^sub>m X) p = seq_scale u (exp_coeff X) p"
  by (simp add: exp_coeff_def seq_scale_def smult_pow_mat) (rule eq_matI, auto simp: mult_ac)

lemma exp_coeff_zero: "exp_coeff (0\<^sub>m n n) p = seq_one n p"
  by (cases p) (simp_all add: exp_coeff_def seq_one_def one_smult_mat)

text \<open>$e^{taX}e^{tbX}=e^{t(a+b)X}$, coefficient by coefficient:
\[ \sum_{q\le p}\frac{(aX)^q}{q!}\,\frac{(bX)^{p-q}}{(p-q)!}=\frac{((a+b)X)^p}{p!}. \]\<close>

lemma exp_coeff_add:
  assumes X: "X \<in> carrier_mat n n"
  shows "cauchy_prod n (exp_coeff (a \<cdot>\<^sub>m X)) (exp_coeff (b \<cdot>\<^sub>m X)) p = exp_coeff ((a + b) \<cdot>\<^sub>m X) p"
proof -
  have Xq: "\<And>q. X ^\<^sub>m q \<in> carrier_mat n n" using X by simp
  have tm: "exp_coeff (a \<cdot>\<^sub>m X) q * exp_coeff (b \<cdot>\<^sub>m X) (p - q)
      = (a ^ q * b ^ (p - q) / (fact q * fact (p - q))) \<cdot>\<^sub>m X ^\<^sub>m p" if "q \<le> p" for q
  proof -
    have "X ^\<^sub>m q * X ^\<^sub>m (p - q) = X ^\<^sub>m p" using that X by (simp add: pow_mat_add[OF X, symmetric])
    hence "(1 / fact q * a ^ q) \<cdot>\<^sub>m X ^\<^sub>m q * ((1 / fact (p - q) * b ^ (p - q)) \<cdot>\<^sub>m X ^\<^sub>m (p - q))
        = (a ^ q * b ^ (p - q) / (fact q * fact (p - q))) \<cdot>\<^sub>m X ^\<^sub>m p"
      by (simp add: smult_mult_smult[OF Xq Xq] field_simps)
    moreover have "exp_coeff (a \<cdot>\<^sub>m X) q = (1 / fact q * a ^ q) \<cdot>\<^sub>m X ^\<^sub>m q"
      "exp_coeff (b \<cdot>\<^sub>m X) (p - q) = (1 / fact (p - q) * b ^ (p - q)) \<cdot>\<^sub>m X ^\<^sub>m (p - q)"
      by (simp_all add: exp_coeff_def smult_pow_mat[OF X]) (rule eq_matI, auto)+
    ultimately show ?thesis by simp
  qed
  have "cauchy_prod n (exp_coeff (a \<cdot>\<^sub>m X)) (exp_coeff (b \<cdot>\<^sub>m X)) p
      = matrix_sum n (\<lambda>q. (a ^ q * b ^ (p - q) / (fact q * fact (p - q))) \<cdot>\<^sub>m X ^\<^sub>m p) (Suc p)"
    unfolding cauchy_prod_def by (rule matrix_sum_cong) (simp add: tm)
  also have "\<dots> = (\<Sum>q<Suc p. a ^ q * b ^ (p - q) / (fact q * fact (p - q))) \<cdot>\<^sub>m X ^\<^sub>m p"
    by (rule matrix_sum_scalar[OF Xq])
  also have "(\<Sum>q<Suc p. a ^ q * b ^ (p - q) / (fact q * fact (p - q))) = (a + b) ^ p / fact p"
  proof -
    have "(a + b) ^ p = (\<Sum>q\<le>p. of_nat (p choose q) * a ^ q * b ^ (p - q))" by (rule binomial_ring)
    also have "\<dots> = fact p * (\<Sum>q\<le>p. a ^ q * b ^ (p - q) / (fact q * fact (p - q)))"
      unfolding sum_distrib_left by (intro sum.cong refl) (simp add: binomial_fact field_simps)
    finally show ?thesis by (simp add: lessThan_Suc_atMost field_simps)
  qed
  also have "((a + b) ^ p / fact p) \<cdot>\<^sub>m X ^\<^sub>m p = exp_coeff ((a + b) \<cdot>\<^sub>m X) p"
    by (simp add: exp_coeff_def smult_pow_mat[OF X]) (rule eq_matI, auto)
  finally show ?thesis .
qed

text \<open>The coefficients of $e^{tY_1}\cdots e^{tY_m}$.\<close>

fun prod_coeff :: "nat \<Rightarrow> complex Matrix.mat list \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
  "prod_coeff n [] = seq_one n"
| "prod_coeff n (Y # Ys) = cauchy_prod n (exp_coeff Y) (prod_coeff n Ys)"

lemma prod_coeff_carrier: "\<forall>Y \<in> set Ys. Y \<in> carrier_mat n n \<Longrightarrow> seq_carrier n (prod_coeff n Ys)"
  by (induction Ys) (auto intro: cauchy_prod_carrier)

text \<open>Concatenating factor lists multiplies the series, scaling all factors scales the series, and
$e^{-tY_m}\cdots e^{-tY_1}$ inverts $e^{tY_1}\cdots e^{tY_m}$:\<close>

lemma prod_coeff_append:
  assumes "\<forall>Y \<in> set Ys. Y \<in> carrier_mat n n" "\<forall>Y \<in> set Zs. Y \<in> carrier_mat n n"
  shows "prod_coeff n (Ys @ Zs) = cauchy_prod n (prod_coeff n Ys) (prod_coeff n Zs)"
  using assms(1)
proof (induction Ys)
  case Nil
  show ?case using prod_coeff_carrier[OF assms(2)] by (simp add: fun_eq_iff cauchy_prod_unit_left)
next
  case (Cons Y Ys)
  have c: "seq_carrier n (exp_coeff Y)" "seq_carrier n (prod_coeff n Ys)" "seq_carrier n (prod_coeff n Zs)"
    using Cons.prems prod_coeff_carrier[OF assms(2)] prod_coeff_carrier[of Ys n] by auto
  have ih: "prod_coeff n (Ys @ Zs) = cauchy_prod n (prod_coeff n Ys) (prod_coeff n Zs)" using Cons by simp
  show ?case unfolding append_Cons prod_coeff.simps ih using cauchy_prod_assoc[OF c] by (simp add: fun_eq_iff)
qed

lemma seq_scale_seq_one: "seq_scale u (seq_one n) = seq_one n"
  by (auto simp: fun_eq_iff seq_scale_def seq_one_def one_smult_mat)

lemma prod_coeff_scale: "\<forall>Y \<in> set Ys. Y \<in> carrier_mat n n \<Longrightarrow> prod_coeff n (map ((\<cdot>\<^sub>m) u) Ys) = seq_scale u (prod_coeff n Ys)"
proof (induction Ys)
  case Nil
  thus ?case by (simp add: seq_scale_seq_one)
next
  case (Cons Y Ys)
  have Y: "Y \<in> carrier_mat n n" and F: "seq_carrier n (prod_coeff n Ys)" using Cons.prems prod_coeff_carrier[of Ys n] by auto
  have t: "exp_coeff (u \<cdot>\<^sub>m Y) = seq_scale u (exp_coeff Y)" by (simp add: fun_eq_iff exp_coeff_smult[OF Y])
  have ih: "prod_coeff n (map ((\<cdot>\<^sub>m) u) Ys) = seq_scale u (prod_coeff n Ys)" using Cons by simp
  show ?case unfolding list.map prod_coeff.simps t ih using seq_scale_cauchy_prod[OF exp_coeff_carrier[OF Y] F] by (simp add: fun_eq_iff)
qed

lemma zero_smult_mat: "A \<in> carrier_mat n n \<Longrightarrow> (0::complex) \<cdot>\<^sub>m A = 0\<^sub>m n n"
  by (rule eq_matI) auto

lemma exp_coeff_inverse:
  assumes Y: "Y \<in> carrier_mat n n"
  shows "cauchy_prod n (exp_coeff ((-1) \<cdot>\<^sub>m Y)) (exp_coeff Y) = seq_one n"
proof -
  have "cauchy_prod n (exp_coeff ((-1) \<cdot>\<^sub>m Y)) (exp_coeff (1 \<cdot>\<^sub>m Y)) p = exp_coeff ((-1 + 1) \<cdot>\<^sub>m Y) p" for p
    by (rule exp_coeff_add[OF Y])
  thus ?thesis using zero_smult_mat[OF Y] by (simp add: fun_eq_iff one_smult_mat exp_coeff_zero)
qed

lemma cauchy_prod_assoc_fun: "seq_carrier n f \<Longrightarrow> seq_carrier n g \<Longrightarrow> seq_carrier n h \<Longrightarrow> cauchy_prod n (cauchy_prod n f g) h = cauchy_prod n f (cauchy_prod n g h)"
  by (simp add: fun_eq_iff cauchy_prod_assoc)

lemma cauchy_prod_unit_right_fun: "seq_carrier n f \<Longrightarrow> cauchy_prod n f (seq_one n) = f"
  by (simp add: fun_eq_iff cauchy_prod_unit_right)

lemma cauchy_prod_unit_left_fun: "seq_carrier n f \<Longrightarrow> cauchy_prod n (seq_one n) f = f"
  by (simp add: fun_eq_iff cauchy_prod_unit_left)

lemma prod_coeff_inverse:
  "\<forall>Y \<in> set Ys. Y \<in> carrier_mat n n \<Longrightarrow> cauchy_prod n (prod_coeff n (rev (map ((\<cdot>\<^sub>m) (-1)) Ys))) (prod_coeff n Ys) = seq_one n"
proof (induction Ys)
  case Nil
  thus ?case by (simp add: fun_eq_iff cauchy_prod_unit_left)
next
  case (Cons Y Ys)
  have Y: "Y \<in> carrier_mat n n" and Ys: "\<forall>Z \<in> set Ys. Z \<in> carrier_mat n n" using Cons.prems by auto
  let ?A = "rev (map ((\<cdot>\<^sub>m) (-1)) Ys)"
  have A: "\<forall>Z \<in> set ?A. Z \<in> carrier_mat n n" using Ys by auto
  have nY: "(-1) \<cdot>\<^sub>m Y \<in> carrier_mat n n" using Y by simp
  have c: "seq_carrier n (prod_coeff n ?A)" "seq_carrier n (exp_coeff ((-1) \<cdot>\<^sub>m Y))" "seq_carrier n (exp_coeff Y)" "seq_carrier n (prod_coeff n Ys)"
    using prod_coeff_carrier[OF A] prod_coeff_carrier[OF Ys] Y nY by auto
  have "prod_coeff n (rev (map ((\<cdot>\<^sub>m) (-1)) (Y # Ys))) = cauchy_prod n (prod_coeff n ?A) (exp_coeff ((-1) \<cdot>\<^sub>m Y))"
    using prod_coeff_append[OF A, of "[(-1) \<cdot>\<^sub>m Y]"] nY by (simp add: cauchy_prod_unit_right_fun)
  hence "cauchy_prod n (prod_coeff n (rev (map ((\<cdot>\<^sub>m) (-1)) (Y # Ys)))) (prod_coeff n (Y # Ys))
      = cauchy_prod n (cauchy_prod n (prod_coeff n ?A) (exp_coeff ((-1) \<cdot>\<^sub>m Y))) (cauchy_prod n (exp_coeff Y) (prod_coeff n Ys))" by simp
  also have "\<dots> = cauchy_prod n (prod_coeff n ?A) (cauchy_prod n (cauchy_prod n (exp_coeff ((-1) \<cdot>\<^sub>m Y)) (exp_coeff Y)) (prod_coeff n Ys))"
    by (simp only: cauchy_prod_assoc_fun[OF c(1,2) cauchy_prod_carrier[OF c(3,4)]] cauchy_prod_assoc_fun[OF c(2,3,4), symmetric])
  also have "\<dots> = cauchy_prod n (prod_coeff n ?A) (prod_coeff n Ys)"
    by (simp only: exp_coeff_inverse[OF Y] cauchy_prod_unit_left_fun[OF c(4)])
  finally show ?case using Cons.IH[OF Ys] by simp
qed

text \<open>$f$ vanishes below degree $q$: $f_p=0$ for $p<q$.\<close>

definition vanishes_below :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> complex Matrix.mat) \<Rightarrow> bool" where
  "vanishes_below n q f \<longleftrightarrow> (\<forall>p<q. f p = 0\<^sub>m n n)"

lemma cauchy_prod_add_left:
  "seq_carrier n f \<Longrightarrow> seq_carrier n g \<Longrightarrow> seq_carrier n h \<Longrightarrow> cauchy_prod n (\<lambda>p. f p + g p) h p = cauchy_prod n f h p + cauchy_prod n g h p"
proof -
  assume a: "seq_carrier n f" "seq_carrier n g" "seq_carrier n h"
  have "cauchy_prod n (\<lambda>p. f p + g p) h p = matrix_sum n (\<lambda>q. f q * h (p - q) + g q * h (p - q)) (Suc p)"
    unfolding cauchy_prod_def by (rule matrix_sum_cong) (rule add_mult_distrib_mat[where nr = n and n = n and nc = n], use a in simp_all)
  also have "\<dots> = cauchy_prod n f h p + cauchy_prod n g h p"
    unfolding cauchy_prod_def by (rule matrix_sum_add_distrib) (use a in simp_all)
  finally show ?thesis .
qed

lemma cauchy_prod_add_right:
  "seq_carrier n f \<Longrightarrow> seq_carrier n g \<Longrightarrow> seq_carrier n h \<Longrightarrow> cauchy_prod n h (\<lambda>p. f p + g p) p = cauchy_prod n h f p + cauchy_prod n h g p"
proof -
  assume a: "seq_carrier n f" "seq_carrier n g" "seq_carrier n h"
  have "cauchy_prod n h (\<lambda>p. f p + g p) p = matrix_sum n (\<lambda>q. h q * f (p - q) + h q * g (p - q)) (Suc p)"
    unfolding cauchy_prod_def by (rule matrix_sum_cong) (rule mult_add_distrib_mat[where nr = n and n = n and nc = n], use a in simp_all)
  also have "\<dots> = cauchy_prod n h f p + cauchy_prod n h g p"
    unfolding cauchy_prod_def by (rule matrix_sum_add_distrib) (use a in simp_all)
  finally show ?thesis .
qed

lemma matrix_sum_zero: "matrix_sum n (\<lambda>r. 0\<^sub>m n n) m = 0\<^sub>m n n"
  by (induction m) simp_all

lemma matrix_sum_single:
  assumes "\<And>q. q < m \<Longrightarrow> F q \<in> carrier_mat n n" and "\<And>q. q < m \<Longrightarrow> q \<noteq> k \<Longrightarrow> F q = 0\<^sub>m n n" and "k < m"
  shows "matrix_sum n F m = F k"
  using assms
proof (induction m)
  case (Suc m)
  show ?case
  proof (cases "k = m")
    case True
    have "matrix_sum n F m = 0\<^sub>m n n"
    proof -
      have "matrix_sum n F m = matrix_sum n (\<lambda>q. 0\<^sub>m n n) m" by (rule matrix_sum_cong) (use Suc.prems True in auto)
      also have "\<dots> = 0\<^sub>m n n" by (induction m) simp_all
      finally show ?thesis .
    qed
    thus ?thesis using True Suc.prems(1)[of m] by simp
  next
    case False
    thus ?thesis using Suc.IH[OF Suc.prems(1,2)] Suc.prems by (simp add: less_Suc_eq matrix_sum_dim)
  qed
qed simp

text \<open>If $d$ vanishes below $q$, then $(d\ast g)_q=d_qg_0$, $(g\ast d)_q=g_0d_q$, both products vanish below
$q$, and the product of two such sequences vanishes at $q>0$ too:\<close>

lemma cauchy_prod_low_left:
  assumes d: "seq_carrier n d" "vanishes_below n q d" and g: "seq_carrier n g"
  shows "cauchy_prod n d g q = d q * g 0"
proof -
  have "matrix_sum n (\<lambda>r. d r * g (q - r)) (Suc q) = d q * g (q - q)"
    by (rule matrix_sum_single) (use d g in \<open>auto simp: vanishes_below_def\<close>)
  thus ?thesis by (simp add: cauchy_prod_def)
qed

lemma cauchy_prod_low_right:
  assumes d: "seq_carrier n d" "vanishes_below n q d" and g: "seq_carrier n g"
  shows "cauchy_prod n g d q = g 0 * d q"
proof -
  have "matrix_sum n (\<lambda>r. g r * d (q - r)) (Suc q) = g 0 * d (q - 0)"
    by (rule matrix_sum_single) (use d g in \<open>auto simp: vanishes_below_def\<close>)
  thus ?thesis by (simp add: cauchy_prod_def)
qed

lemma cauchy_prod_low_below:
  assumes d: "seq_carrier n d" "vanishes_below n q d" and g: "seq_carrier n g" and p: "p < q"
  shows "cauchy_prod n d g p = 0\<^sub>m n n" "cauchy_prod n g d p = 0\<^sub>m n n"
proof -
  have "cauchy_prod n d g p = matrix_sum n (\<lambda>r. 0\<^sub>m n n) (Suc p)"
    unfolding cauchy_prod_def by (rule matrix_sum_cong) (use d g p in \<open>auto simp: vanishes_below_def\<close>)
  thus "cauchy_prod n d g p = 0\<^sub>m n n" by (simp only: matrix_sum_zero)
  have "cauchy_prod n g d p = matrix_sum n (\<lambda>r. 0\<^sub>m n n) (Suc p)"
    unfolding cauchy_prod_def by (rule matrix_sum_cong) (use d g p in \<open>auto simp: vanishes_below_def\<close>)
  thus "cauchy_prod n g d p = 0\<^sub>m n n" by (simp only: matrix_sum_zero)
qed

lemma cauchy_prod_low_both:
  assumes "seq_carrier n d" "vanishes_below n q d" "seq_carrier n e" "vanishes_below n q e" "0 < q"
  shows "cauchy_prod n d e q = 0\<^sub>m n n"
proof -
  have "cauchy_prod n d e q = matrix_sum n (\<lambda>r. 0\<^sub>m n n) (Suc q)"
    unfolding cauchy_prod_def
  proof (rule matrix_sum_cong)
    fix r assume "r < Suc q"
    hence "r < q \<or> q - r < q" using assms(5) by linarith
    thus "d r * e (q - r) = 0\<^sub>m n n" using assms by (auto simp: vanishes_below_def)
  qed
  thus ?thesis by (simp only: matrix_sum_zero)
qed

text \<open>A palindromic formula has odd error order: agreement with $e^{tX}$ below an even degree $q$
extends to degree $q$.\<close>

lemma sym_order:
  assumes Ys: "\<forall>Y \<in> set Ys. Y \<in> carrier_mat n n" and X: "X \<in> carrier_mat n n"
      and pal: "rev Ys = Ys" and ord: "\<forall>p<q. prod_coeff n Ys p = exp_coeff X p" and q: "even q" "0 < q"
  shows "prod_coeff n Ys q = exp_coeff X q"
proof -
  let ?F = "prod_coeff n Ys" and ?E = "exp_coeff X"
  define D where "D = (\<lambda>p. ?F p - ?E p)"
  have F: "seq_carrier n ?F" and E: "seq_carrier n ?E" using prod_coeff_carrier[OF Ys] X by auto
  have Dc: "seq_carrier n D" unfolding seq_carrier_def D_def using seq_carrier_in[OF E] by (simp add: minus_carrier_mat)
  have Dl: "vanishes_below n q D" using ord seq_carrier_in[OF E] by (auto simp: vanishes_below_def D_def minus_r_inv_mat)
  have FE: "?F = (\<lambda>p. ?E p + D p)"
    using F E by (auto simp: fun_eq_iff D_def intro!: eq_matI)
  let ?mE = "seq_scale (-1) ?E" and ?mD = "seq_scale (-1) D"
  have mEc: "seq_carrier n ?mE" and mDc: "seq_carrier n ?mD" and mDl: "vanishes_below n q ?mD"
    using E Dc Dl by (auto simp: vanishes_below_def seq_scale_def)
  have mF: "seq_scale (-1) ?F = (\<lambda>p. ?mE p + ?mD p)"
    using E Dc unfolding FE by (auto simp: fun_eq_iff seq_scale_def add_smult_distrib_left_mat[where nr = n and nc = n])
  have rv: "rev (map ((\<cdot>\<^sub>m) (-1)) Ys) = map ((\<cdot>\<^sub>m) (-1)) Ys" using pal by (metis rev_map)
  have inv: "cauchy_prod n (seq_scale (-1) ?F) ?F = seq_one n"
    using prod_coeff_inverse[OF Ys] unfolding rv prod_coeff_scale[OF Ys] .
  have invE: "cauchy_prod n ?mE ?E q = 0\<^sub>m n n"
  proof -
    have "?mE = exp_coeff ((-1) \<cdot>\<^sub>m X)" by (simp add: fun_eq_iff exp_coeff_smult[OF X])
    thus ?thesis using exp_coeff_inverse[OF X] q(2) by (simp add: seq_one_def)
  qed
  have E0: "?E 0 = 1\<^sub>m n" and mE0: "?mE 0 = 1\<^sub>m n" using X by (simp_all add: exp_coeff_def seq_scale_def one_smult_mat)
  have "0\<^sub>m n n = cauchy_prod n (\<lambda>p. ?mE p + ?mD p) (\<lambda>p. ?E p + D p) q"
    using inv q(2) unfolding mF FE[symmetric] by (simp add: seq_one_def)
  also have "\<dots> = cauchy_prod n ?mE ?E q + cauchy_prod n ?mE D q + (cauchy_prod n ?mD ?E q + cauchy_prod n ?mD D q)"
    using mEc mDc E Dc by (simp add: cauchy_prod_add_left cauchy_prod_add_right seq_carrier_def)
  also have "\<dots> = D q + (-1) ^ q \<cdot>\<^sub>m D q"
    using invE cauchy_prod_low_right[OF Dc Dl mEc] cauchy_prod_low_left[OF mDc mDl E] cauchy_prod_low_both[OF mDc mDl Dc Dl q(2)] E0 mE0 Dc
    by (simp add: seq_scale_def)
  also have "\<dots> = 2 \<cdot>\<^sub>m D q" using q(1) Dc by (auto intro!: eq_matI)
  finally have z: "0\<^sub>m n n = 2 \<cdot>\<^sub>m D q" .
  show ?thesis
  proof (rule eq_matI)
    fix i j assume i: "i < dim_row (exp_coeff X q)" and j: "j < dim_col (exp_coeff X q)"
    have ij: "i < n" "j < n" using i j E by simp_all
    have "0 = 2 * D q $$ (i, j)" using arg_cong[OF z, of "\<lambda>M. M $$ (i, j)"] Dc ij by simp
    hence "D q $$ (i, j) = 0" by simp
    thus "prod_coeff n Ys q $$ (i, j) = exp_coeff X q $$ (i, j)" using F E ij by (simp add: D_def)
  qed (use F E in simp_all)
qed

text \<open>Perturbations of degree $q$ add: if $A_0=B_0=I$ and $D_a$, $D_b$ vanish below $q$, then up to degree $q$
\[ (A+D_a)\ast(B+D_b)=A\ast B+D_a+D_b. \]\<close>

lemma pert2:
  assumes A: "seq_carrier n A" "A 0 = 1\<^sub>m n" and B: "seq_carrier n B" "B 0 = 1\<^sub>m n"
      and Da: "seq_carrier n Da" "vanishes_below n q Da" and Db: "seq_carrier n Db" "vanishes_below n q Db" and q: "0 < q" and p: "p \<le> q"
  shows "cauchy_prod n (\<lambda>p. A p + Da p) (\<lambda>p. B p + Db p) p = cauchy_prod n A B p + Da p + Db p"
proof -
  have e: "cauchy_prod n (\<lambda>p. A p + Da p) (\<lambda>p. B p + Db p) p
      = cauchy_prod n A B p + cauchy_prod n A Db p + (cauchy_prod n Da B p + cauchy_prod n Da Db p)"
    using A B Da Db by (simp add: cauchy_prod_add_left cauchy_prod_add_right seq_carrier_def)
  have AB: "cauchy_prod n A B p \<in> carrier_mat n n" using cauchy_prod_carrier[OF A(1) B(1)] by simp
  show ?thesis
  proof (cases "p < q")
    case True
    thus ?thesis unfolding e using cauchy_prod_low_below[OF Db A(1) True] cauchy_prod_low_below[OF Da B(1) True]
        cauchy_prod_low_below[OF Da Db(1) True] Da Db AB by (simp add: vanishes_below_def)
  next
    case False
    hence pq: "p = q" using p by simp
    have "cauchy_prod n A Db q = Db q" "cauchy_prod n Da B q = Da q" "cauchy_prod n Da Db q = 0\<^sub>m n n"
      using cauchy_prod_low_right[OF Db A(1)] cauchy_prod_low_left[OF Da B(1)] cauchy_prod_low_both[OF Da Db q] A B Da Db by simp_all
    thus ?thesis unfolding e unfolding pq using Da Db cauchy_prod_carrier[OF A(1) B(1)] by (auto intro!: eq_matI)
  qed
qed

lemma cauchy_prod_congr:
  assumes "\<forall>p\<le>q. f p = f' p" "\<forall>p\<le>q. g p = g' p" "p \<le> q"
  shows "cauchy_prod n f g p = cauchy_prod n f' g' p"
  unfolding cauchy_prod_def by (rule matrix_sum_cong) (use assms in auto)

text \<open>The key step of Suzuki's recursion.  If the formula $\Phi$ (with factors $Y$) agrees with $e^{tX}$ below
degree $q$, then the formula made of copies of $\Phi$ with the factors scaled by $c_1,\dots,c_k$ satisfies,
up to degree $q$,
\[ \mathrm{coeff}_p=\frac{\bigl((\sum_jc_j)X\bigr)^p}{p!}+\Bigl(\sum_jc_j^{\,p}\Bigr)\bigl(\mathrm{coeff}_p(\Phi)-X^p/p!\bigr), \]
so the error at degree $q$ vanishes when $\sum_jc_j^{\,q}=0$.\<close>

lemma scaled_copies:
  assumes Ys: "\<forall>Y \<in> set Ys. Y \<in> carrier_mat n n" and X: "X \<in> carrier_mat n n"
      and ord: "\<forall>p<q. prod_coeff n Ys p = exp_coeff X p" and q: "0 < q"
  shows "\<forall>p\<le>q. prod_coeff n (concat (map (\<lambda>c. map ((\<cdot>\<^sub>m) c) Ys) cs)) p
           = exp_coeff (sum_list cs \<cdot>\<^sub>m X) p + (\<Sum>c\<leftarrow>cs. c ^ p) \<cdot>\<^sub>m (prod_coeff n Ys p - exp_coeff X p)"
proof (induction cs)
  case Nil
  show ?case
  proof (intro allI impI)
    fix p assume "p \<le> q"
    have "exp_coeff (0 \<cdot>\<^sub>m X) p = seq_one n p" using zero_smult_mat[OF X] exp_coeff_zero by simp
    show "prod_coeff n (concat (map (\<lambda>c. map ((\<cdot>\<^sub>m) c) Ys) [])) p
        = exp_coeff (sum_list [] \<cdot>\<^sub>m X) p + (\<Sum>c\<leftarrow>[]. c ^ p) \<cdot>\<^sub>m (prod_coeff n Ys p - exp_coeff X p)"
    proof -
      have "prod_coeff n Ys p - exp_coeff X p \<in> carrier_mat n n" using X by (simp add: minus_carrier_mat)
      hence z: "(0::complex) \<cdot>\<^sub>m (prod_coeff n Ys p - exp_coeff X p) = 0\<^sub>m n n" by (rule zero_smult_mat)
      show ?thesis using \<open>exp_coeff (0 \<cdot>\<^sub>m X) p = seq_one n p\<close> by (simp add: z seq_one_def)
    qed
  qed
next
  case (Cons c cs)
  let ?F = "prod_coeff n Ys" and ?E = "exp_coeff X"
  define D where "D = (\<lambda>p. ?F p - ?E p)"
  let ?R = "concat (map (\<lambda>c. map ((\<cdot>\<^sub>m) c) Ys) cs)"
  have F: "seq_carrier n ?F" and E: "seq_carrier n ?E" using prod_coeff_carrier[OF Ys] X by auto
  have Dc: "seq_carrier n D" unfolding seq_carrier_def D_def using seq_carrier_in[OF E] by (simp add: minus_carrier_mat)
  have Dl: "vanishes_below n q D" using ord seq_carrier_in[OF E] by (auto simp: vanishes_below_def D_def)
  have cY: "\<forall>Y \<in> set (map ((\<cdot>\<^sub>m) c) Ys). Y \<in> carrier_mat n n" and cR: "\<forall>Y \<in> set ?R. Y \<in> carrier_mat n n"
    using Ys by auto
  define Ac where "Ac = exp_coeff (c \<cdot>\<^sub>m X)"
  define Dc' where "Dc' = seq_scale c D"
  define Ar where "Ar = exp_coeff (sum_list cs \<cdot>\<^sub>m X)"
  define Dr where "Dr = (\<lambda>p. (\<Sum>c\<leftarrow>cs. c ^ p) \<cdot>\<^sub>m D p)"
  have Acc: "seq_carrier n Ac" "Ac 0 = 1\<^sub>m n" and Arc: "seq_carrier n Ar" "Ar 0 = 1\<^sub>m n"
    using X by (simp_all add: Ac_def Ar_def exp_coeff_def one_smult_mat)
  have Dcc: "seq_carrier n Dc'" "vanishes_below n q Dc'" using Dc Dl by (auto simp: Dc'_def seq_scale_def vanishes_below_def)
  have Drc: "seq_carrier n Dr" "vanishes_below n q Dr" using Dc Dl by (auto simp: Dr_def seq_carrier_def vanishes_below_def)
  have sF: "seq_scale c ?F = (\<lambda>p. Ac p + Dc' p)"
  proof -
    have "?F = (\<lambda>p. ?E p + D p)" using F E by (auto simp: fun_eq_iff D_def intro!: eq_matI)
    hence "seq_scale c ?F = (\<lambda>p. seq_scale c ?E p + seq_scale c D p)"
      using E Dc by (auto simp: fun_eq_iff seq_scale_def add_smult_distrib_left_mat[where nr = n and nc = n])
    thus ?thesis by (simp add: Ac_def Dc'_def fun_eq_iff exp_coeff_smult[OF X])
  qed
  have IH: "\<forall>p\<le>q. prod_coeff n ?R p = Ar p + Dr p" using Cons.IH by (simp add: Ar_def Dr_def D_def)
  show ?case
  proof (intro allI impI)
    fix p assume p: "p \<le> q"
    have "prod_coeff n (concat (map (\<lambda>c. map ((\<cdot>\<^sub>m) c) Ys) (c # cs))) p = cauchy_prod n (seq_scale c ?F) (prod_coeff n ?R) p"
      using prod_coeff_append[OF cY cR] prod_coeff_scale[OF Ys] by simp
    also have "\<dots> = cauchy_prod n (\<lambda>p. Ac p + Dc' p) (\<lambda>p. Ar p + Dr p) p"
      unfolding sF by (rule cauchy_prod_congr) (use IH p in auto)
    also have "\<dots> = cauchy_prod n Ac Ar p + Dc' p + Dr p" by (rule pert2[OF Acc Arc Dcc Drc q p])
    also have "cauchy_prod n Ac Ar p = exp_coeff (sum_list (c # cs) \<cdot>\<^sub>m X) p"
      unfolding Ac_def Ar_def using exp_coeff_add[OF X, of c "sum_list cs" p] by simp
    finally have r: "prod_coeff n (concat (map (\<lambda>c. map ((\<cdot>\<^sub>m) c) Ys) (c # cs))) p
        = exp_coeff (sum_list (c # cs) \<cdot>\<^sub>m X) p + Dc' p + Dr p" .
    have d: "Dc' p + Dr p = (\<Sum>c\<leftarrow>c # cs. c ^ p) \<cdot>\<^sub>m D p"
      using Dc by (simp add: Dc'_def Dr_def seq_scale_def add_smult_distrib_right_mat[OF seq_carrier_in[OF Dc], symmetric])
    have "exp_coeff (sum_list (c # cs) \<cdot>\<^sub>m X) p + Dc' p + Dr p = exp_coeff (sum_list (c # cs) \<cdot>\<^sub>m X) p + (Dc' p + Dr p)"
      by (rule assoc_add_mat[where nr = n and nc = n]) (use X Dcc Drc in simp_all)
    thus "prod_coeff n (concat (map (\<lambda>c. map ((\<cdot>\<^sub>m) c) Ys) (c # cs))) p
        = exp_coeff (sum_list (c # cs) \<cdot>\<^sub>m X) p + (\<Sum>c\<leftarrow>c # cs. c ^ p) \<cdot>\<^sub>m (prod_coeff n Ys p - exp_coeff X p)"
      using r d by (simp add: D_def)
  qed
qed

text \<open>The constant term of a product is $I$ and its linear term the sum of the factors; the sum of the
factors is additive, symmetric under reversal, and linear under scaling.\<close>

lemma prod_coeff_zero: "\<forall>Y \<in> set Ys. Y \<in> carrier_mat n n \<Longrightarrow> prod_coeff n Ys 0 = 1\<^sub>m n"
  by (induction Ys) (auto simp: cauchy_prod_def seq_one_def exp_coeff_def one_smult_mat)

lemma prod_coeff_one: "\<forall>Y \<in> set Ys. Y \<in> carrier_mat n n \<Longrightarrow> prod_coeff n Ys 1 = hamiltonian_sum n Ys"
proof (induction Ys)
  case Nil
  thus ?case by (simp add: seq_one_def)
next
  case (Cons Y Ys)
  have Y: "Y \<in> carrier_mat n n" and Ys: "\<forall>Z \<in> set Ys. Z \<in> carrier_mat n n" using Cons.prems by auto
  have F1: "prod_coeff n Ys 1 \<in> carrier_mat n n" and H: "hamiltonian_sum n Ys \<in> carrier_mat n n"
    using prod_coeff_carrier[OF Ys] hamiltonian_sum_carrier[of Ys n] Ys by auto
  have "prod_coeff n (Y # Ys) 1 = exp_coeff Y 1 * prod_coeff n Ys 0 + exp_coeff Y 0 * prod_coeff n Ys 1"
    using seq_carrier_mult[OF exp_coeff_carrier[OF Y] prod_coeff_carrier[OF Ys], of 0 1] by (simp add: cauchy_prod_def)
  also have "\<dots> = Y + prod_coeff n Ys 1" using Y F1 prod_coeff_zero[OF Ys] by (simp add: exp_coeff_def one_smult_mat)
  finally show ?case using Cons.IH[OF Ys] by simp
qed

lemma hamiltonian_sum_append: "\<forall>Y \<in> set Ys. Y \<in> carrier_mat n n \<Longrightarrow> \<forall>Y \<in> set Zs. Y \<in> carrier_mat n n \<Longrightarrow> hamiltonian_sum n (Ys @ Zs) = hamiltonian_sum n Ys + hamiltonian_sum n Zs"
proof (induction Ys)
  case Nil
  thus ?case using hamiltonian_sum_carrier[of Zs n] by simp
next
  case (Cons Y Ys)
  have c: "Y \<in> carrier_mat n n" "hamiltonian_sum n Ys \<in> carrier_mat n n" "hamiltonian_sum n Zs \<in> carrier_mat n n"
    using Cons.prems hamiltonian_sum_carrier[of Ys n] hamiltonian_sum_carrier[of Zs n] by auto
  thus ?case using Cons by (simp add: assoc_add_mat[OF c])
qed

lemma hamiltonian_sum_rev: "\<forall>Y \<in> set Ys. Y \<in> carrier_mat n n \<Longrightarrow> hamiltonian_sum n (rev Ys) = hamiltonian_sum n Ys"
proof (induction Ys)
  case (Cons Y Ys)
  have c: "Y \<in> carrier_mat n n" "hamiltonian_sum n Ys \<in> carrier_mat n n" using Cons.prems hamiltonian_sum_carrier[of Ys n] by auto
  have "hamiltonian_sum n (rev (Y # Ys)) = hamiltonian_sum n (rev Ys) + (Y + 0\<^sub>m n n)" using Cons.prems by (simp add: hamiltonian_sum_append)
  thus ?case using Cons c by (simp add: comm_add_mat[OF c(2) c(1)])
qed simp

lemma hamiltonian_sum_scale: "\<forall>Y \<in> set Ys. Y \<in> carrier_mat n n \<Longrightarrow> hamiltonian_sum n (map ((\<cdot>\<^sub>m) c) Ys) = c \<cdot>\<^sub>m hamiltonian_sum n Ys"
proof (induction Ys)
  case Nil
  show ?case by (rule eq_matI) auto
next
  case (Cons Y Ys)
  thus ?case using hamiltonian_sum_carrier[of Ys n] by (simp add: add_smult_distrib_left_mat[where nr = n and nc = n])
qed

text \<open>A product formula is a list of factors $(a,H)$ standing for $e^{iatH}$; its coefficients are those
of the matrices \<open>factor_gen (a, H)\<close> $=iaH$.  The symmetric Strang formula
$e^{itH_1/2}\cdots e^{itH_m/2}e^{itH_m/2}\cdots e^{itH_1/2}$ and Suzuki's recursion
$S_{2k+2}=S_{2k}(u)^2\,S_{2k}(1-4u)\,S_{2k}(u)^2$ with $4u^q+(1-4u)^q=0$, $q=2k+3$.\<close>

definition factor_gen :: "real \<times> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "factor_gen x = (\<i> * complex_of_real (fst x)) \<cdot>\<^sub>m snd x"

definition strang :: "complex Matrix.mat list \<Rightarrow> (real \<times> complex Matrix.mat) list" where
  "strang Hs = map (\<lambda>H. (1 / 2, H)) Hs @ rev (map (\<lambda>H. (1 / 2, H)) Hs)"

definition suzuki_weight :: "nat \<Rightarrow> real" where
  "suzuki_weight q = 1 / (4 - root q 4)"

definition suzuki_weights :: "nat \<Rightarrow> real list" where
  "suzuki_weights q = (let u = suzuki_weight q in [u, u, 1 - 4 * u, u, u])"

fun suzuki :: "nat \<Rightarrow> complex Matrix.mat list \<Rightarrow> (real \<times> complex Matrix.mat) list" where
  "suzuki 0 Hs = strang Hs"
| "suzuki (Suc k) Hs = concat (map (\<lambda>c. map (\<lambda>x. (c * fst x, snd x)) (suzuki k Hs)) (suzuki_weights (2 * k + 3)))"

text \<open>Suzuki's weights: for odd $q\ge3$, $u=1/(4-4^{1/q})$ satisfies $4u^q+(1-4u)^q=0$, and the weights
$u,u,1-4u,u,u$ add up to $1$.\<close>

lemma suzuki_weight_cond:
  assumes q: "odd q" "3 \<le> q"
  shows "4 * suzuki_weight q ^ q + (1 - 4 * suzuki_weight q) ^ q = 0"
proof -
  define s where "s = root q 4"
  have sq: "s ^ q = 4" using q by (simp add: s_def)
  have s4: "4 - s \<noteq> 0"
  proof
    assume "4 - s = 0"
    hence "s ^ q = 4 ^ q" by simp
    moreover have "(4::real) ^ q > 4" using power_strict_increasing[of 1 q "4::real"] q by simp
    ultimately show False using sq by simp
  qed
  have "1 - 4 * suzuki_weight q = - s / (4 - s)" using s4 by (simp add: suzuki_weight_def s_def[symmetric] field_simps)
  hence "4 * suzuki_weight q ^ q + (1 - 4 * suzuki_weight q) ^ q = (4 - s ^ q) / (4 - s) ^ q"
    using q(1) s4 by (simp add: suzuki_weight_def s_def[symmetric] power_divide power_minus_odd field_simps)
  thus ?thesis using sq by simp
qed

text \<open>Scaling a factor scales its generator; the formulas consist of factors of the given Hamiltonians, are
$n\times n$, and are palindromes:\<close>

lemma factor_gen_scale: "factor_gen (c * a, H) = complex_of_real c \<cdot>\<^sub>m factor_gen (a, H)"
  by (rule eq_matI) (auto simp: factor_gen_def)

lemma suzuki_snd: "x \<in> set (suzuki k Hs) \<Longrightarrow> snd x \<in> set Hs"
  by (induction k arbitrary: x) (auto simp: strang_def)

lemma suzuki_carrier: "\<forall>H \<in> set Hs. H \<in> carrier_mat n n \<Longrightarrow> \<forall>Y \<in> set (map factor_gen (suzuki k Hs)). Y \<in> carrier_mat n n"
  using suzuki_snd by (fastforce simp: factor_gen_def)

lemma suzuki_palindrome: "rev (suzuki k Hs) = suzuki k Hs"
  by (induction k) (simp_all add: strang_def suzuki_weights_def Let_def rev_map)

text \<open>The Strang formula agrees with $e^{itH}$, $H=\sum_jH_j$, up to degree $2$:\<close>

lemma strang_order:
  assumes Hs: "\<forall>H \<in> set Hs. H \<in> carrier_mat n n"
  shows "\<forall>p\<le>2. prod_coeff n (map factor_gen (strang Hs)) p = exp_coeff (\<i> \<cdot>\<^sub>m hamiltonian_sum n Hs) p"
proof -
  let ?Z = "map ((\<cdot>\<^sub>m) (\<i> / 2)) Hs"
  have st: "map factor_gen (strang Hs) = ?Z @ rev ?Z"
    by (simp add: strang_def factor_gen_def rev_map comp_def)
  have Z: "\<forall>Y \<in> set ?Z. Y \<in> carrier_mat n n" using Hs by auto
  have St: "\<forall>Y \<in> set (map factor_gen (strang Hs)). Y \<in> carrier_mat n n" unfolding st using Z by auto
  have pal: "rev (map factor_gen (strang Hs)) = map factor_gen (strang Hs)" unfolding st by simp
  have H: "hamiltonian_sum n Hs \<in> carrier_mat n n" using hamiltonian_sum_carrier[of Hs n] Hs by auto
  have X: "\<i> \<cdot>\<^sub>m hamiltonian_sum n Hs \<in> carrier_mat n n" using H by simp
  have h2: "hamiltonian_sum n (map factor_gen (strang Hs)) = \<i> \<cdot>\<^sub>m hamiltonian_sum n Hs"
  proof -
    have "hamiltonian_sum n (map factor_gen (strang Hs)) = (\<i> / 2) \<cdot>\<^sub>m hamiltonian_sum n Hs + (\<i> / 2) \<cdot>\<^sub>m hamiltonian_sum n Hs"
      unfolding st hamiltonian_sum_append[OF Z] by (simp add: Z hamiltonian_sum_rev hamiltonian_sum_scale[OF Hs] hamiltonian_sum_append)
    also have "\<dots> = \<i> \<cdot>\<^sub>m hamiltonian_sum n Hs" using H by (auto intro!: eq_matI)
    finally show ?thesis .
  qed
  have ord1: "\<forall>p<2. prod_coeff n (map factor_gen (strang Hs)) p = exp_coeff (\<i> \<cdot>\<^sub>m hamiltonian_sum n Hs) p"
  proof (intro allI impI)
    fix p :: nat assume "p < 2"
    hence "p = 0 \<or> p = 1" by auto
    thus "prod_coeff n (map factor_gen (strang Hs)) p = exp_coeff (\<i> \<cdot>\<^sub>m hamiltonian_sum n Hs) p"
      using prod_coeff_zero[OF St] prod_coeff_one[OF St] h2 X by (auto simp: exp_coeff_def one_smult_mat)
  qed
  have "prod_coeff n (map factor_gen (strang Hs)) 2 = exp_coeff (\<i> \<cdot>\<^sub>m hamiltonian_sum n Hs) 2" by (rule sym_order[OF St X pal ord1]) simp_all
  thus ?thesis using ord1 by (auto simp: le_less)
qed

text \<open>By induction on $k$, using the palindrome property (odd order) and \<open>scaled_copies\<close> with
$\sum_jc_j=1$ and $\sum_jc_j^{2k+3}=0$:
\[ \mathrm{coeff}_p\bigl(S_{2k+2}\bigr)=\frac{(iH)^p}{p!}\qquad(p\le 2k+2). \]\<close>

theorem suzuki_order:
  assumes Hs: "\<forall>H \<in> set Hs. H \<in> carrier_mat n n"
  shows "\<forall>p\<le>2 * k + 2. prod_coeff n (map factor_gen (suzuki k Hs)) p = exp_coeff (\<i> \<cdot>\<^sub>m hamiltonian_sum n Hs) p"
proof (induction k)
  case 0
  thus ?case using strang_order[OF Hs] by simp
next
  case (Suc k)
  let ?S = "map factor_gen (suzuki k Hs)" and ?q = "2 * k + 3" and ?X = "\<i> \<cdot>\<^sub>m hamiltonian_sum n Hs"
  let ?cs = "map complex_of_real (suzuki_weights ?q)"
  have S: "\<forall>Y \<in> set ?S. Y \<in> carrier_mat n n" by (rule suzuki_carrier[OF Hs])
  have X: "?X \<in> carrier_mat n n" using hamiltonian_sum_carrier[of Hs n] Hs by auto
  have ordS: "\<forall>p<?q. prod_coeff n ?S p = exp_coeff ?X p" using Suc.IH by auto
  have mt: "map factor_gen (suzuki (Suc k) Hs) = concat (map (\<lambda>c. map ((\<cdot>\<^sub>m) c) ?S) ?cs)"
    by (simp add: map_concat comp_def factor_gen_scale)
  define u where "u = complex_of_real (suzuki_weight ?q)"
  have cs: "?cs = [u, u, 1 - 4 * u, u, u]" by (simp add: suzuki_weights_def u_def Let_def)
  have sum1: "sum_list ?cs = 1" by (simp add: cs)
  have sumq: "(\<Sum>c\<leftarrow>?cs. c ^ ?q) = 0"
  proof -
    have "(\<Sum>c\<leftarrow>?cs. c ^ ?q) = complex_of_real (4 * suzuki_weight ?q ^ ?q + (1 - 4 * suzuki_weight ?q) ^ ?q)"
      by (simp add: cs u_def)
    thus ?thesis using suzuki_weight_cond[of ?q] by simp
  qed
  have sc: "\<forall>p\<le>?q. prod_coeff n (map factor_gen (suzuki (Suc k) Hs)) p
      = exp_coeff (sum_list ?cs \<cdot>\<^sub>m ?X) p + (\<Sum>c\<leftarrow>?cs. c ^ p) \<cdot>\<^sub>m (prod_coeff n ?S p - exp_coeff ?X p)"
    unfolding mt by (rule scaled_copies[OF S X ordS]) simp
  have ordq: "\<forall>p\<le>?q. prod_coeff n (map factor_gen (suzuki (Suc k) Hs)) p = exp_coeff ?X p"
  proof (intro allI impI)
    fix p assume p: "p \<le> ?q"
    have z: "(\<Sum>c\<leftarrow>?cs. c ^ p) \<cdot>\<^sub>m (prod_coeff n ?S p - exp_coeff ?X p) = 0\<^sub>m n n"
    proof (cases "p < ?q")
      case True
      hence "prod_coeff n ?S p - exp_coeff ?X p = 0\<^sub>m n n" using ordS seq_carrier_in[OF exp_coeff_carrier[OF X]] by simp
      thus ?thesis by (auto intro!: eq_matI)
    next
      case False
      hence "p = ?q" using p by simp
      have "prod_coeff n ?S p - exp_coeff ?X p \<in> carrier_mat n n" using X by (simp add: minus_carrier_mat)
      thus ?thesis using sumq \<open>p = ?q\<close> by (simp add: zero_smult_mat)
    qed
    have e: "prod_coeff n (map factor_gen (suzuki (Suc k) Hs)) p
        = exp_coeff (sum_list ?cs \<cdot>\<^sub>m ?X) p + (\<Sum>c\<leftarrow>?cs. c ^ p) \<cdot>\<^sub>m (prod_coeff n ?S p - exp_coeff ?X p)"
      using sc p by blast
    show "prod_coeff n (map factor_gen (suzuki (Suc k) Hs)) p = exp_coeff ?X p"
      unfolding e z sum1 using seq_carrier_in[OF exp_coeff_carrier[OF X]] X by (simp add: one_smult_mat)
  qed
  have S': "\<forall>Y \<in> set (map factor_gen (suzuki (Suc k) Hs)). Y \<in> carrier_mat n n" by (rule suzuki_carrier[OF Hs])
  have pal': "rev (map factor_gen (suzuki (Suc k) Hs)) = map factor_gen (suzuki (Suc k) Hs)"
    using suzuki_palindrome[of "Suc k" Hs] by (metis rev_map)
  have top: "prod_coeff n (map factor_gen (suzuki (Suc k) Hs)) (?q + 1) = exp_coeff ?X (?q + 1)"
    by (rule sym_order[OF S' X pal']) (use ordq in auto)
  show ?case
  proof (intro allI impI)
    fix p assume "p \<le> 2 * Suc k + 2"
    hence "p \<le> ?q \<or> p = ?q + 1" by arith
    thus "prod_coeff n (map factor_gen (suzuki (Suc k) Hs)) p = exp_coeff ?X p" using ordq top by blast
  qed
qed

end

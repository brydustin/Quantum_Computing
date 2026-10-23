theory Suzuki_Order
  imports Trotter_Product_Formula Matrix_Sums
begin

section \<open>Order conditions for product formulas\<close>

text \<open>Taylor coefficients of products $e^{tY_1}\cdots e^{tY_m}$ as convolutions of matrix sequences.
A palindromic product has odd error order (\<open>sym_order\<close>), and Suzuki's five-fold recursion
raises the order by two (\<open>scaled_copies\<close>), so $S_{2k+2}$ agrees with $e^{itH}$ up to degree
$2k+2$ (\<open>suzuki_order\<close>).\<close>

definition sconv :: "nat \<Rightarrow> (nat \<Rightarrow> complex Matrix.mat) \<Rightarrow> (nat \<Rightarrow> complex Matrix.mat) \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
  "sconv n f g p = matrix_sum n (\<lambda>q. f q * g (p - q)) (Suc p)"

definition carr :: "nat \<Rightarrow> (nat \<Rightarrow> complex Matrix.mat) \<Rightarrow> bool" where
  "carr n f \<longleftrightarrow> (\<forall>p. f p \<in> carrier_mat n n)"

lemma carr_in [simp]: "carr n f \<Longrightarrow> f q \<in> carrier_mat n n"
  by (simp add: carr_def)

lemma carr_row [simp]: "carr n f \<Longrightarrow> dim_row (f q) = n"
  by (rule carrier_matD(1)[OF carr_in])

lemma carr_col [simp]: "carr n f \<Longrightarrow> dim_col (f q) = n"
  by (rule carrier_matD(2)[OF carr_in])

lemma carr_mult [simp]: "carr n f \<Longrightarrow> carr n g \<Longrightarrow> f q * g r \<in> carrier_mat n n"
  by (rule mult_carrier_mat[OF carr_in carr_in])

lemma sconv_carr: "carr n f \<Longrightarrow> carr n g \<Longrightarrow> carr n (sconv n f g)"
  unfolding carr_def sconv_def by (intro allI matrix_sum_dim, rule mult_carrier_mat) auto

lemma sconv_index:
  assumes "carr n f" "carr n g" "i < n" "j < n"
  shows "sconv n f g p $$ (i, j) = (\<Sum>q\<le>p. \<Sum>c<n. f q $$ (i, c) * g (p - q) $$ (c, j))"
proof -
  have "sconv n f g p $$ (i, j) = (\<Sum>q<Suc p. (f q * g (p - q)) $$ (i, j))"
    unfolding sconv_def by (rule matrix_sum_index) (use assms in simp_all)
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

lemma sconv_assoc:
  assumes f: "carr n f" and g: "carr n g" and h: "carr n h"
  shows "sconv n (sconv n f g) h p = sconv n f (sconv n g h) p"
proof (rule eq_matI)
  fix i j assume i: "i < dim_row (sconv n f (sconv n g h) p)" and j: "j < dim_col (sconv n f (sconv n g h) p)"
  have ij: "i < n" "j < n" using i j sconv_carr[OF f sconv_carr[OF g h]] by simp_all
  have fg: "carr n (sconv n f g)" and gh: "carr n (sconv n g h)" using sconv_carr f g h by auto
  have sw1: "(\<Sum>c<n. \<Sum>r\<le>q. \<Sum>e<n. T c r e) = (\<Sum>r\<le>q. \<Sum>e<n. \<Sum>c<n. T c r e)" for T :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex" and q
    by (subst sum.swap) (rule sum.cong[OF refl], rule sum.swap)
  have sw2: "(\<Sum>e<n. \<Sum>s\<le>m. \<Sum>c<n. T e s c) = (\<Sum>s\<le>m. \<Sum>e<n. \<Sum>c<n. T e s c)" for T :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex" and m
    by (rule sum.swap)
  have "sconv n (sconv n f g) h p $$ (i, j)
      = (\<Sum>q\<le>p. \<Sum>c<n. (\<Sum>r\<le>q. \<Sum>e<n. f r $$ (i, e) * g (q - r) $$ (e, c)) * h (p - q) $$ (c, j))"
    unfolding sconv_index[OF fg h ij] using sconv_index[OF f g ij(1)] by (intro sum.cong refl) simp
  also have "\<dots> = (\<Sum>q\<le>p. \<Sum>r\<le>q. \<Sum>e<n. \<Sum>c<n. f r $$ (i, e) * g (q - r) $$ (e, c) * h (p - q) $$ (c, j))"
    by (simp only: sum_distrib_right sw1)
  also have "\<dots> = (\<Sum>r\<le>p. \<Sum>s\<le>p - r. \<Sum>e<n. \<Sum>c<n. f r $$ (i, e) * g s $$ (e, c) * h (p - r - s) $$ (c, j))"
    by (rule triple_reindex)
  also have "\<dots> = (\<Sum>r\<le>p. \<Sum>e<n. f r $$ (i, e) * (\<Sum>s\<le>p - r. \<Sum>c<n. g s $$ (e, c) * h (p - r - s) $$ (c, j)))"
    unfolding sum_distrib_left sw2 by (simp add: mult_ac)
  also have "\<dots> = sconv n f (sconv n g h) p $$ (i, j)"
    unfolding sconv_index[OF f gh ij] using sconv_index[OF g h _ ij(2)] by (intro sum.cong refl) simp
  finally show "sconv n (sconv n f g) h p $$ (i, j) = sconv n f (sconv n g h) p $$ (i, j)" .
qed (use sconv_carr[OF sconv_carr[OF f g] h] sconv_carr[OF f sconv_carr[OF g h]] in \<open>simp_all add: carr_def\<close>)


definition sunit :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
  "sunit n p = (if p = 0 then 1\<^sub>m n else 0\<^sub>m n n)"

definition sscale :: "complex \<Rightarrow> (nat \<Rightarrow> complex Matrix.mat) \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
  "sscale u f p = (u ^ p) \<cdot>\<^sub>m f p"

definition texp :: "complex Matrix.mat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
  "texp X p = complex_of_real (1 / fact p) \<cdot>\<^sub>m X ^\<^sub>m p"

lemma sunit_carr [simp]: "carr n (sunit n)"
  by (simp add: carr_def sunit_def)

lemma sscale_carr [simp]: "carr n f \<Longrightarrow> carr n (sscale u f)"
  by (simp add: carr_def sscale_def)

lemma texp_carr [simp]: "X \<in> carrier_mat n n \<Longrightarrow> carr n (texp X)"
  by (simp add: carr_def texp_def)

lemma sconv_unit_left: "carr n f \<Longrightarrow> sconv n (sunit n) f p = f p"
proof (induction p)
  case 0
  thus ?case by (simp add: sconv_def sunit_def)
next
  case (Suc p)
  have "matrix_sum n (\<lambda>q. sunit n q * f (Suc p - q)) (Suc p) = matrix_sum n (\<lambda>q. if q = 0 then f (Suc p) else 0\<^sub>m n n) (Suc p)"
    by (rule matrix_sum_cong) (use Suc.prems in \<open>auto simp: sunit_def\<close>)
  also have "\<dots> = f (Suc p)"
  proof -
    have z: "matrix_sum n (\<lambda>q. if q = 0 then f (Suc p) else 0\<^sub>m n n) m = f (Suc p)" if "0 < m" for m
      using that by (induction m) (use Suc.prems in \<open>auto simp: gr0_conv_Suc\<close>)
    show ?thesis by (rule z) simp
  qed
  finally show ?case using Suc.prems by (simp add: sconv_def sunit_def)
qed

lemma sconv_unit_right: "carr n f \<Longrightarrow> sconv n f (sunit n) p = f p"
proof (rule eq_matI)
  fix i j assume f: "carr n f" and i: "i < dim_row (f p)" and j: "j < dim_col (f p)"
  have ij: "i < n" "j < n" using i j f by simp_all
  have "sconv n f (sunit n) p $$ (i, j) = (\<Sum>q\<le>p. \<Sum>c<n. f q $$ (i, c) * sunit n (p - q) $$ (c, j))"
    by (rule sconv_index[OF f sunit_carr ij])
  also have "\<dots> = (\<Sum>q\<le>p. if q = p then f p $$ (i, j) else 0)"
  proof (rule sum.cong[OF refl])
    fix q assume q: "q \<in> {..p}"
    show "(\<Sum>c<n. f q $$ (i, c) * sunit n (p - q) $$ (c, j)) = (if q = p then f p $$ (i, j) else 0)"
    proof (cases "q = p")
      case True
      have "(\<Sum>c<n. f p $$ (i, c) * (if c = j then 1 else 0)) = (\<Sum>c<n. if c = j then f p $$ (i, c) else 0)"
        by (intro sum.cong) auto
      also have "\<dots> = f p $$ (i, j)" using ij by simp
      finally have "(\<Sum>c<n. f p $$ (i, c) * (if c = j then 1 else 0)) = f p $$ (i, j)" .
      thus ?thesis using True ij by (simp add: sunit_def one_mat_def)
    qed (use q ij in \<open>auto simp: sunit_def\<close>)
  qed
  also have "\<dots> = f p $$ (i, j)" by simp
  finally show "sconv n f (sunit n) p $$ (i, j) = f p $$ (i, j)" .
qed (simp_all add: sconv_carr[THEN carr_row] sconv_carr[THEN carr_col])

lemma sscale_sconv: "carr n f \<Longrightarrow> carr n g \<Longrightarrow> sconv n (sscale u f) (sscale u g) p = sscale u (sconv n f g) p"
proof (rule eq_matI)
  fix i j assume f: "carr n f" and g: "carr n g" and i: "i < dim_row (sscale u (sconv n f g) p)"
    and j: "j < dim_col (sscale u (sconv n f g) p)"
  have ij: "i < n" "j < n" using i j sconv_carr[OF f g] by (simp_all add: sscale_def)
  have "sconv n (sscale u f) (sscale u g) p $$ (i, j) = (\<Sum>q\<le>p. \<Sum>c<n. (u ^ q * f q $$ (i, c)) * (u ^ (p - q) * g (p - q) $$ (c, j)))"
    unfolding sconv_index[OF sscale_carr[OF f] sscale_carr[OF g] ij] using ij f g by (intro sum.cong refl) (simp add: sscale_def)
  also have "\<dots> = (\<Sum>q\<le>p. \<Sum>c<n. u ^ p * (f q $$ (i, c) * g (p - q) $$ (c, j)))"
    by (intro sum.cong refl) (simp add: mult_ac power_add[symmetric])
  also have "\<dots> = sscale u (sconv n f g) p $$ (i, j)"
    unfolding sscale_def using ij sconv_index[OF f g ij] sconv_carr[OF f g] by (simp add: sum_distrib_left)
  finally show "sconv n (sscale u f) (sscale u g) p $$ (i, j) = sscale u (sconv n f g) p $$ (i, j)" .
qed (simp_all add: sscale_def sconv_carr[THEN carr_row] sconv_carr[THEN carr_col])

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

lemma texp_smult: "X \<in> carrier_mat n n \<Longrightarrow> texp (u \<cdot>\<^sub>m X) p = sscale u (texp X) p"
  by (simp add: texp_def sscale_def smult_pow_mat) (rule eq_matI, auto simp: mult_ac)

lemma texp_zero: "texp (0\<^sub>m n n) p = sunit n p"
  by (cases p) (simp_all add: texp_def sunit_def one_smult_mat)

lemma texp_add:
  assumes X: "X \<in> carrier_mat n n"
  shows "sconv n (texp (a \<cdot>\<^sub>m X)) (texp (b \<cdot>\<^sub>m X)) p = texp ((a + b) \<cdot>\<^sub>m X) p"
proof -
  have Xq: "\<And>q. X ^\<^sub>m q \<in> carrier_mat n n" using X by simp
  have tm: "texp (a \<cdot>\<^sub>m X) q * texp (b \<cdot>\<^sub>m X) (p - q)
      = (a ^ q * b ^ (p - q) / (fact q * fact (p - q))) \<cdot>\<^sub>m X ^\<^sub>m p" if "q \<le> p" for q
  proof -
    have "X ^\<^sub>m q * X ^\<^sub>m (p - q) = X ^\<^sub>m p" using that X by (simp add: pow_mat_add[OF X, symmetric])
    hence "(1 / fact q * a ^ q) \<cdot>\<^sub>m X ^\<^sub>m q * ((1 / fact (p - q) * b ^ (p - q)) \<cdot>\<^sub>m X ^\<^sub>m (p - q))
        = (a ^ q * b ^ (p - q) / (fact q * fact (p - q))) \<cdot>\<^sub>m X ^\<^sub>m p"
      by (simp add: smult_mult_smult[OF Xq Xq] field_simps)
    moreover have "texp (a \<cdot>\<^sub>m X) q = (1 / fact q * a ^ q) \<cdot>\<^sub>m X ^\<^sub>m q"
      "texp (b \<cdot>\<^sub>m X) (p - q) = (1 / fact (p - q) * b ^ (p - q)) \<cdot>\<^sub>m X ^\<^sub>m (p - q)"
      by (simp_all add: texp_def smult_pow_mat[OF X]) (rule eq_matI, auto)+
    ultimately show ?thesis by simp
  qed
  have "sconv n (texp (a \<cdot>\<^sub>m X)) (texp (b \<cdot>\<^sub>m X)) p
      = matrix_sum n (\<lambda>q. (a ^ q * b ^ (p - q) / (fact q * fact (p - q))) \<cdot>\<^sub>m X ^\<^sub>m p) (Suc p)"
    unfolding sconv_def by (rule matrix_sum_cong) (simp add: tm)
  also have "\<dots> = (\<Sum>q<Suc p. a ^ q * b ^ (p - q) / (fact q * fact (p - q))) \<cdot>\<^sub>m X ^\<^sub>m p"
    by (rule matrix_sum_scalar[OF Xq])
  also have "(\<Sum>q<Suc p. a ^ q * b ^ (p - q) / (fact q * fact (p - q))) = (a + b) ^ p / fact p"
  proof -
    have "(a + b) ^ p = (\<Sum>q\<le>p. of_nat (p choose q) * a ^ q * b ^ (p - q))" by (rule binomial_ring)
    also have "\<dots> = fact p * (\<Sum>q\<le>p. a ^ q * b ^ (p - q) / (fact q * fact (p - q)))"
      unfolding sum_distrib_left by (intro sum.cong refl) (simp add: binomial_fact field_simps)
    finally show ?thesis by (simp add: lessThan_Suc_atMost field_simps)
  qed
  also have "((a + b) ^ p / fact p) \<cdot>\<^sub>m X ^\<^sub>m p = texp ((a + b) \<cdot>\<^sub>m X) p"
    by (simp add: texp_def smult_pow_mat[OF X]) (rule eq_matI, auto)
  finally show ?thesis .
qed

fun fcoef :: "nat \<Rightarrow> complex Matrix.mat list \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
  "fcoef n [] = sunit n"
| "fcoef n (Y # Ys) = sconv n (texp Y) (fcoef n Ys)"

lemma fcoef_carr: "\<forall>Y \<in> set Ys. Y \<in> carrier_mat n n \<Longrightarrow> carr n (fcoef n Ys)"
  by (induction Ys) (auto intro: sconv_carr)

lemma fcoef_append:
  assumes "\<forall>Y \<in> set Ys. Y \<in> carrier_mat n n" "\<forall>Y \<in> set Zs. Y \<in> carrier_mat n n"
  shows "fcoef n (Ys @ Zs) = sconv n (fcoef n Ys) (fcoef n Zs)"
  using assms(1)
proof (induction Ys)
  case Nil
  show ?case using fcoef_carr[OF assms(2)] by (simp add: fun_eq_iff sconv_unit_left)
next
  case (Cons Y Ys)
  have c: "carr n (texp Y)" "carr n (fcoef n Ys)" "carr n (fcoef n Zs)"
    using Cons.prems fcoef_carr[OF assms(2)] fcoef_carr[of Ys n] by auto
  have ih: "fcoef n (Ys @ Zs) = sconv n (fcoef n Ys) (fcoef n Zs)" using Cons by simp
  show ?case unfolding append_Cons fcoef.simps ih using sconv_assoc[OF c] by (simp add: fun_eq_iff)
qed

lemma sscale_sunit: "sscale u (sunit n) = sunit n"
  by (auto simp: fun_eq_iff sscale_def sunit_def one_smult_mat)

lemma fcoef_scale: "\<forall>Y \<in> set Ys. Y \<in> carrier_mat n n \<Longrightarrow> fcoef n (map ((\<cdot>\<^sub>m) u) Ys) = sscale u (fcoef n Ys)"
proof (induction Ys)
  case Nil
  thus ?case by (simp add: sscale_sunit)
next
  case (Cons Y Ys)
  have Y: "Y \<in> carrier_mat n n" and F: "carr n (fcoef n Ys)" using Cons.prems fcoef_carr[of Ys n] by auto
  have t: "texp (u \<cdot>\<^sub>m Y) = sscale u (texp Y)" by (simp add: fun_eq_iff texp_smult[OF Y])
  have ih: "fcoef n (map ((\<cdot>\<^sub>m) u) Ys) = sscale u (fcoef n Ys)" using Cons by simp
  show ?case unfolding list.map fcoef.simps t ih using sscale_sconv[OF texp_carr[OF Y] F] by (simp add: fun_eq_iff)
qed

lemma zero_smult_mat: "A \<in> carrier_mat n n \<Longrightarrow> (0::complex) \<cdot>\<^sub>m A = 0\<^sub>m n n"
  by (rule eq_matI) auto

lemma texp_inverse:
  assumes Y: "Y \<in> carrier_mat n n"
  shows "sconv n (texp ((-1) \<cdot>\<^sub>m Y)) (texp Y) = sunit n"
proof -
  have "sconv n (texp ((-1) \<cdot>\<^sub>m Y)) (texp (1 \<cdot>\<^sub>m Y)) p = texp ((-1 + 1) \<cdot>\<^sub>m Y) p" for p
    by (rule texp_add[OF Y])
  thus ?thesis using zero_smult_mat[OF Y] by (simp add: fun_eq_iff one_smult_mat texp_zero)
qed

lemma sconv_assoc_fun: "carr n f \<Longrightarrow> carr n g \<Longrightarrow> carr n h \<Longrightarrow> sconv n (sconv n f g) h = sconv n f (sconv n g h)"
  by (simp add: fun_eq_iff sconv_assoc)

lemma sconv_unit_right_fun: "carr n f \<Longrightarrow> sconv n f (sunit n) = f"
  by (simp add: fun_eq_iff sconv_unit_right)

lemma sconv_unit_left_fun: "carr n f \<Longrightarrow> sconv n (sunit n) f = f"
  by (simp add: fun_eq_iff sconv_unit_left)

lemma fcoef_inverse:
  "\<forall>Y \<in> set Ys. Y \<in> carrier_mat n n \<Longrightarrow> sconv n (fcoef n (rev (map ((\<cdot>\<^sub>m) (-1)) Ys))) (fcoef n Ys) = sunit n"
proof (induction Ys)
  case Nil
  thus ?case by (simp add: fun_eq_iff sconv_unit_left)
next
  case (Cons Y Ys)
  have Y: "Y \<in> carrier_mat n n" and Ys: "\<forall>Z \<in> set Ys. Z \<in> carrier_mat n n" using Cons.prems by auto
  let ?A = "rev (map ((\<cdot>\<^sub>m) (-1)) Ys)"
  have A: "\<forall>Z \<in> set ?A. Z \<in> carrier_mat n n" using Ys by auto
  have nY: "(-1) \<cdot>\<^sub>m Y \<in> carrier_mat n n" using Y by simp
  have c: "carr n (fcoef n ?A)" "carr n (texp ((-1) \<cdot>\<^sub>m Y))" "carr n (texp Y)" "carr n (fcoef n Ys)"
    using fcoef_carr[OF A] fcoef_carr[OF Ys] Y nY by auto
  have "fcoef n (rev (map ((\<cdot>\<^sub>m) (-1)) (Y # Ys))) = sconv n (fcoef n ?A) (texp ((-1) \<cdot>\<^sub>m Y))"
    using fcoef_append[OF A, of "[(-1) \<cdot>\<^sub>m Y]"] nY by (simp add: sconv_unit_right_fun)
  hence "sconv n (fcoef n (rev (map ((\<cdot>\<^sub>m) (-1)) (Y # Ys)))) (fcoef n (Y # Ys))
      = sconv n (sconv n (fcoef n ?A) (texp ((-1) \<cdot>\<^sub>m Y))) (sconv n (texp Y) (fcoef n Ys))" by simp
  also have "\<dots> = sconv n (fcoef n ?A) (sconv n (sconv n (texp ((-1) \<cdot>\<^sub>m Y)) (texp Y)) (fcoef n Ys))"
    by (simp only: sconv_assoc_fun[OF c(1,2) sconv_carr[OF c(3,4)]] sconv_assoc_fun[OF c(2,3,4), symmetric])
  also have "\<dots> = sconv n (fcoef n ?A) (fcoef n Ys)"
    by (simp only: texp_inverse[OF Y] sconv_unit_left_fun[OF c(4)])
  finally show ?case using Cons.IH[OF Ys] by simp
qed

definition low :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> complex Matrix.mat) \<Rightarrow> bool" where
  "low n q f \<longleftrightarrow> (\<forall>p<q. f p = 0\<^sub>m n n)"

lemma sconv_add_left:
  "carr n f \<Longrightarrow> carr n g \<Longrightarrow> carr n h \<Longrightarrow> sconv n (\<lambda>p. f p + g p) h p = sconv n f h p + sconv n g h p"
proof -
  assume a: "carr n f" "carr n g" "carr n h"
  have "sconv n (\<lambda>p. f p + g p) h p = matrix_sum n (\<lambda>q. f q * h (p - q) + g q * h (p - q)) (Suc p)"
    unfolding sconv_def by (rule matrix_sum_cong) (rule add_mult_distrib_mat[where nr = n and n = n and nc = n], use a in simp_all)
  also have "\<dots> = sconv n f h p + sconv n g h p"
    unfolding sconv_def by (rule matrix_sum_add_distrib) (use a in simp_all)
  finally show ?thesis .
qed

lemma sconv_add_right:
  "carr n f \<Longrightarrow> carr n g \<Longrightarrow> carr n h \<Longrightarrow> sconv n h (\<lambda>p. f p + g p) p = sconv n h f p + sconv n h g p"
proof -
  assume a: "carr n f" "carr n g" "carr n h"
  have "sconv n h (\<lambda>p. f p + g p) p = matrix_sum n (\<lambda>q. h q * f (p - q) + h q * g (p - q)) (Suc p)"
    unfolding sconv_def by (rule matrix_sum_cong) (rule mult_add_distrib_mat[where nr = n and n = n and nc = n], use a in simp_all)
  also have "\<dots> = sconv n h f p + sconv n h g p"
    unfolding sconv_def by (rule matrix_sum_add_distrib) (use a in simp_all)
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

lemma sconv_low_left:
  assumes d: "carr n d" "low n q d" and g: "carr n g"
  shows "sconv n d g q = d q * g 0"
proof -
  have "matrix_sum n (\<lambda>r. d r * g (q - r)) (Suc q) = d q * g (q - q)"
    by (rule matrix_sum_single) (use d g in \<open>auto simp: low_def\<close>)
  thus ?thesis by (simp add: sconv_def)
qed

lemma sconv_low_right:
  assumes d: "carr n d" "low n q d" and g: "carr n g"
  shows "sconv n g d q = g 0 * d q"
proof -
  have "matrix_sum n (\<lambda>r. g r * d (q - r)) (Suc q) = g 0 * d (q - 0)"
    by (rule matrix_sum_single) (use d g in \<open>auto simp: low_def\<close>)
  thus ?thesis by (simp add: sconv_def)
qed

lemma sconv_low_below:
  assumes d: "carr n d" "low n q d" and g: "carr n g" and p: "p < q"
  shows "sconv n d g p = 0\<^sub>m n n" "sconv n g d p = 0\<^sub>m n n"
proof -
  have "sconv n d g p = matrix_sum n (\<lambda>r. 0\<^sub>m n n) (Suc p)"
    unfolding sconv_def by (rule matrix_sum_cong) (use d g p in \<open>auto simp: low_def\<close>)
  thus "sconv n d g p = 0\<^sub>m n n" by (simp only: matrix_sum_zero)
  have "sconv n g d p = matrix_sum n (\<lambda>r. 0\<^sub>m n n) (Suc p)"
    unfolding sconv_def by (rule matrix_sum_cong) (use d g p in \<open>auto simp: low_def\<close>)
  thus "sconv n g d p = 0\<^sub>m n n" by (simp only: matrix_sum_zero)
qed

lemma sconv_low_both:
  assumes "carr n d" "low n q d" "carr n e" "low n q e" "0 < q"
  shows "sconv n d e q = 0\<^sub>m n n"
proof -
  have "sconv n d e q = matrix_sum n (\<lambda>r. 0\<^sub>m n n) (Suc q)"
    unfolding sconv_def
  proof (rule matrix_sum_cong)
    fix r assume "r < Suc q"
    hence "r < q \<or> q - r < q" using assms(5) by linarith
    thus "d r * e (q - r) = 0\<^sub>m n n" using assms by (auto simp: low_def)
  qed
  thus ?thesis by (simp only: matrix_sum_zero)
qed

text \<open>A palindromic formula has odd error order: agreement with $e^{tX}$ below an even degree $q$
extends to degree $q$.\<close>

lemma sym_order:
  assumes Ys: "\<forall>Y \<in> set Ys. Y \<in> carrier_mat n n" and X: "X \<in> carrier_mat n n"
      and pal: "rev Ys = Ys" and ord: "\<forall>p<q. fcoef n Ys p = texp X p" and q: "even q" "0 < q"
  shows "fcoef n Ys q = texp X q"
proof -
  let ?F = "fcoef n Ys" and ?E = "texp X"
  define D where "D = (\<lambda>p. ?F p - ?E p)"
  have F: "carr n ?F" and E: "carr n ?E" using fcoef_carr[OF Ys] X by auto
  have Dc: "carr n D" unfolding carr_def D_def using carr_in[OF E] by (simp add: minus_carrier_mat)
  have Dl: "low n q D" using ord carr_in[OF E] by (auto simp: low_def D_def minus_r_inv_mat)
  have FE: "?F = (\<lambda>p. ?E p + D p)"
    using F E by (auto simp: fun_eq_iff D_def intro!: eq_matI)
  let ?mE = "sscale (-1) ?E" and ?mD = "sscale (-1) D"
  have mEc: "carr n ?mE" and mDc: "carr n ?mD" and mDl: "low n q ?mD"
    using E Dc Dl by (auto simp: low_def sscale_def)
  have mF: "sscale (-1) ?F = (\<lambda>p. ?mE p + ?mD p)"
    using E Dc unfolding FE by (auto simp: fun_eq_iff sscale_def add_smult_distrib_left_mat[where nr = n and nc = n])
  have rv: "rev (map ((\<cdot>\<^sub>m) (-1)) Ys) = map ((\<cdot>\<^sub>m) (-1)) Ys" using pal by (metis rev_map)
  have inv: "sconv n (sscale (-1) ?F) ?F = sunit n"
    using fcoef_inverse[OF Ys] unfolding rv fcoef_scale[OF Ys] .
  have invE: "sconv n ?mE ?E q = 0\<^sub>m n n"
  proof -
    have "?mE = texp ((-1) \<cdot>\<^sub>m X)" by (simp add: fun_eq_iff texp_smult[OF X])
    thus ?thesis using texp_inverse[OF X] q(2) by (simp add: sunit_def)
  qed
  have E0: "?E 0 = 1\<^sub>m n" and mE0: "?mE 0 = 1\<^sub>m n" using X by (simp_all add: texp_def sscale_def one_smult_mat)
  have "0\<^sub>m n n = sconv n (\<lambda>p. ?mE p + ?mD p) (\<lambda>p. ?E p + D p) q"
    using inv q(2) unfolding mF FE[symmetric] by (simp add: sunit_def)
  also have "\<dots> = sconv n ?mE ?E q + sconv n ?mE D q + (sconv n ?mD ?E q + sconv n ?mD D q)"
    using mEc mDc E Dc by (simp add: sconv_add_left sconv_add_right carr_def)
  also have "\<dots> = D q + (-1) ^ q \<cdot>\<^sub>m D q"
    using invE sconv_low_right[OF Dc Dl mEc] sconv_low_left[OF mDc mDl E] sconv_low_both[OF mDc mDl Dc Dl q(2)] E0 mE0 Dc
    by (simp add: sscale_def)
  also have "\<dots> = 2 \<cdot>\<^sub>m D q" using q(1) Dc by (auto intro!: eq_matI)
  finally have z: "0\<^sub>m n n = 2 \<cdot>\<^sub>m D q" .
  show ?thesis
  proof (rule eq_matI)
    fix i j assume i: "i < dim_row (texp X q)" and j: "j < dim_col (texp X q)"
    have ij: "i < n" "j < n" using i j E by simp_all
    have "0 = 2 * D q $$ (i, j)" using arg_cong[OF z, of "\<lambda>M. M $$ (i, j)"] Dc ij by simp
    hence "D q $$ (i, j) = 0" by simp
    thus "fcoef n Ys q $$ (i, j) = texp X q $$ (i, j)" using F E ij by (simp add: D_def)
  qed (use F E in simp_all)
qed

lemma pert2:
  assumes A: "carr n A" "A 0 = 1\<^sub>m n" and B: "carr n B" "B 0 = 1\<^sub>m n"
      and Da: "carr n Da" "low n q Da" and Db: "carr n Db" "low n q Db" and q: "0 < q" and p: "p \<le> q"
  shows "sconv n (\<lambda>p. A p + Da p) (\<lambda>p. B p + Db p) p = sconv n A B p + Da p + Db p"
proof -
  have e: "sconv n (\<lambda>p. A p + Da p) (\<lambda>p. B p + Db p) p
      = sconv n A B p + sconv n A Db p + (sconv n Da B p + sconv n Da Db p)"
    using A B Da Db by (simp add: sconv_add_left sconv_add_right carr_def)
  have AB: "sconv n A B p \<in> carrier_mat n n" using sconv_carr[OF A(1) B(1)] by simp
  show ?thesis
  proof (cases "p < q")
    case True
    thus ?thesis unfolding e using sconv_low_below[OF Db A(1) True] sconv_low_below[OF Da B(1) True]
        sconv_low_below[OF Da Db(1) True] Da Db AB by (simp add: low_def)
  next
    case False
    hence pq: "p = q" using p by simp
    have "sconv n A Db q = Db q" "sconv n Da B q = Da q" "sconv n Da Db q = 0\<^sub>m n n"
      using sconv_low_right[OF Db A(1)] sconv_low_left[OF Da B(1)] sconv_low_both[OF Da Db q] A B Da Db by simp_all
    thus ?thesis unfolding e unfolding pq using Da Db sconv_carr[OF A(1) B(1)] by (auto intro!: eq_matI)
  qed
qed

lemma sconv_congr:
  assumes "\<forall>p\<le>q. f p = f' p" "\<forall>p\<le>q. g p = g' p" "p \<le> q"
  shows "sconv n f g p = sconv n f' g' p"
  unfolding sconv_def by (rule matrix_sum_cong) (use assms in auto)

lemma scaled_copies:
  assumes Ys: "\<forall>Y \<in> set Ys. Y \<in> carrier_mat n n" and X: "X \<in> carrier_mat n n"
      and ord: "\<forall>p<q. fcoef n Ys p = texp X p" and q: "0 < q"
  shows "\<forall>p\<le>q. fcoef n (concat (map (\<lambda>c. map ((\<cdot>\<^sub>m) c) Ys) cs)) p
           = texp (sum_list cs \<cdot>\<^sub>m X) p + (\<Sum>c\<leftarrow>cs. c ^ p) \<cdot>\<^sub>m (fcoef n Ys p - texp X p)"
proof (induction cs)
  case Nil
  show ?case
  proof (intro allI impI)
    fix p assume "p \<le> q"
    have "texp (0 \<cdot>\<^sub>m X) p = sunit n p" using zero_smult_mat[OF X] texp_zero by simp
    show "fcoef n (concat (map (\<lambda>c. map ((\<cdot>\<^sub>m) c) Ys) [])) p
        = texp (sum_list [] \<cdot>\<^sub>m X) p + (\<Sum>c\<leftarrow>[]. c ^ p) \<cdot>\<^sub>m (fcoef n Ys p - texp X p)"
    proof -
      have "fcoef n Ys p - texp X p \<in> carrier_mat n n" using X by (simp add: minus_carrier_mat)
      hence z: "(0::complex) \<cdot>\<^sub>m (fcoef n Ys p - texp X p) = 0\<^sub>m n n" by (rule zero_smult_mat)
      show ?thesis using \<open>texp (0 \<cdot>\<^sub>m X) p = sunit n p\<close> by (simp add: z sunit_def)
    qed
  qed
next
  case (Cons c cs)
  let ?F = "fcoef n Ys" and ?E = "texp X"
  define D where "D = (\<lambda>p. ?F p - ?E p)"
  let ?R = "concat (map (\<lambda>c. map ((\<cdot>\<^sub>m) c) Ys) cs)"
  have F: "carr n ?F" and E: "carr n ?E" using fcoef_carr[OF Ys] X by auto
  have Dc: "carr n D" unfolding carr_def D_def using carr_in[OF E] by (simp add: minus_carrier_mat)
  have Dl: "low n q D" using ord carr_in[OF E] by (auto simp: low_def D_def)
  have cY: "\<forall>Y \<in> set (map ((\<cdot>\<^sub>m) c) Ys). Y \<in> carrier_mat n n" and cR: "\<forall>Y \<in> set ?R. Y \<in> carrier_mat n n"
    using Ys by auto
  define Ac where "Ac = texp (c \<cdot>\<^sub>m X)"
  define Dc' where "Dc' = sscale c D"
  define Ar where "Ar = texp (sum_list cs \<cdot>\<^sub>m X)"
  define Dr where "Dr = (\<lambda>p. (\<Sum>c\<leftarrow>cs. c ^ p) \<cdot>\<^sub>m D p)"
  have Acc: "carr n Ac" "Ac 0 = 1\<^sub>m n" and Arc: "carr n Ar" "Ar 0 = 1\<^sub>m n"
    using X by (simp_all add: Ac_def Ar_def texp_def one_smult_mat)
  have Dcc: "carr n Dc'" "low n q Dc'" using Dc Dl by (auto simp: Dc'_def sscale_def low_def)
  have Drc: "carr n Dr" "low n q Dr" using Dc Dl by (auto simp: Dr_def carr_def low_def)
  have sF: "sscale c ?F = (\<lambda>p. Ac p + Dc' p)"
  proof -
    have "?F = (\<lambda>p. ?E p + D p)" using F E by (auto simp: fun_eq_iff D_def intro!: eq_matI)
    hence "sscale c ?F = (\<lambda>p. sscale c ?E p + sscale c D p)"
      using E Dc by (auto simp: fun_eq_iff sscale_def add_smult_distrib_left_mat[where nr = n and nc = n])
    thus ?thesis by (simp add: Ac_def Dc'_def fun_eq_iff texp_smult[OF X])
  qed
  have IH: "\<forall>p\<le>q. fcoef n ?R p = Ar p + Dr p" using Cons.IH by (simp add: Ar_def Dr_def D_def)
  show ?case
  proof (intro allI impI)
    fix p assume p: "p \<le> q"
    have "fcoef n (concat (map (\<lambda>c. map ((\<cdot>\<^sub>m) c) Ys) (c # cs))) p = sconv n (sscale c ?F) (fcoef n ?R) p"
      using fcoef_append[OF cY cR] fcoef_scale[OF Ys] by simp
    also have "\<dots> = sconv n (\<lambda>p. Ac p + Dc' p) (\<lambda>p. Ar p + Dr p) p"
      unfolding sF by (rule sconv_congr) (use IH p in auto)
    also have "\<dots> = sconv n Ac Ar p + Dc' p + Dr p" by (rule pert2[OF Acc Arc Dcc Drc q p])
    also have "sconv n Ac Ar p = texp (sum_list (c # cs) \<cdot>\<^sub>m X) p"
      unfolding Ac_def Ar_def using texp_add[OF X, of c "sum_list cs" p] by simp
    finally have r: "fcoef n (concat (map (\<lambda>c. map ((\<cdot>\<^sub>m) c) Ys) (c # cs))) p
        = texp (sum_list (c # cs) \<cdot>\<^sub>m X) p + Dc' p + Dr p" .
    have d: "Dc' p + Dr p = (\<Sum>c\<leftarrow>c # cs. c ^ p) \<cdot>\<^sub>m D p"
      using Dc by (simp add: Dc'_def Dr_def sscale_def add_smult_distrib_right_mat[OF carr_in[OF Dc], symmetric])
    have "texp (sum_list (c # cs) \<cdot>\<^sub>m X) p + Dc' p + Dr p = texp (sum_list (c # cs) \<cdot>\<^sub>m X) p + (Dc' p + Dr p)"
      by (rule assoc_add_mat[where nr = n and nc = n]) (use X Dcc Drc in simp_all)
    thus "fcoef n (concat (map (\<lambda>c. map ((\<cdot>\<^sub>m) c) Ys) (c # cs))) p
        = texp (sum_list (c # cs) \<cdot>\<^sub>m X) p + (\<Sum>c\<leftarrow>c # cs. c ^ p) \<cdot>\<^sub>m (fcoef n Ys p - texp X p)"
      using r d by (simp add: D_def)
  qed
qed

lemma fcoef_zero: "\<forall>Y \<in> set Ys. Y \<in> carrier_mat n n \<Longrightarrow> fcoef n Ys 0 = 1\<^sub>m n"
  by (induction Ys) (auto simp: sconv_def sunit_def texp_def one_smult_mat)

lemma fcoef_one: "\<forall>Y \<in> set Ys. Y \<in> carrier_mat n n \<Longrightarrow> fcoef n Ys 1 = hsum n Ys"
proof (induction Ys)
  case Nil
  thus ?case by (simp add: sunit_def)
next
  case (Cons Y Ys)
  have Y: "Y \<in> carrier_mat n n" and Ys: "\<forall>Z \<in> set Ys. Z \<in> carrier_mat n n" using Cons.prems by auto
  have F1: "fcoef n Ys 1 \<in> carrier_mat n n" and H: "hsum n Ys \<in> carrier_mat n n"
    using fcoef_carr[OF Ys] hsum_carrier[of Ys n] Ys by auto
  have "fcoef n (Y # Ys) 1 = texp Y 1 * fcoef n Ys 0 + texp Y 0 * fcoef n Ys 1"
    using carr_mult[OF texp_carr[OF Y] fcoef_carr[OF Ys], of 0 1] by (simp add: sconv_def)
  also have "\<dots> = Y + fcoef n Ys 1" using Y F1 fcoef_zero[OF Ys] by (simp add: texp_def one_smult_mat)
  finally show ?case using Cons.IH[OF Ys] by simp
qed

lemma hsum_append: "\<forall>Y \<in> set Ys. Y \<in> carrier_mat n n \<Longrightarrow> \<forall>Y \<in> set Zs. Y \<in> carrier_mat n n \<Longrightarrow> hsum n (Ys @ Zs) = hsum n Ys + hsum n Zs"
proof (induction Ys)
  case Nil
  thus ?case using hsum_carrier[of Zs n] by simp
next
  case (Cons Y Ys)
  have c: "Y \<in> carrier_mat n n" "hsum n Ys \<in> carrier_mat n n" "hsum n Zs \<in> carrier_mat n n"
    using Cons.prems hsum_carrier[of Ys n] hsum_carrier[of Zs n] by auto
  thus ?case using Cons by (simp add: assoc_add_mat[OF c])
qed

lemma hsum_rev: "\<forall>Y \<in> set Ys. Y \<in> carrier_mat n n \<Longrightarrow> hsum n (rev Ys) = hsum n Ys"
proof (induction Ys)
  case (Cons Y Ys)
  have c: "Y \<in> carrier_mat n n" "hsum n Ys \<in> carrier_mat n n" using Cons.prems hsum_carrier[of Ys n] by auto
  have "hsum n (rev (Y # Ys)) = hsum n (rev Ys) + (Y + 0\<^sub>m n n)" using Cons.prems by (simp add: hsum_append)
  thus ?case using Cons c by (simp add: comm_add_mat[OF c(2) c(1)])
qed simp

lemma hsum_scale: "\<forall>Y \<in> set Ys. Y \<in> carrier_mat n n \<Longrightarrow> hsum n (map ((\<cdot>\<^sub>m) c) Ys) = c \<cdot>\<^sub>m hsum n Ys"
proof (induction Ys)
  case Nil
  show ?case by (rule eq_matI) auto
next
  case (Cons Y Ys)
  thus ?case using hsum_carrier[of Ys n] by (simp add: add_smult_distrib_left_mat[where nr = n and nc = n])
qed

text \<open>A product formula is a list of factors $(a,H)$ standing for $e^{iatH}$; its coefficients are those
of the matrices \<open>tomat (a, H)\<close> $=iaH$.  The symmetric Strang formula
$e^{itH_1/2}\cdots e^{itH_m/2}e^{itH_m/2}\cdots e^{itH_1/2}$ and Suzuki's recursion
$S_{2k+2}=S_{2k}(u)^2\,S_{2k}(1-4u)\,S_{2k}(u)^2$ with $4u^q+(1-4u)^q=0$, $q=2k+3$.\<close>

definition tomat :: "real \<times> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "tomat x = (\<i> * complex_of_real (fst x)) \<cdot>\<^sub>m snd x"

definition strang :: "complex Matrix.mat list \<Rightarrow> (real \<times> complex Matrix.mat) list" where
  "strang Hs = map (\<lambda>H. (1 / 2, H)) Hs @ rev (map (\<lambda>H. (1 / 2, H)) Hs)"

definition suz_u :: "nat \<Rightarrow> real" where
  "suz_u q = 1 / (4 - root q 4)"

definition suz_rs :: "nat \<Rightarrow> real list" where
  "suz_rs q = (let u = suz_u q in [u, u, 1 - 4 * u, u, u])"

fun suzuki :: "nat \<Rightarrow> complex Matrix.mat list \<Rightarrow> (real \<times> complex Matrix.mat) list" where
  "suzuki 0 Hs = strang Hs"
| "suzuki (Suc k) Hs = concat (map (\<lambda>c. map (\<lambda>x. (c * fst x, snd x)) (suzuki k Hs)) (suz_rs (2 * k + 3)))"

lemma suz_u_cond:
  assumes q: "odd q" "3 \<le> q"
  shows "4 * suz_u q ^ q + (1 - 4 * suz_u q) ^ q = 0"
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
  have "1 - 4 * suz_u q = - s / (4 - s)" using s4 by (simp add: suz_u_def s_def[symmetric] field_simps)
  hence "4 * suz_u q ^ q + (1 - 4 * suz_u q) ^ q = (4 - s ^ q) / (4 - s) ^ q"
    using q(1) s4 by (simp add: suz_u_def s_def[symmetric] power_divide power_minus_odd field_simps)
  thus ?thesis using sq by simp
qed

lemma tomat_scale: "tomat (c * a, H) = complex_of_real c \<cdot>\<^sub>m tomat (a, H)"
  by (rule eq_matI) (auto simp: tomat_def)

lemma suzuki_snd: "x \<in> set (suzuki k Hs) \<Longrightarrow> snd x \<in> set Hs"
  by (induction k arbitrary: x) (auto simp: strang_def)

lemma suzuki_carrier: "\<forall>H \<in> set Hs. H \<in> carrier_mat n n \<Longrightarrow> \<forall>Y \<in> set (map tomat (suzuki k Hs)). Y \<in> carrier_mat n n"
  using suzuki_snd by (fastforce simp: tomat_def)

lemma suzuki_palindrome: "rev (suzuki k Hs) = suzuki k Hs"
  by (induction k) (simp_all add: strang_def suz_rs_def Let_def rev_map)

lemma strang_order:
  assumes Hs: "\<forall>H \<in> set Hs. H \<in> carrier_mat n n"
  shows "\<forall>p\<le>2. fcoef n (map tomat (strang Hs)) p = texp (\<i> \<cdot>\<^sub>m hsum n Hs) p"
proof -
  let ?Z = "map ((\<cdot>\<^sub>m) (\<i> / 2)) Hs"
  have st: "map tomat (strang Hs) = ?Z @ rev ?Z"
    by (simp add: strang_def tomat_def rev_map comp_def)
  have Z: "\<forall>Y \<in> set ?Z. Y \<in> carrier_mat n n" using Hs by auto
  have St: "\<forall>Y \<in> set (map tomat (strang Hs)). Y \<in> carrier_mat n n" unfolding st using Z by auto
  have pal: "rev (map tomat (strang Hs)) = map tomat (strang Hs)" unfolding st by simp
  have H: "hsum n Hs \<in> carrier_mat n n" using hsum_carrier[of Hs n] Hs by auto
  have X: "\<i> \<cdot>\<^sub>m hsum n Hs \<in> carrier_mat n n" using H by simp
  have h2: "hsum n (map tomat (strang Hs)) = \<i> \<cdot>\<^sub>m hsum n Hs"
  proof -
    have "hsum n (map tomat (strang Hs)) = (\<i> / 2) \<cdot>\<^sub>m hsum n Hs + (\<i> / 2) \<cdot>\<^sub>m hsum n Hs"
      unfolding st hsum_append[OF Z] by (simp add: Z hsum_rev hsum_scale[OF Hs] hsum_append)
    also have "\<dots> = \<i> \<cdot>\<^sub>m hsum n Hs" using H by (auto intro!: eq_matI)
    finally show ?thesis .
  qed
  have ord1: "\<forall>p<2. fcoef n (map tomat (strang Hs)) p = texp (\<i> \<cdot>\<^sub>m hsum n Hs) p"
  proof (intro allI impI)
    fix p :: nat assume "p < 2"
    hence "p = 0 \<or> p = 1" by auto
    thus "fcoef n (map tomat (strang Hs)) p = texp (\<i> \<cdot>\<^sub>m hsum n Hs) p"
      using fcoef_zero[OF St] fcoef_one[OF St] h2 X by (auto simp: texp_def one_smult_mat)
  qed
  have "fcoef n (map tomat (strang Hs)) 2 = texp (\<i> \<cdot>\<^sub>m hsum n Hs) 2" by (rule sym_order[OF St X pal ord1]) simp_all
  thus ?thesis using ord1 by (auto simp: le_less)
qed

theorem suzuki_order:
  assumes Hs: "\<forall>H \<in> set Hs. H \<in> carrier_mat n n"
  shows "\<forall>p\<le>2 * k + 2. fcoef n (map tomat (suzuki k Hs)) p = texp (\<i> \<cdot>\<^sub>m hsum n Hs) p"
proof (induction k)
  case 0
  thus ?case using strang_order[OF Hs] by simp
next
  case (Suc k)
  let ?S = "map tomat (suzuki k Hs)" and ?q = "2 * k + 3" and ?X = "\<i> \<cdot>\<^sub>m hsum n Hs"
  let ?cs = "map complex_of_real (suz_rs ?q)"
  have S: "\<forall>Y \<in> set ?S. Y \<in> carrier_mat n n" by (rule suzuki_carrier[OF Hs])
  have X: "?X \<in> carrier_mat n n" using hsum_carrier[of Hs n] Hs by auto
  have ordS: "\<forall>p<?q. fcoef n ?S p = texp ?X p" using Suc.IH by auto
  have mt: "map tomat (suzuki (Suc k) Hs) = concat (map (\<lambda>c. map ((\<cdot>\<^sub>m) c) ?S) ?cs)"
    by (simp add: map_concat comp_def tomat_scale)
  define u where "u = complex_of_real (suz_u ?q)"
  have cs: "?cs = [u, u, 1 - 4 * u, u, u]" by (simp add: suz_rs_def u_def Let_def)
  have sum1: "sum_list ?cs = 1" by (simp add: cs)
  have sumq: "(\<Sum>c\<leftarrow>?cs. c ^ ?q) = 0"
  proof -
    have "(\<Sum>c\<leftarrow>?cs. c ^ ?q) = complex_of_real (4 * suz_u ?q ^ ?q + (1 - 4 * suz_u ?q) ^ ?q)"
      by (simp add: cs u_def)
    thus ?thesis using suz_u_cond[of ?q] by simp
  qed
  have sc: "\<forall>p\<le>?q. fcoef n (map tomat (suzuki (Suc k) Hs)) p
      = texp (sum_list ?cs \<cdot>\<^sub>m ?X) p + (\<Sum>c\<leftarrow>?cs. c ^ p) \<cdot>\<^sub>m (fcoef n ?S p - texp ?X p)"
    unfolding mt by (rule scaled_copies[OF S X ordS]) simp
  have ordq: "\<forall>p\<le>?q. fcoef n (map tomat (suzuki (Suc k) Hs)) p = texp ?X p"
  proof (intro allI impI)
    fix p assume p: "p \<le> ?q"
    have z: "(\<Sum>c\<leftarrow>?cs. c ^ p) \<cdot>\<^sub>m (fcoef n ?S p - texp ?X p) = 0\<^sub>m n n"
    proof (cases "p < ?q")
      case True
      hence "fcoef n ?S p - texp ?X p = 0\<^sub>m n n" using ordS carr_in[OF texp_carr[OF X]] by simp
      thus ?thesis by (auto intro!: eq_matI)
    next
      case False
      hence "p = ?q" using p by simp
      have "fcoef n ?S p - texp ?X p \<in> carrier_mat n n" using X by (simp add: minus_carrier_mat)
      thus ?thesis using sumq \<open>p = ?q\<close> by (simp add: zero_smult_mat)
    qed
    have e: "fcoef n (map tomat (suzuki (Suc k) Hs)) p
        = texp (sum_list ?cs \<cdot>\<^sub>m ?X) p + (\<Sum>c\<leftarrow>?cs. c ^ p) \<cdot>\<^sub>m (fcoef n ?S p - texp ?X p)"
      using sc p by blast
    show "fcoef n (map tomat (suzuki (Suc k) Hs)) p = texp ?X p"
      unfolding e z sum1 using carr_in[OF texp_carr[OF X]] X by (simp add: one_smult_mat)
  qed
  have S': "\<forall>Y \<in> set (map tomat (suzuki (Suc k) Hs)). Y \<in> carrier_mat n n" by (rule suzuki_carrier[OF Hs])
  have pal': "rev (map tomat (suzuki (Suc k) Hs)) = map tomat (suzuki (Suc k) Hs)"
    using suzuki_palindrome[of "Suc k" Hs] by (metis rev_map)
  have top: "fcoef n (map tomat (suzuki (Suc k) Hs)) (?q + 1) = texp ?X (?q + 1)"
    by (rule sym_order[OF S' X pal']) (use ordq in auto)
  show ?case
  proof (intro allI impI)
    fix p assume "p \<le> 2 * Suc k + 2"
    hence "p \<le> ?q \<or> p = ?q + 1" by arith
    thus "fcoef n (map tomat (suzuki (Suc k) Hs)) p = texp ?X p" using ordq top by blast
  qed
qed

end

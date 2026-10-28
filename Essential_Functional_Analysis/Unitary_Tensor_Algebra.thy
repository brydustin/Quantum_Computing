(*  Title:   Unitary_Tensor_Algebra.thy
    Author:  Dustin Bryant, unitary matrices and Kronecker products: the algebra used from Day 3 on
*)

theory Unitary_Tensor_Algebra
  imports Matrix_Lemmas Isabelle_Marries_Dirac.More_Tensor Isabelle_Marries_Dirac.No_Cloning
begin

hide_const (open) Quantum.X Quantum.Y Quantum.Z Quantum.H Quantum.S Quantum.T
declare cauchy_schwarz_eq [simp del] cauchy_schwarz_col [simp del] eq_from_inner_prod [simp del]

section \<open>Unitary algebra\<close>

text \<open>Library-level consequences of unitarity ($U^\dagger U=I$ and $UU^\dagger=I$ in the
library's definition) used throughout; Paulsen's Day 3 characterisations of unitaries are
in theory Day03\_Unitary\_Matrices.\<close>

lemma unitary_square_dim:
  assumes uA: "unitary A"
  shows "dim_row A = dim_col A"
proof -
  let ?m = "dim_row A" and ?n = "dim_col A"
  have "of_nat ?n = (\<Sum>c<?n. ((A\<^sup>\<dagger>) * A) $$ (c, c))"
    using uA unfolding unitary_def by simp
  also have "\<dots> = (\<Sum>c<?n. \<Sum>r<?m. cnj (A $$ (r, c)) * A $$ (r, c))"
    by (intro sum.cong refl) (simp add: scalar_prod_def dagger_def atLeast0LessThan)
  also have "\<dots> = (\<Sum>r<?m. \<Sum>c<?n. A $$ (r, c) * cnj (A $$ (r, c)))"
    by (subst sum.swap) (simp add: mult.commute)
  also have "\<dots> = (\<Sum>r<?m. (A * (A\<^sup>\<dagger>)) $$ (r, r))"
    by (intro sum.cong refl) (simp add: scalar_prod_def dagger_def atLeast0LessThan)
  also have "\<dots> = of_nat ?m"
    using uA unfolding unitary_def by simp
  finally show ?thesis by simp
qed

lemma unitary_inv_l_dimcol:
  assumes uA: "unitary A"
  shows "(A\<^sup>\<dagger>) * A = 1\<^sub>m (dim_col A)"
  using uA unfolding unitary_def by auto

lemma unitary_inv_r_dimrow:
  assumes uA: "unitary A"
  shows "A * (A\<^sup>\<dagger>) = 1\<^sub>m (dim_row A)"
  using uA unfolding unitary_def by auto

lemma unitary_carrier_square_col:
  assumes uA: "unitary A"
  shows "A \<in> carrier_mat (dim_col A) (dim_col A)"
  using unitary_square_dim uA by blast 

lemma unitary_carrier_square_row:
  assumes uA: "unitary A"
  shows "A \<in> carrier_mat (dim_row A) (dim_row A)"
  using uA unitary_square_dim by auto

lemma unitary_dagger:
  assumes uA: "unitary A"
  shows "unitary (A\<^sup>\<dagger>)"
  using uA unfolding unitary_def by (simp add: dagger_of_dagger_is_id)

lemma unitary_mult:
  assumes UA: "unitary A"
      and UB: "unitary B"
      and dimA: "A \<in> carrier_mat n n"
      and dimB: "B \<in> carrier_mat n n"
  shows "unitary (A * B)"
proof -
  have Ad: "A\<^sup>\<dagger> \<in> carrier_mat n n" and Bd: "B\<^sup>\<dagger> \<in> carrier_mat n n" using dimA dimB by auto
  have A: "(A\<^sup>\<dagger>) * A = 1\<^sub>m n" "A * (A\<^sup>\<dagger>) = 1\<^sub>m n"
    and B: "(B\<^sup>\<dagger>) * B = 1\<^sub>m n" "B * (B\<^sup>\<dagger>) = 1\<^sub>m n"
    using UA UB dimA dimB unfolding unitary_def by auto
  have AB: "(A * B)\<^sup>\<dagger> = (B\<^sup>\<dagger>) * (A\<^sup>\<dagger>)" by (rule dagger_of_prod) (use dimA dimB in simp)
  have "((A * B)\<^sup>\<dagger>) * (A * B) = (B\<^sup>\<dagger>) * (((A\<^sup>\<dagger>) * A) * B)"
    unfolding AB assoc_mult_mat[OF Bd Ad mult_carrier_mat[OF dimA dimB]] assoc_mult_mat[OF Ad dimA dimB] ..
  moreover have "(A * B) * ((A * B)\<^sup>\<dagger>) = A * ((B * (B\<^sup>\<dagger>)) * (A\<^sup>\<dagger>))"
    unfolding AB assoc_mult_mat[OF dimA dimB mult_carrier_mat[OF Bd Ad]] assoc_mult_mat[OF dimB Bd Ad] ..
  ultimately show ?thesis unfolding unitary_def using dimA dimB Ad Bd by (simp add: A B)
qed

section \<open>Kronecker products\<close>

text \<open>Kronecker products of matrices, \<^term>\<open>A \<Otimes> B\<close>: the tensor of identities, the
adjoint $(R\otimes T)^*=R^*\otimes T^*$, the mixed-product property
$(R_1\otimes T_1)(R_2\otimes T_2)=R_1R_2\otimes T_1T_2$, and unitarity of
tensors of unitaries.\<close>

subsection \<open> Tensor of Identities \<close>

lemma tensor_mat_id:
  "Tensor.tensor_mat (1\<^sub>m n) (1\<^sub>m m) = 1\<^sub>m (n * m)"
proof (rule eq_matI)
  fix i j assume "i < dim_row (1\<^sub>m (n * m))" "j < dim_col (1\<^sub>m (n * m))"
  hence ij: "i < n * m" "j < n * m" by simp_all
  hence "0 < n" "0 < m" by (auto intro: gr0I)
  thus "Tensor.tensor_mat (1\<^sub>m n) (1\<^sub>m m) $$ (i, j) = 1\<^sub>m (n * m) $$ (i, j)"
    using ij by (simp add: less_mult_imp_div_less nat_eq_iff_div_mod[of i j m])
qed simp_all

subsection \<open> Mixed-Product Property \<close>

lemma tensor_mat_mult:
  assumes dimAC: "dim_col A = dim_row C"
      and dimBD: "dim_col B = dim_row D"
  shows "Tensor.tensor_mat A B * Tensor.tensor_mat C D =
         Tensor.tensor_mat (A * C) (B * D)"
proof (cases "0 < dim_col A \<and> 0 < dim_col B \<and> 0 < dim_col C \<and> 0 < dim_col D")
  case True
  thus ?thesis by (simp add: mult_distr_tensor[OF dimAC dimBD])
next
  case False
  show ?thesis
  proof (rule eq_matI)
    fix i j
    assume "i < dim_row (Tensor.tensor_mat (A * C) (B * D))" "j < dim_col (Tensor.tensor_mat (A * C) (B * D))"
    hence ij: "i < dim_row A * dim_row B" "j < dim_col C * dim_col D" by simp_all
    hence pos: "0 < dim_row B" "0 < dim_col C" "0 < dim_col D" by (auto intro: gr0I)
    with False have "dim_col A = 0 \<or> dim_col B = 0" by auto
    thus "(Tensor.tensor_mat A B * Tensor.tensor_mat C D) $$ (i, j) = Tensor.tensor_mat (A * C) (B * D) $$ (i, j)"
      using ij pos dimAC dimBD by (auto simp: scalar_prod_def less_mult_imp_div_less)
  qed (use dimAC dimBD in simp_all)
qed

subsection \<open> Corollaries of the Mixed-Product Property \<close>

lemma tensor_adjoint_mult:
  "(Tensor.tensor_mat (A\<^sup>\<dagger>) (B\<^sup>\<dagger>)) * (Tensor.tensor_mat A B) =
   Tensor.tensor_mat ((A\<^sup>\<dagger>) * A) ((B\<^sup>\<dagger>) * B)"
  by (rule tensor_mat_mult, simp_all add: dagger_def)

lemma tensor_mult_adjoint:
  "(Tensor.tensor_mat A B) * (Tensor.tensor_mat (A\<^sup>\<dagger>) (B\<^sup>\<dagger>)) =
   Tensor.tensor_mat (A * (A\<^sup>\<dagger>)) (B * (B\<^sup>\<dagger>))"
  by (rule tensor_mat_mult, simp_all add: dagger_def)

subsection \<open> Tensor Unitarity \<close>

lemma tensor_mat_unitary_carrier:
  assumes dimA: "A \<in> carrier_mat n n"
      and dimB: "B \<in> carrier_mat m m"
      and uA:   "unitary A"
      and uB:   "unitary B"
  shows "unitary (Tensor.tensor_mat A B)"
proof -
  have "(A\<^sup>\<dagger>) * A = 1\<^sub>m n" "A * (A\<^sup>\<dagger>) = 1\<^sub>m n" "(B\<^sup>\<dagger>) * B = 1\<^sub>m m" "B * (B\<^sup>\<dagger>) = 1\<^sub>m m"
    using uA uB dimA dimB unfolding unitary_def by auto
  thus ?thesis
    unfolding unitary_def hermite_cnj_of_tensor tensor_adjoint_mult tensor_mult_adjoint
    using dimA dimB by (simp add: tensor_mat_id)
qed

lemma tensor_mat_unitary:
  assumes uA: "unitary A"
      and uB: "unitary B"
  shows "unitary (Tensor.tensor_mat A B)"
  using tensor_mat_unitary_carrier uA uB unitary_carrier_square_row by blast

lemma tensor_mat_unitary_one_left [simp]:
  assumes uA: "unitary A"
  shows "unitary (Tensor.tensor_mat (1\<^sub>m n) A)"
  using id_is_unitary tensor_mat_unitary uA by blast

lemma tensor_mat_unitary_one_right [simp]:
  assumes uA: "unitary A"
  shows "unitary (Tensor.tensor_mat A (1\<^sub>m n))"
  using id_is_unitary tensor_mat_unitary uA by blast

lemma one_smult_mat: "(1::complex) \<cdot>\<^sub>m M = M"
  by (rule eq_matI) simp_all

lemma mult_index_lt:
  fixes i j n m :: nat
  assumes "i < n" and "j < m"
  shows "i * m + j < n * m"
proof -
  have "i * m + j < (i + 1) * m" using assms(2) by simp
  also have "\<dots> \<le> n * m" using assms(1) by (intro mult_le_mono1) simp
  finally show ?thesis .
qed

lemma mult_index_div_mod:
  fixes i l m :: nat
  assumes "l < m"
  shows "(i * m + l) div m = i" "(i * m + l) mod m = l"
  using assms by simp_all

lemma mult_index_eq_iff:
  fixes i j k l m :: nat
  assumes "k < m" and "l < m"
  shows "i * m + k = j * m + l \<longleftrightarrow> i = j \<and> k = l"
proof
  assume "i * m + k = j * m + l"
  hence "(i * m + k) div m = (j * m + l) div m" "(i * m + k) mod m = (j * m + l) mod m" by simp_all
  thus "i = j \<and> k = l"
    unfolding mult_index_div_mod[OF assms(1)] mult_index_div_mod[OF assms(2)] by simp
qed simp

subsection \<open>Tensor products of matrices\<close>

lemma tensor_index_c:
  fixes A B :: "complex Matrix.mat"
  assumes "A \<in> carrier_mat r c" "B \<in> carrier_mat p q" "i < r * p" "j < c * q" "0 < c" "0 < q"
  shows "Tensor.tensor_mat A B $$ (i,j) = A $$ (i div p, j div q) * B $$ (i mod p, j mod q)"
  using assms by (intro index_tensor_mat) auto

lemma tensor_one_left:
  fixes A :: "complex Matrix.mat"
  assumes Ac: "A \<in> carrier_mat m m" and m: "0 < m"
  shows "Tensor.tensor_mat (1\<^sub>m 1) A = A"
proof (rule eq_matI)
  fix i j assume "i < dim_row A" "j < dim_col A"
  hence i: "i < m" and j: "j < m" using Ac by auto
  show "Tensor.tensor_mat (1\<^sub>m 1) A $$ (i,j) = A $$ (i,j)"
  proof -
    have "Tensor.tensor_mat (1\<^sub>m 1) A $$ (i,j) = 1\<^sub>m 1 $$ (i div m, j div m) * A $$ (i mod m, j mod m)"
      by (rule tensor_index_c[OF one_carrier_mat Ac]) (use i j m in simp_all)
    thus ?thesis using i j by simp
  qed
qed (use Ac in auto)

lemma tensor_one_right:
  fixes A :: "complex Matrix.mat"
  assumes Ac: "A \<in> carrier_mat m m" and m: "0 < m"
  shows "Tensor.tensor_mat A (1\<^sub>m 1) = A"
proof (rule eq_matI)
  fix i j assume "i < dim_row A" "j < dim_col A"
  hence i: "i < m" and j: "j < m" using Ac by auto
  show "Tensor.tensor_mat A (1\<^sub>m 1) $$ (i,j) = A $$ (i,j)"
  proof -
    have "Tensor.tensor_mat A (1\<^sub>m 1) $$ (i,j) = A $$ (i div 1, j div 1) * 1\<^sub>m 1 $$ (i mod 1, j mod 1)"
      by (rule tensor_index_c[OF Ac one_carrier_mat]) (use i j m in simp_all)
    thus ?thesis by simp
  qed
qed (use Ac in auto)

lemma tensor_mat_add_right:
  fixes A B C :: "complex Matrix.mat"
  assumes Ac: "A \<in> carrier_mat r c" and Bc: "B \<in> carrier_mat p q" and Cc: "C \<in> carrier_mat p q"
      and c: "0 < c" and q: "0 < q"
  shows "Tensor.tensor_mat A (B + C) = Tensor.tensor_mat A B + Tensor.tensor_mat A C"
proof (rule eq_matI)
  fix i j assume "i < dim_row (Tensor.tensor_mat A B + Tensor.tensor_mat A C)"
    "j < dim_col (Tensor.tensor_mat A B + Tensor.tensor_mat A C)"
  hence i: "i < r * p" and j: "j < c * q" using Ac Bc Cc by auto
  have p: "0 < p" using i by (cases p) auto
  show "Tensor.tensor_mat A (B + C) $$ (i,j) = (Tensor.tensor_mat A B + Tensor.tensor_mat A C) $$ (i,j)"
    using tensor_index_c[OF Ac add_carrier_mat[OF Cc] i j c q] tensor_index_c[OF Ac Bc i j c q]
      tensor_index_c[OF Ac Cc i j c q] i j p q Ac Bc Cc by (simp add: distrib_left)
qed (use Ac Bc Cc in auto)

lemma tensor_mat_add_left:
  fixes A B C :: "complex Matrix.mat"
  assumes Ac: "A \<in> carrier_mat r c" and Bc: "B \<in> carrier_mat r c" and Cc: "C \<in> carrier_mat p q"
      and c: "0 < c" and q: "0 < q"
  shows "Tensor.tensor_mat (A + B) C = Tensor.tensor_mat A C + Tensor.tensor_mat B C"
proof (rule eq_matI)
  fix i j assume "i < dim_row (Tensor.tensor_mat A C + Tensor.tensor_mat B C)"
    "j < dim_col (Tensor.tensor_mat A C + Tensor.tensor_mat B C)"
  hence i: "i < r * p" and j: "j < c * q" using Ac Bc Cc by auto
  have p: "0 < p" using i by (cases p) auto
  have id: "i div p < r" and jd: "j div q < c" using i j p q by (auto simp: less_mult_imp_div_less)
  show "Tensor.tensor_mat (A + B) C $$ (i,j) = (Tensor.tensor_mat A C + Tensor.tensor_mat B C) $$ (i,j)"
    using tensor_index_c[OF add_carrier_mat[OF Bc] Cc i j c q] tensor_index_c[OF Ac Cc i j c q]
      tensor_index_c[OF Bc Cc i j c q] i j id jd Ac Bc Cc by (simp add: distrib_right)
qed (use Ac Bc Cc in auto)

lemma tensor_mat_smult_right:
  fixes A B :: "complex Matrix.mat"
  assumes Ac: "A \<in> carrier_mat r c" and Bc: "B \<in> carrier_mat p q" and c: "0 < c" and q: "0 < q"
  shows "Tensor.tensor_mat A (k \<cdot>\<^sub>m B) = k \<cdot>\<^sub>m Tensor.tensor_mat A B"
proof (rule eq_matI)
  fix i j assume "i < dim_row (k \<cdot>\<^sub>m Tensor.tensor_mat A B)" "j < dim_col (k \<cdot>\<^sub>m Tensor.tensor_mat A B)"
  hence i: "i < r * p" and j: "j < c * q" using Ac Bc by auto
  have p: "0 < p" using i by (cases p) auto
  show "Tensor.tensor_mat A (k \<cdot>\<^sub>m B) $$ (i,j) = (k \<cdot>\<^sub>m Tensor.tensor_mat A B) $$ (i,j)"
    using tensor_index_c[OF Ac smult_carrier_mat[OF Bc] i j c q] tensor_index_c[OF Ac Bc i j c q]
      i j p q Ac Bc by (simp add: mult_ac)
qed (use Ac Bc in auto)

lemma tensor_mat_smult_left:
  fixes A B :: "complex Matrix.mat"
  assumes Ac: "A \<in> carrier_mat r c" and Bc: "B \<in> carrier_mat p q" and c: "0 < c" and q: "0 < q"
  shows "Tensor.tensor_mat (k \<cdot>\<^sub>m A) B = k \<cdot>\<^sub>m Tensor.tensor_mat A B"
proof (rule eq_matI)
  fix i j assume "i < dim_row (k \<cdot>\<^sub>m Tensor.tensor_mat A B)" "j < dim_col (k \<cdot>\<^sub>m Tensor.tensor_mat A B)"
  hence i: "i < r * p" and j: "j < c * q" using Ac Bc by auto
  have p: "0 < p" using i by (cases p) auto
  have id: "i div p < r" and jd: "j div q < c" using i j p q by (auto simp: less_mult_imp_div_less)
  show "Tensor.tensor_mat (k \<cdot>\<^sub>m A) B $$ (i,j) = (k \<cdot>\<^sub>m Tensor.tensor_mat A B) $$ (i,j)"
    using tensor_index_c[OF smult_carrier_mat[OF Ac] Bc i j c q] tensor_index_c[OF Ac Bc i j c q]
      i j id jd Ac Bc by (simp add: mult_ac)
qed (use Ac Bc in auto)

end

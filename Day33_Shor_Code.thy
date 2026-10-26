theory Day33_Shor_Code
  imports Day32_Recovery_Proposition Day32_Pauli_Expansion Day30_BitFlip_Code
begin

section \<open>Days 32--33: the nine-qubit Shor code\<close>

text \<open>Days 32--33: the nine-qubit Shor code.  The $2^9$-dimensional space is never handled
entrywise: nine qubits are three blocks of three, every single-qubit operator acts inside one
block, and all inner products factor over the blocks (\<open>tensor_inner_prod\<close>).\<close>

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

subsection \<open>Single-qubit operators on nine qubits, and on a block of three\<close>

text \<open>$\tilde U=I\otimes\cdots\otimes I\otimes U\otimes I\otimes\cdots\otimes I$ with $U$ in
position $i$ ($i=0,\dots,8$).\<close>

definition qubit_op :: "nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "qubit_op i U = Tensor.tensor_mat (Tensor.tensor_mat (1\<^sub>m (2^i)) U) (1\<^sub>m (2^(8-i)))"

definition block_op :: "nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "block_op s U = Tensor.tensor_mat (Tensor.tensor_mat (1\<^sub>m (2^s)) U) (1\<^sub>m (2^(2-s)))"

definition on_block :: "nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "on_block b M = Tensor.tensor_mat (Tensor.tensor_mat (1\<^sub>m (8^b)) M) (1\<^sub>m (8^(2-b)))"

text \<open>$\tilde U_i=I_{2^i}\otimes U\otimes I_{2^{8-i}}$ applies $U$ to qubit $i$.  In three blocks of three
qubits, qubit $3b+s$ is qubit $s$ of block $b$:
\[ \tilde U_{3b+s}=I_{8^b}\otimes\bigl(I_{2^s}\otimes U\otimes I_{2^{2-s}}\bigr)\otimes I_{8^{2-b}}, \]
so every computation on $\C^{512}$ reduces to one on $\C^8$.\<close>

lemma qubit_op_carrier:
  assumes U: "U \<in> carrier_mat 2 2" and i: "i < 9"
  shows "qubit_op i U \<in> carrier_mat 512 512"
proof -
  have "Suc i + (8 - i) = 9" using i by simp
  hence "(2::nat) ^ Suc i * 2 ^ (8 - i) = 2 ^ 9" by (metis power_add)
  hence e: "(2::nat) ^ i * 2 * 2 ^ (8 - i) = 512" by (simp add: mult_ac)
  show ?thesis unfolding qubit_op_def using U e by auto
qed

lemma qubit_op_blk:
  assumes b: "b < 3" and s: "s < 3"
  shows "qubit_op (3 * b + s) U = on_block b (block_op s U)"
proof -
  have e1: "1\<^sub>m (2^(3*b+s)) = Tensor.tensor_mat (1\<^sub>m (8^b)) (1\<^sub>m (2^s))"
    by (simp add: tensor_mat_id power_add power_mult)
  have "8 - (3*b+s) = (2-s) + 3*(2-b)" using b s by simp
  hence e2: "1\<^sub>m (2^(8-(3*b+s))) = Tensor.tensor_mat (1\<^sub>m (2^(2-s))) (1\<^sub>m (8^(2-b)))"
    by (simp add: tensor_mat_id power_add power_mult)
  show ?thesis unfolding qubit_op_def on_block_def block_op_def e1 e2 by (simp only: tensor_mat_is_assoc)
qed

lemma qubit_op_blk_div:
  assumes i: "i < 9"
  shows "qubit_op i U = on_block (i div 3) (block_op (i mod 3) U)"
proof -
  have "i = 3 * (i div 3) + i mod 3" by simp
  moreover have "i div 3 < 3" using i by simp
  ultimately show ?thesis using qubit_op_blk[of "i div 3" "i mod 3" U] by simp
qed

lemma block_op_cases:
  fixes U :: "complex Matrix.mat"
  assumes U: "U \<in> carrier_mat 2 2"
  shows "block_op 0 U = Tensor.tensor_mat (Tensor.tensor_mat U (1\<^sub>m 2)) (1\<^sub>m 2)"
    and "block_op 1 U = Tensor.tensor_mat (Tensor.tensor_mat (1\<^sub>m 2) U) (1\<^sub>m 2)"
    and "block_op 2 U = Tensor.tensor_mat (Tensor.tensor_mat (1\<^sub>m 2) (1\<^sub>m 2)) U"
proof -
  have i4: "1\<^sub>m 4 = Tensor.tensor_mat (1\<^sub>m 2) (1\<^sub>m 2)" by (simp add: tensor_mat_id)
  show "block_op 0 U = Tensor.tensor_mat (Tensor.tensor_mat U (1\<^sub>m 2)) (1\<^sub>m 2)"
    unfolding block_op_def using tensor_one_left[OF U] by (simp add: i4 tensor_mat_is_assoc)
  show "block_op 1 U = Tensor.tensor_mat (Tensor.tensor_mat (1\<^sub>m 2) U) (1\<^sub>m 2)" unfolding block_op_def by simp
  have c: "Tensor.tensor_mat (1\<^sub>m 4) U \<in> carrier_mat 8 8" using U by auto
  show "block_op 2 U = Tensor.tensor_mat (Tensor.tensor_mat (1\<^sub>m 2) (1\<^sub>m 2)) U"
    unfolding block_op_def using tensor_one_right[OF c] by (simp add: i4)
qed

lemma block_op_carrier:
  assumes U: "U \<in> carrier_mat 2 2" and s: "s < 3"
  shows "block_op s U \<in> carrier_mat 8 8"
proof -
  have "s = 0 \<or> s = 1 \<or> s = 2" using s by auto
  thus ?thesis using U by (elim disjE) (auto simp: block_op_def)
qed

definition tensor3 :: "complex Matrix.vec \<Rightarrow> complex Matrix.vec \<Rightarrow> complex Matrix.vec \<Rightarrow> complex Matrix.vec" where
  "tensor3 x y z = tensor_vec (tensor_vec x y) z"

lemma tensor3_dim: "dim_vec x = 8 \<Longrightarrow> dim_vec y = 8 \<Longrightarrow> dim_vec z = 8 \<Longrightarrow> dim_vec (tensor3 x y z) = 512"
  unfolding tensor3_def by (simp add: tensor_vec_dim)

lemma on_block_tv3:
  assumes M: "M \<in> carrier_mat 8 8" and x: "dim_vec x = 8" and y: "dim_vec y = 8" and z: "dim_vec z = 8"
  shows "on_block 0 M *\<^sub>v tensor3 x y z = tensor3 (M *\<^sub>v x) y z"
    and "on_block 1 M *\<^sub>v tensor3 x y z = tensor3 x (M *\<^sub>v y) z"
    and "on_block 2 M *\<^sub>v tensor3 x y z = tensor3 x y (M *\<^sub>v z)"
proof -
  have i64: "1\<^sub>m 64 = Tensor.tensor_mat (1\<^sub>m 8) (1\<^sub>m 8)" by (simp add: tensor_mat_id)
  have xy: "dim_vec (tensor_vec x y) = 64" using x y by (simp add: tensor_vec_dim)
  have zc: "z \<in> carrier_vec 8" and yc: "y \<in> carrier_vec 8" and xc: "x \<in> carrier_vec 8"
    using x y z by (auto intro: carrier_vecI)
  have c1: "Tensor.tensor_mat M (1\<^sub>m 8) \<in> carrier_mat 64 64" and c2: "Tensor.tensor_mat (1\<^sub>m 8) M \<in> carrier_mat 64 64"
    and c3: "Tensor.tensor_mat (1\<^sub>m 8) (1\<^sub>m 8) \<in> carrier_mat 64 64" using M by auto
  have "on_block 0 M = Tensor.tensor_mat (Tensor.tensor_mat M (1\<^sub>m 8)) (1\<^sub>m 8)"
    unfolding on_block_def using tensor_one_left[OF M] by (simp add: i64 tensor_mat_is_assoc)
  thus "on_block 0 M *\<^sub>v tensor3 x y z = tensor3 (M *\<^sub>v x) y z" unfolding tensor3_def
    using tensor_mat_vec_mult[OF c1 one_carrier_mat xy z] tensor_mat_vec_mult[OF M one_carrier_mat x y] zc yc by simp
  have "on_block 1 M = Tensor.tensor_mat (Tensor.tensor_mat (1\<^sub>m 8) M) (1\<^sub>m 8)" unfolding on_block_def by simp
  thus "on_block 1 M *\<^sub>v tensor3 x y z = tensor3 x (M *\<^sub>v y) z" unfolding tensor3_def
    using tensor_mat_vec_mult[OF c2 one_carrier_mat xy z] tensor_mat_vec_mult[OF one_carrier_mat M x y] zc xc by simp
  have c: "Tensor.tensor_mat (1\<^sub>m 64) M \<in> carrier_mat 512 512" using M by auto
  have "on_block 2 M = Tensor.tensor_mat (Tensor.tensor_mat (1\<^sub>m 8) (1\<^sub>m 8)) M"
    unfolding on_block_def using tensor_one_right[OF c] by (simp add: i64)
  thus "on_block 2 M *\<^sub>v tensor3 x y z = tensor3 x y (M *\<^sub>v z)" unfolding tensor3_def
    using tensor_mat_vec_mult[OF c3 M xy z]
      tensor_mat_vec_mult[OF one_carrier_mat one_carrier_mat x y] xc yc by (simp add: tensor_mat_id)
qed

subsection \<open>The block vectors $\ket{m}\pm\ket{7-m}$\<close>

text \<open>In a block of three qubits, \<open>ghz_vec p 0\<close> is $\ket{000}\pm\ket{111}$; a bit flip moves it to
\<open>ghz_vec p m\<close> with $m\in\{4,2,1\}$.  These eight vectors are mutually orthogonal.\<close>

definition sign_pm :: "bool \<Rightarrow> complex" where "sign_pm p = (if p then 1 else -1)"

definition ghz_vec :: "bool \<Rightarrow> nat \<Rightarrow> complex Matrix.vec" where
  "ghz_vec p m = unit_vec 8 m + sign_pm p \<cdot>\<^sub>v unit_vec 8 (7 - m)"

text \<open>On a block, with $m=2^{2-s}$ for qubit $s$,
\[ X_s(\ket{000}\pm\ket{111})=\ket m\pm\ket{7-m},\qquad Z_s(\ket{000}\pm\ket{111})=\ket{000}\mp\ket{111}, \]
and $Y_s$ does both, with the factor $-i$.  The eight vectors $\ket m\pm\ket{7-m}$, $m\in\{0,1,2,4\}$,
are orthogonal with norm $\sqrt2$.\<close>

lemma ghz_vec_dim [simp]: "dim_vec (ghz_vec p m) = 8"
  by (simp add: ghz_vec_def)

lemma ghz_vec_index:
  assumes r: "r < 8" and m: "m < 8"
  shows "ghz_vec p m $ r = (if r = m then 1 else 0) + sign_pm p * (if r = 7 - m then 1 else 0)"
  using r m by (simp add: ghz_vec_def)

lemma mult_gvec0:
  assumes M: "M \<in> carrier_mat 8 8" and r: "r < 8"
  shows "(M *\<^sub>v ghz_vec p 0) $ r = M $$ (r,0) + sign_pm p * M $$ (r,7)"
proof -
  have e: "M *\<^sub>v ghz_vec p 0 = M *\<^sub>v unit_vec 8 0 + sign_pm p \<cdot>\<^sub>v (M *\<^sub>v unit_vec 8 7)"
    unfolding ghz_vec_def using M by (simp add: mult_add_distrib_mat_vec mult_mat_vec)
  show ?thesis unfolding e using M r by simp
qed

lemma block_op_entry_cases:
  assumes U: "U \<in> carrier_mat 2 2" and r: "r < 8" and k: "k < 8"
  shows "block_op 0 U $$ (r,k) = U $$ (r div 4, k div 4) * 1\<^sub>m 2 $$ (r div 2 mod 2, k div 2 mod 2) * 1\<^sub>m 2 $$ (r mod 2, k mod 2)"
    and "block_op 1 U $$ (r,k) = 1\<^sub>m 2 $$ (r div 4, k div 4) * U $$ (r div 2 mod 2, k div 2 mod 2) * 1\<^sub>m 2 $$ (r mod 2, k mod 2)"
    and "block_op 2 U $$ (r,k) = 1\<^sub>m 2 $$ (r div 4, k div 4) * 1\<^sub>m 2 $$ (r div 2 mod 2, k div 2 mod 2) * U $$ (r mod 2, k mod 2)"
  unfolding block_op_cases[OF U] by (rule tensor3_index; (use U r k in simp))+

lemma block_op_X_gvec:
  assumes s: "s < 3"
  shows "block_op s Pauli_X *\<^sub>v ghz_vec p 0 = ghz_vec p (2^(2-s))"
proof (rule eq_vecI)
  have M: "block_op s Pauli_X \<in> carrier_mat 8 8" by (rule block_op_carrier[OF Pauli_X_carrier s])
  show "dim_vec (block_op s Pauli_X *\<^sub>v ghz_vec p 0) = dim_vec (ghz_vec p (2^(2-s)))" using M by simp
  fix r assume "r < dim_vec (ghz_vec p (2^(2-s)))"
  hence r: "r < 8" by simp
  have "s = 0 \<or> s = 1 \<or> s = 2" using s by auto
  thus "(block_op s Pauli_X *\<^sub>v ghz_vec p 0) $ r = ghz_vec p (2^(2-s)) $ r"
    unfolding mult_gvec0[OF M r] using idx8[OF r]
    by (elim disjE; simp add: block_op_entry_cases[OF Pauli_X_carrier] block_op_entry_cases(2)[OF Pauli_X_carrier, unfolded One_nat_def] ghz_vec_index; simp add: Pauli_X_def sign_pm_def)
qed

lemma block_op_Y_gvec:
  assumes s: "s < 3"
  shows "block_op s Pauli_Y *\<^sub>v ghz_vec p 0 = (-\<i>) \<cdot>\<^sub>v ghz_vec (\<not> p) (2^(2-s))"
proof (rule eq_vecI)
  have M: "block_op s Pauli_Y \<in> carrier_mat 8 8" by (rule block_op_carrier[OF Pauli_Y_carrier s])
  show "dim_vec (block_op s Pauli_Y *\<^sub>v ghz_vec p 0) = dim_vec ((-\<i>) \<cdot>\<^sub>v ghz_vec (\<not> p) (2^(2-s)))" using M by simp
  fix r assume "r < dim_vec ((-\<i>) \<cdot>\<^sub>v ghz_vec (\<not> p) (2^(2-s)))"
  hence r: "r < 8" by simp
  have "s = 0 \<or> s = 1 \<or> s = 2" using s by auto
  thus "(block_op s Pauli_Y *\<^sub>v ghz_vec p 0) $ r = ((-\<i>) \<cdot>\<^sub>v ghz_vec (\<not> p) (2^(2-s))) $ r"
    unfolding mult_gvec0[OF M r] using idx8[OF r] r
    by (elim disjE; simp add: block_op_entry_cases[OF Pauli_Y_carrier] block_op_entry_cases(2)[OF Pauli_Y_carrier, unfolded One_nat_def] ghz_vec_index; simp add: Pauli_Y_def sign_pm_def)
qed

lemma block_op_Z_gvec:
  assumes s: "s < 3"
  shows "block_op s Pauli_Z *\<^sub>v ghz_vec p 0 = ghz_vec (\<not> p) 0"
proof (rule eq_vecI)
  have M: "block_op s Pauli_Z \<in> carrier_mat 8 8" by (rule block_op_carrier[OF Pauli_Z_carrier s])
  show "dim_vec (block_op s Pauli_Z *\<^sub>v ghz_vec p 0) = dim_vec (ghz_vec (\<not> p) 0)" using M by simp
  fix r assume "r < dim_vec (ghz_vec (\<not> p) 0)"
  hence r: "r < 8" by simp
  have "s = 0 \<or> s = 1 \<or> s = 2" using s by auto
  thus "(block_op s Pauli_Z *\<^sub>v ghz_vec p 0) $ r = ghz_vec (\<not> p) 0 $ r"
    unfolding mult_gvec0[OF M r] using idx8[OF r]
    by (elim disjE; simp add: block_op_entry_cases[OF Pauli_Z_carrier] block_op_entry_cases(2)[OF Pauli_Z_carrier, unfolded One_nat_def] ghz_vec_index; simp add: Pauli_Z_def sign_pm_def)
qed

lemma inner_two_units:
  assumes a: "a < n" and b: "b < n" and c: "c < n" and d: "d < n"
  shows "\<langle>unit_vec n a + \<alpha> \<cdot>\<^sub>v unit_vec n b | unit_vec n c + \<beta> \<cdot>\<^sub>v unit_vec n d\<rangle>
         = (if a = c then 1 else 0) + \<beta> * (if a = d then 1 else 0)
           + cnj \<alpha> * (if b = c then 1 else 0) + cnj \<alpha> * \<beta> * (if b = d then 1 else 0)"
proof -
  let ?u = "unit_vec n a + \<alpha> \<cdot>\<^sub>v unit_vec n b" and ?v = "unit_vec n c + \<beta> \<cdot>\<^sub>v unit_vec n d"
  have "\<langle>?u | ?v\<rangle> = (\<Sum>k \<in> {0..<n}. cnj (?u $ k) * (?v $ k))" by (rule inner_prod_sum) simp_all
  also have "\<dots> = (\<Sum>k \<in> {0..<n}. (if k = a then (if a = c then 1 else 0) else 0)
                  + (if k = a then \<beta> * (if a = d then 1 else 0) else 0)
                  + (if k = b then cnj \<alpha> * (if b = c then 1 else 0) else 0)
                  + (if k = b then cnj \<alpha> * \<beta> * (if b = d then 1 else 0) else 0))"
    by (rule sum.cong) (use a b c d in \<open>auto simp: algebra_simps\<close>)
  also have "\<dots> = (if a = c then 1 else 0) + \<beta> * (if a = d then 1 else 0)
           + cnj \<alpha> * (if b = c then 1 else 0) + cnj \<alpha> * \<beta> * (if b = d then 1 else 0)"
    using a b by (simp only: sum.distrib) simp
  finally show ?thesis .
qed

lemma ghz_vec_inner:
  assumes m: "m \<in> {0,1,2,4}" and m': "m' \<in> {0,1,2,4}"
  shows "\<langle>ghz_vec p m | ghz_vec p' m'\<rangle> = (if m = m' \<and> p = p' then 2 else 0)"
proof -
  have lt: "m < 8" "7 - m < 8" "m' < 8" "7 - m' < 8" using m m' by auto
  show ?thesis unfolding ghz_vec_def inner_two_units[OF lt]
    using m m' by (cases p; cases p') (auto simp: sign_pm_def)
qed

subsection \<open>Code words and the images of the errors\<close>

definition ghz_vec_of :: "bool \<times> nat \<Rightarrow> complex Matrix.vec" where "ghz_vec_of x = ghz_vec (fst x) (snd x)"

text \<open>A label lists the block vectors of a product state, one per block.\<close>

definition label_vec :: "(bool \<times> nat) list \<Rightarrow> complex Matrix.vec" where
  "label_vec l = tensor3 (ghz_vec_of (l ! 0)) (ghz_vec_of (l ! 1)) (ghz_vec_of (l ! 2))"

definition valid_label :: "(bool \<times> nat) list \<Rightarrow> bool" where
  "valid_label l \<longleftrightarrow> length l = 3 \<and> (\<forall>x \<in> set l. snd x \<in> {0,1,2,4})"

definition shor_scale :: complex where "shor_scale = complex_of_real (1 / sqrt 8)"

definition shor_cw :: "bool \<Rightarrow> complex Matrix.vec" where
  "shor_cw p = shor_scale \<cdot>\<^sub>v label_vec (replicate 3 (p, 0))"

text \<open>The notes' code words $\ket{0_L},\ket{1_L}$.\<close>

lemma shor_cw_notes:
  "shor_cw True = complex_of_real (1 / sqrt (2^3)) \<cdot>\<^sub>v
     tensor_vec (tensor_vec (unit_vec 8 0 + unit_vec 8 7) (unit_vec 8 0 + unit_vec 8 7)) (unit_vec 8 0 + unit_vec 8 7)"
  "shor_cw False = complex_of_real (1 / sqrt (2^3)) \<cdot>\<^sub>v
     tensor_vec (tensor_vec (unit_vec 8 0 - unit_vec 8 7) (unit_vec 8 0 - unit_vec 8 7)) (unit_vec 8 0 - unit_vec 8 7)"
proof -
  have m: "unit_vec 8 0 + (-1) \<cdot>\<^sub>v unit_vec 8 7 = (unit_vec 8 0 - unit_vec 8 7 :: complex Matrix.vec)"
    by (rule eq_vecI) simp_all
  show "shor_cw True = complex_of_real (1 / sqrt (2^3)) \<cdot>\<^sub>v
     tensor_vec (tensor_vec (unit_vec 8 0 + unit_vec 8 7) (unit_vec 8 0 + unit_vec 8 7)) (unit_vec 8 0 + unit_vec 8 7)"
    by (simp add: shor_cw_def shor_scale_def label_vec_def tensor3_def ghz_vec_of_def ghz_vec_def sign_pm_def)
  show "shor_cw False = complex_of_real (1 / sqrt (2^3)) \<cdot>\<^sub>v
     tensor_vec (tensor_vec (unit_vec 8 0 - unit_vec 8 7) (unit_vec 8 0 - unit_vec 8 7)) (unit_vec 8 0 - unit_vec 8 7)"
    by (simp add: shor_cw_def shor_scale_def label_vec_def tensor3_def ghz_vec_of_def ghz_vec_def sign_pm_def m)
qed

lemma ghz_vec_of_dim [simp]: "dim_vec (ghz_vec_of x) = 8"
  by (simp add: ghz_vec_of_def)

lemma label_vec_dim [simp]: "dim_vec (label_vec l) = 512"
  unfolding label_vec_def ghz_vec_of_def by (rule tensor3_dim) simp_all

lemma shor_cw_dim [simp]: "dim_vec (shor_cw p) = 512"
  by (simp add: shor_cw_def)

lemma tensor3_smult:
  assumes "dim_vec x = 8" "dim_vec y = 8" "dim_vec z = 8"
  shows "tensor3 (k \<cdot>\<^sub>v x) y z = k \<cdot>\<^sub>v tensor3 x y z" "tensor3 x (k \<cdot>\<^sub>v y) z = k \<cdot>\<^sub>v tensor3 x y z"
    "tensor3 x y (k \<cdot>\<^sub>v z) = k \<cdot>\<^sub>v tensor3 x y z"
  unfolding tensor3_def using assms
  by (simp_all add: tensor_vec_smult_left tensor_vec_smult_right tensor_vec_dim)

lemma qubit_op_tl:
  assumes i: "i < 9" and U: "U \<in> carrier_mat 2 2"
      and act: "block_op (i mod 3) U *\<^sub>v ghz_vec p 0 = \<kappa> \<cdot>\<^sub>v ghz_vec q m"
  shows "qubit_op i U *\<^sub>v label_vec (replicate 3 (p, 0)) = \<kappa> \<cdot>\<^sub>v label_vec ((replicate 3 (p, 0))[i div 3 := (q, m)])"
proof -
  have M: "block_op (i mod 3) U \<in> carrier_mat 8 8" by (rule block_op_carrier[OF U]) simp
  have t0: "label_vec (replicate 3 (p, 0)) = tensor3 (ghz_vec p 0) (ghz_vec p 0) (ghz_vec p 0)" by (simp add: label_vec_def ghz_vec_of_def)
  have "i div 3 = 0 \<or> i div 3 = 1 \<or> i div 3 = 2" using i by auto
  thus ?thesis
  proof (elim disjE)
    assume b: "i div 3 = 0"
    show ?thesis unfolding qubit_op_blk_div[OF i] b t0 on_block_tv3(1)[OF M ghz_vec_dim ghz_vec_dim ghz_vec_dim] act
      by (simp add: label_vec_def ghz_vec_of_def tensor3_smult)
  next
    assume b: "i div 3 = 1"
    show ?thesis unfolding qubit_op_blk_div[OF i] b t0 on_block_tv3(2)[OF M ghz_vec_dim ghz_vec_dim ghz_vec_dim] act
      by (simp add: label_vec_def ghz_vec_of_def tensor3_smult)
  next
    assume b: "i div 3 = 2"
    show ?thesis unfolding qubit_op_blk_div[OF i] b t0 on_block_tv3(3)[OF M ghz_vec_dim ghz_vec_dim ghz_vec_dim] act
      by (simp add: label_vec_def ghz_vec_of_def tensor3_smult)
  qed
qed

lemma qubit_op_X_tl:
  "i < 9 \<Longrightarrow> qubit_op i Pauli_X *\<^sub>v label_vec (replicate 3 (p, 0))
     = label_vec ((replicate 3 (p, 0))[i div 3 := (p, 2^(2 - i mod 3))])"
  using qubit_op_tl[OF _ Pauli_X_carrier, of i p 1 p "2^(2 - i mod 3)"] block_op_X_gvec[of "i mod 3" p] by simp

lemma qubit_op_Y_tl:
  "i < 9 \<Longrightarrow> qubit_op i Pauli_Y *\<^sub>v label_vec (replicate 3 (p, 0))
     = (-\<i>) \<cdot>\<^sub>v label_vec ((replicate 3 (p, 0))[i div 3 := (\<not> p, 2^(2 - i mod 3))])"
  using qubit_op_tl[OF _ Pauli_Y_carrier, of i p "-\<i>" "\<not> p" "2^(2 - i mod 3)"] block_op_Y_gvec[of "i mod 3" p] by simp

lemma qubit_op_Z_tl:
  "i < 9 \<Longrightarrow> qubit_op i Pauli_Z *\<^sub>v label_vec (replicate 3 (p, 0))
     = label_vec ((replicate 3 (p, 0))[i div 3 := (\<not> p, 0)])"
  using qubit_op_tl[OF _ Pauli_Z_carrier, of i p 1 "\<not> p" 0] block_op_Z_gvec[of "i mod 3" p] by simp

lemma label_vec_inner:
  assumes l: "valid_label l" and l': "valid_label l'"
  shows "\<langle>label_vec l | label_vec l'\<rangle> = (if l = l' then 8 else 0)"
proof -
  have len: "length l = 3" "length l' = 3" using l l' by (simp_all add: valid_label_def)
  have mem: "\<And>k. k < 3 \<Longrightarrow> snd (l ! k) \<in> {0,1,2,4} \<and> snd (l' ! k) \<in> {0,1,2,4}"
    using l l' len unfolding valid_label_def by (metis nth_mem)
  have g: "\<And>k. k < 3 \<Longrightarrow> \<langle>ghz_vec_of (l ! k) | ghz_vec_of (l' ! k)\<rangle> = (if l ! k = l' ! k then 2 else 0)"
  proof -
    fix k :: nat assume k: "k < 3"
    show "\<langle>ghz_vec_of (l ! k) | ghz_vec_of (l' ! k)\<rangle> = (if l ! k = l' ! k then 2 else 0)"
      unfolding ghz_vec_of_def using ghz_vec_inner[of "snd (l ! k)" "snd (l' ! k)" "fst (l ! k)" "fst (l' ! k)"] mem[OF k]
      by (auto simp: prod_eq_iff)
  qed
  have e1: "\<langle>label_vec l | label_vec l'\<rangle> = \<langle>tensor_vec (ghz_vec_of (l ! 0)) (ghz_vec_of (l ! 1)) | tensor_vec (ghz_vec_of (l' ! 0)) (ghz_vec_of (l' ! 1))\<rangle>
          * \<langle>ghz_vec_of (l ! 2) | ghz_vec_of (l' ! 2)\<rangle>"
    unfolding label_vec_def tensor3_def by (rule tensor_inner_prod) (simp_all add: tensor_vec_dim)
  have e2: "\<langle>tensor_vec (ghz_vec_of (l ! 0)) (ghz_vec_of (l ! 1)) | tensor_vec (ghz_vec_of (l' ! 0)) (ghz_vec_of (l' ! 1))\<rangle>
          = \<langle>ghz_vec_of (l ! 0) | ghz_vec_of (l' ! 0)\<rangle> * \<langle>ghz_vec_of (l ! 1) | ghz_vec_of (l' ! 1)\<rangle>"
    by (rule tensor_inner_prod) simp_all
  have g0: "\<langle>ghz_vec_of (l ! 0) | ghz_vec_of (l' ! 0)\<rangle> = (if l ! 0 = l' ! 0 then 2 else 0)" by (rule g) simp
  have g1: "\<langle>ghz_vec_of (l ! 1) | ghz_vec_of (l' ! 1)\<rangle> = (if l ! 1 = l' ! 1 then 2 else 0)" by (rule g) simp
  have g2: "\<langle>ghz_vec_of (l ! 2) | ghz_vec_of (l' ! 2)\<rangle> = (if l ! 2 = l' ! 2 then 2 else 0)" by (rule g) simp
  have eqv: "l = l' \<longleftrightarrow> l ! 0 = l' ! 0 \<and> l ! 1 = l' ! 1 \<and> l ! 2 = l' ! 2"
  proof
    assume "l ! 0 = l' ! 0 \<and> l ! 1 = l' ! 1 \<and> l ! 2 = l' ! 2"
    moreover have "\<And>k :: nat. k < 3 \<Longrightarrow> k = 0 \<or> k = 1 \<or> k = 2" by auto
    ultimately show "l = l'" using len by (metis nth_equalityI)
  qed simp
  show ?thesis unfolding e1 e2 g0 g1 g2 eqv by simp
qed

subsection \<open>The 22 correctable errors\<close>

text \<open>In the notes' numbering $I,X_1,\dots,X_9,Y_1,\dots,Y_9,Z_1,Z_4,Z_7$.  Here qubits are counted
from $0$: $I$, $X_i$ and $Y_i$ ($i<9$), and $Z_0,Z_3,Z_6$.\<close>

definition shor_errors :: "complex Matrix.mat list" where
  "shor_errors = 1\<^sub>m 512 # map (\<lambda>i. qubit_op i Pauli_X) [0..<9] @ map (\<lambda>i. qubit_op i Pauli_Y) [0..<9]
     @ map (\<lambda>b. qubit_op (3 * b) Pauli_Z) [0..<3]"

definition shor_labels :: "bool \<Rightarrow> (bool \<times> nat) list list" where
  "shor_labels p = replicate 3 (p, 0)
     # map (\<lambda>i. (replicate 3 (p, 0))[i div 3 := (p, 2^(2 - i mod 3))]) [0..<9]
     @ map (\<lambda>i. (replicate 3 (p, 0))[i div 3 := (\<not> p, 2^(2 - i mod 3))]) [0..<9]
     @ map (\<lambda>b. (replicate 3 (p, 0))[b := (\<not> p, 0)]) [0..<3]"

definition shor_kappa :: "complex list" where
  "shor_kappa = 1 # replicate 9 1 @ replicate 9 (-\<i>) @ replicate 3 1"

lemma shor_lengths [simp]: "length shor_errors = 22" "length (shor_labels p) = 22" "length shor_kappa = 22"
  by (simp_all add: shor_errors_def shor_labels_def shor_kappa_def)

text \<open>One $Z$ per block suffices, since $Z_i$ and $Z_j$ agree on the code when $i$ and $j$ share a
block.  Each error sends a code word
to a multiple of a labelled product vector,
\[ E_j\ket{c_p}=\kappa_j\,8^{-1/2}\,\ket{\ell_j(p)}, \]
and distinct errors give distinct labels, hence orthogonal images.\<close>

lemma shor_errors_cases:
  assumes j: "j < 22"
  obtains "j = 0" "shor_errors ! j = 1\<^sub>m 512" "shor_labels p ! j = replicate 3 (p, 0)" "shor_kappa ! j = 1"
  | i where "i < 9" "j = Suc i" "shor_errors ! j = qubit_op i Pauli_X"
      "shor_labels p ! j = (replicate 3 (p, 0))[i div 3 := (p, 2^(2 - i mod 3))]" "shor_kappa ! j = 1"
  | i where "i < 9" "j = 10 + i" "shor_errors ! j = qubit_op i Pauli_Y"
      "shor_labels p ! j = (replicate 3 (p, 0))[i div 3 := (\<not> p, 2^(2 - i mod 3))]" "shor_kappa ! j = -\<i>"
  | b where "b < 3" "j = 19 + b" "shor_errors ! j = qubit_op (3 * b) Pauli_Z"
      "shor_labels p ! j = (replicate 3 (p, 0))[b := (\<not> p, 0)]" "shor_kappa ! j = 1"
proof -
  consider "j = 0" | "0 < j \<and> j < 10" | "10 \<le> j \<and> j < 19" | "19 \<le> j" using j by linarith
  thus thesis
  proof cases
    case 1 thus thesis using that(1) by (simp add: shor_errors_def shor_labels_def shor_kappa_def)
  next
    case 2
    define i where "i = j - 1"
    have i: "i < 9" and ji: "j = Suc i" using 2 unfolding i_def by auto
    show thesis using that(2)[OF i ji] i ji by (simp add: shor_errors_def shor_labels_def shor_kappa_def nth_append)
  next
    case 3
    define i where "i = j - 10"
    have i: "i < 9" and ji: "j = 10 + i" using 3 unfolding i_def by auto
    show thesis using that(3)[OF i ji] i ji by (simp add: shor_errors_def shor_labels_def shor_kappa_def nth_append)
  next
    case 4
    define b where "b = j - 19"
    have b: "b < 3" and jb: "j = 19 + b" using 4 j unfolding b_def by auto
    show thesis using that(4)[OF b jb] b jb by (simp add: shor_errors_def shor_labels_def shor_kappa_def nth_append)
  qed
qed

lemma shor_errors_carrier: "j < 22 \<Longrightarrow> shor_errors ! j \<in> carrier_mat 512 512"
  by (erule shor_errors_cases) (simp_all add: qubit_op_carrier)

lemma shor_errors_action:
  assumes j: "j < 22"
  shows "shor_errors ! j *\<^sub>v shor_cw p = (shor_kappa ! j * shor_scale) \<cdot>\<^sub>v label_vec (shor_labels p ! j)"
proof -
  have Ec: "shor_errors ! j \<in> carrier_mat 512 512" by (rule shor_errors_carrier[OF j])
  have "shor_errors ! j *\<^sub>v shor_cw p = shor_scale \<cdot>\<^sub>v (shor_errors ! j *\<^sub>v label_vec (replicate 3 (p, 0)))"
    unfolding shor_cw_def by (rule mult_mat_vec[OF Ec]) (rule carrier_vecI, simp)
  also have "\<dots> = (shor_kappa ! j * shor_scale) \<cdot>\<^sub>v label_vec (shor_labels p ! j)"
  proof (rule shor_errors_cases[OF j, of p])
    assume a: "shor_errors ! j = 1\<^sub>m 512" "shor_labels p ! j = replicate 3 (p, 0)" "shor_kappa ! j = 1"
    show ?thesis unfolding a one_mult_mat_vec[OF carrier_vecI[OF label_vec_dim]] by (simp only: mult_1_left)
  next
    fix i assume "i < 9" "shor_errors ! j = qubit_op i Pauli_X"
      "shor_labels p ! j = (replicate 3 (p, 0))[i div 3 := (p, 2^(2 - i mod 3))]" "shor_kappa ! j = 1"
    thus ?thesis using qubit_op_X_tl by simp
  next
    fix i assume "i < 9" "shor_errors ! j = qubit_op i Pauli_Y"
      "shor_labels p ! j = (replicate 3 (p, 0))[i div 3 := (\<not> p, 2^(2 - i mod 3))]" "shor_kappa ! j = -\<i>"
    thus ?thesis using qubit_op_Y_tl by (simp add: smult_smult_assoc mult.commute)
  next
    fix b assume b: "b < 3" "shor_errors ! j = qubit_op (3 * b) Pauli_Z"
      "shor_labels p ! j = (replicate 3 (p, 0))[b := (\<not> p, 0)]" "shor_kappa ! j = 1"
    thus ?thesis using qubit_op_Z_tl[of "3 * b" p] by simp
  qed
  finally show ?thesis .
qed

lemma shor_labels_valid: "j < 22 \<Longrightarrow> valid_label (shor_labels p ! j)"
proof (erule shor_errors_cases[of _ p])
  have upd: "\<And>b q m. m \<in> {0,1,2,4} \<Longrightarrow> valid_label ((replicate 3 (p, 0))[b := (q, m)])"
    unfolding valid_label_def using set_update_subset_insert by fastforce
  have pw: "\<And>i. (2::nat) ^ (2 - i mod 3) \<in> {0,1,2,4}"
  proof -
    fix i :: nat have "i mod 3 = 0 \<or> i mod 3 = 1 \<or> i mod 3 = 2" by auto
    thus "(2::nat) ^ (2 - i mod 3) \<in> {0,1,2,4}" by auto
  qed
  show "shor_labels p ! j = replicate 3 (p, 0) \<Longrightarrow> valid_label (shor_labels p ! j)" by (simp add: valid_label_def)
  show "\<And>i. shor_labels p ! j = (replicate 3 (p, 0))[i div 3 := (p, 2 ^ (2 - i mod 3))] \<Longrightarrow> valid_label (shor_labels p ! j)"
    using upd pw by simp
  show "\<And>i. shor_labels p ! j = (replicate 3 (p, 0))[i div 3 := (\<not> p, 2 ^ (2 - i mod 3))] \<Longrightarrow> valid_label (shor_labels p ! j)"
    using upd pw by simp
  show "\<And>b. shor_labels p ! j = (replicate 3 (p, 0))[b := (\<not> p, 0)] \<Longrightarrow> valid_label (shor_labels p ! j)"
    using upd by simp
qed

lemma shor_labels_distinct: "distinct (shor_labels True @ shor_labels False)"
  unfolding shor_labels_def by code_simp

lemma shor_labels_differ:
  assumes i: "i < 22" and j: "j < 22" and ij: "i \<noteq> j"
  shows "shor_labels p ! i \<noteq> shor_labels p' ! j"
proof -
  have dT: "distinct (shor_labels True)" and dF: "distinct (shor_labels False)"
    and disj: "set (shor_labels True) \<inter> set (shor_labels False) = {}"
    using shor_labels_distinct by simp_all
  show ?thesis
  proof (cases p; cases p')
    assume "p" "p'" thus ?thesis using nth_eq_iff_index_eq[OF dT, of i j] i j ij by simp
  next
    assume "p" "\<not> p'"
    show ?thesis
    proof
      assume "shor_labels p ! i = shor_labels p' ! j"
      hence "shor_labels True ! i = shor_labels False ! j" using \<open>p\<close> \<open>\<not> p'\<close> by simp
      hence eq': "shor_labels True ! i = shor_labels False ! j" .
      have "shor_labels False ! j \<in> set (shor_labels True)" using nth_mem[of i "shor_labels True"] i unfolding eq' by simp
      moreover have "shor_labels False ! j \<in> set (shor_labels False)" using j by simp
      ultimately have "shor_labels False ! j \<in> set (shor_labels True) \<inter> set (shor_labels False)" by (rule IntI)
      thus False using disj by simp
    qed
  next
    assume "\<not> p" "p'"
    show ?thesis
    proof
      assume "shor_labels p ! i = shor_labels p' ! j"
      hence "shor_labels False ! i = shor_labels True ! j" using \<open>\<not> p\<close> \<open>p'\<close> by simp
      hence eq': "shor_labels False ! i = shor_labels True ! j" .
      have "shor_labels True ! j \<in> set (shor_labels False)" using nth_mem[of i "shor_labels False"] i unfolding eq' by simp
      moreover have "shor_labels True ! j \<in> set (shor_labels True)" using j by simp
      ultimately have "shor_labels True ! j \<in> set (shor_labels False) \<inter> set (shor_labels True)" by (rule IntI)
      thus False using disj by blast
    qed
  next
    assume "\<not> p" "\<not> p'" thus ?thesis using nth_eq_iff_index_eq[OF dF, of i j] i j ij by simp
  qed
qed

lemma shor_errors_orth:
  assumes i: "i < 22" and j: "j < 22" and ij: "i \<noteq> j"
  shows "\<langle>shor_errors ! i *\<^sub>v shor_cw p | shor_errors ! j *\<^sub>v shor_cw p'\<rangle> = 0"
proof -
  have "\<langle>label_vec (shor_labels p ! i) | label_vec (shor_labels p' ! j)\<rangle> = 0"
    using label_vec_inner[OF shor_labels_valid[OF i] shor_labels_valid[OF j]] shor_labels_differ[OF i j ij] by simp
  moreover have "dim_vec (label_vec (shor_labels p ! i)) = dim_vec (label_vec (shor_labels p' ! j))"
    by simp
  ultimately show ?thesis unfolding shor_errors_action[OF i] shor_errors_action[OF j]
    by (simp only: No_Cloning.inner_prod_distrib_left inner_prod_right_smult' mult_zero_right)
qed

lemma shor_scale_sq: "cnj shor_scale * shor_scale = 1 / 8"
proof -
  have "sqrt 8 * sqrt 8 = (8::real)" by simp
  hence "(1 / sqrt 8) * (1 / sqrt 8) = (1/8::real)" by (simp add: divide_simps)
  thus ?thesis unfolding shor_scale_def by (simp only: complex_cnj_complex_of_real of_real_mult[symmetric]) simp
qed

lemma shor_cw_inner: "\<langle>shor_cw p | shor_cw p'\<rangle> = (if p = p' then 1 else 0)"
proof -
  have v: "valid_label (replicate 3 (q, 0))" for q by (simp add: valid_label_def)
  have "\<langle>shor_cw p | shor_cw p'\<rangle> = cnj shor_scale * shor_scale * \<langle>label_vec (replicate 3 (p, 0)) | label_vec (replicate 3 (p', 0))\<rangle>"
  proof -
    have "dim_vec (label_vec (replicate 3 (p, 0))) = dim_vec (label_vec (replicate 3 (p', 0)))" by simp
    thus ?thesis unfolding shor_cw_def by (simp only: No_Cloning.inner_prod_distrib_left inner_prod_right_smult' mult_ac)
  qed
  also have "\<dots> = (if p = p' then 1 else 0)" unfolding label_vec_inner[OF v v] shor_scale_sq by simp
  finally show ?thesis .
qed

subsection \<open>The code space and its projection\<close>

definition shor_V :: "complex Matrix.mat" where "shor_V = mat_of_cols 512 [shor_cw True, shor_cw False]"

definition shor_P :: "complex Matrix.mat" where "shor_P = shor_V * (shor_V\<^sup>\<dagger>)"

definition shor_state :: "complex \<Rightarrow> complex \<Rightarrow> complex Matrix.vec" where
  "shor_state \<alpha> \<beta> = \<alpha> \<cdot>\<^sub>v shor_cw True + \<beta> \<cdot>\<^sub>v shor_cw False"

lemma shor_state_dim [simp]: "dim_vec (shor_state \<alpha> \<beta>) = 512"
  by (simp add: shor_state_def)

lemma shor_V_carrier: "shor_V \<in> carrier_mat 512 2"
  unfolding shor_V_def using mat_of_cols_carrier[of 512 "[shor_cw True, shor_cw False]"] by (simp add: numeral_2_eq_2)

lemma shor_orthonormal: "orthonormal_list 512 [shor_cw True, shor_cw False]"
  unfolding orthonormal_list_def
proof (intro conjI allI impI ballI)
  fix v assume "v \<in> set [shor_cw True, shor_cw False]" thus "dim_vec v = 512" by auto
next
  fix i j assume "i < length [shor_cw True, shor_cw False]" "j < length [shor_cw True, shor_cw False]"
  hence "i = 0 \<or> i = 1" "j = 0 \<or> j = 1" by auto
  thus "\<langle>[shor_cw True, shor_cw False] ! i | [shor_cw True, shor_cw False] ! j\<rangle> = (if i = j then 1 else 0)"
    by (elim disjE) (simp_all add: shor_cw_inner)
qed

lemma shor_VdV: "(shor_V\<^sup>\<dagger>) * shor_V = 1\<^sub>m 2"
  unfolding shor_V_def using cols_mat_dagger_left[OF shor_orthonormal] by (simp add: numeral_2_eq_2)

lemma mat_vec_unit_col:
  fixes M :: "complex Matrix.mat"
  assumes M: "M \<in> carrier_mat n k" and a: "a < k"
  shows "M *\<^sub>v unit_vec k a = Matrix.col M a"
  by (rule eq_vecI) (use M a in auto)

lemma shor_V_col: "a < 2 \<Longrightarrow> Matrix.col shor_V a = [shor_cw True, shor_cw False] ! a"
  unfolding shor_V_def by (rule col_mat_of_cols) (auto simp: less_2_cases_iff intro!: carrier_vecI)

lemma shor_V_unit: "shor_V *\<^sub>v unit_vec 2 0 = shor_cw True" "shor_V *\<^sub>v unit_vec 2 1 = shor_cw False"
  using mat_vec_unit_col[OF shor_V_carrier, of 0] mat_vec_unit_col[OF shor_V_carrier, of 1]
    shor_V_col[of 0] shor_V_col[of 1] by simp_all

lemma shor_P_projection: "projection 512 shor_P"
proof -
  have Vc: "shor_V \<in> carrier_mat 512 2" by (rule shor_V_carrier)
  have Vdc: "shor_V\<^sup>\<dagger> \<in> carrier_mat 2 512" by (rule dagger_carrier[OF Vc])
  have Pc: "shor_P \<in> carrier_mat 512 512" unfolding shor_P_def using Vc Vdc by simp
  have "shor_P\<^sup>\<dagger> = ((shor_V\<^sup>\<dagger>)\<^sup>\<dagger>) * (shor_V\<^sup>\<dagger>)"
    unfolding shor_P_def by (rule dagger_of_prod) (use Vc Vdc in simp)
  hence h: "shor_P\<^sup>\<dagger> = shor_P" unfolding shor_P_def dagger_of_dagger_is_id .
  have "shor_P * shor_P = shor_V * (((shor_V\<^sup>\<dagger>) * shor_V) * (shor_V\<^sup>\<dagger>))"
    unfolding shor_P_def
    by (simp only: assoc_mult_mat[OF Vc Vdc mult_carrier_mat[OF Vc Vdc]] assoc_mult_mat[OF Vdc Vc Vdc])
  also have "\<dots> = shor_P" unfolding shor_VdV shor_P_def by (simp only: left_mult_one_mat[OF Vdc])
  finally show ?thesis unfolding projection_def hermitian_def using Pc h by simp
qed

lemma shor_P_cw: "shor_P *\<^sub>v shor_cw p = shor_cw p"
proof -
  define a where "a = (if p then 0 else 1 :: nat)"
  have a: "a < 2" unfolding a_def by simp
  have cw: "shor_cw p = shor_V *\<^sub>v unit_vec 2 a" unfolding a_def using shor_V_unit by simp
  have Vc: "shor_V \<in> carrier_mat 512 2" by (rule shor_V_carrier)
  have Vdc: "shor_V\<^sup>\<dagger> \<in> carrier_mat 2 512" by (rule dagger_carrier[OF Vc])
  have e: "unit_vec 2 a \<in> carrier_vec 2" by simp
  have "shor_P *\<^sub>v (shor_V *\<^sub>v unit_vec 2 a) = shor_V *\<^sub>v ((shor_V\<^sup>\<dagger>) *\<^sub>v (shor_V *\<^sub>v unit_vec 2 a))"
    unfolding shor_P_def using Vc Vdc e by (simp add: assoc_mult_mat_vec)
  also have "(shor_V\<^sup>\<dagger>) *\<^sub>v (shor_V *\<^sub>v unit_vec 2 a) = unit_vec 2 a"
    using assoc_mult_mat_vec[OF Vdc Vc e] unfolding shor_VdV by simp
  finally show ?thesis unfolding cw .
qed

lemma shor_P_fixes: "shor_P *\<^sub>v shor_state \<alpha> \<beta> = shor_state \<alpha> \<beta>"
proof -
  have Pc: "shor_P \<in> carrier_mat 512 512" using shor_P_projection by (simp add: projection_def)
  have c: "\<And>p. shor_cw p \<in> carrier_vec 512" by (rule carrier_vecI) simp
  show ?thesis unfolding shor_state_def
    using Pc c by (simp add: mult_add_distrib_mat_vec[of shor_P 512 512] mult_mat_vec[of shor_P 512 512] shor_P_cw)
qed

subsection \<open>Proposition (Day 33): orthogonal images, and $Z_1v=Z_2v=Z_3v$\<close>

lemma gram_entry:
  fixes A B :: "complex Matrix.mat"
  assumes A: "A \<in> carrier_mat n k" and B: "B \<in> carrier_mat n k" and a: "a < k" and b: "b < k"
  shows "((A\<^sup>\<dagger>) * B) $$ (a,b) = \<langle>Matrix.col A a | Matrix.col B b\<rangle>"
proof -
  have "((A\<^sup>\<dagger>) * B) $$ (a,b) = (\<Sum>i<n. cnj (A $$ (i,a)) * B $$ (i,b))"
    using A B a b by (simp add: scalar_prod_def dagger_def)
  also have "\<dots> = \<langle>Matrix.col A a | Matrix.col B b\<rangle>"
  proof -
    have dA: "dim_vec (Matrix.col A a) = n" and dB: "dim_vec (Matrix.col B b) = n" using A B by simp_all
    show ?thesis unfolding inner_prod_sum[OF dA dB] atLeast0LessThan
      by (rule sum.cong) (use A B a b in auto)
  qed
  finally show ?thesis .
qed

lemma sandwich_VVd:
  fixes V W :: "complex Matrix.mat"
  assumes V: "V \<in> carrier_mat n k" and W: "W \<in> carrier_mat n n"
  shows "(V * (V\<^sup>\<dagger>)) * W * (V * (V\<^sup>\<dagger>)) = V * ((V\<^sup>\<dagger>) * W * V) * (V\<^sup>\<dagger>)"
proof -
  have Vd: "V\<^sup>\<dagger> \<in> carrier_mat k n" by (rule dagger_carrier[OF V])
  have VdW: "(V\<^sup>\<dagger>) * W \<in> carrier_mat k n" by (rule mult_carrier_mat[OF Vd W])
  have "(V * (V\<^sup>\<dagger>)) * W * (V * (V\<^sup>\<dagger>)) = V * ((V\<^sup>\<dagger>) * W) * (V * (V\<^sup>\<dagger>))"
    by (simp only: assoc_mult_mat[OF V Vd W])
  also have "\<dots> = V * (((V\<^sup>\<dagger>) * W) * (V * (V\<^sup>\<dagger>)))"
    by (rule assoc_mult_mat[OF V VdW mult_carrier_mat[OF V Vd]])
  also have "((V\<^sup>\<dagger>) * W) * (V * (V\<^sup>\<dagger>)) = (((V\<^sup>\<dagger>) * W) * V) * (V\<^sup>\<dagger>)"
    by (rule assoc_mult_mat[OF VdW V Vd, symmetric])
  also have "V * ((((V\<^sup>\<dagger>) * W) * V) * (V\<^sup>\<dagger>)) = (V * (((V\<^sup>\<dagger>) * W) * V)) * (V\<^sup>\<dagger>)"
    by (rule assoc_mult_mat[OF V mult_carrier_mat[OF VdW V] Vd, symmetric])
  finally show ?thesis .
qed

lemma qubit_op_unitary: "unitary U \<Longrightarrow> unitary (qubit_op i U)"
  unfolding qubit_op_def by simp

lemma shor_errors_unitary: "U \<in> set shor_errors \<Longrightarrow> U \<in> carrier_mat 512 512 \<and> unitary U"
proof -
  assume "U \<in> set shor_errors"
  then obtain j where j: "j < 22" and U: "U = shor_errors ! j" by (metis in_set_conv_nth shor_lengths(1))
  show ?thesis unfolding U
    by (rule shor_errors_cases[OF j, of True])
       (simp_all add: qubit_op_carrier qubit_op_unitary Pauli_X_unitary Pauli_Y_unitary Pauli_Z_unitary)
qed

theorem shor_orthogonal_images:
  assumes i: "i < 22" and j: "j < 22" and ij: "i \<noteq> j"
  shows "shor_P * (((shor_errors ! i)\<^sup>\<dagger>) * shor_errors ! j) * shor_P = 0\<^sub>m 512 512"
proof -
  let ?Ui = "shor_errors ! i" and ?Uj = "shor_errors ! j" and ?V = shor_V
  have Uic: "?Ui \<in> carrier_mat 512 512" and Ujc: "?Uj \<in> carrier_mat 512 512"
    by (rule shor_errors_carrier[OF i]) (rule shor_errors_carrier[OF j])
  have Vc: "?V \<in> carrier_mat 512 2" by (rule shor_V_carrier)
  have Vdc: "?V\<^sup>\<dagger> \<in> carrier_mat 2 512" by (rule dagger_carrier[OF Vc])
  have Uidc: "?Ui\<^sup>\<dagger> \<in> carrier_mat 512 512" by (rule dagger_carrier[OF Uic])
  have UVi: "?Ui * ?V \<in> carrier_mat 512 2" and UVj: "?Uj * ?V \<in> carrier_mat 512 2" using Uic Ujc Vc by auto
  have G0: "((?Ui * ?V)\<^sup>\<dagger>) * (?Uj * ?V) = 0\<^sub>m 2 2"
  proof (rule eq_matI)
    fix a b assume "a < dim_row (0\<^sub>m 2 2 :: complex Matrix.mat)" "b < dim_col (0\<^sub>m 2 2 :: complex Matrix.mat)"
    hence a: "a < 2" and b: "b < 2" by simp_all
    have ca: "Matrix.col (?Ui * ?V) a = ?Ui *\<^sub>v [shor_cw True, shor_cw False] ! a"
      using col_mult2[OF Uic Vc a] shor_V_col[OF a] by simp
    have cb: "Matrix.col (?Uj * ?V) b = ?Uj *\<^sub>v [shor_cw True, shor_cw False] ! b"
      using col_mult2[OF Ujc Vc b] shor_V_col[OF b] by simp
    obtain pa where pa: "[shor_cw True, shor_cw False] ! a = shor_cw pa" using a
      by (cases a) (auto simp: less_2_cases_iff)
    obtain pb where pb: "[shor_cw True, shor_cw False] ! b = shor_cw pb" using b
      by (cases b) (auto simp: less_2_cases_iff)
    show "(((?Ui * ?V)\<^sup>\<dagger>) * (?Uj * ?V)) $$ (a,b) = (0\<^sub>m 2 2 :: complex Matrix.mat) $$ (a,b)"
      unfolding gram_entry[OF UVi UVj a b] ca cb pa pb shor_errors_orth[OF i j ij] using a b by simp
  qed (use UVi UVj shor_V_carrier in simp_all)
  have "(?V\<^sup>\<dagger>) * (?Ui\<^sup>\<dagger> * ?Uj) * ?V = ((?Ui * ?V)\<^sup>\<dagger>) * (?Uj * ?V)"
  proof -
    have "(?Ui * ?V)\<^sup>\<dagger> = (?V\<^sup>\<dagger>) * (?Ui\<^sup>\<dagger>)" by (rule dagger_of_prod) (use Uic Vc in simp)
    thus ?thesis using Vdc Uidc Ujc Vc
      by (simp add: assoc_mult_mat[of "?V\<^sup>\<dagger>" 2 512 "?Ui\<^sup>\<dagger>" 512 "?Uj * ?V" 2]
          assoc_mult_mat[of "?V\<^sup>\<dagger>" 2 512 "?Ui\<^sup>\<dagger> * ?Uj" 512 ?V 2]
          assoc_mult_mat[of "?Ui\<^sup>\<dagger>" 512 512 ?Uj 512 ?V 2])
  qed
  hence inner0: "(?V\<^sup>\<dagger>) * (?Ui\<^sup>\<dagger> * ?Uj) * ?V = 0\<^sub>m 2 2" unfolding G0 .
  have W: "?Ui\<^sup>\<dagger> * ?Uj \<in> carrier_mat 512 512" using Uidc Ujc by simp
  have "shor_P * (?Ui\<^sup>\<dagger> * ?Uj) * shor_P = ?V * ((?V\<^sup>\<dagger>) * (?Ui\<^sup>\<dagger> * ?Uj) * ?V) * (?V\<^sup>\<dagger>)"
    unfolding shor_P_def by (rule sandwich_VVd[OF Vc W])
  also have "\<dots> = 0\<^sub>m 512 512" unfolding inner0 using Vc Vdc by simp
  finally show ?thesis .
qed

lemma shor_recovery_setting: "recovery_setting 512 shor_P shor_errors"
  by (rule recovery_setting_unitaries[OF shor_P_projection])
     (use shor_errors_unitary shor_orthogonal_images in auto)

lemma qubit_op_Z_cw:
  assumes i: "i < 9"
  shows "qubit_op i Pauli_Z *\<^sub>v shor_cw p = qubit_op (3 * (i div 3)) Pauli_Z *\<^sub>v shor_cw p"
proof -
  have i': "3 * (i div 3) < 9" using i by simp
  have c: "label_vec (replicate 3 (p, 0)) \<in> carrier_vec 512" by (rule carrier_vecI) simp
  show ?thesis unfolding shor_cw_def
    using qubit_op_Z_tl[OF i] qubit_op_Z_tl[OF i']
      mult_mat_vec[OF qubit_op_carrier[OF Pauli_Z_carrier i] c]
      mult_mat_vec[OF qubit_op_carrier[OF Pauli_Z_carrier i'] c] by simp
qed

theorem shor_Z_coincide:
  assumes i: "i < 9" and j: "j < 9" and ij: "i div 3 = j div 3"
  shows "qubit_op i Pauli_Z *\<^sub>v shor_state \<alpha> \<beta> = qubit_op j Pauli_Z *\<^sub>v shor_state \<alpha> \<beta>"
proof -
  have c: "\<And>p. shor_cw p \<in> carrier_vec 512" by (rule carrier_vecI) simp
  have e: "\<And>k. k < 9 \<Longrightarrow> qubit_op k Pauli_Z *\<^sub>v shor_state \<alpha> \<beta>
      = \<alpha> \<cdot>\<^sub>v (qubit_op (3 * (k div 3)) Pauli_Z *\<^sub>v shor_cw True) + \<beta> \<cdot>\<^sub>v (qubit_op (3 * (k div 3)) Pauli_Z *\<^sub>v shor_cw False)"
  proof -
    fix k :: nat assume k: "k < 9"
    have Zc: "qubit_op k Pauli_Z \<in> carrier_mat 512 512" by (rule qubit_op_carrier[OF Pauli_Z_carrier k])
    show "qubit_op k Pauli_Z *\<^sub>v shor_state \<alpha> \<beta>
      = \<alpha> \<cdot>\<^sub>v (qubit_op (3 * (k div 3)) Pauli_Z *\<^sub>v shor_cw True) + \<beta> \<cdot>\<^sub>v (qubit_op (3 * (k div 3)) Pauli_Z *\<^sub>v shor_cw False)"
      unfolding shor_state_def using Zc c qubit_op_Z_cw[OF k]
      by (simp add: mult_add_distrib_mat_vec[OF Zc] mult_mat_vec[OF Zc])
  qed
  show ?thesis unfolding e[OF i] e[OF j] ij ..
qed

text \<open>The Day 32 proposition as first stated (distinct 1-Paulis map $V$ to orthogonal subspaces)
is false: $Z_1\ne Z_2$, yet $Z_1\ket{0_L}=Z_2\ket{0_L}\ne0$.  The notes correct it on Day 33.\<close>

lemma shor_notes_Z1_Z2:
  "qubit_op 0 Pauli_Z \<noteq> qubit_op 1 Pauli_Z"
  "\<langle>qubit_op 0 Pauli_Z *\<^sub>v shor_cw True | qubit_op 1 Pauli_Z *\<^sub>v shor_cw True\<rangle> = 1"
proof -
  have e0: "qubit_op 0 Pauli_Z $$ (256, 256) = -1"
  proof -
    have q: "qubit_op 0 Pauli_Z = Tensor.tensor_mat Pauli_Z (1\<^sub>m 256)"
      using tensor_one_left[OF Pauli_Z_carrier] by (simp add: qubit_op_def)
    have "qubit_op 0 Pauli_Z $$ (256, 256)
          = Pauli_Z $$ (256 div 256, 256 div 256) * 1\<^sub>m 256 $$ (256 mod 256, 256 mod 256)"
      unfolding q by (rule tensor_index_c) (auto simp: Pauli_Z_def)
    thus ?thesis by (simp add: Pauli_Z_def)
  qed
  have e1: "qubit_op 1 Pauli_Z $$ (256, 256) = 1"
  proof -
    have q: "qubit_op 1 Pauli_Z = Tensor.tensor_mat (Tensor.tensor_mat (1\<^sub>m 2) Pauli_Z) (1\<^sub>m 128)"
      by (simp add: qubit_op_def)
    have a: "qubit_op 1 Pauli_Z $$ (256, 256)
          = Tensor.tensor_mat (1\<^sub>m 2) Pauli_Z $$ (256 div 128, 256 div 128) * 1\<^sub>m 128 $$ (256 mod 128, 256 mod 128)"
      unfolding q by (rule tensor_index_c) (auto simp: Pauli_Z_def)
    have b: "Tensor.tensor_mat (1\<^sub>m 2) Pauli_Z $$ (2, 2) = 1\<^sub>m 2 $$ (2 div 2, 2 div 2) * Pauli_Z $$ (2 mod 2, 2 mod 2)"
      by (rule tensor_index_c) auto
    show ?thesis using a b by (simp add: Pauli_Z_def)
  qed
  show "qubit_op 0 Pauli_Z \<noteq> qubit_op 1 Pauli_Z" using e0 e1 by auto
  have "qubit_op 1 Pauli_Z *\<^sub>v shor_cw True = qubit_op 0 Pauli_Z *\<^sub>v shor_cw True"
    using qubit_op_Z_cw[of 1 True] by simp
  moreover have "qubit_op 0 Pauli_Z *\<^sub>v shor_cw True = shor_errors ! 19 *\<^sub>v shor_cw True"
    by (simp add: shor_errors_def nth_append)
  moreover have "\<langle>shor_errors ! 19 *\<^sub>v shor_cw True | shor_errors ! 19 *\<^sub>v shor_cw True\<rangle> = 1"
  proof -
    have v: "valid_label (shor_labels True ! 19)" by (rule shor_labels_valid) simp
    have d: "dim_vec (label_vec (shor_labels True ! 19)) = dim_vec (label_vec (shor_labels True ! 19))" ..
    have k: "shor_kappa ! 19 = 1" by (simp add: shor_kappa_def nth_append)
    have ac: "shor_scale * (cnj shor_scale * 8) = (cnj shor_scale * shor_scale) * 8" by (simp only: mult_ac)
    show ?thesis unfolding shor_errors_action[of 19 True, simplified] k
      by (simp only: No_Cloning.inner_prod_distrib_left[OF d] inner_prod_right_smult' label_vec_inner[OF v v] simp_thms(6) if_True
          mult_1_left) (simp only: ac shor_scale_sq, simp)
  qed
  ultimately show "\<langle>qubit_op 0 Pauli_Z *\<^sub>v shor_cw True | qubit_op 1 Pauli_Z *\<^sub>v shor_cw True\<rangle> = 1" by simp
qed

subsection \<open>Shor's theorem\<close>

lemma pauli_decomp:
  fixes U :: "complex Matrix.mat"
  assumes U: "U \<in> carrier_mat 2 2"
  shows "U = ((U $$ (0,0) + U $$ (1,1)) / 2) \<cdot>\<^sub>m 1\<^sub>m 2 + ((U $$ (0,1) + U $$ (1,0)) / 2) \<cdot>\<^sub>m Pauli_X
           + (-\<i> * (U $$ (0,1) - U $$ (1,0)) / 2) \<cdot>\<^sub>m Pauli_Y + ((U $$ (0,0) - U $$ (1,1)) / 2) \<cdot>\<^sub>m Pauli_Z"
    (is "U = ?R")
proof (rule eq_matI)
  fix i j assume "i < dim_row ?R" "j < dim_col ?R"
  hence "i < 2" "j < 2" by (simp_all add: Pauli_Z_def)
  hence "i = 0 \<or> i = 1" "j = 0 \<or> j = 1" by auto
  thus "U $$ (i,j) = ?R $$ (i,j)"
    by (elim disjE) (simp_all add: Pauli_X_def Pauli_Y_def Pauli_Z_def field_simps)
qed (use U in \<open>simp_all add: Pauli_Z_def\<close>)

lemma qubit_op_add:
  assumes A: "A \<in> carrier_mat 2 2" and B: "B \<in> carrier_mat 2 2"
  shows "qubit_op i (A + B) = qubit_op i A + qubit_op i B"
proof -
  have p: "0 < (2::nat) ^ i" "0 < (2::nat) ^ (8 - i)" by simp_all
  have IA: "Tensor.tensor_mat (1\<^sub>m (2^i)) A \<in> carrier_mat (2^i * 2) (2^i * 2)" using A by auto
  have IB: "Tensor.tensor_mat (1\<^sub>m (2^i)) B \<in> carrier_mat (2^i * 2) (2^i * 2)" using B by auto
  show ?thesis unfolding qubit_op_def
    using tensor_mat_add_right[OF one_carrier_mat A B p(1)] tensor_mat_add_left[OF IA IB one_carrier_mat _ p(2)] p
    by simp
qed

lemma qubit_op_smult:
  assumes A: "A \<in> carrier_mat 2 2"
  shows "qubit_op i (k \<cdot>\<^sub>m A) = k \<cdot>\<^sub>m qubit_op i A"
proof -
  have p: "0 < (2::nat) ^ i" "0 < (2::nat) ^ (8 - i)" by simp_all
  have IA: "Tensor.tensor_mat (1\<^sub>m (2^i)) A \<in> carrier_mat (2^i * 2) (2^i * 2)" using A by auto
  show ?thesis unfolding qubit_op_def
    using tensor_mat_smult_right[OF one_carrier_mat A p(1)] tensor_mat_smult_left[OF IA one_carrier_mat _ p(2)] p
    by simp
qed

lemma qubit_op_one:
  assumes i: "i < 9"
  shows "qubit_op i (1\<^sub>m 2) = 1\<^sub>m 512"
proof -
  have "Suc i + (8 - i) = 9" using i by simp
  hence "(2::nat) ^ Suc i * 2 ^ (8 - i) = 2 ^ 9" by (metis power_add)
  hence e: "(2::nat) ^ i * 2 * 2 ^ (8 - i) = 512" by (simp add: mult_ac)
  show ?thesis unfolding qubit_op_def tensor_mat_id e ..
qed

lemma shor_errors_nth:
  assumes i: "i < 9" and b: "b < 3"
  shows "shor_errors ! 0 = 1\<^sub>m 512" "shor_errors ! Suc i = qubit_op i Pauli_X"
    "shor_errors ! (10 + i) = qubit_op i Pauli_Y" "shor_errors ! (19 + b) = qubit_op (3 * b) Pauli_Z"
  using i b by (simp_all add: shor_errors_def nth_append)

text \<open>Shor: one CPTP recovery map $R$ corrects every single-qubit unitary error on every qubit,
for every state $\psi=a\ket{0_L}+b\ket{1_L}$ of the code space.\<close>

theorem shor_code_theorem:
  "\<exists>Rs. kraus_operators 512 512 Rs \<and>
     (\<forall>U i \<alpha> \<beta>. U \<in> carrier_mat 2 2 \<longrightarrow> unitary U \<longrightarrow> i < 9 \<longrightarrow>
        kraus_map_dim 512 Rs (qubit_op i U * (shor_state \<alpha> \<beta> \<oslash> shor_state \<alpha> \<beta>) * ((qubit_op i U)\<^sup>\<dagger>))
        = shor_state \<alpha> \<beta> \<oslash> shor_state \<alpha> \<beta>)"
proof (intro exI conjI allI impI)
  let ?Rs = "Day32_Recovery_Proposition.recovery_ops 512 shor_P shor_errors"
  show "kraus_operators 512 512 ?Rs" by (rule recovery_ops_kraus_operators[OF shor_recovery_setting])
  fix U :: "complex Matrix.mat" and i :: nat and \<alpha> \<beta> :: complex
  assume Uc: "U \<in> carrier_mat 2 2" and Uu: "unitary U" and i: "i < 9"
  define \<psi> where "\<psi> = shor_state \<alpha> \<beta>"
  have \<psi>d: "dim_vec \<psi> = 512" unfolding \<psi>_def by simp
  have \<psi>c: "\<psi> \<in> carrier_vec 512" by (rule carrier_vecI[OF \<psi>d])
  have \<psi>V: "shor_P *\<^sub>v \<psi> = \<psi>" unfolding \<psi>_def by (rule shor_P_fixes)
  define c0 where "c0 = (U $$ (0,0) + U $$ (1,1)) / 2"
  define c1 where "c1 = (U $$ (0,1) + U $$ (1,0)) / 2"
  define c2 where "c2 = -\<i> * (U $$ (0,1) - U $$ (1,0)) / 2"
  define c3 where "c3 = (U $$ (0,0) - U $$ (1,1)) / 2"
  have Ueq: "U = c0 \<cdot>\<^sub>m 1\<^sub>m 2 + c1 \<cdot>\<^sub>m Pauli_X + c2 \<cdot>\<^sub>m Pauli_Y + c3 \<cdot>\<^sub>m Pauli_Z"
    unfolding c0_def c1_def c2_def c3_def by (rule pauli_decomp[OF Uc])
  have norm: "(cmod c0)\<^sup>2 + (cmod c1)\<^sup>2 + (cmod c2)\<^sup>2 + (cmod c3)\<^sup>2 = 1"
    by (rule pauli_expansion_unitary[OF Uu Ueq])
  define b where "b = i div 3"
  have b: "b < 3" unfolding b_def using i by simp
  have b3: "3 * b < 9" using b by simp
  \<comment> \<open>The error, expanded in the Pauli basis, acting on the code space.\<close>
  have Xc: "qubit_op i Pauli_X \<in> carrier_mat 512 512" and Yc: "qubit_op i Pauli_Y \<in> carrier_mat 512 512"
    and Zc: "qubit_op i Pauli_Z \<in> carrier_mat 512 512"
    by (simp_all add: qubit_op_carrier i)
  have Qeq: "qubit_op i U = c0 \<cdot>\<^sub>m 1\<^sub>m 512 + c1 \<cdot>\<^sub>m qubit_op i Pauli_X + c2 \<cdot>\<^sub>m qubit_op i Pauli_Y
      + c3 \<cdot>\<^sub>m qubit_op i Pauli_Z"
  proof -
    have c: "c0 \<cdot>\<^sub>m 1\<^sub>m 2 \<in> carrier_mat 2 2" "c1 \<cdot>\<^sub>m Pauli_X \<in> carrier_mat 2 2"
      "c2 \<cdot>\<^sub>m Pauli_Y \<in> carrier_mat 2 2" "c3 \<cdot>\<^sub>m Pauli_Z \<in> carrier_mat 2 2" by simp_all
    show ?thesis unfolding Ueq
      by (simp only: qubit_op_add[OF add_carrier_mat[OF c(3)] c(4)] qubit_op_add[OF add_carrier_mat[OF c(2)] c(3)]
          qubit_op_add[OF c(1) c(2)] qubit_op_smult one_carrier_mat Pauli_X_carrier Pauli_Y_carrier
          Pauli_Z_carrier qubit_op_one[OF i])
  qed
  have act: "qubit_op i U *\<^sub>v \<psi> = c0 \<cdot>\<^sub>v \<psi> + c1 \<cdot>\<^sub>v (qubit_op i Pauli_X *\<^sub>v \<psi>)
      + c2 \<cdot>\<^sub>v (qubit_op i Pauli_Y *\<^sub>v \<psi>) + c3 \<cdot>\<^sub>v (qubit_op (3 * b) Pauli_Z *\<^sub>v \<psi>)"
  proof -
    have Z: "qubit_op i Pauli_Z *\<^sub>v \<psi> = qubit_op (3 * b) Pauli_Z *\<^sub>v \<psi>"
      unfolding \<psi>_def by (rule shor_Z_coincide[OF i b3]) (simp add: b_def)
    show ?thesis unfolding Qeq Z[symmetric] using Xc Yc Zc \<psi>c
      by (simp add: add_mult_distrib_mat_vec[of _ 512 512] smult_mat_mult_vec[OF carrier_matI[OF refl refl] carrier_vecI])
  qed
  \<comment> \<open>The same vector as a combination of the 22 correctable errors.\<close>
  define a where "a = (\<lambda>j. (if j = 0 then c0 else 0) + (if j = Suc i then c1 else 0)
      + (if j = 10 + i then c2 else 0) + (if j = 19 + b then c3 else 0))"
  define \<phi> where "\<phi> = vec_sum 512 {j. j < length shor_errors} (\<lambda>j. a j \<cdot>\<^sub>v (shor_errors ! j *\<^sub>v \<psi>))"
  have \<phi>_eq: "\<phi> = qubit_op i U *\<^sub>v \<psi>"
  proof (rule eq_vecI)
    show "dim_vec \<phi> = dim_vec (qubit_op i U *\<^sub>v \<psi>)" unfolding \<phi>_def using qubit_op_carrier[OF Uc i] by simp
    fix k assume "k < dim_vec (qubit_op i U *\<^sub>v \<psi>)"
    hence k: "k < 512" using qubit_op_carrier[OF Uc i] by simp
    let ?w = "\<lambda>j. (shor_errors ! j *\<^sub>v \<psi>) $ k"
    have wd: "\<And>j. j < 22 \<Longrightarrow> dim_vec (shor_errors ! j *\<^sub>v \<psi>) = 512"
      using carrier_matD(1)[OF shor_errors_carrier] by simp
    have "\<phi> $ k = (\<Sum>j \<in> {j. j < 22}. (a j \<cdot>\<^sub>v (shor_errors ! j *\<^sub>v \<psi>)) $ k)"
      unfolding \<phi>_def using k by simp
    also have "\<dots> = (\<Sum>j \<in> {j. j < 22}. a j * ?w j)"
      by (rule sum.cong) (use k wd in auto)
    also have "\<dots> = (\<Sum>j \<in> {j. j < 22}. (if j = 0 then c0 * ?w 0 else 0) + (if j = Suc i then c1 * ?w (Suc i) else 0)
        + (if j = 10 + i then c2 * ?w (10 + i) else 0) + (if j = 19 + b then c3 * ?w (19 + b) else 0))"
      by (rule sum.cong) (auto simp: a_def distrib_right)
    also have "\<dots> = c0 * ?w 0 + c1 * ?w (Suc i) + c2 * ?w (10 + i) + c3 * ?w (19 + b)"
      using i b by (simp add: sum.distrib)
    also have "\<dots> = (qubit_op i U *\<^sub>v \<psi>) $ k"
      unfolding act shor_errors_nth[OF i b] using k Xc Yc \<psi>c qubit_op_carrier[OF Pauli_Z_carrier b3]
      by simp
    finally show "\<phi> $ k = (qubit_op i U *\<^sub>v \<psi>) $ k" .
  qed
  have weights: "(\<Sum>j < length shor_errors. (cmod (a j))\<^sup>2) = 1"
  proof -
    have "\<And>j. (cmod (a j))\<^sup>2 = (if j = 0 then (cmod c0)\<^sup>2 else 0) + (if j = Suc i then (cmod c1)\<^sup>2 else 0)
        + (if j = 10 + i then (cmod c2)\<^sup>2 else 0) + (if j = 19 + b then (cmod c3)\<^sup>2 else 0)"
      using i b by (auto simp: a_def)
    hence "(\<Sum>j < length shor_errors. (cmod (a j))\<^sup>2) = (cmod c0)\<^sup>2 + (cmod c1)\<^sup>2 + (cmod c2)\<^sup>2 + (cmod c3)\<^sup>2"
      using i b by (simp add: sum.distrib)
    thus ?thesis using norm by simp
  qed
  have "kraus_map_dim 512 ?Rs (\<phi> \<oslash> \<phi>) = complex_of_real (\<Sum>j < length shor_errors. (cmod (a j))\<^sup>2) \<cdot>\<^sub>m (\<psi> \<oslash> \<psi>)"
    unfolding \<phi>_def by (rule recovery_linear_combination[OF shor_recovery_setting \<psi>d \<psi>V])
  also have "\<dots> = \<psi> \<oslash> \<psi>" unfolding weights by (rule eq_matI) simp_all
  finally have R: "kraus_map_dim 512 ?Rs (\<phi> \<oslash> \<phi>) = \<psi> \<oslash> \<psi>" .
  have "qubit_op i U * (\<psi> \<oslash> \<psi>) * ((qubit_op i U)\<^sup>\<dagger>) = \<phi> \<oslash> \<phi>"
    unfolding \<phi>_eq by (rule conj_outer_prod[OF qubit_op_carrier[OF Uc i] \<psi>d])
  thus "kraus_map_dim 512 ?Rs (qubit_op i U * (shor_state \<alpha> \<beta> \<oslash> shor_state \<alpha> \<beta>) * ((qubit_op i U)\<^sup>\<dagger>))
        = shor_state \<alpha> \<beta> \<oslash> shor_state \<alpha> \<beta>" using R unfolding \<psi>_def by simp
qed

end

theory Day30_BitFlip_Code
  imports QC_Prelims Quantum_Channels
begin

section \<open>Day 30: the three-qubit bit-flip code and its recovery map (D30-3, D30-4)\<close>

text \<open>The syndrome projections $P_0=\ketbra{000}{000}+\ketbra{111}{111}$, \dots, as diagonal
$0/1$ matrices ($\ket{abc}\leftrightarrow e_{4a+2b+c}$), and the single flips
$X\otimes I\otimes I$, $I\otimes X\otimes I$, $I\otimes I\otimes X$ as permutation matrices.\<close>

definition syndrome_proj :: "nat set \<Rightarrow> complex Matrix.mat" where
  "syndrome_proj K = Matrix.mat 8 8 (\<lambda>(i,j). if i = j \<and> i \<in> K then 1 else 0)"

abbreviation "P\<^sub>0 \<equiv> syndrome_proj {0, 7}"
abbreviation "P\<^sub>1 \<equiv> syndrome_proj {4, 3}"
abbreviation "P\<^sub>2 \<equiv> syndrome_proj {2, 5}"
abbreviation "P\<^sub>3 \<equiv> syndrome_proj {1, 6}"

definition flip_bit_mat :: "nat \<Rightarrow> complex Matrix.mat" where
  "flip_bit_mat b = Matrix.mat 8 8 (\<lambda>(i,j). if j = (if i div 2^b mod 2 = 0 then i + 2^b else i - 2^b) then 1 else 0)"

abbreviation "X\<^sub>1 \<equiv> flip_bit_mat 2"
abbreviation "X\<^sub>2 \<equiv> flip_bit_mat 1"
abbreviation "X\<^sub>3 \<equiv> flip_bit_mat 0"

text \<open>The code space is $\spn\{\ket{000},\ket{111}\}$.  A flip of qubit $j$ moves it into the span of
the two words with bit $j$ flipped, so the syndrome projections are the projections onto
\[ P_0:\ \{\ket{000},\ket{111}\},\quad P_1:\ \{\ket{100},\ket{011}\},\quad
   P_2:\ \{\ket{010},\ket{101}\},\quad P_3:\ \{\ket{001},\ket{110}\}, \]
and $X_j$ flips qubit $j$ (e.g.\ $X_1=X\otimes I\otimes I$).  Recovery measures
$P_0,\dots,P_3$ and applies $X_j$ after outcome $j$.\<close>

lemma syndrome_proj_carrier [simp]: "syndrome_proj K \<in> carrier_mat 8 8"
  by (simp add: syndrome_proj_def)

lemma flip_bit_mat_carrier [simp]: "flip_bit_mat b \<in> carrier_mat 8 8"
  by (simp add: flip_bit_mat_def)

lemma syndrome_proj_dims [simp]: "dim_row (syndrome_proj K) = 8" "dim_col (syndrome_proj K) = 8"
  by (simp_all add: syndrome_proj_def)

lemma flip_bit_mat_dims [simp]: "dim_row (flip_bit_mat b) = 8" "dim_col (flip_bit_mat b) = 8"
  by (simp_all add: flip_bit_mat_def)

lemma encode_mat_dims [simp]: "dim_row encode_mat = 8" "dim_col encode_mat = 2"
  using carrier_matD[OF encode_mat_carrier] by simp_all

lemma flip_proj_carrier [simp]: "flip_bit_mat b * syndrome_proj K \<in> carrier_mat 8 8"
  by (rule mult_carrier_mat[OF flip_bit_mat_carrier syndrome_proj_carrier])

lemma b3_cases: "b < (3::nat) \<Longrightarrow> b = 0 \<or> b = 1 \<or> b = 2" by auto

(* Entry of an 8x8 product as an abstract sum: unrolling the sum and splitting every if does not terminate. *)

lemma mat_mult_entry_8:
  fixes A B :: "complex Matrix.mat"
  assumes "A \<in> carrier_mat 8 8" "B \<in> carrier_mat 8 8" "i < 8" "j < 8"
  shows "(A * B) $$ (i,j) = (\<Sum>k<8. A $$ (i,k) * B $$ (k,j))"
  using assms by (simp add: scalar_prod_def atLeast0LessThan)

lemma syndrome_proj_index:
  assumes "i < 8" "j < 8"
  shows "syndrome_proj K $$ (i,j) = (if i = j \<and> i \<in> K then 1 else 0)"
  using assms by (simp add: syndrome_proj_def)

lemma syndrome_proj_two:
  assumes a: "a < 8" and b: "b < 8" and ab: "a \<noteq> b"
  shows "syndrome_proj {a, b} = unit_vec 8 a \<oslash> unit_vec 8 a + unit_vec 8 b \<oslash> unit_vec 8 b"
proof (rule eq_matI)
  have ca: "unit_vec 8 a \<oslash> unit_vec 8 a \<in> carrier_mat 8 8" and cb: "unit_vec 8 b \<oslash> unit_vec 8 b \<in> carrier_mat 8 8"
    by (rule outer_prod_carrier; simp)+
  fix i j assume "i < dim_row (unit_vec 8 a \<oslash> unit_vec 8 a + unit_vec 8 b \<oslash> unit_vec 8 b)"
             "j < dim_col (unit_vec 8 a \<oslash> unit_vec 8 a + unit_vec 8 b \<oslash> unit_vec 8 b)"
  hence i: "i < 8" and j: "j < 8" using carrier_matD[OF ca] carrier_matD[OF cb] by auto
  have "(unit_vec 8 a \<oslash> unit_vec 8 a + unit_vec 8 b \<oslash> unit_vec 8 b) $$ (i,j)
        = (unit_vec 8 a \<oslash> unit_vec 8 a) $$ (i,j) + (unit_vec 8 b \<oslash> unit_vec 8 b) $$ (i,j)"
    using i j carrier_matD[OF cb] by simp
  also have "\<dots> = unit_vec 8 a $ i * cnj (unit_vec 8 a $ j) + unit_vec 8 b $ i * cnj (unit_vec 8 b $ j)"
    using i j by (simp add: outer_prod_index)
  also have "\<dots> = syndrome_proj {a, b} $$ (i,j)"
    using i j a b ab by (auto simp: syndrome_proj_def)
  finally show "syndrome_proj {a, b} $$ (i,j) = (unit_vec 8 a \<oslash> unit_vec 8 a + unit_vec 8 b \<oslash> unit_vec 8 b) $$ (i,j)" ..
qed (use carrier_matD[OF outer_prod_carrier[of "unit_vec 8 a" 8 "unit_vec 8 a" 8]]
          carrier_matD[OF outer_prod_carrier[of "unit_vec 8 b" 8 "unit_vec 8 b" 8]]
     in \<open>auto simp: syndrome_proj_def\<close>)

lemma syndrome_proj_as_outer:
  "P\<^sub>0 = unit_vec 8 0 \<oslash> unit_vec 8 0 + unit_vec 8 7 \<oslash> unit_vec 8 7"
  "P\<^sub>1 = unit_vec 8 4 \<oslash> unit_vec 8 4 + unit_vec 8 3 \<oslash> unit_vec 8 3"
  "P\<^sub>2 = unit_vec 8 2 \<oslash> unit_vec 8 2 + unit_vec 8 5 \<oslash> unit_vec 8 5"
  "P\<^sub>3 = unit_vec 8 1 \<oslash> unit_vec 8 1 + unit_vec 8 6 \<oslash> unit_vec 8 6"
  by (rule syndrome_proj_two; simp)+

text \<open>The flips are the notes' tensors.\<close>

lemma tensor3_index:
  fixes A B C :: "complex Matrix.mat"
  assumes A: "A \<in> carrier_mat 2 2" and B: "B \<in> carrier_mat 2 2" and C: "C \<in> carrier_mat 2 2"
    and i: "i < 8" and j: "j < 8"
  shows "Tensor.tensor_mat (Tensor.tensor_mat A B) C $$ (i,j)
         = A $$ (i div 4, j div 4) * B $$ (i div 2 mod 2, j div 2 mod 2) * C $$ (i mod 2, j mod 2)"
proof -
  have dA: "dim_row A = 2" "dim_col A = 2" and dB: "dim_row B = 2" "dim_col B = 2"
    and dC: "dim_row C = 2" "dim_col C = 2" using A B C by auto
  have dAB: "dim_row (Tensor.tensor_mat A B) = 4" "dim_col (Tensor.tensor_mat A B) = 4"
    by (simp_all add: dA dB)
  have e1: "Tensor.tensor_mat (Tensor.tensor_mat A B) C $$ (i,j)
        = Tensor.tensor_mat A B $$ (i div 2, j div 2) * C $$ (i mod 2, j mod 2)"
    by (rule index_tensor_mat[OF dAB(1) dAB(2) dC(1) dC(2)]) (use i j in simp_all)
  have e2: "Tensor.tensor_mat A B $$ (i div 2, j div 2)
        = A $$ (i div 2 div 2, j div 2 div 2) * B $$ (i div 2 mod 2, j div 2 mod 2)"
    by (rule index_tensor_mat[OF dA(1) dA(2) dB(1) dB(2)]) (use i j in simp_all)
  show ?thesis unfolding e1 e2 by (simp add: div_mult2_eq[symmetric])
qed

lemma flips_as_tensors:
  "X\<^sub>1 = Tensor.tensor_mat (Tensor.tensor_mat Pauli_X (1\<^sub>m 2)) (1\<^sub>m 2)"
  "X\<^sub>2 = Tensor.tensor_mat (Tensor.tensor_mat (1\<^sub>m 2) Pauli_X) (1\<^sub>m 2)"
  "X\<^sub>3 = Tensor.tensor_mat (Tensor.tensor_mat (1\<^sub>m 2) (1\<^sub>m 2)) Pauli_X"
proof -
  have c1: "Pauli_X \<in> carrier_mat 2 2" and c2: "(1\<^sub>m 2 :: complex Matrix.mat) \<in> carrier_mat 2 2" by simp_all
  have Xb: "\<And>b i j. i < 8 \<Longrightarrow> j < 8 \<Longrightarrow>
      flip_bit_mat b $$ (i,j) = (if j = (if i div 2^b mod 2 = 0 then i + 2^b else i - 2^b) then 1 else 0)"
    by (simp add: flip_bit_mat_def)
  show "X\<^sub>1 = Tensor.tensor_mat (Tensor.tensor_mat Pauli_X (1\<^sub>m 2)) (1\<^sub>m 2)"
  proof (rule eq_matI)
    fix i j assume "i < dim_row (Tensor.tensor_mat (Tensor.tensor_mat Pauli_X (1\<^sub>m 2)) (1\<^sub>m 2))" and "j < dim_col (Tensor.tensor_mat (Tensor.tensor_mat Pauli_X (1\<^sub>m 2)) (1\<^sub>m 2))"
    hence i: "i < 8" and j: "j < 8" by (simp_all add: Pauli_X_def)
    show "X\<^sub>1 $$ (i,j) = Tensor.tensor_mat (Tensor.tensor_mat Pauli_X (1\<^sub>m 2)) (1\<^sub>m 2) $$ (i,j)"
      unfolding tensor3_index[OF c1 c2 c2 i j] Xb[OF i j] using idx8[OF i] idx8[OF j]
      by (elim disjE) (simp_all add: Pauli_X_def)
  qed (simp_all add: Pauli_X_def)
  show "X\<^sub>2 = Tensor.tensor_mat (Tensor.tensor_mat (1\<^sub>m 2) Pauli_X) (1\<^sub>m 2)"
  proof (rule eq_matI)
    fix i j assume "i < dim_row (Tensor.tensor_mat (Tensor.tensor_mat (1\<^sub>m 2) Pauli_X) (1\<^sub>m 2))" and "j < dim_col (Tensor.tensor_mat (Tensor.tensor_mat (1\<^sub>m 2) Pauli_X) (1\<^sub>m 2))"
    hence i: "i < 8" and j: "j < 8" by (simp_all add: Pauli_X_def)
    show "X\<^sub>2 $$ (i,j) = Tensor.tensor_mat (Tensor.tensor_mat (1\<^sub>m 2) Pauli_X) (1\<^sub>m 2) $$ (i,j)"
      unfolding tensor3_index[OF c2 c1 c2 i j] Xb[OF i j] using idx8[OF i] idx8[OF j]
      by (elim disjE) (simp_all add: Pauli_X_def)
  qed (simp_all add: Pauli_X_def)
  show "X\<^sub>3 = Tensor.tensor_mat (Tensor.tensor_mat (1\<^sub>m 2) (1\<^sub>m 2)) Pauli_X"
  proof (rule eq_matI)
    fix i j assume "i < dim_row (Tensor.tensor_mat (Tensor.tensor_mat (1\<^sub>m 2) (1\<^sub>m 2)) Pauli_X)" and "j < dim_col (Tensor.tensor_mat (Tensor.tensor_mat (1\<^sub>m 2) (1\<^sub>m 2)) Pauli_X)"
    hence i: "i < 8" and j: "j < 8" by (simp_all add: Pauli_X_def)
    show "X\<^sub>3 $$ (i,j) = Tensor.tensor_mat (Tensor.tensor_mat (1\<^sub>m 2) (1\<^sub>m 2)) Pauli_X $$ (i,j)"
      unfolding tensor3_index[OF c2 c2 c1 i j] Xb[OF i j] using idx8[OF i] idx8[OF j]
      by (elim disjE) (simp_all add: Pauli_X_def)
  qed (simp_all add: Pauli_X_def)
qed

lemma flip_bit_mat_mult_vec:
  assumes b: "b < 3" and vd: "dim_vec v = 8" and i: "i < 8"
  shows "(flip_bit_mat b *\<^sub>v v) $ i = v $ (if i div 2^b mod 2 = 0 then i + 2^b else i - 2^b)"
proof -
  let ?t = "if i div 2^b mod 2 = 0 then i + 2^b else i - 2^b"
  have t8: "?t < 8" using b3_cases[OF b] idx8[OF i] by (elim disjE) simp_all
  have "(flip_bit_mat b *\<^sub>v v) $ i = (\<Sum>j = 0..<8. (if j = ?t then 1 else 0) * v $ j)"
    using i vd by (simp add: scalar_prod_def flip_bit_mat_def)
  also have "\<dots> = (\<Sum>j = 0..<8. if j = ?t then v $ j else 0)" by (intro sum.cong refl) simp
  also have "\<dots> = (if ?t \<in> {0..<8} then v $ ?t else 0)" by (simp only: sum.delta[OF finite_atLeastLessThan])
  also have "\<dots> = v $ ?t" using t8 by (simp only: atLeastLessThan_iff if_True le0 simp_thms)
  finally show ?thesis .
qed

lemma syndrome_proj_mult_vec:
  assumes vd: "dim_vec v = 8" and i: "i < 8"
  shows "(syndrome_proj K *\<^sub>v v) $ i = (if i \<in> K then v $ i else 0)"
proof -
  have "(syndrome_proj K *\<^sub>v v) $ i = (\<Sum>j = 0..<8. (if i = j \<and> i \<in> K then 1 else 0) * v $ j)"
    using i vd by (simp add: scalar_prod_def syndrome_proj_def)
  also have "\<dots> = (\<Sum>j = 0..<8. if j = i then (if i \<in> K then v $ i else 0) else 0)"
    by (intro sum.cong refl) auto
  also have "\<dots> = (if i \<in> {0..<8} then (if i \<in> K then v $ i else 0) else 0)"
    by (simp only: sum.delta[OF finite_atLeastLessThan])
  also have "\<dots> = (if i \<in> K then v $ i else 0)" using i by (simp only: atLeastLessThan_iff if_True le0 simp_thms)
  finally show ?thesis .
qed

lemma syndrome_proj_hermitian: "(syndrome_proj K)\<^sup>\<dagger> = syndrome_proj K"
  by (rule eq_matI) (auto simp: syndrome_proj_def dagger_def)

lemma syndrome_proj_idem: "syndrome_proj K * syndrome_proj K = syndrome_proj K"
proof (rule eq_matI)
  fix i j assume "i < dim_row (syndrome_proj K)" "j < dim_col (syndrome_proj K)"
  hence i: "i < 8" and j: "j < 8" by simp_all
  have "(syndrome_proj K * syndrome_proj K) $$ (i,j) = (\<Sum>k<8. syndrome_proj K $$ (i,k) * syndrome_proj K $$ (k,j))"
    by (rule mat_mult_entry_8[OF syndrome_proj_carrier syndrome_proj_carrier i j])
  also have "\<dots> = (\<Sum>k<8. if k = i then (if i = j \<and> i \<in> K then 1 else 0) else 0)"
  proof (intro sum.cong refl)
    fix k :: nat assume "k \<in> {..<8}"
    hence k: "k < 8" by simp
    show "syndrome_proj K $$ (i,k) * syndrome_proj K $$ (k,j) = (if k = i then (if i = j \<and> i \<in> K then 1 else 0) else 0)"
      unfolding syndrome_proj_index[OF i k] syndrome_proj_index[OF k j] by (cases "k = i") auto
  qed
  also have "\<dots> = (if i \<in> {..<8} then (if i = j \<and> i \<in> K then 1 else 0) else 0)"
    by (simp only: sum.delta[OF finite_lessThan])
  also have "\<dots> = (if i = j \<and> i \<in> K then 1 else 0)" using i by (simp only: lessThan_iff if_True)
  finally show "(syndrome_proj K * syndrome_proj K) $$ (i,j) = syndrome_proj K $$ (i,j)"
    unfolding syndrome_proj_index[OF i j] .
qed simp_all

lemma syndrome_proj_sum:
  "P\<^sub>0 + P\<^sub>1 + P\<^sub>2 + P\<^sub>3 = 1\<^sub>m 8"
proof (rule eq_matI)
  fix i j assume "i < dim_row (1\<^sub>m 8 :: complex Matrix.mat)" "j < dim_col (1\<^sub>m 8 :: complex Matrix.mat)"
  hence i: "i < 8" and j: "j < 8" by simp_all
  show "(P\<^sub>0 + P\<^sub>1 + P\<^sub>2 + P\<^sub>3) $$ (i,j) = (1\<^sub>m 8 :: complex Matrix.mat) $$ (i,j)"
    using idx8[OF i] idx8[OF j] by (elim disjE) (simp_all add: syndrome_proj_def)
qed (simp_all add: syndrome_proj_def)

text \<open>The flip \<open>flip_bit_mat b\<close> permutes the basis by the involution \<open>flip_tgt b\<close>.\<close>

definition flip_tgt :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "flip_tgt b i = (if i div 2^b mod 2 = 0 then i + 2^b else i - 2^b)"

lemma flip_tgt_lt:
  assumes b: "b < 3" and i: "i < 8" shows "flip_tgt b i < 8"
  unfolding flip_tgt_def using b3_cases[OF b] idx8[OF i] by (elim disjE) simp_all

lemma flip_tgt_invol:
  assumes b: "b < 3" and i: "i < 8" shows "flip_tgt b (flip_tgt b i) = i"
  unfolding flip_tgt_def using b3_cases[OF b] idx8[OF i] by (elim disjE) simp_all

lemma flip_bit_mat_index:
  assumes i: "i < 8" and j: "j < 8"
  shows "flip_bit_mat b $$ (i,j) = (if j = flip_tgt b i then 1 else 0)"
  using i j by (simp add: flip_bit_mat_def flip_tgt_def)

lemma flip_tgt_iff:
  assumes b: "b < 3" and i: "i < 8" and j: "j < 8"
  shows "i = flip_tgt b j \<longleftrightarrow> j = flip_tgt b i"
proof
  assume "i = flip_tgt b j"
  hence "flip_tgt b i = flip_tgt b (flip_tgt b j)" by simp
  thus "j = flip_tgt b i" using flip_tgt_invol[OF b j] by simp
next
  assume "j = flip_tgt b i"
  hence "flip_tgt b j = flip_tgt b (flip_tgt b i)" by simp
  thus "i = flip_tgt b j" using flip_tgt_invol[OF b i] by simp
qed

lemma flip_bit_mat_hermitian:
  assumes b: "b < 3"
  shows "(flip_bit_mat b)\<^sup>\<dagger> = flip_bit_mat b"
proof (rule eq_matI)
  fix i j assume "i < dim_row (flip_bit_mat b)" "j < dim_col (flip_bit_mat b)"
  hence i: "i < 8" and j: "j < 8" by simp_all
  have "(flip_bit_mat b)\<^sup>\<dagger> $$ (i,j) = cnj (flip_bit_mat b $$ (j,i))" using i j by (simp add: dagger_def)
  also have "\<dots> = (if i = flip_tgt b j then 1 else 0)" unfolding flip_bit_mat_index[OF j i] by simp
  also have "\<dots> = (if j = flip_tgt b i then 1 else 0)" unfolding flip_tgt_iff[OF b i j] ..
  also have "\<dots> = flip_bit_mat b $$ (i,j)" by (rule flip_bit_mat_index[OF i j, symmetric])
  finally show "(flip_bit_mat b)\<^sup>\<dagger> $$ (i,j) = flip_bit_mat b $$ (i,j)" .
qed (simp_all add: dagger_def)

lemma flip_bit_mat_squared:
  assumes b: "b < 3"
  shows "flip_bit_mat b * flip_bit_mat b = 1\<^sub>m 8"
proof (rule eq_matI)
  fix i j assume "i < dim_row (1\<^sub>m 8 :: complex Matrix.mat)" "j < dim_col (1\<^sub>m 8 :: complex Matrix.mat)"
  hence i: "i < 8" and j: "j < 8" by simp_all
  have "(flip_bit_mat b * flip_bit_mat b) $$ (i,j) = (\<Sum>k<8. flip_bit_mat b $$ (i,k) * flip_bit_mat b $$ (k,j))"
    by (rule mat_mult_entry_8[OF flip_bit_mat_carrier flip_bit_mat_carrier i j])
  also have "\<dots> = (\<Sum>k<8. if k = flip_tgt b i then (if j = flip_tgt b (flip_tgt b i) then 1 else 0) else 0)"
  proof (intro sum.cong refl)
    fix k :: nat assume "k \<in> {..<8}"
    hence k: "k < 8" by simp
    show "flip_bit_mat b $$ (i,k) * flip_bit_mat b $$ (k,j)
          = (if k = flip_tgt b i then (if j = flip_tgt b (flip_tgt b i) then 1 else 0) else 0)"
      unfolding flip_bit_mat_index[OF i k] flip_bit_mat_index[OF k j] by (cases "k = flip_tgt b i") auto
  qed
  also have "\<dots> = (if flip_tgt b i \<in> {..<8} then (if j = flip_tgt b (flip_tgt b i) then 1 else 0) else 0)"
    by (simp only: sum.delta[OF finite_lessThan])
  also have "\<dots> = (if j = i then 1 else 0)"
    using flip_tgt_lt[OF b i] flip_tgt_invol[OF b i] by (simp only: lessThan_iff if_True)
  finally show "(flip_bit_mat b * flip_bit_mat b) $$ (i,j) = (1\<^sub>m 8 :: complex Matrix.mat) $$ (i,j)"
    using i j by auto
qed simp_all

text \<open>Kraus operators of the recovery map $R(Y)=P_0YP_0+\sum_{k}X_kP_kYP_kX_k$.\<close>

definition bitflip_recovery_ops :: "complex Matrix.mat list" where
  "bitflip_recovery_ops = [P\<^sub>0, X\<^sub>1 * P\<^sub>1, X\<^sub>2 * P\<^sub>2, X\<^sub>3 * P\<^sub>3]"

definition bitflip_recovery_map :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "bitflip_recovery_map = kraus_map_dim 8 bitflip_recovery_ops"

lemma flip_proj_dag_mult:
  assumes b: "b < 3"
  shows "((flip_bit_mat b * syndrome_proj K)\<^sup>\<dagger>) * (flip_bit_mat b * syndrome_proj K) = syndrome_proj K"
proof -
  let ?X = "flip_bit_mat b" and ?P = "syndrome_proj K"
  have Xc: "?X \<in> carrier_mat 8 8" and Pc: "?P \<in> carrier_mat 8 8" by simp_all
  have dag: "(?X * ?P)\<^sup>\<dagger> = ?P * ?X"
  proof -
    have "(?X * ?P)\<^sup>\<dagger> = (?P\<^sup>\<dagger>) * (?X\<^sup>\<dagger>)" by (rule dagger_of_prod) simp
    thus ?thesis by (simp add: syndrome_proj_hermitian flip_bit_mat_hermitian[OF b])
  qed
  have "((?X * ?P)\<^sup>\<dagger>) * (?X * ?P) = (?P * ?X) * (?X * ?P)" by (simp only: dag)
  also have "\<dots> = ?P * ?X * ?X * ?P" by (rule assoc_mult_mat[OF mult_carrier_mat[OF Pc Xc] Xc Pc, symmetric])
  also have "\<dots> = ?P * (?X * ?X) * ?P" by (simp only: assoc_mult_mat[OF Pc Xc Xc])
  also have "\<dots> = ?P * ?P" by (simp only: flip_bit_mat_squared[OF b] right_mult_one_mat[OF Pc])
  also have "\<dots> = ?P" by (rule syndrome_proj_idem)
  finally show ?thesis .
qed

theorem bitflip_recovery_ops_kraus: "kraus_operators 8 8 bitflip_recovery_ops"
proof -
  have c: "\<forall>W \<in> set bitflip_recovery_ops. W \<in> carrier_mat 8 8" by (auto simp: bitflip_recovery_ops_def)
  have "foldr (\<lambda>W acc. (W\<^sup>\<dagger>) * W + acc) bitflip_recovery_ops (0\<^sub>m 8 8)
        = P\<^sub>0 + (P\<^sub>1 + (P\<^sub>2 + (P\<^sub>3 + 0\<^sub>m 8 8)))"
    by (simp add: bitflip_recovery_ops_def flip_proj_dag_mult syndrome_proj_hermitian syndrome_proj_idem)
  also have "\<dots> = P\<^sub>0 + P\<^sub>1 + P\<^sub>2 + P\<^sub>3"
    by (rule eq_matI) (simp_all add: syndrome_proj_def add.assoc)
  also have "\<dots> = 1\<^sub>m 8" by (rule syndrome_proj_sum)
  finally show ?thesis using c by (simp add: kraus_operators_def)
qed

corollary bitflip_recovery_map_CPTP: "bitflip_recovery_map \<in> CPTP 8 8"
  unfolding bitflip_recovery_map_def by (rule kraus_is_cptp[OF bitflip_recovery_ops_kraus]) simp_all

text \<open>The encoded state $\psi=a\ket{000}+b\ket{111}$ and its single-flip corruptions.\<close>

lemma encode_mat_mult_vec:
  assumes xd: "dim_vec x = 2" and i: "i < 8"
  shows "(encode_mat *\<^sub>v x) $ i = (if i = 0 then x $ 0 else if i = 7 then x $ 1 else 0)"
  using i xd by (simp add: scalar_prod_def encode_mat_def numeral_2_eq_2)

lemma encode_mat_dim [simp]: "dim_vec (encode_mat *\<^sub>v x) = 8" by simp

lemma recovery_kraus_term:
  fixes \<phi> :: "complex Matrix.vec"
  assumes \<phi>d: "dim_vec \<phi> = 8"
  shows "bitflip_recovery_map (\<phi> \<oslash> \<phi>) =
     (P\<^sub>0 *\<^sub>v \<phi>) \<oslash> (P\<^sub>0 *\<^sub>v \<phi>) + ((X\<^sub>1 *\<^sub>v (P\<^sub>1 *\<^sub>v \<phi>)) \<oslash> (X\<^sub>1 *\<^sub>v (P\<^sub>1 *\<^sub>v \<phi>))
     + ((X\<^sub>2 *\<^sub>v (P\<^sub>2 *\<^sub>v \<phi>)) \<oslash> (X\<^sub>2 *\<^sub>v (P\<^sub>2 *\<^sub>v \<phi>))
     + ((X\<^sub>3 *\<^sub>v (P\<^sub>3 *\<^sub>v \<phi>)) \<oslash> (X\<^sub>3 *\<^sub>v (P\<^sub>3 *\<^sub>v \<phi>)) + 0\<^sub>m 8 8)))"
proof -
  have XP: "\<And>b K. flip_bit_mat b * syndrome_proj K \<in> carrier_mat 8 8" by (rule flip_proj_carrier)
  have assoc: "\<And>b K. (flip_bit_mat b * syndrome_proj K) *\<^sub>v \<phi> = flip_bit_mat b *\<^sub>v (syndrome_proj K *\<^sub>v \<phi>)"
    by (rule assoc_mult_mat_vec[OF flip_bit_mat_carrier syndrome_proj_carrier carrier_vecI[OF \<phi>d]])
  show ?thesis
    unfolding bitflip_recovery_map_def bitflip_recovery_ops_def
    by (simp only: kraus_map_dim_Cons kraus_map_dim_Nil
          conj_outer_prod[OF syndrome_proj_carrier \<phi>d] conj_outer_prod[OF XP \<phi>d] assoc)
qed

theorem bit_flip_code_recovery:
  fixes x :: "complex Matrix.vec"
  assumes xd: "dim_vec x = 2"
  defines "\<psi> \<equiv> encode_mat *\<^sub>v x"
  shows "bitflip_recovery_map (\<psi> \<oslash> \<psi>) = \<psi> \<oslash> \<psi>"
    and "bitflip_recovery_map ((X\<^sub>1 *\<^sub>v \<psi>) \<oslash> (X\<^sub>1 *\<^sub>v \<psi>)) = \<psi> \<oslash> \<psi>"
    and "bitflip_recovery_map ((X\<^sub>2 *\<^sub>v \<psi>) \<oslash> (X\<^sub>2 *\<^sub>v \<psi>)) = \<psi> \<oslash> \<psi>"
    and "bitflip_recovery_map ((X\<^sub>3 *\<^sub>v \<psi>) \<oslash> (X\<^sub>3 *\<^sub>v \<psi>)) = \<psi> \<oslash> \<psi>"
proof -
  have \<psi>d: "dim_vec \<psi> = 8" by (simp add: \<psi>_def)
  have \<psi>i: "\<And>i. i < 8 \<Longrightarrow> \<psi> $ i = (if i = 0 then x $ 0 else if i = 7 then x $ 1 else 0)"
    unfolding \<psi>_def by (rule encode_mat_mult_vec[OF xd])
  \<comment> \<open>the corrupted states\<close>
  have lt2: "(2::nat) < 3" and lt1: "(1::nat) < 3" and lt0: "(0::nat) < 3" by simp_all
  have X1\<psi>: "\<And>i :: nat. i < 8 \<Longrightarrow> (X\<^sub>1 *\<^sub>v \<psi>) $ i = (if i = 4 then x $ 0 else if i = 3 then x $ 1 else 0)"
  proof -
    fix i :: nat assume i: "i < 8"
    show "(X\<^sub>1 *\<^sub>v \<psi>) $ i = (if i = 4 then x $ 0 else if i = 3 then x $ 1 else 0)"
      unfolding flip_bit_mat_mult_vec[OF lt2 \<psi>d i] using idx8[OF i] by (elim disjE) (simp_all add: \<psi>i)
  qed
  have X2\<psi>: "\<And>i :: nat. i < 8 \<Longrightarrow> (X\<^sub>2 *\<^sub>v \<psi>) $ i = (if i = 2 then x $ 0 else if i = 5 then x $ 1 else 0)"
  proof -
    fix i :: nat assume i: "i < 8"
    show "(X\<^sub>2 *\<^sub>v \<psi>) $ i = (if i = 2 then x $ 0 else if i = 5 then x $ 1 else 0)"
      unfolding flip_bit_mat_mult_vec[OF lt1 \<psi>d i] using idx8[OF i] by (elim disjE) (simp_all add: \<psi>i)
  qed
  have X3\<psi>: "\<And>i :: nat. i < 8 \<Longrightarrow> (X\<^sub>3 *\<^sub>v \<psi>) $ i = (if i = 1 then x $ 0 else if i = 6 then x $ 1 else 0)"
  proof -
    fix i :: nat assume i: "i < 8"
    show "(X\<^sub>3 *\<^sub>v \<psi>) $ i = (if i = 1 then x $ 0 else if i = 6 then x $ 1 else 0)"
      unfolding flip_bit_mat_mult_vec[OF lt0 \<psi>d i] using idx8[OF i] by (elim disjE) (simp_all add: \<psi>i)
  qed
  have Xd: "\<And>b. dim_vec (flip_bit_mat b *\<^sub>v \<psi>) = 8" by simp
  \<comment> \<open>A generic evaluation: for $\varphi$ supported on $K$ (in the sense below), $P_K\varphi=\varphi$ and
      $P_{K'}\varphi=0$ for the other syndromes; then the flip returns $\psi$.\<close>
  have P_fix: "\<And>\<phi> K. dim_vec \<phi> = 8 \<Longrightarrow> (\<And>i. i < 8 \<Longrightarrow> i \<notin> K \<Longrightarrow> \<phi> $ i = 0) \<Longrightarrow> syndrome_proj K *\<^sub>v \<phi> = \<phi>"
  proof (rule eq_vecI)
    fix \<phi> :: "complex Matrix.vec" and K :: "nat set" and i :: nat
    assume d: "dim_vec \<phi> = 8" and z: "\<And>i. i < 8 \<Longrightarrow> i \<notin> K \<Longrightarrow> \<phi> $ i = 0" and "i < dim_vec \<phi>"
    hence i: "i < 8" by simp
    show "(syndrome_proj K *\<^sub>v \<phi>) $ i = \<phi> $ i" unfolding syndrome_proj_mult_vec[OF d i] using z[OF i] by auto
  qed simp
  have P_kill: "\<And>\<phi> K. dim_vec \<phi> = 8 \<Longrightarrow> (\<And>i. i < 8 \<Longrightarrow> i \<in> K \<Longrightarrow> \<phi> $ i = 0) \<Longrightarrow> syndrome_proj K *\<^sub>v \<phi> = 0\<^sub>v 8"
  proof (rule eq_vecI)
    fix \<phi> :: "complex Matrix.vec" and K :: "nat set" and i :: nat
    assume d: "dim_vec \<phi> = 8" and z: "\<And>i. i < 8 \<Longrightarrow> i \<in> K \<Longrightarrow> \<phi> $ i = 0" and "i < dim_vec (0\<^sub>v 8 :: complex Matrix.vec)"
    hence i: "i < 8" by simp
    show "(syndrome_proj K *\<^sub>v \<phi>) $ i = (0\<^sub>v 8 :: complex Matrix.vec) $ i"
      unfolding syndrome_proj_mult_vec[OF d i] using z[OF i] i by auto
  qed simp
  have X_zero: "\<And>b. b < 3 \<Longrightarrow> flip_bit_mat b *\<^sub>v (0\<^sub>v 8) = 0\<^sub>v 8"
  proof (rule eq_vecI)
    fix b i :: nat assume b: "b < 3" and "i < dim_vec (0\<^sub>v 8 :: complex Matrix.vec)"
    hence i: "i < 8" by simp
    have d0: "dim_vec (0\<^sub>v 8 :: complex Matrix.vec) = 8" by simp
    show "(flip_bit_mat b *\<^sub>v (0\<^sub>v 8)) $ i = (0\<^sub>v 8 :: complex Matrix.vec) $ i"
      unfolding flip_bit_mat_mult_vec[OF b d0 i] using flip_tgt_lt[OF b i, unfolded flip_tgt_def] i by simp
  qed simp
  have XX: "\<And>b. b < 3 \<Longrightarrow> flip_bit_mat b *\<^sub>v (flip_bit_mat b *\<^sub>v \<psi>) = \<psi>"
  proof -
    fix b :: nat assume b: "b < 3"
    have "flip_bit_mat b *\<^sub>v (flip_bit_mat b *\<^sub>v \<psi>) = (flip_bit_mat b * flip_bit_mat b) *\<^sub>v \<psi>"
      by (rule assoc_mult_mat_vec[OF flip_bit_mat_carrier flip_bit_mat_carrier carrier_vecI[OF \<psi>d], symmetric])
    also have "\<dots> = \<psi>" unfolding flip_bit_mat_squared[OF b] by (rule one_mult_mat_vec[OF carrier_vecI[OF \<psi>d]])
    finally show "flip_bit_mat b *\<^sub>v (flip_bit_mat b *\<^sub>v \<psi>) = \<psi>" .
  qed
  have X1X1: "X\<^sub>1 *\<^sub>v (X\<^sub>1 *\<^sub>v \<psi>) = \<psi>" and X2X2: "X\<^sub>2 *\<^sub>v (X\<^sub>2 *\<^sub>v \<psi>) = \<psi>" and X3X3: "X\<^sub>3 *\<^sub>v (X\<^sub>3 *\<^sub>v \<psi>) = \<psi>"
    using XX[of 2] XX[of 1] XX[of 0] by simp_all
  have oc: "\<psi> \<oslash> \<psi> \<in> carrier_mat 8 8" by (rule outer_prod_carrier[OF \<psi>d \<psi>d])
  have z8: "(0\<^sub>v 8 :: complex Matrix.vec) \<oslash> 0\<^sub>v 8 = 0\<^sub>m 8 8" by (rule outer_prod_zero_vec)
  \<comment> \<open>no error\<close>
  have a0: "P\<^sub>0 *\<^sub>v \<psi> = \<psi>" by (rule P_fix[OF \<psi>d]) (auto simp: \<psi>i)
  have a1: "P\<^sub>1 *\<^sub>v \<psi> = 0\<^sub>v 8" by (rule P_kill[OF \<psi>d]) (auto simp: \<psi>i)
  have a2: "P\<^sub>2 *\<^sub>v \<psi> = 0\<^sub>v 8" by (rule P_kill[OF \<psi>d]) (auto simp: \<psi>i)
  have a3: "P\<^sub>3 *\<^sub>v \<psi> = 0\<^sub>v 8" by (rule P_kill[OF \<psi>d]) (auto simp: \<psi>i)
  show "bitflip_recovery_map (\<psi> \<oslash> \<psi>) = \<psi> \<oslash> \<psi>"
    unfolding recovery_kraus_term[OF \<psi>d] a0 a1 a2 a3 using oc z8 X_zero by simp
  \<comment> \<open>error on qubit 1\<close>
  have b0: "P\<^sub>0 *\<^sub>v (X\<^sub>1 *\<^sub>v \<psi>) = 0\<^sub>v 8" by (rule P_kill[OF Xd]) (simp only: X1\<psi>, auto)
  have b1: "P\<^sub>1 *\<^sub>v (X\<^sub>1 *\<^sub>v \<psi>) = X\<^sub>1 *\<^sub>v \<psi>" by (rule P_fix[OF Xd]) (simp only: X1\<psi>, auto)
  have b2: "P\<^sub>2 *\<^sub>v (X\<^sub>1 *\<^sub>v \<psi>) = 0\<^sub>v 8" by (rule P_kill[OF Xd]) (simp only: X1\<psi>, auto)
  have b3: "P\<^sub>3 *\<^sub>v (X\<^sub>1 *\<^sub>v \<psi>) = 0\<^sub>v 8" by (rule P_kill[OF Xd]) (simp only: X1\<psi>, auto)
  show "bitflip_recovery_map ((X\<^sub>1 *\<^sub>v \<psi>) \<oslash> (X\<^sub>1 *\<^sub>v \<psi>)) = \<psi> \<oslash> \<psi>"
    unfolding recovery_kraus_term[OF Xd] b0 b1 b2 b3 X1X1 using oc z8 X_zero by simp
  \<comment> \<open>error on qubit 2\<close>
  have c0: "P\<^sub>0 *\<^sub>v (X\<^sub>2 *\<^sub>v \<psi>) = 0\<^sub>v 8" by (rule P_kill[OF Xd]) (simp only: X2\<psi>, auto)
  have c1: "P\<^sub>1 *\<^sub>v (X\<^sub>2 *\<^sub>v \<psi>) = 0\<^sub>v 8" by (rule P_kill[OF Xd]) (simp only: X2\<psi>, auto)
  have c2: "P\<^sub>2 *\<^sub>v (X\<^sub>2 *\<^sub>v \<psi>) = X\<^sub>2 *\<^sub>v \<psi>" by (rule P_fix[OF Xd]) (simp only: X2\<psi>, auto)
  have c3: "P\<^sub>3 *\<^sub>v (X\<^sub>2 *\<^sub>v \<psi>) = 0\<^sub>v 8" by (rule P_kill[OF Xd]) (simp only: X2\<psi>, auto)
  show "bitflip_recovery_map ((X\<^sub>2 *\<^sub>v \<psi>) \<oslash> (X\<^sub>2 *\<^sub>v \<psi>)) = \<psi> \<oslash> \<psi>"
    unfolding recovery_kraus_term[OF Xd] c0 c1 c2 c3 X2X2 using oc z8 X_zero by simp
  \<comment> \<open>error on qubit 3\<close>
  have d0: "P\<^sub>0 *\<^sub>v (X\<^sub>3 *\<^sub>v \<psi>) = 0\<^sub>v 8" by (rule P_kill[OF Xd]) (simp only: X3\<psi>, auto)
  have d1: "P\<^sub>1 *\<^sub>v (X\<^sub>3 *\<^sub>v \<psi>) = 0\<^sub>v 8" by (rule P_kill[OF Xd]) (simp only: X3\<psi>, auto)
  have d2: "P\<^sub>2 *\<^sub>v (X\<^sub>3 *\<^sub>v \<psi>) = 0\<^sub>v 8" by (rule P_kill[OF Xd]) (simp only: X3\<psi>, auto)
  have d3: "P\<^sub>3 *\<^sub>v (X\<^sub>3 *\<^sub>v \<psi>) = X\<^sub>3 *\<^sub>v \<psi>" by (rule P_fix[OF Xd]) (simp only: X3\<psi>, auto)
  show "bitflip_recovery_map ((X\<^sub>3 *\<^sub>v \<psi>) \<oslash> (X\<^sub>3 *\<^sub>v \<psi>)) = \<psi> \<oslash> \<psi>"
    unfolding recovery_kraus_term[OF Xd] d0 d1 d2 d3 X3X3 using oc z8 X_zero by simp
qed

end

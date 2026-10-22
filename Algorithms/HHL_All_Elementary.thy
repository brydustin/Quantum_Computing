theory HHL_All_Elementary
  imports HHL_State_Preparation
begin

section \<open>Removing the assumed gates\<close>

text \<open>For $n=2^s$ the HHL circuits had two kinds of non-elementary gates besides the oracle calls:
the preparation $U_b$ and ancilla rotations controlled by the last clock qubit across the system
register.  The rotations are routed by adjacent swaps (\<open>route_cv0\<close>), and $U_b$ is built for every
normalised $b$ from the rotation cascade and a diagonal unitary (\<open>bprep\<close>), so every gate is
elementary or an oracle call (\<open>hhl_elementary\<close>, \<open>hhl_apx_elementary\<close>).  Exact universality
(\<open>exact_universality\<close>) compiles the oracle calls as well (\<open>hhl_compiled\<close>, \<open>hhl_apx_compiled\<close>),
with no bound on the number of gates.\<close>

subsection \<open>Routing ancilla rotations by adjacent swaps\<close>

lemma ctrl_blocks_left_one:
  assumes B: "\<And>c. c < N \<Longrightarrow> B c \<in> carrier_mat m m" and n0: "0 < n" and m0: "0 < m"
  shows "ctrl_blocks N (n * m) (\<lambda>c. 1\<^sub>m n \<Otimes> B c) = ctrl_blocks (N * n) m (\<lambda>d. B (d div n))"
proof (rule eq_matI)
  fix x y assume "x < dim_row (ctrl_blocks (N * n) m (\<lambda>d. B (d div n)))" "y < dim_col (ctrl_blocks (N * n) m (\<lambda>d. B (d div n)))"
  hence xy: "x < N * n * m" "y < N * n * m" by simp_all
  have d: "z div (n * m) = z div m div n" for z by (simp add: div_mult2_eq Groups.mult.commute[of n m])
  have md: "z mod (n * m) div m = z div m mod n" "z mod (n * m) mod m = z mod m" for z
    using m0 by (simp_all add: mod_mult2_eq Groups.mult.commute[of n m] div_mult2_eq mod_mod_cancel)
  have d2: "z div (m * n) = z div m div n" for z by (simp add: div_mult2_eq)
  have q: "x div m = y div m \<longleftrightarrow> x div m div n = y div m div n \<and> x div m mod n = y div m mod n"
  proof
    assume h: "x div m div n = y div m div n \<and> x div m mod n = y div m mod n"
    have "x div m = x div m div n * n + x div m mod n" by simp
    also have "\<dots> = y div m div n * n + y div m mod n" using h by simp
    also have "\<dots> = y div m" by simp
    finally show "x div m = y div m" .
  qed simp
  have xc: "x div m div n < N" using xy by (simp add: less_mult_imp_div_less div_mult2_eq[symmetric] Groups.mult_ac)
  have Bc: "B (x div m div n) \<in> carrier_mat m m" by (rule B[OF xc])
  have nm: "x mod (n * m) < n * m" "y mod (n * m) < n * m" using n0 m0 by simp_all
  have t: "(1\<^sub>m n \<Otimes> B (x div m div n)) $$ (x mod (n * m), y mod (n * m))
           = 1\<^sub>m n $$ (x div m mod n, y div m mod n) * B (x div m div n) $$ (x mod m, y mod m)"
    using index_tensor_mat[of "1\<^sub>m n" n n "B (x div m div n)" m m "x mod (n * m)" "y mod (n * m)"] Bc nm n0 m0
    by (simp add: md)
  have dx: "x div m < N * n" "y div m < N * n" using xy by (simp_all add: less_mult_imp_div_less)
  show "ctrl_blocks N (n * m) (\<lambda>c. 1\<^sub>m n \<Otimes> B c) $$ (x, y) = ctrl_blocks (N * n) m (\<lambda>d. B (d div n)) $$ (x, y)"
  proof (cases "x div m = y div m")
    case True
    have l: "ctrl_blocks N (n * m) (\<lambda>c. 1\<^sub>m n \<Otimes> B c) $$ (x, y) = (1\<^sub>m n \<Otimes> B (x div m div n)) $$ (x mod (n * m), y mod (n * m))"
      using xy True q by (simp add: ctrl_blocks_index d2 Groups.mult_ac)
    have r: "ctrl_blocks (N * n) m (\<lambda>d. B (d div n)) $$ (x, y) = B (x div m div n) $$ (x mod m, y mod m)"
      using xy True by (simp add: ctrl_blocks_index)
    show ?thesis unfolding l r t using True n0 by simp
  next
    case False
    have l: "ctrl_blocks N (n * m) (\<lambda>c. 1\<^sub>m n \<Otimes> B c) $$ (x, y) = 0"
    proof (cases "x div (n * m) = y div (n * m)")
      case True
      hence "x div m mod n \<noteq> y div m mod n" using False q d by simp
      hence "(1\<^sub>m n \<Otimes> B (x div m div n)) $$ (x mod (n * m), y mod (n * m)) = 0" unfolding t using n0 by simp
      thus ?thesis using xy True by (simp add: ctrl_blocks_index d2 Groups.mult_ac)
    qed (use xy in \<open>simp add: ctrl_blocks_index Groups.mult_ac\<close>)
    show ?thesis unfolding l using xy False by (simp add: ctrl_blocks_index)
  qed
qed (simp_all add: Groups.mult_ac)

definition up_ops :: "nat \<Rightarrow> (bool \<times> nat) list" where
  "up_ops s = map (\<lambda>j. (False, j)) [0..<s]"

lemma gs_div2: "x < 4 \<Longrightarrow> gs x div 2 = x mod 2"
proof -
  assume "x < 4"
  hence "x = 0 \<or> x = 1 \<or> x = 2 \<or> x = 3" by auto
  thus ?thesis by (auto simp: gs_def)
qed

lemma div2_mod2: "z div 2 mod 2 = z mod 4 div 2" for z :: nat
proof -
  have "z mod 4 = z mod (2 * 2)" by simp
  thus ?thesis by (simp only: mod_mult2_eq) simp
qed

lemma up_ops_bit: "apply_ops (up_ops s) d div 2 ^ s mod 2 = d mod 2"
proof (induction s)
  case 0 show ?case by (simp add: up_ops_def)
next
  case (Suc s)
  let ?x = "apply_ops (up_ops s) d"
  have e: "up_ops (Suc s) = up_ops s @ [(False, s)]" by (simp add: up_ops_def)
  have g: "\<And>x. x < 4 \<Longrightarrow> gs x < 4" using gs_props(1) by blast
  have "apply_ops (up_ops (Suc s)) d div 2 ^ Suc s mod 2 = lift2 gs s ?x div 2 ^ s div 2 mod 2"
    unfolding e apply_ops_snoc by (simp add: opf_def opg_def div_mult2_eq Groups.mult.commute[of 2])
  also have "\<dots> = lift2 gs s ?x div 2 ^ s mod 4 div 2" by (rule div2_mod2)
  also have "\<dots> = gs (?x div 2 ^ s mod 4) div 2" by (simp only: lift2_digits(2)[OF g])
  also have "\<dots> = ?x div 2 ^ s mod 4 mod 2" by (rule gs_div2) simp
  also have "\<dots> = ?x div 2 ^ s mod 2" by (simp add: mod_mod_cancel)
  finally show ?case using Suc.IH by simp
qed

lemma up_ops_pos: "(b, j) \<in> set (up_ops s) \<Longrightarrow> j + 2 \<le> k + s" if "1 \<le> k"
  using that by (auto simp: up_ops_def)

text \<open>\<open>route k s U\<close>: $U$ conjugated so that the ancilla is moved next to the clock by
adjacent swaps, applied, and moved back.\<close>

definition route :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat list" where
  "route k s U = map (cgate (k + s) 2) (rev (up_ops s))
     @ [(pmat (2 ^ (k + s)) (apply_ops (rev (up_ops s))) \<Otimes> 1\<^sub>m 2) * U * (pmat (2 ^ (k + s)) (apply_ops (up_ops s)) \<Otimes> 1\<^sub>m 2)]
     @ map (cgate (k + s) 2) (up_ops s)"

lemma route_circuit:
  assumes k: "1 \<le> k" and U: "U \<in> carrier_mat (2 ^ (k + s) * 2) (2 ^ (k + s) * 2)"
  shows "circuit_mat (2 ^ (k + s) * 2) (route k s U) = U"
proof -
  let ?K = "2 ^ (k + s) * 2" and ?N = "2 ^ (k + s)"
  let ?F = "pmat ?N (apply_ops (rev (up_ops s))) \<Otimes> 1\<^sub>m 2" and ?H = "pmat ?N (apply_ops (up_ops s)) \<Otimes> 1\<^sub>m 2"
  have pos: "\<And>b j. (b, j) \<in> set (up_ops s) \<Longrightarrow> j + 2 \<le> k + s" using up_ops_pos[OF k] by blast
  have posr: "\<And>b j. (b, j) \<in> set (rev (up_ops s)) \<Longrightarrow> j + 2 \<le> k + s" using pos by simp
  have Fc: "?F \<in> carrier_mat ?K ?K" and Hc: "?H \<in> carrier_mat ?K ?K" by (simp_all add: tensor_carrier)
  have cg: "\<And>U. U \<in> set (map (cgate (k + s) 2) os) \<Longrightarrow> U \<in> carrier_mat ?K ?K" for os
    by (auto simp: cgate_def intro!: tensor_carrier[OF pmat_carrier one_carrier_mat, simplified])
  have Mc: "?F * U * ?H \<in> carrier_mat ?K ?K" by (rule mult_carrier_mat[OF mult_carrier_mat[OF Fc U] Hc])
  have c1: "circuit_mat ?K (map (cgate (k + s) 2) (rev (up_ops s))) = ?F" by (rule circuit_cgates) (use posr in auto)
  have c2: "circuit_mat ?K (map (cgate (k + s) 2) (up_ops s)) = ?H" by (rule circuit_cgates) (use pos in auto)
  have inv: "?H * ?F = 1\<^sub>m ?K"
  proof -
    have "?H * ?F = (pmat ?N (apply_ops (up_ops s)) * pmat ?N (apply_ops (rev (up_ops s)))) \<Otimes> (1\<^sub>m 2 * 1\<^sub>m 2)"
      by (rule mult_distr_tensor[symmetric]) simp_all
    also have "pmat ?N (apply_ops (up_ops s)) * pmat ?N (apply_ops (rev (up_ops s))) = pmat ?N (apply_ops (up_ops s) \<circ> apply_ops (rev (up_ops s)))"
      by (rule pmat_mult) (rule apply_ops_lt[OF posr])
    also have "apply_ops (up_ops s) \<circ> apply_ops (rev (up_ops s)) = id"
      using apply_ops_rev[of "rev (up_ops s)"] by (auto simp: fun_eq_iff)
    finally show ?thesis by (simp only: pmat_id right_mult_one_mat[OF one_carrier_mat] tensor_mat_id)
  qed
  let ?xs = "map (cgate (k + s) 2) (rev (up_ops s))" and ?M = "?F * U * ?H"
  have "circuit_mat ?K (route k s U) = circuit_mat ?K (map (cgate (k + s) 2) (up_ops s)) * circuit_mat ?K (?xs @ [?M])"
    unfolding route_def append_assoc[symmetric] by (rule circuit_mat_append) (use cg Mc in auto)
  also have "circuit_mat ?K (?xs @ [?M]) = circuit_mat ?K [?M] * circuit_mat ?K ?xs"
    by (rule circuit_mat_append) (use cg Mc in auto)
  also have "circuit_mat ?K [?M] = ?M" using Mc by simp
  finally have e: "circuit_mat ?K (route k s U) = ?H * (?F * U * ?H * ?F)" unfolding c1 c2 by (simp add: assoc_mult_mat[OF Mc Fc Fc, symmetric])
  have "?H * (?F * U * ?H * ?F) = (?H * ?F) * U * (?H * ?F)"
  proof -
    have "?F * U * ?H * ?F = ?F * (U * (?H * ?F))"
      using assoc_mult_mat[OF mult_carrier_mat[OF Fc U] Hc Fc] assoc_mult_mat[OF Fc U mult_carrier_mat[OF Hc Fc]] by simp
    hence "?H * (?F * U * ?H * ?F) = (?H * ?F) * (U * (?H * ?F))"
      using assoc_mult_mat[OF Hc Fc mult_carrier_mat[OF U mult_carrier_mat[OF Hc Fc]]] by simp
    also have "\<dots> = (?H * ?F) * U * (?H * ?F)"
      using assoc_mult_mat[OF mult_carrier_mat[OF Hc Fc] U mult_carrier_mat[OF Hc Fc]] by simp
    finally show ?thesis .
  qed
  thus ?thesis unfolding e inv using U by simp
qed

lemma cv0_ctrl:
  assumes W: "Wr \<in> carrier_mat 2 2"
  shows "cv0 k (2 ^ s) Wr = ctrl_blocks (2 ^ k * 2 ^ s) 2 (\<lambda>d. if odd (d div 2 ^ s) then Wr else 1\<^sub>m 2)"
proof -
  have "cv0 k (2 ^ s) Wr = ctrl_blocks (2 ^ k) (2 ^ s * 2) (\<lambda>c. 1\<^sub>m (2 ^ s) \<Otimes> (if odd c then Wr else 1\<^sub>m 2))"
    unfolding cv0_def by (rule ctrl_blocks_cong) (simp add: tensor_mat_id)
  also have "\<dots> = ctrl_blocks (2 ^ k * 2 ^ s) 2 (\<lambda>d. if odd (d div 2 ^ s) then Wr else 1\<^sub>m 2)"
    by (rule ctrl_blocks_left_one) (use W in auto)
  finally show ?thesis .
qed

lemma route_middle:
  assumes k: "1 \<le> k" and W: "Wr \<in> carrier_mat 2 2"
  shows "(pmat (2 ^ (k + s)) (apply_ops (rev (up_ops s))) \<Otimes> 1\<^sub>m 2) * cv0 k (2 ^ s) Wr * (pmat (2 ^ (k + s)) (apply_ops (up_ops s)) \<Otimes> 1\<^sub>m 2)
         = cv0 (k + s) 1 Wr"
proof -
  let ?N = "2 ^ (k + s)" and ?B = "\<lambda>d. if odd (d div 2 ^ s) then Wr else 1\<^sub>m 2"
  have pos: "\<And>b j. (b, j) \<in> set (up_ops s) \<Longrightarrow> j + 2 \<le> k + s" using up_ops_pos[OF k] by blast
  have N: "(2::nat) ^ k * 2 ^ s = ?N" by (simp add: power_add)
  have "(pmat ?N (apply_ops (rev (up_ops s))) \<Otimes> 1\<^sub>m 2) * ctrl_blocks ?N 2 ?B * (pmat ?N (apply_ops (up_ops s)) \<Otimes> 1\<^sub>m 2)
        = ctrl_blocks ?N 2 (\<lambda>c. ?B (apply_ops (up_ops s) c))"
    by (rule ctrl_conj) (use apply_ops_lt[OF pos] apply_ops_rev W in auto)
  also have "\<dots> = ctrl_blocks ?N 2 (\<lambda>c. if odd c then Wr else 1\<^sub>m 2)"
    by (rule ctrl_blocks_cong) (simp add: odd_iff_mod_2_eq_one up_ops_bit)
  also have "\<dots> = cv0 (k + s) 1 Wr" unfolding cv0_def left_tensor_id[OF W] Groups.monoid_mult_class.mult_1_left ..
  finally show ?thesis unfolding cv0_ctrl[OF W] N .
qed

theorem route_cv0:
  assumes k: "1 \<le> k" and W: "Wr \<in> carrier_mat 2 2" "Quantum.unitary Wr"
  shows "circuit_mat (2 ^ k * (2 ^ s * 2)) (route k s (cv0 k (2 ^ s) Wr)) = cv0 k (2 ^ s) Wr"
    and "\<And>U. U \<in> set (route k s (cv0 k (2 ^ s) Wr)) \<Longrightarrow> elementary (2 ^ k * (2 ^ s * 2)) U"
proof -
  have K: "(2::nat) ^ k * (2 ^ s * 2) = 2 ^ (k + s) * 2" by (simp add: power_add)
  have c: "cv0 k (2 ^ s) Wr \<in> carrier_mat (2 ^ (k + s) * 2) (2 ^ (k + s) * 2)" unfolding K[symmetric] cv0_def by (rule ctrl_blocks_carrier)
  show "circuit_mat (2 ^ k * (2 ^ s * 2)) (route k s (cv0 k (2 ^ s) Wr)) = cv0 k (2 ^ s) Wr"
    unfolding K by (rule route_circuit[OF k c])
  fix U assume U: "U \<in> set (route k s (cv0 k (2 ^ s) Wr))"
  have pos: "\<And>b j. (b, j) \<in> set (up_ops s) \<Longrightarrow> j + 2 \<le> k + s" using up_ops_pos[OF k] by blast
  have "U = cv0 (k + s) 1 Wr \<or> (\<exists>b j. (b, j) \<in> set (up_ops s) \<and> U = cgate (k + s) 2 (b, j))"
    using U unfolding route_def route_middle[OF k W(1)] by auto
  moreover have "elementary (2 ^ (k + s) * (1 * 2)) (cv0 (k + s) 1 Wr)" by (rule cv0_one_elementary) (use k W in auto)
  moreover have "\<And>b j. (b, j) \<in> set (up_ops s) \<Longrightarrow> elementary (2 ^ (k + s) * 2) (cgate (k + s) 2 (b, j))"
    by (rule cgate_elementary) (use pos in auto)
  ultimately show "elementary (2 ^ k * (2 ^ s * 2)) U" unfolding K by auto
qed


subsection \<open>Diagonal unitaries\<close>

definition dmat :: "nat \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> complex Matrix.mat" where
  "dmat N \<phi> = mat_diag N (\<lambda>r. cis (\<phi> r))"

definition Qm :: "complex Matrix.mat" where
  "Qm = Matrix.mat 2 2 (\<lambda>(i, j). complex_of_real (1 / sqrt 2) * (if i = 0 then 1 else if j = 0 then \<i> else - \<i>))"

lemma Qm_carrier [simp]: "Qm \<in> carrier_mat 2 2" by (simp add: Qm_def)

lemma sum2: "(\<Sum>u\<in>{0..<2}. f u) = f 0 + f (1::nat)" for f :: "nat \<Rightarrow> complex"
  by (simp add: numeral_2_eq_2)

lemma Qm_unitary: "Quantum.unitary Qm"
proof -
  have s: "complex_of_real (1 / sqrt 2) * complex_of_real (1 / sqrt 2) = 1 / 2"
    by (simp flip: of_real_mult)
  have s2: "complex_of_real (sqrt 2) * complex_of_real (sqrt 2) = 2" by (simp flip: of_real_mult)
  have "(Qm\<^sup>\<dagger>) * Qm = 1\<^sub>m 2" "Qm * (Qm\<^sup>\<dagger>) = 1\<^sub>m 2"
    by (rule eq_matI, auto simp: Qm_def dagger_def scalar_prod_def sum2 less_Suc_eq numeral_2_eq_2 s s2)+
  thus ?thesis by (simp add: Quantum.unitary_def Qm_def)
qed

lemma Qm_Rot: "(Qm\<^sup>\<dagger>) * Rot b * Qm = dmat 2 (\<lambda>a. if a = 0 then - b else b)"
proof -
  have s: "complex_of_real (1 / sqrt 2) * complex_of_real (1 / sqrt 2) = 1 / 2"
    by (simp flip: of_real_mult)
  have s2: "complex_of_real (sqrt 2) * complex_of_real (sqrt 2) = 2" by (simp flip: of_real_mult)
  show ?thesis
    by (rule eq_matI) (auto simp: Qm_def Rot_def dmat_def mat_diag_def dagger_def scalar_prod_def sum2 less_Suc_eq numeral_2_eq_2 s s2
        cis.ctr complex_eq_iff algebra_simps)
qed

lemma dmat_carrier [simp]: "dmat N \<phi> \<in> carrier_mat N N" by (simp add: dmat_def mat_diag_def)

lemma dmat_mult: "dmat N f * dmat N g = dmat N (\<lambda>x. f x + g x)"
  unfolding dmat_def mat_diag_diag by (simp add: cis_mult)

lemma dmat_cong: "(\<And>x. x < N \<Longrightarrow> f x = g x) \<Longrightarrow> dmat N f = dmat N g"
  by (rule eq_matI) (auto simp: dmat_def mat_diag_def)

lemma dmat_zero: "dmat N (\<lambda>_. 0) = 1\<^sub>m N" by (simp add: dmat_def)

lemma dmat_unitary: "Quantum.unitary (dmat N \<phi>)"
proof -
  have d: "(dmat N \<phi>)\<^sup>\<dagger> = dmat N (\<lambda>x. - \<phi> x)" by (rule eq_matI) (auto simp: dmat_def mat_diag_def dagger_def cis_cnj)
  show ?thesis unfolding Quantum.unitary_def d dmat_mult by (simp add: dmat_zero dmat_def mat_diag_def)
qed

lemma dmat_tensor_one: "dmat N \<alpha> \<Otimes> 1\<^sub>m 2 = dmat (N * 2) (\<lambda>x. \<alpha> (x div 2))"
proof (rule eq_matI)
  fix r t assume "r < dim_row (dmat (N * 2) (\<lambda>x. \<alpha> (x div 2)))" "t < dim_col (dmat (N * 2) (\<lambda>x. \<alpha> (x div 2)))"
  hence rt: "r < N * 2" "t < N * 2" by (simp_all add: dmat_def mat_diag_def)
  have N0: "0 < N" using rt by (cases N) auto
  have q: "r = t \<longleftrightarrow> r div 2 = t div 2 \<and> r mod 2 = t mod 2"
    by (metis div_mult_mod_eq)
  have "(dmat N \<alpha> \<Otimes> 1\<^sub>m 2) $$ (r, t) = dmat N \<alpha> $$ (r div 2, t div 2) * 1\<^sub>m 2 $$ (r mod 2, t mod 2)"
    using index_tensor_mat[of "dmat N \<alpha>" N N "1\<^sub>m 2" 2 2 r t] rt N0 by (simp add: Groups.mult_ac dmat_def mat_diag_def)
  also have "\<dots> = dmat (N * 2) (\<lambda>x. \<alpha> (x div 2)) $$ (r, t)"
    using rt q by (simp add: dmat_def mat_diag_def less_mult_imp_div_less)
  finally show "(dmat N \<alpha> \<Otimes> 1\<^sub>m 2) $$ (r, t) = dmat (N * 2) (\<lambda>x. \<alpha> (x div 2)) $$ (r, t)" .
qed (simp_all add: dmat_def mat_diag_def)

lemma ctrl_dmat: "ctrl_blocks N 2 (\<lambda>c. dmat 2 (\<psi> c)) = dmat (N * 2) (\<lambda>x. \<psi> (x div 2) (x mod 2))"
proof (rule eq_matI)
  fix r t assume "r < dim_row (dmat (N * 2) (\<lambda>x. \<psi> (x div 2) (x mod 2)))" "t < dim_col (dmat (N * 2) (\<lambda>x. \<psi> (x div 2) (x mod 2)))"
  hence rt: "r < N * 2" "t < N * 2" by (simp_all add: dmat_def mat_diag_def)
  have q: "r = t \<longleftrightarrow> r div 2 = t div 2 \<and> r mod 2 = t mod 2"
    by (metis div_mult_mod_eq)
  show "ctrl_blocks N 2 (\<lambda>c. dmat 2 (\<psi> c)) $$ (r, t) = dmat (N * 2) (\<lambda>x. \<psi> (x div 2) (x mod 2)) $$ (r, t)"
    using rt q by (auto simp: ctrl_blocks_index dmat_def mat_diag_def)
qed (simp_all add: dmat_def mat_diag_def)

definition ph_mean :: "(nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> real" where "ph_mean \<phi> c = (\<phi> (2 * c) + \<phi> (2 * c + 1)) / 2"
definition ph_diff :: "(nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> real" where "ph_diff \<phi> c = (\<phi> (2 * c + 1) - \<phi> (2 * c)) / 2"

lemma dmat_split:
  "dmat (N * 2) \<phi> = (dmat N (ph_mean \<phi>) \<Otimes> 1\<^sub>m 2) * ctrl_blocks N 2 (\<lambda>c. dmat 2 (\<lambda>a. if a = 0 then - ph_diff \<phi> c else ph_diff \<phi> c))"
proof -
  have "\<phi> x = ph_mean \<phi> (x div 2) + (if x mod 2 = 0 then - ph_diff \<phi> (x div 2) else ph_diff \<phi> (x div 2))" for x
  proof (cases "x mod 2 = 0")
    case True
    have x: "x = 2 * (x div 2)" using div_mult_mod_eq[of x 2] True by simp
    have "\<phi> x = \<phi> (2 * (x div 2))" by (subst x) (rule refl)
    thus ?thesis using True by (simp add: ph_mean_def ph_diff_def field_simps)
  next
    case False
    hence x: "x = 2 * (x div 2) + 1" using div_mult_mod_eq[of x 2] by simp
    have "\<phi> x = \<phi> (2 * (x div 2) + 1)" by (subst x) (rule refl)
    thus ?thesis using False by (simp add: ph_mean_def ph_diff_def field_simps)
  qed
  thus ?thesis unfolding dmat_tensor_one ctrl_dmat dmat_mult by (intro dmat_cong) simp
qed

text \<open>\<open>diag_gates k \<phi>\<close>: the diagonal unitary $\ket x\mapsto e^{i\phi_x}\ket x$ on $k+1$ qubits.  The phase
difference within each pair is a uniformly controlled rotation conjugated by \<open>Qm\<close>; the mean
phase is a diagonal unitary on the first $k$ qubits.\<close>

fun diag_gates :: "nat \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> complex Matrix.mat list" where
  "diag_gates 0 \<phi> = [dmat 2 \<phi>]"
| "diag_gates (Suc k) \<phi> = (1\<^sub>m (2 ^ Suc k) \<Otimes> Qm) # ucr_gates (Suc k) 1 (ph_diff \<phi>)
     @ (1\<^sub>m (2 ^ Suc k) \<Otimes> (Qm\<^sup>\<dagger>)) # map (\<lambda>U. U \<Otimes> 1\<^sub>m 2) (diag_gates k (ph_mean \<phi>))"

lemma Qm_dagger_carrier [simp]: "Qm\<^sup>\<dagger> \<in> carrier_mat 2 2" by (simp add: dagger_def Qm_def)

lemma ucr1_carrier: "U \<in> set (ucr_gates j 1 \<theta>) \<Longrightarrow> U \<in> carrier_mat (2 ^ j * 2) (2 ^ j * 2)"
  using ucr_gates_ok[of U j 1 \<theta>] by simp

lemma diag_gates_carrier: "U \<in> set (diag_gates k \<phi>) \<Longrightarrow> U \<in> carrier_mat (2 ^ Suc k) (2 ^ Suc k)"
proof (induction k arbitrary: \<phi> U)
  case 0 thus ?case by simp
next
  case (Suc k)
  have K: "(2::nat) ^ Suc (Suc k) = 2 ^ Suc k * 2" by simp
  have a: "1\<^sub>m (2 ^ Suc k) \<Otimes> B \<in> carrier_mat (2 ^ Suc k * 2) (2 ^ Suc k * 2)" if "B \<in> carrier_mat 2 2" for B
    by (rule tensor_carrier[OF one_carrier_mat that])
  have b: "V \<Otimes> 1\<^sub>m 2 \<in> carrier_mat (2 ^ Suc k * 2) (2 ^ Suc k * 2)" if "V \<in> carrier_mat (2 ^ Suc k) (2 ^ Suc k)" for V
    by (rule tensor_carrier[OF that one_carrier_mat])
  have "U = 1\<^sub>m (2 ^ Suc k) \<Otimes> Qm \<or> U \<in> set (ucr_gates (Suc k) 1 (ph_diff \<phi>)) \<or> U = 1\<^sub>m (2 ^ Suc k) \<Otimes> (Qm\<^sup>\<dagger>)
        \<or> (\<exists>V \<in> set (diag_gates k (ph_mean \<phi>)). U = V \<Otimes> 1\<^sub>m 2)" using Suc.prems by auto
  thus ?case unfolding K using a[OF Qm_carrier] a[OF Qm_dagger_carrier] ucr1_carrier b Suc.IH by blast
qed

theorem diag_gates_circuit: "circuit_mat (2 ^ Suc k) (diag_gates k \<phi>) = dmat (2 ^ Suc k) \<phi>"
proof (induction k arbitrary: \<phi>)
  case 0
  show ?case by (simp add: left_mult_one_mat[OF dmat_carrier])
next
  case (Suc k)
  let ?N = "2 ^ Suc k :: nat" and ?\<beta> = "ph_diff \<phi>"
  let ?G1 = "1\<^sub>m ?N \<Otimes> Qm" and ?G2 = "1\<^sub>m ?N \<Otimes> (Qm\<^sup>\<dagger>)" and ?R = "ucr_gates (Suc k) 1 ?\<beta>"
  let ?T = "map (\<lambda>U. U \<Otimes> 1\<^sub>m 2) (diag_gates k (ph_mean \<phi>))"
  have K: "(2::nat) ^ Suc (Suc k) = ?N * 2" by simp
  have G1: "?G1 = ctrl_blocks ?N 2 (\<lambda>_. Qm)" by (rule ctrl_const) simp_all
  have G2: "?G2 = ctrl_blocks ?N 2 (\<lambda>_. Qm\<^sup>\<dagger>)" by (rule ctrl_const) simp_all
  have Tc: "\<And>U. U \<in> set ?T \<Longrightarrow> U \<in> carrier_mat (?N * 2) (?N * 2)"
    using diag_gates_carrier tensor_carrier[OF _ one_carrier_mat, of _ ?N 2] by auto
  have Rc: "\<And>U. U \<in> set ?R \<Longrightarrow> U \<in> carrier_mat (?N * 2) (?N * 2)" by (rule ucr1_carrier)
  have G2c: "?G2 \<in> carrier_mat (?N * 2) (?N * 2)" by (rule tensor_carrier[OF one_carrier_mat Qm_dagger_carrier])
  have cT: "circuit_mat (?N * 2) ?T = dmat ?N (ph_mean \<phi>) \<Otimes> 1\<^sub>m 2"
    using circuit_mat_tensor_right[of "diag_gates k (ph_mean \<phi>)" ?N 2] diag_gates_carrier Suc.IH by simp
  have cR: "circuit_mat (?N * 2) ?R = ctrl_blocks ?N 2 (\<lambda>c. Rot (?\<beta> c))"
  proof -
    have l: "1\<^sub>m 1 \<Otimes> Rot a = Rot a" for a by (rule left_tensor_id[OF Rot_carrier])
    show ?thesis using ucr_circuit[of 1 "Suc k" ?\<beta>] by (simp add: l[unfolded One_nat_def])
  qed
  have "circuit_mat (?N * 2) (diag_gates (Suc k) \<phi>) = circuit_mat (?N * 2) (?R @ ?G2 # ?T) * ?G1" by simp
  also have "circuit_mat (?N * 2) (?R @ ?G2 # ?T) = circuit_mat (?N * 2) (?G2 # ?T) * circuit_mat (?N * 2) ?R"
    by (rule circuit_mat_append) (use Rc Tc G2c in auto)
  also have "circuit_mat (?N * 2) (?G2 # ?T) = (dmat ?N (ph_mean \<phi>) \<Otimes> 1\<^sub>m 2) * ?G2" unfolding circuit_mat.simps cT ..
  finally have e: "circuit_mat (?N * 2) (diag_gates (Suc k) \<phi>)
      = (dmat ?N (ph_mean \<phi>) \<Otimes> 1\<^sub>m 2) * ctrl_blocks ?N 2 (\<lambda>_. Qm\<^sup>\<dagger>) * ctrl_blocks ?N 2 (\<lambda>c. Rot (?\<beta> c)) * ctrl_blocks ?N 2 (\<lambda>_. Qm)"
    unfolding cR G1 G2 .
  have "(dmat ?N (ph_mean \<phi>) \<Otimes> 1\<^sub>m 2) * ctrl_blocks ?N 2 (\<lambda>_. Qm\<^sup>\<dagger>) * ctrl_blocks ?N 2 (\<lambda>c. Rot (?\<beta> c)) * ctrl_blocks ?N 2 (\<lambda>_. Qm)
        = (dmat ?N (ph_mean \<phi>) \<Otimes> 1\<^sub>m 2) * (ctrl_blocks ?N 2 (\<lambda>_. Qm\<^sup>\<dagger>) * ctrl_blocks ?N 2 (\<lambda>c. Rot (?\<beta> c)) * ctrl_blocks ?N 2 (\<lambda>_. Qm))"
  proof -
    have Dc: "dmat ?N (ph_mean \<phi>) \<Otimes> 1\<^sub>m 2 \<in> carrier_mat (?N * 2) (?N * 2)" by (rule tensor_carrier) simp_all
    have Ac: "ctrl_blocks ?N 2 (\<lambda>_. Qm\<^sup>\<dagger>) \<in> carrier_mat (?N * 2) (?N * 2)"
      and Bc: "ctrl_blocks ?N 2 (\<lambda>c. Rot (?\<beta> c)) \<in> carrier_mat (?N * 2) (?N * 2)"
      and Cc: "ctrl_blocks ?N 2 (\<lambda>_. Qm) \<in> carrier_mat (?N * 2) (?N * 2)" by (rule ctrl_blocks_carrier)+
    show ?thesis by (simp only: assoc_mult_mat[OF mult_carrier_mat[OF Dc Ac] Bc Cc] assoc_mult_mat[OF Dc Ac mult_carrier_mat[OF Bc Cc]] assoc_mult_mat[OF Ac Bc Cc])
  qed
  also have "ctrl_blocks ?N 2 (\<lambda>_. Qm\<^sup>\<dagger>) * ctrl_blocks ?N 2 (\<lambda>c. Rot (?\<beta> c)) * ctrl_blocks ?N 2 (\<lambda>_. Qm)
             = ctrl_blocks ?N 2 (\<lambda>c. (Qm\<^sup>\<dagger>) * Rot (?\<beta> c) * Qm)"
    using mult_carrier_mat[OF Qm_dagger_carrier Rot_carrier] by (simp add: ctrl_blocks_mult)
  also have "\<dots> = ctrl_blocks ?N 2 (\<lambda>c. dmat 2 (\<lambda>a. if a = 0 then - ?\<beta> c else ?\<beta> c))" by (simp add: Qm_Rot)
  finally show ?case unfolding K e dmat_split[symmetric] .
qed

lemma elementary_one_qubit:
  assumes G: "G \<in> carrier_mat 2 2" "Quantum.unitary G"
  shows "elementary 2 G"
proof -
  have e: "G = 1\<^sub>m 1 \<Otimes> (G \<Otimes> 1\<^sub>m 1)" unfolding right_tensor_id[OF G(1)] left_tensor_id[OF G(1)] ..
  show ?thesis unfolding elementary_def
    by (rule exI[of _ 1], rule exI[of _ 1], rule exI[of _ 1], rule exI[of _ G]) (use e G in simp)
qed

theorem diag_gates_elementary: "U \<in> set (diag_gates k \<phi>) \<Longrightarrow> elementary (2 ^ Suc k) U"
proof (induction k arbitrary: \<phi> U)
  case 0
  thus ?case using elementary_one_qubit[OF dmat_carrier dmat_unitary] by simp
next
  case (Suc k)
  have K: "(2::nat) ^ Suc (Suc k) = 2 ^ Suc k * 2" by simp
  have q: "elementary (2 ^ Suc k * 2) (1\<^sub>m (2 ^ Suc k) \<Otimes> Qm)" "elementary (2 ^ Suc k * 2) (1\<^sub>m (2 ^ Suc k) \<Otimes> (Qm\<^sup>\<dagger>))"
    by (rule elementary_left[OF elementary_one_qubit[OF Qm_carrier Qm_unitary]], simp)
       (rule elementary_left[OF elementary_one_qubit[OF Qm_dagger_carrier unitary_dagger[OF Qm_unitary]]], simp)
  have r: "elementary (2 ^ Suc k * 2) V" if "V \<in> set (ucr_gates (Suc k) 1 (ph_diff \<phi>))" for V
    using ucr_one_elementary[OF that] by (simp only: mult_1)
  have t: "elementary (2 ^ Suc k * 2) (V \<Otimes> 1\<^sub>m 2)" if "V \<in> set (diag_gates k (ph_mean \<phi>))" for V
    by (rule elementary_right[OF Suc.IH[OF that]]) simp
  have "U = 1\<^sub>m (2 ^ Suc k) \<Otimes> Qm \<or> U \<in> set (ucr_gates (Suc k) 1 (ph_diff \<phi>)) \<or> U = 1\<^sub>m (2 ^ Suc k) \<Otimes> (Qm\<^sup>\<dagger>)
        \<or> (\<exists>V \<in> set (diag_gates k (ph_mean \<phi>)). U = V \<Otimes> 1\<^sub>m 2)" using Suc.prems by auto
  thus ?case unfolding K using q r t by blast
qed

subsection \<open>Preparing an arbitrary state\<close>

lemma circuit_elementary_unitary:
  assumes E: "\<And>U. U \<in> set Us \<Longrightarrow> elementary K U"
  shows "circuit_mat K Us \<in> carrier_mat K K" "Quantum.unitary (circuit_mat K Us)"
proof -
  have ok: "\<And>U. U \<in> set Us \<Longrightarrow> U \<in> carrier_mat K K \<and> Complex_Matrix.unitary U"
    using E elementary_unitary unitary_bridge by blast
  show c: "circuit_mat K Us \<in> carrier_mat K K" by (rule circuit_mat_carrier) (use ok in blast)
  interpret state_sig "[K]" .
  have dd: "d = K" by (simp add: d_def)
  have "Complex_Matrix.unitary (circuit_mat K Us)" using circuit_mat_unitary[of Us] ok unfolding dd by blast
  hence r: "circuit_mat K Us * Complex_Matrix.adjoint (circuit_mat K Us) = 1\<^sub>m K"
    using c unfolding Complex_Matrix.unitary_def inverts_mat_def by simp
  have l: "Complex_Matrix.adjoint (circuit_mat K Us) * circuit_mat K Us = 1\<^sub>m K"
    by (rule mat_mult_left_right_inverse[OF c adjoint_dim[OF c] r])
  show "Quantum.unitary (circuit_mat K Us)" using c r l unfolding Quantum.unitary_def dagger_eq_adjoint by simp
qed

lemma dmat_mult_vec: "dim_vec v = N \<Longrightarrow> dmat N \<phi> *\<^sub>v v = Matrix.vec N (\<lambda>x. cis (\<phi> x) * v $ x)"
proof (rule eq_vecI)
  fix x assume v: "dim_vec v = N" and "x < dim_vec (Matrix.vec N (\<lambda>x. cis (\<phi> x) * v $ x))"
  hence x: "x < N" by simp
  have "(dmat N \<phi> *\<^sub>v v) $ x = (\<Sum>u\<in>{0..<N}. (if x = u then cis (\<phi> x) else 0) * v $ u)"
    using x v by (simp add: dmat_def mat_diag_def scalar_prod_def mult_mat_vec_def cong: if_cong)
  also have "\<dots> = (\<Sum>u\<in>{0..<N}. if u = x then cis (\<phi> x) * v $ x else 0)" by (rule sum.cong) auto
  also have "\<dots> = cis (\<phi> x) * v $ x" using x by simp
  finally show "(dmat N \<phi> *\<^sub>v v) $ x = Matrix.vec N (\<lambda>x. cis (\<phi> x) * v $ x) $ x" using x by simp
qed (simp add: dmat_def mat_diag_def)

text \<open>Any normalised $\ket b$ on $s\ge1$ qubits: the magnitudes by the rotation cascade, then the
phases by a diagonal unitary.\<close>

definition bprep_gates :: "nat \<Rightarrow> complex Matrix.vec \<Rightarrow> complex Matrix.mat list" where
  "bprep_gates s b = prep_gates s (\<lambda>x. cmod (b $ x)) @ diag_gates (s - 1) (\<lambda>x. Arg (b $ x))"

theorem bprep:
  assumes s: "1 \<le> s" and b: "dim_vec b = 2 ^ s" "\<parallel>b\<parallel> = 1"
  shows "circuit_mat (2 ^ s) (bprep_gates s b) *\<^sub>v unit_vec (2 ^ s) 0 = b"
    and "\<And>U. U \<in> set (bprep_gates s b) \<Longrightarrow> elementary (2 ^ s) U"
    and "circuit_mat (2 ^ s) (bprep_gates s b) \<in> carrier_mat (2 ^ s) (2 ^ s)"
    and "Quantum.unitary (circuit_mat (2 ^ s) (bprep_gates s b))"
proof -
  let ?a = "\<lambda>x. cmod (b $ x)" and ?P = "prep_gates s (\<lambda>x. cmod (b $ x))" and ?D = "diag_gates (s - 1) (\<lambda>x. Arg (b $ x))"
  have S: "Suc (s - 1) = s" using s by simp
  have n: "(\<Sum>x<2 ^ s. (?a x)\<^sup>2) = 1"
  proof -
    have "sqrt (\<Sum>x<2 ^ s. (?a x)\<^sup>2) = 1" using b unfolding cpx_vec_length_def by simp
    thus ?thesis by simp
  qed
  note sp = state_prep[OF n norm_ge_zero]
  have eD: "\<And>U. U \<in> set ?D \<Longrightarrow> elementary (2 ^ s) U" using diag_gates_elementary[of _ "s - 1"] S by metis
  show el: "\<And>U. U \<in> set (bprep_gates s b) \<Longrightarrow> elementary (2 ^ s) U"
    unfolding bprep_gates_def using sp(2) eD by auto
  show "circuit_mat (2 ^ s) (bprep_gates s b) \<in> carrier_mat (2 ^ s) (2 ^ s)"
    "Quantum.unitary (circuit_mat (2 ^ s) (bprep_gates s b))" using circuit_elementary_unitary[OF el] by blast+
  have Pc: "\<And>U. U \<in> set ?P \<Longrightarrow> U \<in> carrier_mat (2 ^ s) (2 ^ s)" using sp(2) elementary_unitary(1) by blast
  have Dc: "\<And>U. U \<in> set ?D \<Longrightarrow> U \<in> carrier_mat (2 ^ s) (2 ^ s)" using eD elementary_unitary(1) by blast
  have cP: "circuit_mat (2 ^ s) ?P \<in> carrier_mat (2 ^ s) (2 ^ s)" by (rule circuit_mat_carrier[OF Pc])
  have cD: "circuit_mat (2 ^ s) ?D = dmat (2 ^ s) (\<lambda>x. Arg (b $ x))" using diag_gates_circuit[of "s - 1"] S by metis
  have ap: "circuit_mat (2 ^ s) (?P @ ?D) = circuit_mat (2 ^ s) ?D * circuit_mat (2 ^ s) ?P"
    by (rule circuit_mat_append) (use Pc Dc in auto)
  have "circuit_mat (2 ^ s) (bprep_gates s b) *\<^sub>v unit_vec (2 ^ s) 0 = (dmat (2 ^ s) (\<lambda>x. Arg (b $ x)) * circuit_mat (2 ^ s) ?P) *\<^sub>v unit_vec (2 ^ s) 0"
    unfolding bprep_gates_def ap cD ..
  also have "\<dots> = dmat (2 ^ s) (\<lambda>x. Arg (b $ x)) *\<^sub>v (circuit_mat (2 ^ s) ?P *\<^sub>v unit_vec (2 ^ s) 0)"
    by (rule assoc_mult_mat_vec[OF dmat_carrier cP]) simp
  also have "\<dots> = Matrix.vec (2 ^ s) (\<lambda>x. cis (Arg (b $ x)) * complex_of_real (cmod (b $ x)))"
    unfolding sp(1) by (simp add: dmat_mult_vec) (rule eq_vecI, simp_all)
  also have "\<dots> = b"
    by (rule eq_vecI) (use b(1) in \<open>simp_all add: Groups.mult.commute[of "cis _"] rcis_cmod_Arg flip: rcis_def\<close>)
  finally show "circuit_mat (2 ^ s) (bprep_gates s b) *\<^sub>v unit_vec (2 ^ s) 0 = b" .
qed


subsection \<open>Refining the HHL gate lists\<close>

lemma prep_gate_circuit:
  assumes G: "\<And>U. U \<in> set G \<Longrightarrow> U \<in> carrier_mat m m" and m: "0 < m" and N: "0 < N"
  shows "circuit_mat (N * (m * 2)) (map (prep_gate N) G) = prep_gate N (circuit_mat m G)"
proof -
  have e: "map (prep_gate N) G = map (\<lambda>U. 1\<^sub>m N \<Otimes> U) (map (\<lambda>U. U \<Otimes> 1\<^sub>m 2) G)" by (simp add: prep_gate_def)
  have "circuit_mat (N * (m * 2)) (map (\<lambda>U. 1\<^sub>m N \<Otimes> U) (map (\<lambda>U. U \<Otimes> 1\<^sub>m 2) G))
                 = 1\<^sub>m N \<Otimes> circuit_mat (m * 2) (map (\<lambda>U. U \<Otimes> 1\<^sub>m 2) G)"
    by (rule circuit_mat_tensor_left) (use G m N tensor_carrier[OF _ one_carrier_mat, of _ m 2] in auto)
  also have "circuit_mat (m * 2) (map (\<lambda>U. U \<Otimes> 1\<^sub>m 2) G) = circuit_mat m G \<Otimes> 1\<^sub>m 2"
    by (rule circuit_mat_tensor_right) (use G m in auto)
  finally show ?thesis unfolding e prep_gate_def .
qed

lemma prep_gate_elementary: "elementary m U \<Longrightarrow> 0 < N \<Longrightarrow> elementary (N * (m * 2)) (prep_gate N U)"
  unfolding prep_gate_def by (rule elementary_left[OF elementary_right]) simp_all

text \<open>\<open>elem_refine k s b Us\<close>: the preparation of $\ket b$ and the ancilla rotations controlled
by the last clock qubit replaced by elementary gates.\<close>

definition elem_refine :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.vec \<Rightarrow> complex Matrix.mat list \<Rightarrow> complex Matrix.mat list" where
  "elem_refine k s b Us = concat (map (\<lambda>U. if U = prep_gate (2 ^ k) (circuit_mat (2 ^ s) (bprep_gates s b)) then map (prep_gate (2 ^ k)) (bprep_gates s b)
     else if (\<exists>a. U = cv0 k (2 ^ s) (Rot a)) then route k s U else [U]) Us)"

lemma elem_refine_props:
  assumes Us: "\<And>U. U \<in> set Us \<Longrightarrow> U \<in> carrier_mat (2 ^ k * (2 ^ s * 2)) (2 ^ k * (2 ^ s * 2)) \<and> Complex_Matrix.unitary U"
    and k: "1 \<le> k" and s: "1 \<le> s" and b: "dim_vec b = 2 ^ s" "\<parallel>b\<parallel> = 1"
  shows "circuit_mat (2 ^ k * (2 ^ s * 2)) (elem_refine k s b Us) = circuit_mat (2 ^ k * (2 ^ s * 2)) Us"
    and "\<And>W. W \<in> set (elem_refine k s b Us) \<Longrightarrow> W \<in> carrier_mat (2 ^ k * (2 ^ s * 2)) (2 ^ k * (2 ^ s * 2)) \<and> Complex_Matrix.unitary W"
    and "\<And>W. W \<in> set (elem_refine k s b Us) \<Longrightarrow> elementary (2 ^ k * (2 ^ s * 2)) W
           \<or> (W \<in> set Us \<and> W \<noteq> prep_gate (2 ^ k) (circuit_mat (2 ^ s) (bprep_gates s b)) \<and> (\<forall>a. W \<noteq> cv0 k (2 ^ s) (Rot a)))"
proof -
  let ?K = "2 ^ k * (2 ^ s * 2)" and ?P = "prep_gate (2 ^ k) (circuit_mat (2 ^ s) (bprep_gates s b))"
  let ?f = "\<lambda>U. if U = ?P then map (prep_gate (2 ^ k)) (bprep_gates s b) else if (\<exists>a. U = cv0 k (2 ^ s) (Rot a)) then route k s U else [U]"
  note bp = bprep[OF s b]
  have bc: "\<And>U. U \<in> set (bprep_gates s b) \<Longrightarrow> U \<in> carrier_mat (2 ^ s) (2 ^ s)" using bp(2) elementary_unitary(1) by blast
  have kind: "elementary ?K W \<or> (W \<in> set Us \<and> W \<noteq> ?P \<and> (\<forall>a. W \<noteq> cv0 k (2 ^ s) (Rot a)))" if W: "W \<in> set (elem_refine k s b Us)" for W
  proof -
    obtain U where U: "U \<in> set Us" and WU: "W \<in> set (?f U)" using W unfolding elem_refine_def set_concat set_map by blast
    show ?thesis
    proof (cases "U = ?P")
      case True
      then obtain G where "G \<in> set (bprep_gates s b)" "W = prep_gate (2 ^ k) G" using WU by auto
      thus ?thesis using prep_gate_elementary[OF bp(2)] by simp
    next
      case nP: False
      show ?thesis
      proof (cases "\<exists>a. U = cv0 k (2 ^ s) (Rot a)")
        case True
        then obtain a where a: "U = cv0 k (2 ^ s) (Rot a)" by blast
        have "W \<in> set (route k s (cv0 k (2 ^ s) (Rot a)))" using WU nP True a by simp
        thus ?thesis using route_cv0(2)[OF k Rot_carrier Rot_unitary] by blast
      next
        case False
        thus ?thesis using WU nP U by auto
      qed
    qed
  qed
  show ok: "\<And>W. W \<in> set (elem_refine k s b Us) \<Longrightarrow> W \<in> carrier_mat ?K ?K \<and> Complex_Matrix.unitary W"
  proof -
    fix W assume W: "W \<in> set (elem_refine k s b Us)"
    show "W \<in> carrier_mat ?K ?K \<and> Complex_Matrix.unitary W"
      using kind[OF W] Us elementary_unitary unitary_bridge by blast
  qed
  show "\<And>W. W \<in> set (elem_refine k s b Us) \<Longrightarrow> elementary ?K W \<or> (W \<in> set Us \<and> W \<noteq> ?P \<and> (\<forall>a. W \<noteq> cv0 k (2 ^ s) (Rot a)))"
    by (rule kind)
  have each: "circuit_mat ?K (?f U) = U" if U: "U \<in> set Us" for U
  proof (cases "U = ?P")
    case True
    have "circuit_mat ?K (map (prep_gate (2 ^ k)) (bprep_gates s b)) = ?P" by (rule prep_gate_circuit) (use bc in auto)
    thus ?thesis using True by simp
  next
    case nP: False
    show ?thesis
    proof (cases "\<exists>a. U = cv0 k (2 ^ s) (Rot a)")
      case True
      then obtain a where a: "U = cv0 k (2 ^ s) (Rot a)" by blast
      show ?thesis using nP True a route_cv0(1)[OF k Rot_carrier Rot_unitary] by simp
    next
      case False
      have "U \<in> carrier_mat ?K ?K" using Us[OF U] by blast
      thus ?thesis using nP False by simp
    qed
  qed
  have "circuit_mat ?K (elem_refine k s b Us) = circuit_mat ?K (map (circuit_mat ?K) (map ?f Us))"
    unfolding elem_refine_def by (rule circuit_mat_concat) (use ok in \<open>auto simp: elem_refine_def\<close>)
  also have "map (circuit_mat ?K) (map ?f Us) = Us" using each by (induction Us) auto
  finally show "circuit_mat ?K (elem_refine k s b Us) = circuit_mat ?K Us" .
qed

subsection \<open>HHL with every gate elementary apart from the oracle calls\<close>

text \<open>For $n=2^s$ and every normalised $b$, no preparation gate is assumed: in the exact-phase
program every gate is elementary or a controlled $U^{\pm2^j}$.\<close>

theorem hhl_elementary:
  fixes A :: "complex Matrix.mat" and b :: "complex Matrix.vec" and s k :: nat and t0 C :: real
  assumes A: "A \<in> carrier_mat (2 ^ s) (2 ^ s)" "Quantum_Computing_3_10.hermitian A" and s: "1 \<le> s" and k: "1 \<le> k" and t0: "0 < t0"
    and spec: "\<And>l. l \<in> herm_spectrum A \<Longrightarrow> \<exists>j. 0 < j \<and> j < 2 ^ k \<and> l = reg_eig t0 (2 ^ k) j"
    and b: "dim_vec b = 2 ^ s" "\<parallel>b\<parallel> = 1"
    and Cb: "\<And>j. j < 2 ^ k \<Longrightarrow> \<bar>C / reg_eig t0 (2 ^ k) j\<bar> \<le> 1"
  defines "K \<equiv> 2 ^ k * (2 ^ s * 2)"
    and "Gs \<equiv> elem_refine k s b (hhl_fine_gates A (circuit_mat (2 ^ s) (bprep_gates s b)) t0 k C)"
  shows "state_sig.hoare_total_correct [2 ^ k, 2 ^ s, 2] (complex_of_real (C\<^sup>2 * \<parallel>herm_inv A *\<^sub>v b\<parallel>\<^sup>2) \<cdot>\<^sub>m 1\<^sub>m K)
           (hhl_prog K Gs) (anc_proj K 1)"
    and "state_sig.hoare_total_correct [2 ^ k, 2 ^ s, 2] (1\<^sub>m K) (hhl_prog K Gs)
           (anc_proj K 0 + outer_prod (hhl_target A k b) (hhl_target A k b))"
    and "C \<noteq> 0 \<Longrightarrow> state_sig.hoare_total_correct [2 ^ k, 2 ^ s, 2] (1\<^sub>m K) (hhl_rus_prog K Gs)
           (outer_prod (hhl_target A k b) (hhl_target A k b))"
    and "\<And>U. U \<in> set Gs \<Longrightarrow> elementary K U
           \<or> (\<exists>j<k. U = ctrl_bit (2 ^ k) (2 ^ s * 2) j ((evolution A t0 \<Otimes> 1\<^sub>m 2) ^\<^sub>m 2 ^ j)
                   \<or> U = ctrl_bit (2 ^ k) (2 ^ s * 2) j (((evolution A t0 \<Otimes> 1\<^sub>m 2) ^\<^sub>m 2 ^ j)\<^sup>\<dagger>))"
proof -
  let ?Ub = "circuit_mat (2 ^ s) (bprep_gates s b)"
  note bp = bprep[OF s b]
  have Ub: "?Ub \<in> carrier_mat (2 ^ s) (2 ^ s)" "Quantum.unitary ?Ub" "?Ub *\<^sub>v unit_vec (2 ^ s) 0 = b"
    using bp by simp_all
  have n0: "0 < (2::nat) ^ s" by simp
  note fok = fine_gates_ok[OF A n0 k t0 spec Ub Cb]
  note fc = hhl_fine_circuit[OF A n0 k t0 spec Ub Cb]
  let ?F = "hhl_fine_gates A ?Ub t0 k C"
  have r1: "circuit_mat (2 ^ k * (2 ^ s * 2)) (elem_refine k s b ?F) = circuit_mat (2 ^ k * (2 ^ s * 2)) ?F"
    by (rule elem_refine_props(1)[OF _ k s b]) (rule fok)
  have r2: "\<And>W. W \<in> set (elem_refine k s b ?F) \<Longrightarrow> W \<in> carrier_mat (2 ^ k * (2 ^ s * 2)) (2 ^ k * (2 ^ s * 2)) \<and> Complex_Matrix.unitary W"
    by (rule elem_refine_props(2)[OF _ k s b]) (rule fok)
  have r3: "\<And>W. W \<in> set (elem_refine k s b ?F) \<Longrightarrow> elementary (2 ^ k * (2 ^ s * 2)) W
           \<or> (W \<in> set ?F \<and> W \<noteq> prep_gate (2 ^ k) ?Ub \<and> (\<forall>a. W \<noteq> cv0 k (2 ^ s) (Rot a)))"
    by (rule elem_refine_props(3)[OF _ k s b]) (rule fok)
  have ok: "\<And>U. U \<in> set Gs \<Longrightarrow> U \<in> carrier_mat (2 ^ k * (2 ^ s * 2)) (2 ^ k * (2 ^ s * 2)) \<and> Complex_Matrix.unitary U"
    unfolding Gs_def by (rule r2)
  have circ: "circuit_mat (2 ^ k * (2 ^ s * 2)) Gs = circuit_mat (2 ^ k * (2 ^ s * 2)) (hhl_gates A ?Ub t0 k C)"
    unfolding Gs_def r1 by (rule fc)
  show "state_sig.hoare_total_correct [2 ^ k, 2 ^ s, 2] (complex_of_real (C\<^sup>2 * \<parallel>herm_inv A *\<^sub>v b\<parallel>\<^sup>2) \<cdot>\<^sub>m 1\<^sub>m K)
           (hhl_prog K Gs) (anc_proj K 1)"
    unfolding K_def by (rule hhl_prog_success_total[OF A n0 k t0 spec Ub Cb ok circ])
  show "state_sig.hoare_total_correct [2 ^ k, 2 ^ s, 2] (1\<^sub>m K) (hhl_prog K Gs)
           (anc_proj K 0 + outer_prod (hhl_target A k b) (hhl_target A k b))"
    unfolding K_def by (rule hhl_prog_correct_total[OF A n0 k t0 spec Ub Cb ok circ])
  show "C \<noteq> 0 \<Longrightarrow> state_sig.hoare_total_correct [2 ^ k, 2 ^ s, 2] (1\<^sub>m K) (hhl_rus_prog K Gs)
           (outer_prod (hhl_target A k b) (hhl_target A k b))"
    unfolding K_def by (rule hhl_rus_prog_total[OF A n0 k t0 spec Ub Cb ok circ])
  fix U assume U: "U \<in> set Gs"
  have "elementary K U \<or> (U \<in> set (hhl_fine_gates A ?Ub t0 k C) \<and> U \<noteq> prep_gate (2 ^ k) ?Ub \<and> (\<forall>a. U \<noteq> cv0 k (2 ^ s) (Rot a)))"
    using r3[OF U[unfolded Gs_def]] unfolding K_def .
  moreover have "U \<in> set (hhl_fine_gates A ?Ub t0 k C) \<Longrightarrow> elementary K U
         \<or> (\<exists>j<k. U = ctrl_bit (2 ^ k) (2 ^ s * 2) j ((evolution A t0 \<Otimes> 1\<^sub>m 2) ^\<^sub>m 2 ^ j)
                 \<or> U = ctrl_bit (2 ^ k) (2 ^ s * 2) j (((evolution A t0 \<Otimes> 1\<^sub>m 2) ^\<^sub>m 2 ^ j)\<^sup>\<dagger>))
         \<or> U = prep_gate (2 ^ k) ?Ub \<or> (\<exists>a. U = cv0 k (2 ^ s) (Rot a))"
    unfolding K_def by (rule hhl_fine_gate_kinds[OF A n0 k t0 spec Ub Cb])
  ultimately show "elementary K U
           \<or> (\<exists>j<k. U = ctrl_bit (2 ^ k) (2 ^ s * 2) j ((evolution A t0 \<Otimes> 1\<^sub>m 2) ^\<^sub>m 2 ^ j)
                   \<or> U = ctrl_bit (2 ^ k) (2 ^ s * 2) j (((evolution A t0 \<Otimes> 1\<^sub>m 2) ^\<^sub>m 2 ^ j)\<^sup>\<dagger>))" by blast
qed

text \<open>The paper's regime: every gate is elementary or a call of the simulation $V$.\<close>

theorem hhl_apx_elementary:
  fixes A V :: "complex Matrix.mat" and b :: "complex Matrix.vec" and s k :: nat and t0 C \<theta> lmin \<epsilon> \<eta> :: real
  assumes A: "A \<in> carrier_mat (2 ^ s) (2 ^ s)" "Quantum_Computing_3_10.hermitian A" and s: "1 \<le> s" and t0: "0 < t0" and k: "1 \<le> k"
      and C: "0 < C" and th: "0 < \<theta>" "\<theta> < 1" and lmin: "2 * C / \<theta> \<le> lmin"
      and spec: "\<And>l. l \<in> herm_spectrum A \<Longrightarrow> lmin \<le> l \<and> t0 * l \<le> pi / 2"
      and b: "dim_vec b = 2 ^ s" "\<parallel>b\<parallel> = 1" and e: "0 < \<epsilon>"
      and NQ: "sqrt (8 * pi\<^sup>2 * (2 + pi\<^sup>2) * \<theta> ^ 4 / (t0\<^sup>2 * C\<^sup>2 * (1 - \<theta>\<^sup>2)) + 512 * pi ^ 6 / (t0 ^ 4 * lmin ^ 4)) / \<epsilon> \<le> real (2 ^ k)"
      and V: "V \<in> carrier_mat (2 ^ s) (2 ^ s)" "Quantum.unitary V" and Vc: "op_close (2 ^ s) \<eta> V (evolution A t0)" and eta: "0 \<le> \<eta>"
      and small: "\<epsilon> + 2 * real (2 ^ k - 1) * \<eta> \<le> C * t0 / pi"
  defines "K \<equiv> 2 ^ k * (2 ^ s * 2)"
    and "Gs \<equiv> elem_refine k s b (fine3_gates k (2 ^ s) (circuit_mat (2 ^ s) (bprep_gates s b)) (\<lambda>c. arcsin (clamp (C / reg_eig t0 (2 ^ k) c)))
                (qgates (2 ^ k) (2 ^ s * 2) (V \<Otimes> 1\<^sub>m 2) (hhl_full_prog A t0 (2 ^ k) C (win_prep_mat k (2 ^ s) (circuit_mat (2 ^ s) (bprep_gates s b))))))"
  shows "state_sig.hoare_total_correct [2 ^ k, 2 ^ s, 2] (complex_of_real ((C * t0 / pi)\<^sup>2 * (1 - (apx_e A b (2 ^ k) C \<epsilon> \<eta>)\<^sup>2)) \<cdot>\<^sub>m 1\<^sub>m K)
           (prog_meas K (anc_proj K) Gs) (outer_prod (apx_t A b (2 ^ k)) (apx_t A b (2 ^ k)))"
    and "state_sig.hoare_total_correct [2 ^ k, 2 ^ s, 2] (complex_of_real (1 - (apx_e A b (2 ^ k) C \<epsilon> \<eta>)\<^sup>2) \<cdot>\<^sub>m 1\<^sub>m K)
           (rus_meas K (anc_proj K) Gs) (outer_prod (apx_t A b (2 ^ k)) (apx_t A b (2 ^ k)))"
    and "\<And>U. U \<in> set Gs \<Longrightarrow> elementary K U \<or> (\<exists>P d. U = call_mat (2 ^ k) (2 ^ s * 2) (V \<Otimes> 1\<^sub>m 2) P d)"
proof -
  let ?Ub = "circuit_mat (2 ^ s) (bprep_gates s b)"
  let ?n = "2 ^ s :: nat" and ?\<theta>s = "\<lambda>c. arcsin (clamp (C / reg_eig t0 (2 ^ k) c))"
  let ?Us = "qgates (2 ^ k) (?n * 2) (V \<Otimes> 1\<^sub>m 2) (hhl_full_prog A t0 (2 ^ k) C (win_prep_mat k ?n ?Ub))"
  let ?G3 = "fine3_gates k ?n ?Ub ?\<theta>s ?Us"
  note bp = bprep[OF s b]
  have UbP: "?Ub \<in> carrier_mat ?n ?n" "Quantum.unitary ?Ub" "?Ub *\<^sub>v unit_vec ?n 0 = b" using bp by simp_all
  have N: "2 \<le> (2::nat) ^ k" using power_increasing[of 1 k "2::nat"] k by simp
  have n0: "0 < ?n" by simp
  interpret state_sig "[2 ^ k, 2 ^ s, 2]" .
  have dd: "d = K" by (simp add: d_def K_def)
  note wp = win_prep_gates_props[OF k n0 UbP]
  note P = wp(3,4,5)
  note ab = apx_basics[OF A t0 N C th lmin spec b e NQ V Vc eta P small]
  have g: "gates_ok K (hhl_full_prog A t0 (2 ^ k) C (win_prep_mat k ?n ?Ub))" unfolding K_def by (rule ab(4))
  have ok: "\<And>U. U \<in> set ?Us \<Longrightarrow> U \<in> carrier_mat (2 ^ k * (?n * 2)) (2 ^ k * (?n * 2)) \<and> Complex_Matrix.unitary U"
    using qgates_ok[OF ab(2,3), where c = "hhl_full_prog A t0 (2 ^ k) C (win_prep_mat k ?n ?Ub)"] g by (simp add: K_def)
  have ok3: "\<And>W. W \<in> set ?G3 \<Longrightarrow> W \<in> carrier_mat (2 ^ k * (?n * 2)) (2 ^ k * (?n * 2)) \<and> Complex_Matrix.unitary W"
    by (rule fine3_gates_props(2)[OF _ k n0 UbP]) (rule ok)
  note h3 = hhl_apx_fine3[OF A t0 k C th lmin spec b e NQ V Vc eta UbP small]
  have r1: "circuit_mat K (elem_refine k s b ?G3) = circuit_mat K ?G3"
    unfolding K_def by (rule elem_refine_props(1)[OF _ k s b]) (rule ok3)
  have r2: "\<And>W. W \<in> set (elem_refine k s b ?G3) \<Longrightarrow> W \<in> carrier_mat K K \<and> Complex_Matrix.unitary W"
    unfolding K_def by (rule elem_refine_props(2)[OF _ k s b]) (rule ok3)
  have r3: "\<And>W. W \<in> set (elem_refine k s b ?G3) \<Longrightarrow> elementary K W
           \<or> (W \<in> set ?G3 \<and> W \<noteq> prep_gate (2 ^ k) ?Ub \<and> (\<forall>a. W \<noteq> cv0 k ?n (Rot a)))"
    unfolding K_def by (rule elem_refine_props(3)[OF _ k s b]) (rule ok3)
  have d0: "0 < d" unfolding dd K_def by simp
  have okd: "\<And>U. U \<in> set ?G3 \<Longrightarrow> U \<in> carrier_mat d d \<and> Complex_Matrix.unitary U" using ok3 unfolding dd K_def .
  have okG: "\<And>U. U \<in> set Gs \<Longrightarrow> U \<in> carrier_mat d d \<and> Complex_Matrix.unitary U" using r2 unfolding dd Gs_def .
  have circ: "circuit_mat d Gs = circuit_mat d ?G3" using r1 unfolding dd Gs_def .
  have Mc: "anc_proj d 0 \<in> carrier_mat d d" by simp
  show "hoare_total_correct (complex_of_real ((C * t0 / pi)\<^sup>2 * (1 - (apx_e A b (2 ^ k) C \<epsilon> \<eta>)\<^sup>2)) \<cdot>\<^sub>m 1\<^sub>m K)
           (prog_meas K (anc_proj K) Gs) (outer_prod (apx_t A b (2 ^ k)) (apx_t A b (2 ^ k)))"
    using meas_transfer(1)[where Us = ?G3 and Us' = Gs and M = "anc_proj d", OF d0 okd okG circ Mc] h3(1) unfolding dd K_def by simp
  show "hoare_total_correct (complex_of_real (1 - (apx_e A b (2 ^ k) C \<epsilon> \<eta>)\<^sup>2) \<cdot>\<^sub>m 1\<^sub>m K)
           (rus_meas K (anc_proj K) Gs) (outer_prod (apx_t A b (2 ^ k)) (apx_t A b (2 ^ k)))"
    using meas_transfer(2)[where Us = ?G3 and Us' = Gs and M = "anc_proj d", OF d0 okd okG circ Mc] h3(2) unfolding dd K_def by simp
  fix U assume U: "U \<in> set Gs"
  have "elementary K U \<or> (U \<in> set ?G3 \<and> U \<noteq> prep_gate (2 ^ k) ?Ub \<and> (\<forall>a. U \<noteq> cv0 k ?n (Rot a)))"
    by (rule r3[OF U[unfolded Gs_def]])
  thus "elementary K U \<or> (\<exists>P d. U = call_mat (2 ^ k) (2 ^ s * 2) (V \<Otimes> 1\<^sub>m 2) P d)"
    using h3(3) unfolding K_def by blast
qed


subsection \<open>Exact universality\<close>

lemma mult_dmat_index:
  assumes Wm: "Wm \<in> carrier_mat N N" and i: "i < N" and l: "l < N"
  shows "(Wm * dmat N \<phi>) $$ (i, l) = Wm $$ (i, l) * cis (\<phi> l)"
proof -
  have "(Wm * dmat N \<phi>) $$ (i, l) = (\<Sum>u<N. Wm $$ (i, u) * (if u = l then cis (\<phi> u) else 0))"
    using Wm i l by (simp add: dmat_def mat_diag_def scalar_prod_def atLeast0LessThan cong: if_cong)
  also have "\<dots> = (\<Sum>u<N. if u = l then Wm $$ (i, l) * cis (\<phi> l) else 0)" by (rule sum.cong) auto
  finally show ?thesis using l by simp
qed

lemma conj_rank1_entry:
  assumes Wm: "Wm \<in> carrier_mat N N" "Wm * (Wm\<^sup>\<dagger>) = 1\<^sub>m N" and i: "i < N" and j: "j < N" and k: "k < N"
  shows "(Wm * dmat N (\<lambda>x. if x = k then \<theta> else 0) * (Wm\<^sup>\<dagger>)) $$ (i, j)
         = (if i = j then 1 else 0) + (cis \<theta> - 1) * Wm $$ (i, k) * cnj (Wm $$ (j, k))"
proof -
  let ?D = "dmat N (\<lambda>x. if x = k then \<theta> else 0)"
  have WD: "Wm * ?D \<in> carrier_mat N N" using Wm(1) by simp
  have "(Wm * ?D * (Wm\<^sup>\<dagger>)) $$ (i, j) = (\<Sum>l<N. (Wm * ?D) $$ (i, l) * Wm\<^sup>\<dagger> $$ (l, j))"
    using WD Wm(1) i j by (simp add: scalar_prod_def dagger_def atLeast0LessThan Matrix.row_def dmat_def mat_diag_def carrier_matD[OF WD] carrier_matD[OF Wm(1)])
  also have "\<dots> = (\<Sum>l<N. Wm $$ (i, l) * cnj (Wm $$ (j, l)) + (if l = k then (cis \<theta> - 1) * Wm $$ (i, k) * cnj (Wm $$ (j, k)) else 0))"
    by (rule sum.cong) (use Wm(1) i j in \<open>auto simp: mult_dmat_index dagger_def algebra_simps\<close>)
  also have "\<dots> = (\<Sum>l<N. Wm $$ (i, l) * cnj (Wm $$ (j, l))) + (cis \<theta> - 1) * Wm $$ (i, k) * cnj (Wm $$ (j, k))"
    using k by (simp add: sum.distrib)
  also have "(\<Sum>l<N. Wm $$ (i, l) * cnj (Wm $$ (j, l))) = (Wm * (Wm\<^sup>\<dagger>)) $$ (i, j)"
    using Wm(1) i j by (simp add: scalar_prod_def dagger_def atLeast0LessThan)
  finally show ?thesis using Wm(2) i j by simp
qed

lemma circuit_dmats: "circuit_mat N (map (\<lambda>k. dmat N (f k)) L) = dmat N (\<lambda>x. sum_list (map (\<lambda>k. f k x) L))"
proof (induction L)
  case Nil show ?case by (simp add: dmat_zero)
next
  case (Cons k L) thus ?case by (simp add: dmat_mult Groups.add.commute)
qed

lemma conj_circuit:
  assumes P: "P \<in> carrier_mat N N" "(P\<^sup>\<dagger>) * P = 1\<^sub>m N" "P * (P\<^sup>\<dagger>) = 1\<^sub>m N"
    and Ds: "\<And>D. D \<in> set Ds \<Longrightarrow> D \<in> carrier_mat N N"
  shows "P * circuit_mat N Ds * (P\<^sup>\<dagger>) = circuit_mat N (map (\<lambda>D. P * D * (P\<^sup>\<dagger>)) Ds)"
  using Ds
proof (induction Ds)
  case Nil show ?case using P by simp
next
  case (Cons D Ds)
  have Dc: "D \<in> carrier_mat N N" using Cons.prems by simp
  have Cc: "circuit_mat N Ds \<in> carrier_mat N N" by (rule circuit_mat_carrier) (use Cons.prems in auto)
  have Pd: "P\<^sup>\<dagger> \<in> carrier_mat N N" using P(1) by (rule dagger_carrier)
  have IH: "P * circuit_mat N Ds * (P\<^sup>\<dagger>) = circuit_mat N (map (\<lambda>D. P * D * (P\<^sup>\<dagger>)) Ds)" by (rule Cons.IH) (use Cons.prems in auto)
  have "P * circuit_mat N (D # Ds) * (P\<^sup>\<dagger>) = P * (circuit_mat N Ds * D) * (P\<^sup>\<dagger>)" by simp
  also have "\<dots> = (P * circuit_mat N Ds * (P\<^sup>\<dagger>)) * (P * D * (P\<^sup>\<dagger>))"
  proof -
    have "(P * circuit_mat N Ds * (P\<^sup>\<dagger>)) * (P * D * (P\<^sup>\<dagger>)) = P * circuit_mat N Ds * ((P\<^sup>\<dagger>) * P) * D * (P\<^sup>\<dagger>)"
      using P(1) Cc Pd Dc by (simp add: assoc_mult_mat[of _ N N _ N _ N])
    also have "\<dots> = P * (circuit_mat N Ds * D) * (P\<^sup>\<dagger>)" using P Cc Pd Dc by (simp add: assoc_mult_mat[of _ N N _ N _ N])
    finally show ?thesis by simp
  qed
  finally show ?case unfolding IH by simp
qed

text \<open>Exact universality: every unitary on $m\ge1$ qubits is a product of elementary gates.  By the
spectral theorem $U=\prod_k(I+(\lambda_k-1)p_kp_k^*)$; each factor is $Q_kD_kQ_k^*$ with $Q_k$ the
preparation circuit of the eigenvector $p_k$ and $D_k$ a phase on $\ket0$.\<close>

definition eig_gates :: "nat \<Rightarrow> complex Matrix.vec \<Rightarrow> real \<Rightarrow> complex Matrix.mat list" where
  "eig_gates m p \<theta> = rev (map dagger (bprep_gates m p)) @ diag_gates (m - 1) (\<lambda>x. if x = 0 then \<theta> else 0) @ bprep_gates m p"

lemma eig_gates:
  assumes m: "1 \<le> m" and p: "dim_vec p = 2 ^ m" "\<parallel>p\<parallel> = 1"
  shows "\<And>G. G \<in> set (eig_gates m p \<theta>) \<Longrightarrow> elementary (2 ^ m) G"
    and "\<And>i j. i < 2 ^ m \<Longrightarrow> j < 2 ^ m \<Longrightarrow> circuit_mat (2 ^ m) (eig_gates m p \<theta>) $$ (i, j)
           = (if i = j then 1 else 0) + (cis \<theta> - 1) * p $ i * cnj (p $ j)"
proof -
  let ?N = "2 ^ m :: nat" and ?Q = "circuit_mat (2 ^ m) (bprep_gates m p)" and ?E = "\<lambda>x. if x = 0 then \<theta> else 0"
  note bp = bprep[OF m p]
  have S: "Suc (m - 1) = m" using m by simp
  have eD: "\<And>G. G \<in> set (diag_gates (m - 1) ?E) \<Longrightarrow> elementary ?N G" using diag_gates_elementary[of _ "m - 1"] S by metis
  show el: "\<And>G. G \<in> set (eig_gates m p \<theta>) \<Longrightarrow> elementary ?N G"
    unfolding eig_gates_def using bp(2) eD elementary_dagger by auto
  have bc: "\<And>G. G \<in> set (bprep_gates m p) \<Longrightarrow> G \<in> carrier_mat ?N ?N" using bp(2) elementary_unitary(1) by blast
  have rc: "\<And>G. G \<in> set (rev (map dagger (bprep_gates m p))) \<Longrightarrow> G \<in> carrier_mat ?N ?N" using bc dagger_carrier by auto
  have dc: "\<And>G. G \<in> set (diag_gates (m - 1) ?E) \<Longrightarrow> G \<in> carrier_mat ?N ?N" using eD elementary_unitary(1) by blast
  have c1: "circuit_mat ?N (eig_gates m p \<theta>) = circuit_mat ?N (diag_gates (m - 1) ?E @ bprep_gates m p) * circuit_mat ?N (rev (map dagger (bprep_gates m p)))"
    unfolding eig_gates_def by (rule circuit_mat_append) (use rc dc bc in auto)
  have c2: "circuit_mat ?N (diag_gates (m - 1) ?E @ bprep_gates m p) = ?Q * circuit_mat ?N (diag_gates (m - 1) ?E)"
    by (rule circuit_mat_append) (use dc bc in auto)
  have cD: "circuit_mat ?N (diag_gates (m - 1) ?E) = dmat ?N ?E" using diag_gates_circuit[of "m - 1"] S by metis
  have cR: "circuit_mat ?N (rev (map dagger (bprep_gates m p))) = ?Q\<^sup>\<dagger>" by (rule circuit_mat_dagger[OF bc])
  have e: "circuit_mat ?N (eig_gates m p \<theta>) = ?Q * dmat ?N ?E * (?Q\<^sup>\<dagger>)" unfolding c1 c2 cD cR ..
  have QQ: "?Q * (?Q\<^sup>\<dagger>) = 1\<^sub>m ?N" using bp(3,4) unfolding Quantum.unitary_def by auto
  fix i j assume i: "i < ?N" and j: "j < ?N"
  have Qi: "?Q $$ (l, 0) = p $ l" if "l < ?N" for l
    using mult_unit_vec_index[OF bp(3) _ that, of 0] bp(1) by simp
  show "circuit_mat ?N (eig_gates m p \<theta>) $$ (i, j) = (if i = j then 1 else 0) + (cis \<theta> - 1) * p $ i * cnj (p $ j)"
    unfolding e using conj_rank1_entry[OF bp(3) QQ i j, of 0 \<theta>] Qi[OF i] Qi[OF j] by simp
qed

theorem exact_universality:
  assumes U: "U \<in> carrier_mat (2 ^ m) (2 ^ m)" "Quantum.unitary U" and m: "1 \<le> m"
  shows "\<exists>Gs. (\<forall>G \<in> set Gs. elementary (2 ^ m) G) \<and> circuit_mat (2 ^ m) Gs = U"
proof -
  let ?N = "2 ^ m :: nat"
  obtain es where es: "char_poly U = (\<Prod>e\<leftarrow>es. [:- e, 1:])" using complex_mat_char_poly_factorizable[OF U(1)] by blast
  obtain B P Q where BPQ: "unitary_schur_decomposition U es = (B, P, Q)" by (cases "unitary_schur_decomposition U es") auto
  have Uu: "Complex_Matrix.unitary U" by (rule unitary_bridge[OF U])
  have normal: "U * adjoint U = adjoint U * U" using unitary_simps[OF U(1) Uu] by simp
  note sd = normal_complex_mat_has_spectral_decomposition[OF U(1) normal es BPQ]
  have Pc: "P \<in> carrier_mat ?N ?N" and Bc: "B \<in> carrier_mat ?N ?N" and UPB: "U = P * B * adjoint P"
    using sd U(1) unfolding similar_mat_wit_def Let_def by auto
  have Pu: "Complex_Matrix.unitary P" and dB: "diagonal_mat B" using sd by blast+
  have PP: "adjoint P * P = 1\<^sub>m ?N" "P * adjoint P = 1\<^sub>m ?N" using unitary_simps[OF Pc Pu] by simp_all
  have aPc: "adjoint P \<in> carrier_mat ?N ?N" using Pc by (rule adjoint_dim)
  have B_eq: "B = adjoint P * U * P"
  proof (rule unitary_elim[OF Bc _ Pc Pu])
    show "adjoint P * U * P \<in> carrier_mat ?N ?N" using aPc U(1) Pc by simp
    have "P * (adjoint P * U * P) * adjoint P = (P * adjoint P) * U * (P * adjoint P)"
      using Pc aPc U(1) by (simp add: assoc_mult_mat[of _ ?N ?N _ ?N _ ?N])
    thus "P * B * adjoint P = P * (adjoint P * U * P) * adjoint P" using PP U(1) UPB by (simp add: left_mult_one_mat right_mult_one_mat)
  qed
  have Bu: "Complex_Matrix.unitary B"
    unfolding B_eq by (rule unitary_times_unitary[OF mult_carrier_mat[OF aPc U(1)] Pc unitary_times_unitary[OF aPc U(1) unitary_adjoint[OF Pc Pu] Uu] Pu])
  have BB: "B * adjoint B = 1\<^sub>m ?N" using unitary_simps[OF Bc Bu] by simp
  have Bk: "cmod (B $$ (k, k)) = 1" if k: "k < ?N" for k
  proof -
    have "1 = (B * adjoint B) $$ (k, k)" using BB k by simp
    also have "\<dots> = (\<Sum>l<?N. B $$ (k, l) * cnj (B $$ (k, l)))"
      using Bc k by (simp add: scalar_prod_def adjoint_eval atLeast0LessThan)
    also have "\<dots> = (\<Sum>l<?N. if l = k then B $$ (k, k) * cnj (B $$ (k, k)) else 0)"
      by (rule sum.cong) (use dB Bc k in \<open>auto simp: diagonal_mat_def\<close>)
    also have "\<dots> = complex_of_real ((cmod (B $$ (k, k)))\<^sup>2)" using k by (simp add: complex_mult_cnj cmod_power2 del: of_real_power)
    finally have "(cmod (B $$ (k, k)))\<^sup>2 = 1" by (metis of_real_eq_1_iff)
    thus ?thesis using norm_ge_zero[of "B $$ (k, k)"] by (auto simp: power2_eq_1_iff)
  qed
  define \<theta> where "\<theta> k = Arg (B $$ (k, k))" for k
  have Bd: "B = dmat ?N \<theta>"
  proof (rule eq_matI)
    fix i j assume "i < dim_row (dmat ?N \<theta>)" "j < dim_col (dmat ?N \<theta>)"
    hence ij: "i < ?N" "j < ?N" by (simp_all add: dmat_def mat_diag_def)
    show "B $$ (i, j) = dmat ?N \<theta> $$ (i, j)"
    proof (cases "i = j")
      case True
      have "B $$ (i, i) \<noteq> 0" using Bk[OF ij(1)] by auto
      hence "cis (\<theta> i) = B $$ (i, i)" unfolding \<theta>_def using Bk[OF ij(1)] by (simp add: cis_Arg sgn_div_norm)
      thus ?thesis using True ij by (simp add: dmat_def mat_diag_def)
    next
      case False thus ?thesis using dB Bc ij by (simp add: diagonal_mat_def dmat_def mat_diag_def)
    qed
  qed (use Bc in \<open>simp_all add: dmat_def mat_diag_def\<close>)
  define Ds where "Ds = map (\<lambda>k. dmat ?N (\<lambda>x. if x = k then \<theta> k else 0)) [0..<?N]"
  have cDs: "circuit_mat ?N Ds = B"
  proof -
    have "circuit_mat ?N Ds = dmat ?N (\<lambda>x. sum_list (map (\<lambda>k. if x = k then \<theta> k else 0) [0..<?N]))"
      unfolding Ds_def by (rule circuit_dmats)
    also have "\<dots> = dmat ?N \<theta>"
    proof (rule dmat_cong)
      fix x assume x: "x < ?N"
      have "sum_list (map (\<lambda>k. if x = k then \<theta> k else 0) [0..<?N]) = (\<Sum>k<?N. if x = k then \<theta> k else 0)"
        by (simp add: sum_list_sum_nth atLeast0LessThan)
      also have "\<dots> = \<theta> x" using x by simp
      finally show "sum_list (map (\<lambda>k. if x = k then \<theta> k else 0) [0..<?N]) = \<theta> x" .
    qed
    finally show ?thesis using Bd by simp
  qed
  have Pd: "P\<^sup>\<dagger> = adjoint P" by (simp add: dagger_eq_adjoint)
  have Uc: "U = circuit_mat ?N (map (\<lambda>D. P * D * (P\<^sup>\<dagger>)) Ds)"
  proof -
    have "U = P * circuit_mat ?N Ds * (P\<^sup>\<dagger>)" using UPB cDs Pd by simp
    also have "\<dots> = circuit_mat ?N (map (\<lambda>D. P * D * (P\<^sup>\<dagger>)) Ds)"
      by (rule conj_circuit) (use Pc PP Pd in \<open>auto simp: Ds_def\<close>)
    finally show ?thesis .
  qed
  define Gs where "Gs = concat (map (\<lambda>k. eig_gates m (Matrix.col P k) (\<theta> k)) [0..<?N])"
  have pk: "dim_vec (Matrix.col P k) = ?N" "\<parallel>Matrix.col P k\<parallel> = 1" if k: "k < ?N" for k
  proof -
    show "dim_vec (Matrix.col P k) = ?N" using Pc by simp
    have "(\<Sum>i<?N. (cmod (Matrix.col P k $ i))\<^sup>2) = 1"
    proof -
      have "complex_of_real (\<Sum>i<?N. (cmod (Matrix.col P k $ i))\<^sup>2) = (\<Sum>i<?N. cnj (P $$ (i, k)) * P $$ (i, k))"
        using Pc k by (simp add: complex_mult_cnj cmod_power2 Groups.mult.commute[of "cnj _"] del: of_real_power)
      also have "\<dots> = (adjoint P * P) $$ (k, k)" using Pc k by (simp add: scalar_prod_def adjoint_eval atLeast0LessThan)
      also have "\<dots> = 1" using PP k by simp
      finally show ?thesis by (metis of_real_eq_1_iff)
    qed
    thus "\<parallel>Matrix.col P k\<parallel> = 1" using Pc unfolding cpx_vec_length_def by simp
  qed
  have el: "\<forall>G \<in> set Gs. elementary ?N G" unfolding Gs_def using eig_gates(1)[OF m pk] by auto
  have each: "circuit_mat ?N (eig_gates m (Matrix.col P k) (\<theta> k)) = P * dmat ?N (\<lambda>x. if x = k then \<theta> k else 0) * (P\<^sup>\<dagger>)" if k: "k < ?N" for k
  proof (rule eq_matI)
    fix i j assume "i < dim_row (P * dmat ?N (\<lambda>x. if x = k then \<theta> k else 0) * (P\<^sup>\<dagger>))" "j < dim_col (P * dmat ?N (\<lambda>x. if x = k then \<theta> k else 0) * (P\<^sup>\<dagger>))"
    hence ij: "i < ?N" "j < ?N" using Pc by simp_all
    have PPd: "P * (P\<^sup>\<dagger>) = 1\<^sub>m ?N" using PP Pd by simp
    show "circuit_mat ?N (eig_gates m (Matrix.col P k) (\<theta> k)) $$ (i, j) = (P * dmat ?N (\<lambda>x. if x = k then \<theta> k else 0) * (P\<^sup>\<dagger>)) $$ (i, j)"
      unfolding eig_gates(2)[OF m pk[OF k] ij] conj_rank1_entry[OF Pc PPd ij k] using Pc ij k by simp
  next
    show "dim_row (circuit_mat ?N (eig_gates m (Matrix.col P k) (\<theta> k))) = dim_row (P * dmat ?N (\<lambda>x. if x = k then \<theta> k else 0) * (P\<^sup>\<dagger>))"
      "dim_col (circuit_mat ?N (eig_gates m (Matrix.col P k) (\<theta> k))) = dim_col (P * dmat ?N (\<lambda>x. if x = k then \<theta> k else 0) * (P\<^sup>\<dagger>))"
      using circuit_mat_carrier[of "eig_gates m (Matrix.col P k) (\<theta> k)" ?N] eig_gates(1)[OF m pk[OF k]] elementary_unitary(1) Pc by auto
  qed
  have "circuit_mat ?N Gs = circuit_mat ?N (map (circuit_mat ?N) (map (\<lambda>k. eig_gates m (Matrix.col P k) (\<theta> k)) [0..<?N]))"
    unfolding Gs_def by (rule circuit_mat_concat) (use eig_gates(1)[OF m pk] elementary_unitary(1) in auto)
  also have "map (circuit_mat ?N) (map (\<lambda>k. eig_gates m (Matrix.col P k) (\<theta> k)) [0..<?N]) = map (\<lambda>D. P * D * (P\<^sup>\<dagger>)) Ds"
    unfolding Ds_def using each by simp
  finally have "circuit_mat ?N Gs = U" using Uc by simp
  thus ?thesis using el by blast
qed

subsection \<open>Compiled HHL programs\<close>

lemma elementary_compile:
  assumes Us: "\<And>U. U \<in> set Us \<Longrightarrow> U \<in> carrier_mat (2 ^ q) (2 ^ q) \<and> Complex_Matrix.unitary U" and q: "1 \<le> q"
  shows "\<exists>Gs. (\<forall>G \<in> set Gs. elementary (2 ^ q) G) \<and> circuit_mat (2 ^ q) Gs = circuit_mat (2 ^ q) Us"
proof -
  let ?K = "2 ^ q :: nat" and ?C = "circuit_mat (2 ^ q) Us"
  have c: "?C \<in> carrier_mat ?K ?K" by (rule circuit_mat_carrier) (use Us in blast)
  interpret state_sig "[2 ^ q]" .
  have dd: "d = ?K" by (simp add: d_def)
  have "Complex_Matrix.unitary ?C" using circuit_mat_unitary[of Us] Us unfolding dd by blast
  hence r: "?C * Complex_Matrix.adjoint ?C = 1\<^sub>m ?K" using c unfolding Complex_Matrix.unitary_def inverts_mat_def by simp
  have l: "Complex_Matrix.adjoint ?C * ?C = 1\<^sub>m ?K" by (rule mat_mult_left_right_inverse[OF c adjoint_dim[OF c] r])
  have "Quantum.unitary ?C" using c r l unfolding Quantum.unitary_def dagger_eq_adjoint by simp
  thus ?thesis using exact_universality[OF c _ q] by blast
qed

text \<open>Every oracle call can itself be compiled: for $n=2^s$ there are exact-phase HHL programs in
which every gate is elementary.  Universality bounds no gate count, so the call counts above remain
the cost statements.\<close>

theorem hhl_compiled:
  fixes A :: "complex Matrix.mat" and b :: "complex Matrix.vec" and s k :: nat and t0 C :: real
  assumes A: "A \<in> carrier_mat (2 ^ s) (2 ^ s)" "Quantum_Computing_3_10.hermitian A" and s: "1 \<le> s" and k: "1 \<le> k" and t0: "0 < t0"
    and spec: "\<And>l. l \<in> herm_spectrum A \<Longrightarrow> \<exists>j. 0 < j \<and> j < 2 ^ k \<and> l = reg_eig t0 (2 ^ k) j"
    and b: "dim_vec b = 2 ^ s" "\<parallel>b\<parallel> = 1"
    and Cb: "\<And>j. j < 2 ^ k \<Longrightarrow> \<bar>C / reg_eig t0 (2 ^ k) j\<bar> \<le> 1"
  defines "K \<equiv> 2 ^ k * (2 ^ s * 2)"
  shows "\<exists>Gs. (\<forall>G \<in> set Gs. elementary K G)
     \<and> state_sig.hoare_total_correct [2 ^ k, 2 ^ s, 2] (complex_of_real (C\<^sup>2 * \<parallel>herm_inv A *\<^sub>v b\<parallel>\<^sup>2) \<cdot>\<^sub>m 1\<^sub>m K)
           (hhl_prog K Gs) (anc_proj K 1)
     \<and> state_sig.hoare_total_correct [2 ^ k, 2 ^ s, 2] (1\<^sub>m K) (hhl_prog K Gs)
           (anc_proj K 0 + outer_prod (hhl_target A k b) (hhl_target A k b))
     \<and> (C \<noteq> 0 \<longrightarrow> state_sig.hoare_total_correct [2 ^ k, 2 ^ s, 2] (1\<^sub>m K) (hhl_rus_prog K Gs)
           (outer_prod (hhl_target A k b) (hhl_target A k b)))"
proof -
  let ?Ub = "circuit_mat (2 ^ s) (bprep_gates s b)"
  note bp = bprep[OF s b]
  have Ub: "?Ub \<in> carrier_mat (2 ^ s) (2 ^ s)" "Quantum.unitary ?Ub" "?Ub *\<^sub>v unit_vec (2 ^ s) 0 = b"
    using bp by simp_all
  have n0: "0 < (2::nat) ^ s" by simp
  have K: "K = 2 ^ (k + s + 1)" unfolding K_def by (simp add: power_add)
  note fok = fine_gates_ok[OF A n0 k t0 spec Ub Cb]
  note fc = hhl_fine_circuit[OF A n0 k t0 spec Ub Cb]
  have fokK: "\<And>U. U \<in> set (hhl_fine_gates A ?Ub t0 k C) \<Longrightarrow> U \<in> carrier_mat (2 ^ (k + s + 1)) (2 ^ (k + s + 1)) \<and> Complex_Matrix.unitary U"
    using fok unfolding K[unfolded K_def] .
  obtain Gs where el: "\<forall>G \<in> set Gs. elementary (2 ^ (k + s + 1)) G"
    and cG: "circuit_mat (2 ^ (k + s + 1)) Gs = circuit_mat (2 ^ (k + s + 1)) (hhl_fine_gates A ?Ub t0 k C)"
    using elementary_compile[OF fokK] by auto
  have ok: "\<And>U. U \<in> set Gs \<Longrightarrow> U \<in> carrier_mat (2 ^ k * (2 ^ s * 2)) (2 ^ k * (2 ^ s * 2)) \<and> Complex_Matrix.unitary U"
    using el elementary_unitary unitary_bridge unfolding K[unfolded K_def, symmetric] by blast
  have circ: "circuit_mat (2 ^ k * (2 ^ s * 2)) Gs = circuit_mat (2 ^ k * (2 ^ s * 2)) (hhl_gates A ?Ub t0 k C)"
    using cG fc unfolding K[unfolded K_def, symmetric] by simp
  have "\<forall>G \<in> set Gs. elementary K G" using el unfolding K .
  moreover have "state_sig.hoare_total_correct [2 ^ k, 2 ^ s, 2] (complex_of_real (C\<^sup>2 * \<parallel>herm_inv A *\<^sub>v b\<parallel>\<^sup>2) \<cdot>\<^sub>m 1\<^sub>m K)
           (hhl_prog K Gs) (anc_proj K 1)"
    unfolding K_def by (rule hhl_prog_success_total[OF A n0 k t0 spec Ub Cb ok circ])
  moreover have "state_sig.hoare_total_correct [2 ^ k, 2 ^ s, 2] (1\<^sub>m K) (hhl_prog K Gs)
           (anc_proj K 0 + outer_prod (hhl_target A k b) (hhl_target A k b))"
    unfolding K_def by (rule hhl_prog_correct_total[OF A n0 k t0 spec Ub Cb ok circ])
  moreover have "C \<noteq> 0 \<longrightarrow> state_sig.hoare_total_correct [2 ^ k, 2 ^ s, 2] (1\<^sub>m K) (hhl_rus_prog K Gs)
           (outer_prod (hhl_target A k b) (hhl_target A k b))"
    unfolding K_def using hhl_rus_prog_total[OF A n0 k t0 spec Ub Cb ok circ] by blast
  ultimately show ?thesis by blast
qed

theorem hhl_apx_compiled:
  fixes A V :: "complex Matrix.mat" and b :: "complex Matrix.vec" and s k :: nat and t0 C \<theta> lmin \<epsilon> \<eta> :: real
  assumes A: "A \<in> carrier_mat (2 ^ s) (2 ^ s)" "Quantum_Computing_3_10.hermitian A" and s: "1 \<le> s" and t0: "0 < t0" and k: "1 \<le> k"
      and C: "0 < C" and th: "0 < \<theta>" "\<theta> < 1" and lmin: "2 * C / \<theta> \<le> lmin"
      and spec: "\<And>l. l \<in> herm_spectrum A \<Longrightarrow> lmin \<le> l \<and> t0 * l \<le> pi / 2"
      and b: "dim_vec b = 2 ^ s" "\<parallel>b\<parallel> = 1" and e: "0 < \<epsilon>"
      and NQ: "sqrt (8 * pi\<^sup>2 * (2 + pi\<^sup>2) * \<theta> ^ 4 / (t0\<^sup>2 * C\<^sup>2 * (1 - \<theta>\<^sup>2)) + 512 * pi ^ 6 / (t0 ^ 4 * lmin ^ 4)) / \<epsilon> \<le> real (2 ^ k)"
      and V: "V \<in> carrier_mat (2 ^ s) (2 ^ s)" "Quantum.unitary V" and Vc: "op_close (2 ^ s) \<eta> V (evolution A t0)" and eta: "0 \<le> \<eta>"
      and small: "\<epsilon> + 2 * real (2 ^ k - 1) * \<eta> \<le> C * t0 / pi"
  defines "K \<equiv> 2 ^ k * (2 ^ s * 2)"
  shows "\<exists>Gs. (\<forall>G \<in> set Gs. elementary K G)
     \<and> state_sig.hoare_total_correct [2 ^ k, 2 ^ s, 2] (complex_of_real ((C * t0 / pi)\<^sup>2 * (1 - (apx_e A b (2 ^ k) C \<epsilon> \<eta>)\<^sup>2)) \<cdot>\<^sub>m 1\<^sub>m K)
           (prog_meas K (anc_proj K) Gs) (outer_prod (apx_t A b (2 ^ k)) (apx_t A b (2 ^ k)))
     \<and> state_sig.hoare_total_correct [2 ^ k, 2 ^ s, 2] (complex_of_real (1 - (apx_e A b (2 ^ k) C \<epsilon> \<eta>)\<^sup>2) \<cdot>\<^sub>m 1\<^sub>m K)
           (rus_meas K (anc_proj K) Gs) (outer_prod (apx_t A b (2 ^ k)) (apx_t A b (2 ^ k)))"
proof -
  let ?Ub = "circuit_mat (2 ^ s) (bprep_gates s b)"
  let ?n = "2 ^ s :: nat" and ?\<theta>s = "\<lambda>c. arcsin (clamp (C / reg_eig t0 (2 ^ k) c))"
  let ?Us = "qgates (2 ^ k) (?n * 2) (V \<Otimes> 1\<^sub>m 2) (hhl_full_prog A t0 (2 ^ k) C (win_prep_mat k ?n ?Ub))"
  let ?G3 = "fine3_gates k ?n ?Ub ?\<theta>s ?Us"
  note bp = bprep[OF s b]
  have UbP: "?Ub \<in> carrier_mat ?n ?n" "Quantum.unitary ?Ub" "?Ub *\<^sub>v unit_vec ?n 0 = b" using bp by simp_all
  have N: "2 \<le> (2::nat) ^ k" using power_increasing[of 1 k "2::nat"] k by simp
  have n0: "0 < ?n" by simp
  have KK: "K = 2 ^ (k + s + 1)" unfolding K_def by (simp add: power_add)
  interpret state_sig "[2 ^ k, 2 ^ s, 2]" .
  have dd: "d = K" by (simp add: d_def K_def)
  note wp = win_prep_gates_props[OF k n0 UbP]
  note P = wp(3,4,5)
  note ab = apx_basics[OF A t0 N C th lmin spec b e NQ V Vc eta P small]
  have g: "gates_ok K (hhl_full_prog A t0 (2 ^ k) C (win_prep_mat k ?n ?Ub))" unfolding K_def by (rule ab(4))
  have ok: "\<And>U. U \<in> set ?Us \<Longrightarrow> U \<in> carrier_mat (2 ^ k * (?n * 2)) (2 ^ k * (?n * 2)) \<and> Complex_Matrix.unitary U"
    using qgates_ok[OF ab(2,3), where c = "hhl_full_prog A t0 (2 ^ k) C (win_prep_mat k ?n ?Ub)"] g by (simp add: K_def)
  have ok3: "\<And>W. W \<in> set ?G3 \<Longrightarrow> W \<in> carrier_mat (2 ^ k * (?n * 2)) (2 ^ k * (?n * 2)) \<and> Complex_Matrix.unitary W"
    by (rule fine3_gates_props(2)[OF _ k n0 UbP]) (rule ok)
  note h3 = hhl_apx_fine3[OF A t0 k C th lmin spec b e NQ V Vc eta UbP small]
  have ok3K: "\<And>W. W \<in> set ?G3 \<Longrightarrow> W \<in> carrier_mat (2 ^ (k + s + 1)) (2 ^ (k + s + 1)) \<and> Complex_Matrix.unitary W"
    using ok3 unfolding KK[unfolded K_def] .
  obtain Gs where el: "\<forall>G \<in> set Gs. elementary (2 ^ (k + s + 1)) G"
    and cG: "circuit_mat (2 ^ (k + s + 1)) Gs = circuit_mat (2 ^ (k + s + 1)) ?G3"
    using elementary_compile[OF ok3K] by auto
  have d0: "0 < d" unfolding dd K_def by simp
  have okd: "\<And>U. U \<in> set ?G3 \<Longrightarrow> U \<in> carrier_mat d d \<and> Complex_Matrix.unitary U" using ok3 unfolding dd K_def .
  have okG: "\<And>U. U \<in> set Gs \<Longrightarrow> U \<in> carrier_mat d d \<and> Complex_Matrix.unitary U"
    using el elementary_unitary unitary_bridge unfolding dd KK by blast
  have circ: "circuit_mat d Gs = circuit_mat d ?G3" using cG unfolding dd KK .
  have Mc: "anc_proj d 0 \<in> carrier_mat d d" by simp
  have "\<forall>G \<in> set Gs. elementary K G" using el unfolding KK .
  moreover have "hoare_total_correct (complex_of_real ((C * t0 / pi)\<^sup>2 * (1 - (apx_e A b (2 ^ k) C \<epsilon> \<eta>)\<^sup>2)) \<cdot>\<^sub>m 1\<^sub>m K)
           (prog_meas K (anc_proj K) Gs) (outer_prod (apx_t A b (2 ^ k)) (apx_t A b (2 ^ k)))"
    using meas_transfer(1)[where Us = ?G3 and Us' = Gs and M = "anc_proj d", OF d0 okd okG circ Mc] h3(1) unfolding dd K_def by simp
  moreover have "hoare_total_correct (complex_of_real (1 - (apx_e A b (2 ^ k) C \<epsilon> \<eta>)\<^sup>2) \<cdot>\<^sub>m 1\<^sub>m K)
           (rus_meas K (anc_proj K) Gs) (outer_prod (apx_t A b (2 ^ k)) (apx_t A b (2 ^ k)))"
    using meas_transfer(2)[where Us = ?G3 and Us' = Gs and M = "anc_proj d", OF d0 okd okG circ Mc] h3(2) unfolding dd K_def by simp
  ultimately show ?thesis by blast
qed

end

theory Clean_Ancillas
  imports Comparator_Gates
begin

section \<open>Gates on clean ancillas\<close>

text \<open>\<open>anc A N\<close> embeds $\ket v$ as $\ket 0\ket v$ (ancillas in the high wires).  A gate $U$ on
the large space stands for $G$ when $U\ket0\ket v = \ket0\,G\ket v$, i.e.\ $U \cdot \mathrm{anc} = \mathrm{anc} \cdot G$.\<close>

definition anc :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
  "anc A N = Matrix.mat (A * N) N (\<lambda>(r, c). if r = c then 1 else 0)"

lemma anc_carrier [simp]: "anc A N \<in> carrier_mat (A * N) N" by (simp add: anc_def)
lemma dim_anc [simp]: "dim_row (anc A N) = A * N" "dim_col (anc A N) = N" by (simp_all add: anc_def)

definition stands_for :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat \<Rightarrow> bool" where
  "stands_for A N U G \<longleftrightarrow> U \<in> carrier_mat (A * N) (A * N) \<and> G \<in> carrier_mat N N \<and> U * anc A N = anc A N * G"

lemma stands_for_iff:
  assumes U: "U \<in> carrier_mat (A * N) (A * N)" and G: "G \<in> carrier_mat N N" and A: "0 < A"
  shows "stands_for A N U G \<longleftrightarrow> (\<forall>r < A * N. \<forall>c < N. U $$ (r, c) = (if r < N then G $$ (r, c) else 0))"
proof -
  have N: "N \<le> A * N" using A by simp
  have l: "(U * anc A N) $$ (r, c) = U $$ (r, c)" if "r < A * N" "c < N" for r c
  proof -
    have col: "Matrix.col (anc A N) c = unit_vec (A * N) c"
      using that N by (intro eq_vecI) (auto simp: anc_def unit_vec_def)
    have cA: "c < A * N" using that(2) N by linarith
    have "(U * anc A N) $$ (r, c) = Matrix.row U r \<bullet> Matrix.col (anc A N) c"
      by (rule index_mult_mat) (use that U in auto)
    also have "\<dots> = Matrix.row U r $ c" unfolding col by (rule scalar_prod_right_unit[OF cA])
    finally show ?thesis using that U cA by simp
  qed
  have r: "(anc A N * G) $$ (r, c) = (if r < N then G $$ (r, c) else 0)" if "r < A * N" "c < N" for r c
  proof -
    have rw: "Matrix.row (anc A N) r = (if r < N then unit_vec N r else 0\<^sub>v N)"
      using that by (intro eq_vecI) (auto simp: anc_def unit_vec_def)
    have "(anc A N * G) $$ (r, c) = Matrix.row (anc A N) r \<bullet> Matrix.col G c"
      by (rule index_mult_mat) (use that G in auto)
    also have "\<dots> = (if r < N then G $$ (r, c) else 0)" unfolding rw using that G by auto
    finally show ?thesis .
  qed
  have "U * anc A N = anc A N * G \<longleftrightarrow> (\<forall>r < A * N. \<forall>c < N. (U * anc A N) $$ (r, c) = (anc A N * G) $$ (r, c))"
  proof
    assume e: "U * anc A N = anc A N * G"
    show "\<forall>r < A * N. \<forall>c < N. (U * anc A N) $$ (r, c) = (anc A N * G) $$ (r, c)" unfolding e by simp
  next
    assume h: "\<forall>r < A * N. \<forall>c < N. (U * anc A N) $$ (r, c) = (anc A N * G) $$ (r, c)"
    show "U * anc A N = anc A N * G"
    proof (rule eq_matI)
      fix i j assume "i < dim_row (anc A N * G)" "j < dim_col (anc A N * G)"
      hence "i < A * N" "j < N" using G by simp_all
      thus "(U * anc A N) $$ (i, j) = (anc A N * G) $$ (i, j)" using h by blast
    qed (use U G in simp_all)
  qed
  thus ?thesis using U G l r by (simp add: stands_for_def)
qed

lemma stands_for_lift:
  assumes G: "G \<in> carrier_mat N N" and A: "0 < A"
  shows "stands_for A N (1\<^sub>m A \<Otimes> G) G"
proof -
  have NA: "N \<le> A * N" using mult_le_mono1[of 1 A N] A by simp
  have U: "1\<^sub>m A \<Otimes> G \<in> carrier_mat (A * N) (A * N)" using G by simp
  have "(1\<^sub>m A \<Otimes> G) $$ (r, c) = (if r < N then G $$ (r, c) else 0)" if "r < A * N" "c < N" for r c
  proof -
    have "(1\<^sub>m A \<Otimes> G) $$ (r, c) = 1\<^sub>m A $$ (r div N, c div N) * G $$ (r mod N, c mod N)"
      using index_tensor_mat[of "1\<^sub>m A" A A G N N r c] that G A less_le_trans[OF that(2) NA] by simp
    moreover have "1\<^sub>m A $$ (r div N, 0) = (if r < N then 1 else 0)"
    proof -
      have N0: "0 < N" using that by simp
      have "r div N < A" using that N0 by (simp add: div_less_iff_less_mult)
      thus ?thesis using A N0 by (simp add: div_eq_0_iff)
    qed
    ultimately show ?thesis using that by auto
  qed
  thus ?thesis using stands_for_iff[OF U G A] by simp
qed

lemma stands_for_pmat:
  assumes f: "\<And>c. c < N \<Longrightarrow> f c = g c" and g: "\<And>c. c < N \<Longrightarrow> g c < N" and A: "0 < A"
  shows "stands_for A N (pmat (A * N) f) (pmat N g)"
proof -
  have "pmat (A * N) f $$ (r, c) = (if r < N then pmat N g $$ (r, c) else 0)" if "r < A * N" "c < N" for r c
    using that f[of c] g[of c] A by (auto simp: pmat_def less_le_trans[of c N "A * N"])
  thus ?thesis using stands_for_iff[OF pmat_carrier pmat_carrier A] by simp
qed

lemma stands_for_mult:
  assumes u: "stands_for A N U G" and v: "stands_for A N U2 G2"
  shows "stands_for A N (U2 * U) (G2 * G)"
proof -
  have c: "U \<in> carrier_mat (A * N) (A * N)" "G \<in> carrier_mat N N" "U2 \<in> carrier_mat (A * N) (A * N)" "G2 \<in> carrier_mat N N"
    and eu: "U * anc A N = anc A N * G" and ev: "U2 * anc A N = anc A N * G2"
    using u v by (simp_all add: stands_for_def)
  have "U2 * U * anc A N = U2 * (U * anc A N)" by (rule assoc_mult_mat[OF c(3) c(1) anc_carrier])
  also have "\<dots> = U2 * anc A N * G" unfolding eu by (rule assoc_mult_mat[OF c(3) anc_carrier c(2), symmetric])
  also have "\<dots> = anc A N * G2 * G" unfolding ev ..
  also have "\<dots> = anc A N * (G2 * G)" by (rule assoc_mult_mat[OF anc_carrier c(4) c(2)])
  finally show ?thesis using c by (simp add: stands_for_def mult_carrier_mat)
qed

lemma stands_for_circuit:
  assumes "list_all2 (stands_for A N) Us Gs"
  shows "stands_for A N (circuit_mat (A * N) Us) (circuit_mat N Gs)"
  using assms
proof (induction rule: list_all2_induct)
  case Nil
  have "1\<^sub>m (A * N) * anc A N = anc A N * 1\<^sub>m N"
    by (simp add: left_mult_one_mat[OF anc_carrier] right_mult_one_mat[OF anc_carrier])
  thus ?case by (simp add: stands_for_def)
next
  case (Cons U Us G Gs)
  thus ?case by (simp add: stands_for_mult)
qed

text \<open>The compiled comparator stands for \<open>cmp_gate\<close> on $2m+5$ clean ancillas.\<close>

lemma anc_size: "(2::nat) ^ (4 * m + 6) = 2 ^ (2 * m + 5) * (2 ^ m * 2 ^ m * 2)"
proof -
  have e: "4 * m + 6 = (2 * m + 5) + (2 * m + 1)" by simp
  have "(2::nat) ^ (4 * m + 6) = 2 ^ (2 * m + 5) * 2 ^ (2 * m + 1)" by (simp only: e power_add)
  thus ?thesis unfolding data_size .
qed

theorem cmp_compiled_stands_for:
  "stands_for (2 ^ (2 * m + 5)) (2 ^ m * 2 ^ m * 2) (circuit_mat (2 ^ (4 * m + 6)) (compile (4 * m + 6) (sort_flag m)))
     (cmp_gate (2 ^ m))"
proof -
  have ok: "\<forall>g \<in> set (sort_flag m). rg_ok (4 * m + 6) g" using sort_flag_ok by blast
  have "circuit_mat (2 ^ (4 * m + 6)) (compile (4 * m + 6) (sort_flag m)) = pmat (2 ^ (4 * m + 6)) (rcirc (sort_flag m))"
    by (rule compile_props(1)[OF ok])
  moreover have "stands_for (2 ^ (2 * m + 5)) (2 ^ m * 2 ^ m * 2) (pmat (2 ^ (2 * m + 5) * (2 ^ m * 2 ^ m * 2)) (rcirc (sort_flag m)))
      (pmat (2 ^ m * 2 ^ m * 2) (cmp_perm (2 ^ m)))"
    by (rule stands_for_pmat) (simp_all add: S_cmp_perm invol_lt[OF cmp_perm_invol])
  ultimately show ?thesis unfolding cmp_gate_def anc_size by simp
qed

end

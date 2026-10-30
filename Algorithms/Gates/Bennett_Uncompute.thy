theory Bennett_Uncompute
  imports Comparator_Scan
begin

section \<open>Compute, copy, uncompute\<close>

lemma flip_bit_commute: "flip_bit p (flip_bit q x) = flip_bit q (flip_bit p (x :: nat))"
  by (rule bit_eqI) (auto simp: bit_flip_bit_iff)

lemma rg_flip_other: "ob \<notin> wires g \<Longrightarrow> rg g (flip_bit ob w) = flip_bit ob (rg g w)"
  by (cases g) (auto simp: bit_flip_bit_iff flip_bit_commute)

lemma rcirc_flip_other: "\<forall>g \<in> set gs. ob \<notin> wires g \<Longrightarrow> rcirc gs (flip_bit ob w) = flip_bit ob (rcirc gs w)"
  by (induction gs arbitrary: w) (simp_all add: rg_flip_other)

text \<open>Bennett's trick: the result bit $r$ of $C$ is copied into an untouched bit $ob$, then $C$ is
undone.\<close>

text_raw \<open>
\begin{center}\normalfont
\begin{quantikz}[row sep=0.3cm, column sep=0.45cm]
\lstick{input} & \gate[3]{C}\qwbundle{} & \qw & \gate[3]{C^{-1}} & \qw \rstick{input}\\
\lstick{scratch $\ket{0}$} & \qwbundle{} & \qw & & \qw \rstick{$\ket{0}$}\\
\lstick{result $r$} & & \ctrl{1} & & \qw \\
\lstick{$ob$} & \qw & \targ{} & \qw & \qw \rstick{$ob \oplus r$}
\end{quantikz}
\end{center}
\<close>

lemma compute_copy_uncompute:
  assumes ok: "\<forall>g \<in> set C. rg_ok M g" and ob: "\<forall>g \<in> set C. ob \<notin> wires g" and ro: "r \<noteq> ob"
  shows "rcirc (C @ [CX r ob] @ rev C) z = (if bit (rcirc C z) r then flip_bit ob z else z)"
proof -
  have "\<forall>g \<in> set (rev C). ob \<notin> wires g" using ob by simp
  thus ?thesis
    using rcirc_rev[OF ok, of z] by (simp add: rcirc_append rcirc_flip_other)
qed

section \<open>The comparator\<close>


definition cmp_circ :: "nat \<Rightarrow> rgate list" where "cmp_circ m = NOT (ew m m) # cscan m m"

lemma length_comp: "length (cmp_circ m) = 5 * m + 1" by (simp add: cmp_circ_def length_scan)

text \<open>With the scratch bits clear, the comparator sets $r$ to $[y<x]$.\<close>

lemma comp_correct:
  fixes x y :: nat
  assumes x: "x < 2 ^ m" and y: "y < 2 ^ m"
      and zx: "\<And>j. j < m \<Longrightarrow> bit z (xw m j) \<longleftrightarrow> bit x j" and zy: "\<And>j. j < m \<Longrightarrow> bit z (yw j) \<longleftrightarrow> bit y j"
      and clear: "\<forall>k\<le>m. \<not> bit z (ew m k)" "\<forall>k<m. \<not> bit z (tw m k)" "\<not> bit z (rw m)"
  shows "bit (rcirc (cmp_circ m) z) (rw m) \<longleftrightarrow> y < x"
proof -
  let ?z = "flip_bit (ew m m) z"
  have hi: "\<not> bit x k" "\<not> bit y k" if "m \<le> k" for k
    using x y that by (simp_all add: bit_iff_odd div_less order_less_le_trans)
  have z1: "bit ?z (ew m m)" "\<not> bit ?z (rw m)" "\<forall>k<m. \<not> bit ?z (tw m k) \<and> \<not> bit ?z (ew m k)"
    and z2: "\<And>j. j < m \<Longrightarrow> bit ?z (xw m j) \<longleftrightarrow> bit x j" "\<And>j. j < m \<Longrightarrow> bit ?z (yw j) \<longleftrightarrow> bit y j"
    using clear zx zy by (auto simp: bit_flip_bit_iff pos_defs)
  have "bit (rcirc (cmp_circ m) z) (rw m) \<longleftrightarrow> (\<exists>j<m. bit x j \<and> \<not> bit y j \<and> (\<forall>k. j < k \<and> k < m \<longrightarrow> (bit x k \<longleftrightarrow> bit y k)))"
    unfolding cmp_circ_def rcirc_Cons rg.simps using scan_correct[of m m ?z] z1 z2 by (simp cong: conj_cong) blast
  also have "\<dots> \<longleftrightarrow> (\<exists>j. bit x j \<and> \<not> bit y j \<and> (\<forall>k>j. bit x k \<longleftrightarrow> bit y k))"
  proof
    assume "\<exists>j<m. bit x j \<and> \<not> bit y j \<and> (\<forall>k. j < k \<and> k < m \<longrightarrow> (bit x k \<longleftrightarrow> bit y k))"
    then obtain j where j: "j < m" "bit x j" "\<not> bit y j" "\<forall>k. j < k \<and> k < m \<longrightarrow> (bit x k \<longleftrightarrow> bit y k)" by blast
    have "bit x k \<longleftrightarrow> bit y k" if "j < k" for k
    proof (cases "k < m")
      case False thus ?thesis using hi by simp
    qed (use j that in blast)
    thus "\<exists>j. bit x j \<and> \<not> bit y j \<and> (\<forall>k>j. bit x k \<longleftrightarrow> bit y k)" using j by blast
  next
    assume "\<exists>j. bit x j \<and> \<not> bit y j \<and> (\<forall>k>j. bit x k \<longleftrightarrow> bit y k)"
    then obtain j where j: "bit x j" "\<not> bit y j" "\<forall>k>j. bit x k \<longleftrightarrow> bit y k" by blast
    have "j < m" using j(1) hi(1)[of j] by (cases "j < m") simp_all
    thus "\<exists>j<m. bit x j \<and> \<not> bit y j \<and> (\<forall>k. j < k \<and> k < m \<longrightarrow> (bit x k \<longleftrightarrow> bit y k))" using j by blast
  qed
  also have "\<dots> \<longleftrightarrow> y < x" by (rule less_iff_first_diff[symmetric])
  finally show ?thesis .
qed


end

theory Wire_Placement
  imports Wire_Gates
begin

section \<open>Moving circuits onto other wires\<close>

subsection \<open>Reversible circuits\<close>

text \<open>Renaming the wires of a reversible circuit by \<open>vs\<close> places its permutation on the wires \<open>vs\<close>.\<close>

lemma rg_rename_bits:
  assumes vs: "distinct vs" and g: "rg_ok (length vs) g"
  shows "\<And>p. p \<notin> set vs \<Longrightarrow> bit (rg (rename ((!) vs) g) y) p = bit y p"
    and "dig vs (rg (rename ((!) vs) g) y) = rg g (dig vs y)"
proof -
  have act: "active (rename ((!) vs) g) y = active g (dig vs y)" using g by (cases g) (simp_all add: bit_dig)
  have tg: "targ (rename ((!) vs) g) = vs ! targ g" by (cases g) simp_all
  have tK: "targ g < length vs" using g by (cases g) simp_all
  show "\<And>p. p \<notin> set vs \<Longrightarrow> bit (rg (rename ((!) vs) g) y) p = bit y p"
    using tK nth_mem[OF tK] by (auto simp: bit_rg tg)
  show "dig vs (rg (rename ((!) vs) g) y) = rg g (dig vs y)"
  proof (rule bit_eqI)
    fix l
    have "l < length vs \<Longrightarrow> vs ! l = vs ! targ g \<longleftrightarrow> l = targ g" using nth_eq_iff_index_eq[OF vs _ tK] by simp
    thus "bit (dig vs (rg (rename ((!) vs) g) y)) l \<longleftrightarrow> bit (rg g (dig vs y)) l"
      using tK by (auto simp: bit_dig bit_rg tg act)
  qed
qed

lemma rcirc_rename_bits:
  assumes vs: "distinct vs" and rs: "\<forall>g \<in> set rs. rg_ok (length vs) g"
  shows "\<And>p. p \<notin> set vs \<Longrightarrow> bit (rcirc (map (rename ((!) vs)) rs) y) p = bit y p"
    and "dig vs (rcirc (map (rename ((!) vs)) rs) y) = rcirc rs (dig vs y)"
proof -
  have "(\<forall>p. p \<notin> set vs \<longrightarrow> bit (rcirc (map (rename ((!) vs)) rs) y) p = bit y p)
      \<and> dig vs (rcirc (map (rename ((!) vs)) rs) y) = rcirc rs (dig vs y)"
    using rs
  proof (induction rs arbitrary: y)
    case (Cons g rs)
    have okg: "rg_ok (length vs) g" and okr: "\<forall>g \<in> set rs. rg_ok (length vs) g" using Cons.prems by simp_all
    note G = rg_rename_bits[OF vs okg] and IH = Cons.IH[OF okr]
    show ?case using IH G by simp
  qed simp
  thus "\<And>p. p \<notin> set vs \<Longrightarrow> bit (rcirc (map (rename ((!) vs)) rs) y) p = bit y p"
    and "dig vs (rcirc (map (rename ((!) vs)) rs) y) = rcirc rs (dig vs y)" by simp_all
qed

lemma rg_ok_rename:
  assumes vs: "distinct vs" "\<And>v. v \<in> set vs \<Longrightarrow> v < K" and g: "rg_ok (length vs) g"
  shows "rg_ok K (rename ((!) vs) g)"
  using g vs by (cases g) (auto simp: nth_eq_iff_index_eq)

theorem pmat_rename:
  assumes vs: "distinct vs" "\<And>v. v \<in> set vs \<Longrightarrow> v < K" and rs: "\<forall>g \<in> set rs. rg_ok (length vs) g"
  shows "pmat (2 ^ K) (rcirc (map (rename ((!) vs)) rs)) = wg K vs (pmat (2 ^ length vs) (rcirc rs))"
proof (rule eq_matI)
  let ?R = "rcirc (map (rename ((!) vs)) rs)"
  fix x y assume "x < dim_row (wg K vs (pmat (2 ^ length vs) (rcirc rs)))" "y < dim_col (wg K vs (pmat (2 ^ length vs) (rcirc rs)))"
  hence x: "x < 2 ^ K" and y: "y < 2 ^ K" by simp_all
  note B = rcirc_rename_bits[OF vs(1) rs]
  have ok: "\<forall>g \<in> set (map (rename ((!) vs)) rs). rg_ok K g" using rs rg_ok_rename[OF vs] by auto
  have Ry: "?R y < 2 ^ K" by (rule rcirc_lt[OF ok y])
  have rl: "rcirc rs (dig vs y) < 2 ^ length vs" by (rule rcirc_lt[OF rs dig_lt])
  have "x = ?R y \<longleftrightarrow> (\<forall>i<K. i \<notin> set vs \<longrightarrow> bit x i = bit y i) \<and> dig vs x = rcirc rs (dig vs y)"
  proof
    assume h: "(\<forall>i<K. i \<notin> set vs \<longrightarrow> bit x i = bit y i) \<and> dig vs x = rcirc rs (dig vs y)"
    show "x = ?R y"
    proof (rule bits_eq_nat[OF x Ry])
      fix i assume i: "i < K"
      show "bit x i = bit (?R y) i"
      proof (cases "i \<in> set vs")
        case True
        then obtain l where l: "l < length vs" "vs ! l = i" by (auto simp: in_set_conv_nth)
        have "bit (dig vs x) l = bit (dig vs (?R y)) l" using h B(2) by simp
        thus ?thesis using l by (simp add: bit_dig)
      qed (use h i B(1) in simp)
    qed
  qed (use B in auto)
  thus "pmat (2 ^ K) ?R $$ (x, y) = wg K vs (pmat (2 ^ length vs) (rcirc rs)) $$ (x, y)"
    using x y dig_lt[of vs] rl by (auto simp: pmat_def wg_index)
qed simp_all

corollary compile_rename:
  assumes vs: "distinct vs" "\<And>v. v \<in> set vs \<Longrightarrow> v < K" and rs: "\<forall>g \<in> set rs. rg_ok (length vs) g"
  shows "circuit_mat (2 ^ K) (compile K (map (rename ((!) vs)) rs)) = wg K vs (pmat (2 ^ length vs) (rcirc rs))"
    "\<forall>U \<in> set (compile K (map (rename ((!) vs)) rs)). elementary (2 ^ K) U"
    "length (compile K (map (rename ((!) vs)) rs)) \<le> length rs * (6 * K + 7)"
proof -
  have ok: "\<forall>g \<in> set (map (rename ((!) vs)) rs). rg_ok K g" using rs rg_ok_rename[OF vs] by auto
  note C = compile_props[OF ok]
  show "circuit_mat (2 ^ K) (compile K (map (rename ((!) vs)) rs)) = wg K vs (pmat (2 ^ length vs) (rcirc rs))"
    unfolding C(1) by (rule pmat_rename[OF vs rs])
  show "\<forall>U \<in> set (compile K (map (rename ((!) vs)) rs)). elementary (2 ^ K) U" by (rule C(2))
  show "length (compile K (map (rename ((!) vs)) rs)) \<le> length rs * (6 * K + 7)" using C(3) by simp
qed

subsection \<open>Circuits on clean ancillas\<close>

lemma dig_append: "dig (xs @ ys) x = dig xs x + 2 ^ length xs * dig ys x"
  by (induction xs) simp_all

text \<open>A circuit on $n$ data wires and $p$ clean ancillas above them, placed on wires \<open>vs\<close> of a
register of $R$ wires with $a$ clean ancillas above: the data wires go into the register, the
ancillas into the ancillas.\<close>

theorem stands_for_wg:
  assumes S: "stands_for (2 ^ p) (2 ^ n) U G" and vs: "distinct vs" "length vs = n + p"
    and lo: "\<And>l. l < n \<Longrightarrow> vs ! l < Kr" and hi: "\<And>l. l < p \<Longrightarrow> Kr \<le> vs ! (n + l) \<and> vs ! (n + l) < Kr + a"
  shows "stands_for (2 ^ a) (2 ^ Kr) (wg (Kr + a) vs U) (wg Kr (take n vs) G)"
proof -
  have Uc: "U \<in> carrier_mat (2 ^ (n + p)) (2 ^ (n + p))" and Gc: "G \<in> carrier_mat (2 ^ n) (2 ^ n)"
    using S by (simp_all add: stands_for_def power_add ac_simps)
  have KK: "(2::nat) ^ a * 2 ^ Kr = 2 ^ (Kr + a)" by (simp add: power_add)
  have SI: "\<And>u v. u < 2 ^ n * 2 ^ p \<Longrightarrow> v < 2 ^ n \<Longrightarrow> U $$ (u, v) = (if u < 2 ^ n then G $$ (u, v) else 0)"
    using S stands_for_iff[of U "2 ^ p" "2 ^ n" G] by (auto simp: stands_for_def ac_simps)
  have tn: "length (take n vs) = n" using vs(2) by simp
  have dvs: "dig vs z = dig (take n vs) z + 2 ^ n * dig (drop n vs) z" for z
    using dig_append[of "take n vs" "drop n vs" z] tn by simp
  have dr0: "dig (drop n vs) z = 0 \<longleftrightarrow> (\<forall>l<p. \<not> bit z (vs ! (n + l)))" for z
  proof -
    have "dig (drop n vs) z = 0 \<longleftrightarrow> (\<forall>l. \<not> bit (dig (drop n vs) z) l)" by (simp add: bit_eq_iff)
    also have "\<dots> \<longleftrightarrow> (\<forall>l<p. \<not> bit z (vs ! (n + l)))" using vs(2) by (auto simp: bit_dig)
    finally show ?thesis .
  qed
  have lowR: "\<forall>l<p. \<not> bit z (vs ! (n + l))" if z: "z < 2 ^ Kr" for z :: nat
  proof (intro allI impI)
    fix l assume "l < p"
    thus "\<not> bit z (vs ! (n + l))" using hi bit_above[OF z] by blast
  qed
  have tvs: "\<And>i. i < Kr \<Longrightarrow> i \<in> set vs \<longleftrightarrow> i \<in> set (take n vs)"
  proof -
    fix i assume i: "i < Kr"
    have "i \<in> set (drop n vs) \<Longrightarrow> False"
    proof -
      assume "i \<in> set (drop n vs)"
      then obtain l where "l < p" "vs ! (n + l) = i" using vs(2) by (auto simp: in_set_conv_nth)
      thus False using hi i by fastforce
    qed
    moreover have "set vs = set (take n vs) \<union> set (drop n vs)"
      using set_append[of "take n vs" "drop n vs"] by simp
    ultimately show "i \<in> set vs \<longleftrightarrow> i \<in> set (take n vs)" by blast
  qed
  have "\<forall>r < (2::nat) ^ a * 2 ^ Kr. \<forall>c < (2::nat) ^ Kr. wg (Kr + a) vs U $$ (r, c) = (if r < 2 ^ Kr then wg Kr (take n vs) G $$ (r, c) else 0)"
  proof (intro allI impI)
    fix r c :: nat assume r: "r < 2 ^ a * 2 ^ Kr" and c: "c < 2 ^ Kr"
    have r': "r < 2 ^ (Kr + a)" using r KK by simp
    have c': "c < 2 ^ (Kr + a)" using c less_le_trans[OF c power_increasing[of Kr "Kr + a" "2::nat"]] by simp
    have dc: "dig vs c = dig (take n vs) c" using dvs dr0 lowR[OF c] by simp
    have dcl: "dig vs c < 2 ^ n" using dc dig_lt[of "take n vs"] tn by simp
    have dl: "dig vs r < 2 ^ n * 2 ^ p" using dig_lt[of vs r] vs(2) by (simp add: power_add)
    have L: "wg (Kr + a) vs U $$ (r, c) = (if \<forall>i<Kr + a. i \<notin> set vs \<longrightarrow> bit r i = bit c i
        then (if dig vs r < 2 ^ n then G $$ (dig vs r, dig vs c) else 0) else 0)"
      unfolding wg_index[OF r' c'] using SI[OF dl dcl] by auto
    show "wg (Kr + a) vs U $$ (r, c) = (if r < 2 ^ Kr then wg Kr (take n vs) G $$ (r, c) else 0)"
    proof (cases "r < 2 ^ Kr")
      case True
      have dr: "dig vs r = dig (take n vs) r" using dvs dr0 lowR[OF True] by simp
      have cnd: "(\<forall>i<Kr + a. i \<notin> set vs \<longrightarrow> bit r i = bit c i) \<longleftrightarrow> (\<forall>i<Kr. i \<notin> set (take n vs) \<longrightarrow> bit r i = bit c i)"
      proof
        assume h: "\<forall>i<Kr + a. i \<notin> set vs \<longrightarrow> bit r i = bit c i"
        show "\<forall>i<Kr. i \<notin> set (take n vs) \<longrightarrow> bit r i = bit c i" using h tvs by auto
      next
        assume h: "\<forall>i<Kr. i \<notin> set (take n vs) \<longrightarrow> bit r i = bit c i"
        show "\<forall>i<Kr + a. i \<notin> set vs \<longrightarrow> bit r i = bit c i"
        proof (intro allI impI)
          fix i assume i: "i < Kr + a" "i \<notin> set vs"
          show "bit r i = bit c i"
          proof (cases "i < Kr")
            case False
            thus ?thesis using True c bit_above[of r Kr i] bit_above[of c Kr i] by auto
          qed (use h i tvs in auto)
        qed
      qed
      show ?thesis unfolding L wg_index[OF True c] dr dc cnd using True dig_lt[of "take n vs" r] tn by auto
    next
      case False
      then obtain i where i: "Kr \<le> i" "i < Kr + a" "bit r i"
      proof -
        have "\<not> (\<forall>i. Kr \<le> i \<longrightarrow> \<not> bit r i)"
        proof
          assume h: "\<forall>i. Kr \<le> i \<longrightarrow> \<not> bit r i"
          have "r = take_bit Kr r" by (rule bit_eqI) (use h not_le in \<open>auto simp: bit_take_bit_iff\<close>)
          thus False using False take_bit_nat_less_exp[of Kr r] by simp
        qed
        then obtain i where "Kr \<le> i" "bit r i" by blast
        moreover have "i < Kr + a"
        proof (rule ccontr)
          assume "\<not> i < Kr + a"
          thus False using bit_above[OF r', of i] \<open>bit r i\<close> by simp
        qed
        ultimately show ?thesis using that by blast
      qed
      have ci: "\<not> bit c i" using c i(1) bit_above[of c Kr i] by auto
      show ?thesis
      proof (cases "i \<in> set vs")
        case True
        then obtain l where l: "l < n + p" "vs ! l = i" using vs(2) by (auto simp: in_set_conv_nth)
        have "\<not> l < n" using lo l(2) i(1) by fastforce
        hence l': "l = n + (l - n)" "l - n < p" using l(1) by simp_all
        have "dig (drop n vs) r \<noteq> 0" using dr0[of r] i(3) l(2) l' by force
        hence "2 ^ n \<le> 2 ^ n * dig (drop n vs) r" by simp
        hence "\<not> dig vs r < 2 ^ n" using dvs[of r] by linarith
        thus ?thesis unfolding L using False by simp
      next
        case False
        hence "\<not> (\<forall>i<Kr + a. i \<notin> set vs \<longrightarrow> bit r i = bit c i)" using i ci by blast
        thus ?thesis unfolding L using \<open>\<not> r < 2 ^ Kr\<close> by auto
      qed
    qed
  qed
  moreover have "wg (Kr + a) vs U \<in> carrier_mat (2 ^ a * 2 ^ Kr) (2 ^ a * 2 ^ Kr)" using KK by simp
  moreover have "wg Kr (take n vs) G \<in> carrier_mat (2 ^ Kr) (2 ^ Kr)" by simp
  ultimately show ?thesis using stands_for_iff by simp
qed

end

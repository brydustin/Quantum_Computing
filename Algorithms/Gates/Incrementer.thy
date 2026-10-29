theory Incrementer
  imports Multi_Controlled_NOT
begin

section \<open>A reversible incrementer\<close>

text \<open>Adding $1$ flips bit $q$ exactly when all lower bits are set.  The circuit flips bit $i$
under a multi-controlled NOT on bits $0, \dots, i-1$, from the top bit down, with $m$ clean
ancillas above the $m$ data wires.\<close>

lemma bit_Suc_add_one: "bit (x + 1) q \<longleftrightarrow> bit x q \<noteq> (\<forall>l<q. bit x l)" for x :: nat
proof (induction q arbitrary: x)
  case 0
  show ?case by (simp add: bit_0)
next
  case (Suc q)
  have all: "(\<forall>l<Suc q. bit x l) \<longleftrightarrow> odd x \<and> (\<forall>l<q. bit (x div 2) l)"
    by (auto simp: less_Suc_eq_0_disj bit_0 bit_Suc)
  show ?case
  proof (cases "odd x")
    case True
    hence "(x + 1) div 2 = x div 2 + 1" by (auto elim: oddE)
    thus ?thesis using Suc.IH[of "x div 2"] True all by (simp add: bit_Suc)
  next
    case False
    hence "(x + 1) div 2 = x div 2" by (auto elim: evenE)
    thus ?thesis using False all by (simp add: bit_Suc)
  qed
qed

definition incr_gates :: "nat \<Rightarrow> nat \<Rightarrow> rgate list" where
  "incr_gates m i = concat (map (\<lambda>q. mcx (\<lambda>l. l) (\<lambda>l. m + l) q [q]) (rev [0..<i]))"

lemma incr_gates_Suc: "incr_gates m (Suc i) = mcx (\<lambda>l. l) (\<lambda>l. m + l) i [i] @ incr_gates m i"
  by (simp add: incr_gates_def)

lemma incr_ok:
  assumes q: "q < m"
  shows "ladder_ok (2 * m) (\<lambda>l. l) (\<lambda>l. m + l) q" "targets_ok (2 * m) (\<lambda>l. l) (\<lambda>l. m + l) q [q]"
  using q by (auto simp: ladder_ok_def inj_on_def targets_ok_def)

lemma incr_bits:
  assumes i: "i \<le> m" and x: "\<And>l. l < m \<Longrightarrow> \<not> bit x (m + l)"
  shows "bit (rcirc (incr_gates m i) x) q \<longleftrightarrow> (if q < i then bit x q \<noteq> (\<forall>l<q. bit x l) else bit x q)"
  using i x
proof (induction i arbitrary: x q)
  case 0
  show ?case by (simp add: incr_gates_def)
next
  case (Suc i)
  let ?y = "rcirc (mcx (\<lambda>l. l) (\<lambda>l. m + l) i [i]) x"
  have im: "i < m" using Suc.prems(1) by simp
  note ok = incr_ok[OF im]
  have xi: "\<And>l. l \<le> i \<Longrightarrow> \<not> bit x (m + l)" using Suc.prems(2) im by simp
  have y: "?y = (if \<forall>l<i. bit x l then flip_bit i x else x)" using mcx_rcirc[OF ok(1) xi ok(2)] by auto
  have yb: "bit ?y q' \<longleftrightarrow> (if q' = i \<and> (\<forall>l<i. bit x l) then \<not> bit x q' else bit x q')" for q'
    unfolding y by (auto simp: bit_flip_bit_iff)
  have ya: "\<And>l. l < m \<Longrightarrow> \<not> bit ?y (m + l)" using yb Suc.prems(2) im by auto
  have IH: "bit (rcirc (incr_gates m i) ?y) q \<longleftrightarrow> (if q < i then bit ?y q \<noteq> (\<forall>l<q. bit ?y l) else bit ?y q)"
    by (rule Suc.IH) (use Suc.prems(1) ya in auto)
  have "bit (rcirc (incr_gates m (Suc i)) x) q \<longleftrightarrow> bit (rcirc (incr_gates m i) ?y) q"
    by (simp add: incr_gates_Suc rcirc_append)
  also have "\<dots> \<longleftrightarrow> (if q < Suc i then bit x q \<noteq> (\<forall>l<q. bit x l) else bit x q)"
    unfolding IH by (auto simp: yb less_Suc_eq)
  finally show ?case .
qed

theorem incr_rcirc:
  assumes x: "x < 2 ^ m"
  shows "rcirc (incr_gates m m) x = (x + 1) mod 2 ^ m"
proof (rule bit_eqI)
  fix q
  have hi: "\<not> bit x q" if "m \<le> q" for q
  proof -
    have "x < 2 ^ q" using less_le_trans[OF x power_increasing[OF that, of "2::nat"]] by simp
    thus ?thesis by (simp add: bit_iff_odd)
  qed
  have xa: "\<And>l. l < m \<Longrightarrow> \<not> bit x (m + l)" using hi by simp
  show "bit (rcirc (incr_gates m m) x) q \<longleftrightarrow> bit ((x + 1) mod 2 ^ m) q"
    using incr_bits[OF order_refl xa, of q] hi[of q] bit_Suc_add_one[of x q]
    by (simp add: bit_take_bit_iff flip: take_bit_eq_mod)
qed

lemma incr_rg_ok:
  assumes i: "i \<le> m"
  shows "\<forall>g \<in> set (incr_gates m i). rg_ok (2 * m) g"
proof -
  have R: "\<forall>g \<in> set (mcx (\<lambda>l. l) (\<lambda>l. m + l) q [q]). rg_ok (2 * m) g" if "q < m" for q
    by (rule mcx_rg_ok[OF incr_ok(1)[OF that] incr_ok(2)[OF that]])
  show ?thesis
  proof
    fix g assume "g \<in> set (incr_gates m i)"
    then obtain q where q: "q < i" "g \<in> set (mcx (\<lambda>l. l) (\<lambda>l. m + l) q [q])" by (auto simp: incr_gates_def)
    have "q < m" using q(1) i by simp
    thus "rg_ok (2 * m) g" using R q(2) by blast
  qed
qed

lemma length_incr: "length (incr_gates m i) = i * (i + 2)"
proof (induction i)
  case (Suc i)
  thus ?case by (simp add: incr_gates_Suc length_mcx algebra_simps)
qed (simp add: incr_gates_def)

end

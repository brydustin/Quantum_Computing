theory Bit_Compare
  imports Reversible_Gates
begin

section \<open>Comparing numbers bit by bit\<close>

text \<open>$y<x$ iff $x$ has a $1$ at the highest bit where $x$ and $y$ differ.\<close>

lemma less_iff_first_diff:
  fixes x y :: nat
  shows "y < x \<longleftrightarrow> (\<exists>j. bit x j \<and> \<not> bit y j \<and> (\<forall>k>j. bit x k \<longleftrightarrow> bit y k))"
proof (induction x arbitrary: y rule: less_induct)
  case (less x)
  show ?case
  proof (cases "x div 2 = y div 2")
    case True
    have hi: "bit x (Suc k) \<longleftrightarrow> bit y (Suc k)" for k using True by (simp add: bit_Suc)
    have "y < x \<longleftrightarrow> odd x \<and> even y" using True by presburger
    also have "\<dots> \<longleftrightarrow> (\<exists>j. bit x j \<and> \<not> bit y j \<and> (\<forall>k>j. bit x k \<longleftrightarrow> bit y k))"
    proof
      assume "odd x \<and> even y"
      thus "\<exists>j. bit x j \<and> \<not> bit y j \<and> (\<forall>k>j. bit x k \<longleftrightarrow> bit y k)"
        using hi by (intro exI[of _ 0]) (auto simp: bit_0 gr0_conv_Suc)
    next
      assume "\<exists>j. bit x j \<and> \<not> bit y j \<and> (\<forall>k>j. bit x k \<longleftrightarrow> bit y k)"
      then obtain j where j: "bit x j" "\<not> bit y j" by blast
      have "j = 0" using j hi by (cases j) auto
      thus "odd x \<and> even y" using j by (simp add: bit_0)
    qed
    finally show ?thesis .
  next
    case False
    hence x0: "x \<noteq> 0 \<or> y \<noteq> 0" by auto
    have lt: "y < x \<longleftrightarrow> y div 2 < x div 2" using False by (auto dest: div_le_mono[of _ _ 2] simp: less_le)
    show ?thesis
    proof (cases "x = 0")
      case True thus ?thesis by (auto simp: bit_0)
    next
      case x: False
      have "x div 2 < x" using x by simp
      note IH = less.IH[OF this, of "y div 2"]
      have "y < x \<longleftrightarrow> (\<exists>j. bit (x div 2) j \<and> \<not> bit (y div 2) j \<and> (\<forall>k>j. bit (x div 2) k \<longleftrightarrow> bit (y div 2) k))"
        unfolding lt IH ..
      also have "\<dots> \<longleftrightarrow> (\<exists>j. bit x j \<and> \<not> bit y j \<and> (\<forall>k>j. bit x k \<longleftrightarrow> bit y k))"
      proof
        assume "\<exists>j. bit (x div 2) j \<and> \<not> bit (y div 2) j \<and> (\<forall>k>j. bit (x div 2) k \<longleftrightarrow> bit (y div 2) k)"
        then obtain j where j: "bit (x div 2) j" "\<not> bit (y div 2) j" "\<forall>k>j. bit (x div 2) k \<longleftrightarrow> bit (y div 2) k" by blast
        show "\<exists>j. bit x j \<and> \<not> bit y j \<and> (\<forall>k>j. bit x k \<longleftrightarrow> bit y k)"
        proof (intro exI[of _ "Suc j"] conjI allI impI)
          show "bit x (Suc j)" "\<not> bit y (Suc j)" using j by (simp_all add: bit_Suc)
          fix k assume "Suc j < k"
          then obtain k' where "k = Suc k'" "j < k'" by (cases k) auto
          thus "bit x k \<longleftrightarrow> bit y k" using j(3) by (simp add: bit_Suc)
        qed
      next
        assume "\<exists>j. bit x j \<and> \<not> bit y j \<and> (\<forall>k>j. bit x k \<longleftrightarrow> bit y k)"
        then obtain j where j: "bit x j" "\<not> bit y j" "\<forall>k>j. bit x k \<longleftrightarrow> bit y k" by blast
        have "j \<noteq> 0"
        proof
          assume "j = 0"
          hence "bit x (Suc k) \<longleftrightarrow> bit y (Suc k)" for k using j(3) by simp
          hence "x div 2 = y div 2" by (intro bit_eqI) (simp add: bit_Suc[symmetric])
          thus False using False by simp
        qed
        then obtain j' where "j = Suc j'" by (cases j) auto
        thus "\<exists>j. bit (x div 2) j \<and> \<not> bit (y div 2) j \<and> (\<forall>k>j. bit (x div 2) k \<longleftrightarrow> bit (y div 2) k)"
          using j by (intro exI[of _ j']) (auto simp: bit_Suc[symmetric])
      qed
      finally show ?thesis .
    qed
  qed
qed

end

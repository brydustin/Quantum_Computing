theory Comparator_Scan
  imports Bit_Compare
begin

section \<open>The comparator scan\<close>

text \<open>Layout for $m$-bit numbers: $y_i$ at bit $i+1$, $x_i$ at bit $m+1+i$, the flags
$e_i$ (``equal above $i$'') at $2m+1+i$, temporaries $t_i$ at $3m+2+i$, the result $r$ at $4m+2$.\<close>


definition yw :: "nat \<Rightarrow> nat" where "yw i = Suc i"
definition xw :: "nat \<Rightarrow> nat \<Rightarrow> nat" where "xw m i = m + 1 + i"
definition ew :: "nat \<Rightarrow> nat \<Rightarrow> nat" where "ew m i = 2 * m + 1 + i"
definition tw :: "nat \<Rightarrow> nat \<Rightarrow> nat" where "tw m i = 3 * m + 2 + i"
definition rw :: "nat \<Rightarrow> nat" where "rw m = 4 * m + 2"

text \<open>One bit: $y_i \gets x_i\oplus y_i$, $t_i \gets e_{i+1}\wedge d_i$, $r \mathrel{\oplus}= t_i\wedge x_i$,
$e_i \gets e_{i+1}\oplus t_i = e_{i+1}\wedge\neg d_i$.\<close>

definition cstep :: "nat \<Rightarrow> nat \<Rightarrow> rgate list" where
  "cstep m i = [CNOT (xw m i) (yw i), TOF (ew m (Suc i)) (yw i) (tw m i), TOF (tw m i) (xw m i) (rw m),
             CNOT (ew m (Suc i)) (ew m i), CNOT (tw m i) (ew m i)]"

fun cscan :: "nat \<Rightarrow> nat \<Rightarrow> rgate list" where
  "cscan m 0 = []"
| "cscan m (Suc i) = cstep m i @ cscan m i"

lemma length_scan: "length (cscan m i) = 5 * i"
  by (induction i) (simp_all add: cstep_def)

lemmas pos_defs = yw_def xw_def ew_def tw_def rw_def

text \<open>After the scan, $r$ records whether $x$ has a $1$ at the first difference below the flag.\<close>

lemma scan_correct:
  assumes "i \<le> m" and "\<forall>k<i. \<not> bit z (tw m k) \<and> \<not> bit z (ew m k)"
  shows "bit (rcirc (cscan m i) z) (rw m) \<longleftrightarrow>
         (bit z (rw m) \<noteq> (bit z (ew m i) \<and> (\<exists>j<i. bit z (xw m j) \<and> \<not> bit z (yw j) \<and>
            (\<forall>k. j < k \<and> k < i \<longrightarrow> (bit z (xw m k) \<longleftrightarrow> bit z (yw k))))))"
  using assms
proof (induction i arbitrary: z)
  case 0 thus ?case by simp
next
  case (Suc i)
  let ?z = "rcirc (cstep m i) z"
  let ?d = "bit z (xw m i) \<noteq> bit z (yw i)"
  have im: "i < m" using Suc.prems(1) by simp
  have zR: "bit ?z (rw m) \<longleftrightarrow> (bit z (rw m) \<noteq> (bit z (ew m (Suc i)) \<and> ?d \<and> bit z (xw m i)))"
   and zE: "bit ?z (ew m i) \<longleftrightarrow> bit z (ew m (Suc i)) \<and> \<not> ?d"
   and zX: "\<And>j. j < i \<Longrightarrow> bit ?z (xw m j) \<longleftrightarrow> bit z (xw m j)"
   and zY: "\<And>j. j < i \<Longrightarrow> bit ?z (yw j) \<longleftrightarrow> bit z (yw j)"
   and zTE: "\<forall>k<i. \<not> bit ?z (tw m k) \<and> \<not> bit ?z (ew m k)"
    using Suc.prems(2) im by (auto simp: cstep_def bit_flip_bit_iff pos_defs)
  have IH: "bit (rcirc (cscan m i) ?z) (rw m) \<longleftrightarrow>
         (bit ?z (rw m) \<noteq> (bit ?z (ew m i) \<and> (\<exists>j<i. bit ?z (xw m j) \<and> \<not> bit ?z (yw j) \<and>
            (\<forall>k. j < k \<and> k < i \<longrightarrow> (bit ?z (xw m k) \<longleftrightarrow> bit ?z (yw k))))))"
    using Suc.IH[of ?z] im zTE by simp
  have ex: "(\<exists>j<Suc i. bit z (xw m j) \<and> \<not> bit z (yw j) \<and> (\<forall>k. j < k \<and> k < Suc i \<longrightarrow> (bit z (xw m k) \<longleftrightarrow> bit z (yw k))))
       \<longleftrightarrow> (?d \<and> bit z (xw m i)) \<or> (\<not> ?d \<and> (\<exists>j<i. bit z (xw m j) \<and> \<not> bit z (yw j) \<and>
            (\<forall>k. j < k \<and> k < i \<longrightarrow> (bit z (xw m k) \<longleftrightarrow> bit z (yw k)))))"
    by (auto simp: less_Suc_eq)
  show ?case unfolding cscan.simps rcirc_append IH zR zE ex
    by (simp add: zX zY cong: conj_cong) blast
qed


end

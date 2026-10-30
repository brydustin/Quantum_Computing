theory Comparator_Scan
  imports Bit_Compare
begin

section \<open>The comparator scan\<close>

text \<open>Layout for $m$-bit numbers: $y_i$ at bit $i+1$, $x_i$ at bit $m+1+i$, the flags
$e_i$ (``equal above $i$'') at $2m+1+i$, temporaries $t_i$ at $3m+2+i$, the result $r$ at $4m+2$.\<close>

text_raw \<open>
\begin{center}\normalfont
\begin{tikzpicture}[x=0.82cm,y=0.9cm, blk/.style={draw, minimum height=0.7cm, anchor=west, font=\small}]
\node[blk, fill=gray!20, minimum width=0.82cm] at (0,0) {$b$};
\node[blk, fill=blue!15, minimum width=2.3cm] at (0.82,0) {$y_0\,\cdots\,y_{m-1}$};
\node[blk, fill=blue!30, minimum width=2.3cm] at (3.62,0) {$x_0\,\cdots\,x_{m-1}$};
\node[blk, fill=green!20, minimum width=2.3cm] at (6.42,0) {$e_0\,\cdots\,e_{m}$};
\node[blk, fill=orange!25, minimum width=2.3cm] at (9.22,0) {$t_0\,\cdots\,t_{m-1}$};
\node[blk, fill=red!25, minimum width=0.82cm] at (12.02,0) {$r$};
\foreach \x/\l in {0.41/0, 1.0/1, 3.8/m{+}1, 6.6/2m{+}1, 9.4/3m{+}2, 12.43/4m{+}2} {\node[font=\scriptsize] at (\x,-0.6) {$\l$};}
\end{tikzpicture}\\[0.2em]
{\small Wires of the comparator, low to high.}
\end{center}
\<close>


definition yw :: "nat \<Rightarrow> nat" where "yw i = Suc i"
definition xw :: "nat \<Rightarrow> nat \<Rightarrow> nat" where "xw m i = m + 1 + i"
definition ew :: "nat \<Rightarrow> nat \<Rightarrow> nat" where "ew m i = 2 * m + 1 + i"
definition tw :: "nat \<Rightarrow> nat \<Rightarrow> nat" where "tw m i = 3 * m + 2 + i"
definition rw :: "nat \<Rightarrow> nat" where "rw m = 4 * m + 2"

text \<open>One bit: $y_i \gets x_i\oplus y_i$, $t_i \gets e_{i+1}\wedge d_i$, $r \mathrel{\oplus}= t_i\wedge x_i$,
$e_i \gets e_{i+1}\oplus t_i = e_{i+1}\wedge\neg d_i$.\<close>

definition cstep :: "nat \<Rightarrow> nat \<Rightarrow> rgate list" where
  "cstep m i = [CX (xw m i) (yw i), TOF (ew m (Suc i)) (yw i) (tw m i), TOF (tw m i) (xw m i) (rw m),
             CX (ew m (Suc i)) (ew m i), CX (tw m i) (ew m i)]"

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

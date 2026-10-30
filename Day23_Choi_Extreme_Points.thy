(*  Title:   Day23_Choi_Extreme_Points.thy
    Author:  Dustin Bryant, after Vern Paulsen's lecture of 19 October 2011 (Day 23)
*)

theory Day23_Choi_Extreme_Points
  imports Day22_Minimal_Kraus
begin

section \<open>Day 23 (19 October 2011): Choi's Theorem 3, extreme points of UCP and CPTP\<close>

text \<open>Day 22 stated and Day 23 proves:
\begin{notestheorem}[Choi 3]
If $\Phi:M_n\to M_d$ is unital and completely positive, $\Phi(X)=\sum_{i=1}^rV_i^*XV_i$ with
$r=\crk(\Phi)$, then $\Phi$ is extreme in $UCP(M_n,M_d)$ if and only if
$\{V_i^*V_j:1\le i,j\le r\}\subseteq M_d$ is linearly independent.
\end{notestheorem}
\begin{notescor}
If $\Phi:M_d\to M_n$ is completely positive and trace preserving, $\Phi(X)=\sum_{i=1}^rV_iXV_i^*$
with $r=\crk(\Phi)$, then $\Phi$ is extreme in $CPTP(M_d,M_n)$ iff $\{V_i^*V_j\}$ is linearly
independent (apply the theorem to $\Phi^*$).
\end{notescor}
The notes' proof.  ($\Rightarrow$) If $\sum_{ij}\lambda_{ij}V_i^*V_j=0$ it suffices to treat
Hermitian $\mu=(\mu_{ij})$ with $-I\le\mu\le I$: writing $I\pm\mu=(\alpha_{ij})^*(\alpha_{ij})$ and
$W_i=\sum_j\alpha_{ij}V_j$ shows that $\psi_\pm(X)=\sum_iV_i^*XV_i\pm\sum_{ij}\mu_{ij}V_i^*XV_j$
are UCP with $\Phi=\tfrac12(\psi_++\psi_-)$, so extremality gives $\psi_+=\Phi$, and Choi 2
(unitary freedom) forces $I+\mu=U^*U=I$, i.e. $\mu=0$.  ($\Leftarrow$) If
$\Phi=\tfrac12(\psi_1+\psi_2)$ with $\psi_k(X)=\sum_pW_p^*XW_p$, Choi 2 gives
$W_p/\sqrt2=\sum_j\alpha_{pj}V_j$ with $U^*U=I_r$; unitality of $\psi_1$ and linear
independence of the $V_i^*V_j$ force $U_1^*U_1=\tfrac12I_r$, whence $\psi_1=\Phi=\psi_2$.
Examples: $X\mapsto U^*XU$ is extreme; $\tfrac12(U_1^*XU_1+U_2^*XU_2)$, $X\mapsto\tr(X)I_d$
and $X\mapsto\diag(X)$ are not.

The formalisation proves the corollary first, for maps $\Phi(X)=\sum_iV_iXV_i^*$ with a fixed
linearly independent Kraus list (what $r=\crk(\Phi)$ gives, Day 22), and the theorem from it by
duality.  Everything goes through the quadratic Kraus maps $\psi_T(X)=\sum_{i,j}T_{ij}V_iXV_j^*$
and their Choi matrices $VTV^*$.  The direction ($\Rightarrow$) is the notes' perturbation
argument; for ($\Leftarrow$) a CP Radon--Nikodym theorem takes the place of Choi 2.  The
examples are in the next theory.\<close>

subsection \<open>Extreme points\<close>

text \<open>A point of a set $S$ of maps is extreme if it is not the midpoint of two other points of $S$.
Maps are compared on $M_n$: the two points are linear on $M_n$, and one of them differs from $\Phi$
at some matrix (then so does the other).  This defines the extreme points of
$\mathrm{CPTP}(M_n,M_d)$ and of $\mathrm{UCP}(M_n,M_d)$ at once.\<close>

definition midpoint_pair ::
  "nat \<Rightarrow> nat \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) set \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat)
     \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow> bool"
where
  "midpoint_pair n d S \<Phi> \<Phi>\<^sub>1 \<Phi>\<^sub>2 \<longleftrightarrow>
     \<Phi>\<^sub>1 \<in> S \<and> \<Phi>\<^sub>2 \<in> S \<and> lin_on n d (carrier_mat n n) \<Phi>\<^sub>1 \<and> lin_on n d (carrier_mat n n) \<Phi>\<^sub>2 \<and>
     (\<exists>X \<in> carrier_mat n n. \<Phi>\<^sub>1 X \<noteq> \<Phi> X) \<and>
     (\<forall>X \<in> carrier_mat n n. \<Phi> X = (1/2 :: complex) \<cdot>\<^sub>m \<Phi>\<^sub>1 X + (1/2 :: complex) \<cdot>\<^sub>m \<Phi>\<^sub>2 X)"

definition extreme_point ::
  "nat \<Rightarrow> nat \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) set \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow> bool"
where
  "extreme_point n d S \<Phi> \<longleftrightarrow> \<Phi> \<in> S \<and> \<not> (\<exists>\<Phi>\<^sub>1 \<Phi>\<^sub>2. midpoint_pair n d S \<Phi> \<Phi>\<^sub>1 \<Phi>\<^sub>2)"

abbreviation extreme_CPTP :: "nat \<Rightarrow> nat \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow> bool"
  where "extreme_CPTP n d \<equiv> extreme_point n d (CPTP n d)"

abbreviation extreme_UCP :: "nat \<Rightarrow> nat \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow> bool"
  where "extreme_UCP n d \<equiv> extreme_point n d (UCP n d)"

lemma midpoint_pair_cong:
  assumes "\<And>X. X \<in> carrier_mat n n \<Longrightarrow> \<Phi> X = \<Psi> X"
  shows "midpoint_pair n d S \<Phi> \<Phi>\<^sub>1 \<Phi>\<^sub>2 \<longleftrightarrow> midpoint_pair n d S \<Psi> \<Phi>\<^sub>1 \<Phi>\<^sub>2"
  using assms unfolding midpoint_pair_def by auto

text \<open>A Kraus representation of a channel, and what it gives.\<close>

definition cptp_kraus_rep ::
  "nat \<Rightarrow> nat \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow>
       complex Matrix.mat list \<Rightarrow> bool"
where
  "cptp_kraus_rep n d \<Phi> Vs \<equiv>
     kraus_operators n d Vs \<and>
     (\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi> X = kraus_map_dim d Vs X)"

lemma cptp_kraus_rep_facts:
  assumes "cptp_kraus_rep n d \<Phi> Vs"
  shows "\<forall>V \<in> set Vs. V \<in> carrier_mat d n" "sum_wdag_w n Vs = 1\<^sub>m n"
    "\<And>X. X \<in> carrier_mat n n \<Longrightarrow> \<Phi> X = kraus_map_dim d Vs X"
    "\<And>X. X \<in> carrier_mat n n \<Longrightarrow> \<Phi> X \<in> carrier_mat d d"
  using assms kraus_map_dim_carrier
  by (auto simp: cptp_kraus_rep_def kraus_operators_altdef)

subsection \<open>Quadratic Kraus maps\<close>

text \<open>The quadratic Kraus map of a list $V_1,\dots,V_k$ and a matrix $T\in M_k$ is
\[ \psi_T(X)=\sum_{i,j}T_{ij}\,V_iXV_j^*. \]
It is linear in $X$ and in $T$, and $\psi_I$ is the Kraus map of the list.\<close>

definition kraus_quad_map ::
  "nat \<Rightarrow> complex Matrix.mat list \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat"
where
  "kraus_quad_map d Vs T X = msum d d (\<lambda>(i, j). T $$ (i, j) \<cdot>\<^sub>m (Vs ! i * X * ((Vs ! j)\<^sup>\<dagger>)))
     (List.product [0..<length Vs] [0..<length Vs])"

lemma kraus_quad_map_dims [simp]:
  "dim_row (kraus_quad_map d Vs T X) = d" "dim_col (kraus_quad_map d Vs T X) = d"
  by (simp_all add: kraus_quad_map_def)

lemma kraus_list_nth:
  assumes "\<forall>V \<in> set Vs. V \<in> carrier_mat d n" and "i < length Vs"
  shows "Vs ! i \<in> carrier_mat d n" "dim_row (Vs ! i) = d" "dim_col (Vs ! i) = n"
  using assms by auto

lemma kraus_quad_term_carrier:
  assumes Vs: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n" and X: "X \<in> carrier_mat n n"
      and i: "i < length Vs" and j: "j < length Vs"
  shows "Vs ! i * X * ((Vs ! j)\<^sup>\<dagger>) \<in> carrier_mat d d"
  using mult_carrier_mat[OF mult_carrier_mat[OF kraus_list_nth(1)[OF Vs i] X]
                            dagger_carrier[OF kraus_list_nth(1)[OF Vs j]]] .

lemma kraus_quad_map_carrier:
  assumes Vs: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n" and X: "X \<in> carrier_mat n n"
  shows "kraus_quad_map d Vs T X \<in> carrier_mat d d"
  unfolding kraus_quad_map_def
  by (rule msum_pairs_carrier) (use kraus_quad_term_carrier[OF Vs X] in auto)

lemma kraus_quad_map_index:
  assumes Vs: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n" and X: "X \<in> carrier_mat n n"
      and r: "r < d" and c: "c < d"
  shows "kraus_quad_map d Vs T X $$ (r, c)
       = (\<Sum>i<length Vs. \<Sum>j<length Vs. T $$ (i, j) * (Vs ! i * X * ((Vs ! j)\<^sup>\<dagger>)) $$ (r, c))"
  unfolding kraus_quad_map_def
  by (subst msum_pairs_index)
     (use kraus_quad_term_carrier[OF Vs X] r c in \<open>auto intro!: sum.cong simp: kraus_list_nth[OF Vs]\<close>)

lemma kraus_quad_map_lin_on:
  assumes Vs: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
  shows "lin_on n d (carrier_mat n n) (kraus_quad_map d Vs T)"
  unfolding lin_on_def
proof (intro conjI ballI allI)
  fix A B :: "complex Matrix.mat" assume A: "A \<in> carrier_mat n n" and B: "B \<in> carrier_mat n n"
  have e: "(Vs ! i * (A + B) * ((Vs ! j)\<^sup>\<dagger>)) $$ (r, s)
         = (Vs ! i * A * ((Vs ! j)\<^sup>\<dagger>)) $$ (r, s) + (Vs ! i * B * ((Vs ! j)\<^sup>\<dagger>)) $$ (r, s)"
    if "i < length Vs" "j < length Vs" "r < d" "s < d" for i j r s
  proof -
    have Vi: "Vs ! i \<in> carrier_mat d n" using kraus_list_nth(1)[OF Vs that(1)] .
    have Vj: "(Vs ! j)\<^sup>\<dagger> \<in> carrier_mat n d" using dagger_carrier[OF kraus_list_nth(1)[OF Vs that(2)]] .
    have "Vs ! i * (A + B) * ((Vs ! j)\<^sup>\<dagger>)
        = Vs ! i * A * ((Vs ! j)\<^sup>\<dagger>) + Vs ! i * B * ((Vs ! j)\<^sup>\<dagger>)"
      using Vi Vj A B by (simp add: mult_add_distrib_mat add_mult_distrib_mat[of _ d n])
    thus ?thesis using carrier_matD[OF Vi] carrier_matD[OF Vj] A B that by simp
  qed
  show "kraus_quad_map d Vs T (A + B) = kraus_quad_map d Vs T A + kraus_quad_map d Vs T B"
  proof (rule eq_matI)
    fix r s assume "r < dim_row (kraus_quad_map d Vs T A + kraus_quad_map d Vs T B)"
      "s < dim_col (kraus_quad_map d Vs T A + kraus_quad_map d Vs T B)"
    hence r: "r < d" and s: "s < d" by auto
    have "kraus_quad_map d Vs T (A + B) $$ (r, s)
        = (\<Sum>i<length Vs. \<Sum>j<length Vs. T $$ (i, j) * (Vs ! i * A * ((Vs ! j)\<^sup>\<dagger>)) $$ (r, s)
                                       + T $$ (i, j) * (Vs ! i * B * ((Vs ! j)\<^sup>\<dagger>)) $$ (r, s))"
      by (simp only: kraus_quad_map_index[OF Vs add_carrier_mat[OF B] r s])
         (intro sum.cong refl, simp add: e r s distrib_left)
    also have "\<dots> = kraus_quad_map d Vs T A $$ (r, s) + kraus_quad_map d Vs T B $$ (r, s)"
      by (simp only: kraus_quad_map_index[OF Vs A r s] kraus_quad_map_index[OF Vs B r s] sum.distrib)
    also have "\<dots> = (kraus_quad_map d Vs T A + kraus_quad_map d Vs T B) $$ (r, s)"
      using r s by simp
    finally show "kraus_quad_map d Vs T (A + B) $$ (r, s)
        = (kraus_quad_map d Vs T A + kraus_quad_map d Vs T B) $$ (r, s)" .
  qed auto
next
  fix A :: "complex Matrix.mat" and c :: complex assume A: "A \<in> carrier_mat n n"
  have e: "(Vs ! i * (c \<cdot>\<^sub>m A) * ((Vs ! j)\<^sup>\<dagger>)) $$ (r, s) = c * (Vs ! i * A * ((Vs ! j)\<^sup>\<dagger>)) $$ (r, s)"
    if "i < length Vs" "j < length Vs" "r < d" "s < d" for i j r s
  proof -
    have Vi: "Vs ! i \<in> carrier_mat d n" using kraus_list_nth(1)[OF Vs that(1)] .
    have Vj: "(Vs ! j)\<^sup>\<dagger> \<in> carrier_mat n d" using dagger_carrier[OF kraus_list_nth(1)[OF Vs that(2)]] .
    have "Vs ! i * (c \<cdot>\<^sub>m A) * ((Vs ! j)\<^sup>\<dagger>) = c \<cdot>\<^sub>m (Vs ! i * A * ((Vs ! j)\<^sup>\<dagger>))"
      by (simp only: mult_smult_distrib[OF Vi A] mult_smult_assoc_mat[OF mult_carrier_mat[OF Vi A] Vj])
    thus ?thesis using carrier_matD[OF Vi] carrier_matD[OF Vj] A that by simp
  qed
  show "kraus_quad_map d Vs T (c \<cdot>\<^sub>m A) = c \<cdot>\<^sub>m kraus_quad_map d Vs T A"
  proof (rule eq_matI)
    fix r s assume "r < dim_row (c \<cdot>\<^sub>m kraus_quad_map d Vs T A)" "s < dim_col (c \<cdot>\<^sub>m kraus_quad_map d Vs T A)"
    hence r: "r < d" and s: "s < d" by auto
    have "kraus_quad_map d Vs T (c \<cdot>\<^sub>m A) $$ (r, s)
        = (\<Sum>i<length Vs. \<Sum>j<length Vs. c * (T $$ (i, j) * (Vs ! i * A * ((Vs ! j)\<^sup>\<dagger>)) $$ (r, s)))"
      by (simp only: kraus_quad_map_index[OF Vs smult_carrier_mat[OF A] r s])
         (intro sum.cong refl, simp add: e r s mult.left_commute)
    also have "\<dots> = c * kraus_quad_map d Vs T A $$ (r, s)"
      by (simp only: kraus_quad_map_index[OF Vs A r s] sum_distrib_left)
    also have "\<dots> = (c \<cdot>\<^sub>m kraus_quad_map d Vs T A) $$ (r, s)"
      using r s by simp
    finally show "kraus_quad_map d Vs T (c \<cdot>\<^sub>m A) $$ (r, s) = (c \<cdot>\<^sub>m kraus_quad_map d Vs T A) $$ (r, s)" .
  qed auto
qed (use kraus_quad_map_carrier[OF Vs] in auto)

lemma kraus_quad_map_coeff:
  assumes Vs: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n" and X: "X \<in> carrier_mat n n"
      and S: "S \<in> carrier_mat (length Vs) (length Vs)" and T: "T \<in> carrier_mat (length Vs) (length Vs)"
  shows "kraus_quad_map d Vs (a \<cdot>\<^sub>m S + b \<cdot>\<^sub>m T) X
       = a \<cdot>\<^sub>m kraus_quad_map d Vs S X + b \<cdot>\<^sub>m kraus_quad_map d Vs T X"
proof (rule eq_matI)
  fix r s assume "r < dim_row (a \<cdot>\<^sub>m kraus_quad_map d Vs S X + b \<cdot>\<^sub>m kraus_quad_map d Vs T X)"
    "s < dim_col (a \<cdot>\<^sub>m kraus_quad_map d Vs S X + b \<cdot>\<^sub>m kraus_quad_map d Vs T X)"
  hence r: "r < d" and s: "s < d" using kraus_quad_map_carrier[OF Vs X, where T = T] by auto
  have e: "(a \<cdot>\<^sub>m S + b \<cdot>\<^sub>m T) $$ (i, j) = a * S $$ (i, j) + b * T $$ (i, j)"
    if "i < length Vs" "j < length Vs" for i j
    using S T that by simp
  let ?e = "\<lambda>i j. (Vs ! i * X * ((Vs ! j)\<^sup>\<dagger>)) $$ (r, s)"
  have "kraus_quad_map d Vs (a \<cdot>\<^sub>m S + b \<cdot>\<^sub>m T) X $$ (r, s)
      = (\<Sum>i<length Vs. \<Sum>j<length Vs. a * (S $$ (i, j) * ?e i j) + b * (T $$ (i, j) * ?e i j))"
    by (simp only: kraus_quad_map_index[OF Vs X r s]) (intro sum.cong refl, simp add: e distrib_right mult.assoc)
  also have "\<dots> = a * kraus_quad_map d Vs S X $$ (r, s) + b * kraus_quad_map d Vs T X $$ (r, s)"
    by (simp only: kraus_quad_map_index[OF Vs X r s] sum.distrib sum_distrib_left mult.assoc)
  also have "\<dots> = (a \<cdot>\<^sub>m kraus_quad_map d Vs S X + b \<cdot>\<^sub>m kraus_quad_map d Vs T X) $$ (r, s)"
    using kraus_quad_map_carrier[OF Vs X, where T = S] kraus_quad_map_carrier[OF Vs X, where T = T] r s
    by simp
  finally show "kraus_quad_map d Vs (a \<cdot>\<^sub>m S + b \<cdot>\<^sub>m T) X $$ (r, s)
      = (a \<cdot>\<^sub>m kraus_quad_map d Vs S X + b \<cdot>\<^sub>m kraus_quad_map d Vs T X) $$ (r, s)" .
qed (use kraus_quad_map_carrier[OF Vs X, where T = S] kraus_quad_map_carrier[OF Vs X, where T = T] in auto)

lemma kraus_quad_map_smult:
  assumes Vs: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n" and X: "X \<in> carrier_mat n n"
      and T: "T \<in> carrier_mat (length Vs) (length Vs)"
  shows "kraus_quad_map d Vs (a \<cdot>\<^sub>m T) X = a \<cdot>\<^sub>m kraus_quad_map d Vs T X"
proof (rule eq_matI)
  fix r s assume "r < dim_row (a \<cdot>\<^sub>m kraus_quad_map d Vs T X)" "s < dim_col (a \<cdot>\<^sub>m kraus_quad_map d Vs T X)"
  hence r: "r < d" and s: "s < d" by auto
  have "kraus_quad_map d Vs (a \<cdot>\<^sub>m T) X $$ (r, s)
      = (\<Sum>i<length Vs. \<Sum>j<length Vs. a * (T $$ (i, j) * (Vs ! i * X * ((Vs ! j)\<^sup>\<dagger>)) $$ (r, s)))"
    by (simp only: kraus_quad_map_index[OF Vs X r s]) (intro sum.cong refl, use T in \<open>simp add: mult.assoc\<close>)
  also have "\<dots> = a * kraus_quad_map d Vs T X $$ (r, s)"
    by (simp only: kraus_quad_map_index[OF Vs X r s] sum_distrib_left)
  finally show "kraus_quad_map d Vs (a \<cdot>\<^sub>m T) X $$ (r, s) = (a \<cdot>\<^sub>m kraus_quad_map d Vs T X) $$ (r, s)"
    using r s by simp
qed auto

lemma kraus_quad_map_one:
  assumes Vs: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n" and X: "X \<in> carrier_mat n n"
  shows "kraus_quad_map d Vs (1\<^sub>m (length Vs)) X = kraus_map_dim d Vs X"
proof (rule eq_matI)
  fix r s assume "r < dim_row (kraus_map_dim d Vs X)" "s < dim_col (kraus_map_dim d Vs X)"
  hence r: "r < d" and s: "s < d" using kraus_map_dim_carrier[OF Vs X] by auto
  have "kraus_quad_map d Vs (1\<^sub>m (length Vs)) X $$ (r, s)
      = (\<Sum>i<length Vs. \<Sum>j<length Vs. (if i = j then (Vs ! i * X * ((Vs ! j)\<^sup>\<dagger>)) $$ (r, s) else 0))"
    by (simp only: kraus_quad_map_index[OF Vs X r s]) (intro sum.cong refl, simp)
  also have "\<dots> = (\<Sum>i<length Vs. (Vs ! i * X * ((Vs ! i)\<^sup>\<dagger>)) $$ (r, s))"
    by (intro sum.cong refl) simp
  also have "\<dots> = kraus_map_dim d Vs X $$ (r, s)"
    by (simp add: kraus_map_dim_entry_sum_list[OF Vs X r s] sum_list_sum_nth atLeast0LessThan)
  finally show "kraus_quad_map d Vs (1\<^sub>m (length Vs)) X $$ (r, s) = kraus_map_dim d Vs X $$ (r, s)" .
qed (use kraus_quad_map_carrier[OF Vs X, where T = "1\<^sub>m (length Vs)"] kraus_map_dim_carrier[OF Vs X] in auto)

subsubsection \<open>The Choi matrix\<close>

text \<open>The Choi matrix of $\psi_T$ is $VTV^*$, where the columns of $V$ are the vectorised $V_i$.\<close>

definition kraus_vec_mat :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat list \<Rightarrow> complex Matrix.mat"
  where "kraus_vec_mat d n Vs = mat_of_cols (n*d) (map (vec_of_kraus d n) Vs)"

lemma kraus_vec_mat_carrier [simp]: "kraus_vec_mat d n Vs \<in> carrier_mat (n*d) (length Vs)"
  by (simp add: kraus_vec_mat_def mat_of_cols_def)

lemma kraus_vec_mat_dims [simp]:
  "dim_row (kraus_vec_mat d n Vs) = n*d" "dim_col (kraus_vec_mat d n Vs) = length Vs"
  by (simp_all add: kraus_vec_mat_def)

lemma kraus_vec_mat_index:
  assumes "r < n*d" and "k < length Vs"
  shows "kraus_vec_mat d n Vs $$ (r, k) = Vs ! k $$ (r mod d, r div d)"
  using assms by (simp add: kraus_vec_mat_def mat_of_cols_def vec_of_kraus_index)

lemma choi_matrix_kraus_quad_map:
  assumes Vs: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n" and T: "T \<in> carrier_mat (length Vs) (length Vs)"
      and n: "0 < n" and d: "0 < d"
  shows "choi_matrix n d (kraus_quad_map d Vs T) = kraus_vec_mat d n Vs * T * ((kraus_vec_mat d n Vs)\<^sup>\<dagger>)"
proof (rule eq_matI)
  let ?M = "kraus_vec_mat d n Vs" and ?k = "length Vs"
  have M: "?M \<in> carrier_mat (n*d) ?k" by simp
  fix r c assume "r < dim_row (?M * T * (?M\<^sup>\<dagger>))" "c < dim_col (?M * T * (?M\<^sup>\<dagger>))"
  hence r: "r < n*d" and c: "c < n*d" by auto
  have rd: "r div d < n" "r mod d < d" and cd: "c div d < n" "c mod d < d"
    using r c d by (auto simp: less_mult_imp_div_less mult.commute)
  have "choi_matrix n d (kraus_quad_map d Vs T) $$ (r, c)
      = kraus_quad_map d Vs T (mat_unit (r div d) (c div d) n n) $$ (r mod d, c mod d)"
    using r c by (simp add: choi_matrix_def)
  also have "\<dots> = (\<Sum>i<?k. \<Sum>j<?k. T $$ (i, j) * (Vs ! i $$ (r mod d, r div d) * cnj (Vs ! j $$ (c mod d, c div d))))"
    using rd cd
    by (simp only: kraus_quad_map_index[OF Vs mat_unit_carrier rd(2) cd(2)])
       (auto intro!: sum.cong simp: sandwich_mat_unit_entry[OF kraus_list_nth(1)[OF Vs] kraus_list_nth(1)[OF Vs]])
  also have "\<dots> = (\<Sum>j<?k. (\<Sum>i<?k. ?M $$ (r, i) * T $$ (i, j)) * cnj (?M $$ (c, j)))"
    using r c by (subst sum.swap) (simp add: kraus_vec_mat_index sum_distrib_left sum_distrib_right mult_ac)
  also have "\<dots> = (?M * T * (?M\<^sup>\<dagger>)) $$ (r, c)"
    using M T r c by (simp add: mat_mult_entry[of _ "n*d" ?k _ ?k] dagger_def)
  finally show "choi_matrix n d (kraus_quad_map d Vs T) $$ (r, c) = (?M * T * (?M\<^sup>\<dagger>)) $$ (r, c)" .
qed (auto simp: choi_matrix_def)

text \<open>So $\psi_T$ is completely positive for $T\ge0$, by Choi's theorem (Day 19).\<close>

lemma kraus_quad_map_cp:
  assumes Vs: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n" and T: "T \<in> carrier_mat (length Vs) (length Vs)"
      and psdT: "psd T" and n: "0 < n" and d: "0 < d"
  shows "completely_positive n d (kraus_quad_map d Vs T)"
proof -
  let ?M = "kraus_vec_mat d n Vs"
  have "psd ((?M\<^sup>\<dagger>)\<^sup>\<dagger> * T * (?M\<^sup>\<dagger>))"
    by (rule psd_conjugate[OF T psdT dagger_carrier[OF kraus_vec_mat_carrier]])
  hence "psd (choi_matrix n d (kraus_quad_map d Vs T))"
    by (simp add: choi_matrix_kraus_quad_map[OF Vs T n d] dagger_of_dagger_is_id)
  thus ?thesis
    using choi_theorem[OF lin_on_choi_hyps[OF kraus_quad_map_lin_on[OF Vs]] n d] by simp
qed

text \<open>If the $V_i$ are linearly independent, so are the columns of $V$, and $\psi_T=0$ on $M_n$ only
for $T=0$.\<close>

lemma kraus_quad_map_eq_zero:
  assumes Vs: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n" and li: "lin_indep_complex_mat d n Vs"
      and A: "A \<in> carrier_mat (length Vs) (length Vs)" and n: "0 < n" and d: "0 < d"
      and z: "\<And>X. X \<in> carrier_mat n n \<Longrightarrow> kraus_quad_map d Vs A X = 0\<^sub>m d d"
  shows "A = 0\<^sub>m (length Vs) (length Vs)"
proof -
  let ?M = "kraus_vec_mat d n Vs"
  have "?M * A * (?M\<^sup>\<dagger>) = choi_matrix n d (kraus_quad_map d Vs A)"
    by (rule choi_matrix_kraus_quad_map[OF Vs A n d, symmetric])
  also have "\<dots> = choi_matrix n d (\<lambda>X. 0\<^sub>m d d)" by (rule choi_matrix_cong) (rule z)
  also have "\<dots> = 0\<^sub>m (n*d) (n*d)" by (rule eq_matI) (use d in \<open>simp_all add: choi_matrix_def\<close>)
  finally have z': "?M * A * (?M\<^sup>\<dagger>) = 0\<^sub>m (n*d) (n*d)" .
  have li': "lin_indep_vecs (n*d) (map (vec_of_kraus d n) Vs)"
    by (rule lin_indep_complex_mat_vec_of_kraus[OF li d])
  obtain B where B: "B \<in> carrier_mat (length Vs) (length Vs)"
    and GB: "(?M\<^sup>\<dagger> * ?M) * B = 1\<^sub>m (length Vs)" and BG: "B * (?M\<^sup>\<dagger> * ?M) = 1\<^sub>m (length Vs)"
    using gram_inverse[OF li'] unfolding kraus_vec_mat_def length_map by blast
  show ?thesis by (rule frame_cancel[OF kraus_vec_mat_carrier A B BG GB z'])
qed

subsubsection \<open>The pair sum and the trace\<close>

text \<open>The pair sum $P_T=\sum_{i,j}T_{ij}V_j^*V_i\in M_n$.  By cyclicity
$\Tr(V_i\rho V_j^*)=\Tr(V_j^*V_i\rho)$, so $\Tr\psi_T(\rho)=\Tr(P_T\rho)$, and $\psi_T$ is trace
preserving iff $P_T=I_n$.\<close>

definition kraus_pair_sum :: "nat \<Rightarrow> complex Matrix.mat list \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat"
where
  "kraus_pair_sum n Vs A = msum n n (\<lambda>(i, j). A $$ (i, j) \<cdot>\<^sub>m ((Vs ! j)\<^sup>\<dagger> * Vs ! i))
     (List.product [0..<length Vs] [0..<length Vs])"

lemma kraus_pair_sum_dims [simp]:
  "dim_row (kraus_pair_sum n Vs A) = n" "dim_col (kraus_pair_sum n Vs A) = n"
  by (simp_all add: kraus_pair_sum_def)

lemma kraus_pair_term_carrier:
  assumes Vs: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n" and i: "i < length Vs" and j: "j < length Vs"
  shows "(Vs ! j)\<^sup>\<dagger> * Vs ! i \<in> carrier_mat n n"
  using mult_carrier_mat[OF dagger_carrier[OF kraus_list_nth(1)[OF Vs j]] kraus_list_nth(1)[OF Vs i]] .

lemma kraus_pair_sum_index:
  assumes Vs: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n" and r: "r < n" and c: "c < n"
  shows "kraus_pair_sum n Vs A $$ (r, c)
       = (\<Sum>i<length Vs. \<Sum>j<length Vs. A $$ (i, j) * ((Vs ! j)\<^sup>\<dagger> * Vs ! i) $$ (r, c))"
  unfolding kraus_pair_sum_def
  by (subst msum_pairs_index)
     (use kraus_pair_term_carrier[OF Vs] r c in \<open>auto intro!: sum.cong simp: kraus_list_nth[OF Vs]\<close>)

lemma kraus_pair_sum_coeff:
  assumes Vs: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
      and S: "S \<in> carrier_mat (length Vs) (length Vs)" and T: "T \<in> carrier_mat (length Vs) (length Vs)"
  shows "kraus_pair_sum n Vs (a \<cdot>\<^sub>m S + b \<cdot>\<^sub>m T) = a \<cdot>\<^sub>m kraus_pair_sum n Vs S + b \<cdot>\<^sub>m kraus_pair_sum n Vs T"
proof (rule eq_matI)
  fix r c assume "r < dim_row (a \<cdot>\<^sub>m kraus_pair_sum n Vs S + b \<cdot>\<^sub>m kraus_pair_sum n Vs T)"
    "c < dim_col (a \<cdot>\<^sub>m kraus_pair_sum n Vs S + b \<cdot>\<^sub>m kraus_pair_sum n Vs T)"
  hence r: "r < n" and c: "c < n" by auto
  let ?e = "\<lambda>i j. ((Vs ! j)\<^sup>\<dagger> * Vs ! i) $$ (r, c)"
  have "kraus_pair_sum n Vs (a \<cdot>\<^sub>m S + b \<cdot>\<^sub>m T) $$ (r, c)
      = (\<Sum>i<length Vs. \<Sum>j<length Vs. a * (S $$ (i, j) * ?e i j) + b * (T $$ (i, j) * ?e i j))"
    by (simp only: kraus_pair_sum_index[OF Vs r c]) (intro sum.cong refl, use S T in \<open>simp add: distrib_right mult.assoc\<close>)
  also have "\<dots> = a * kraus_pair_sum n Vs S $$ (r, c) + b * kraus_pair_sum n Vs T $$ (r, c)"
    by (simp only: kraus_pair_sum_index[OF Vs r c] sum.distrib sum_distrib_left mult.assoc)
  also have "\<dots> = (a \<cdot>\<^sub>m kraus_pair_sum n Vs S + b \<cdot>\<^sub>m kraus_pair_sum n Vs T) $$ (r, c)"
    using r c by simp
  finally show "kraus_pair_sum n Vs (a \<cdot>\<^sub>m S + b \<cdot>\<^sub>m T) $$ (r, c)
      = (a \<cdot>\<^sub>m kraus_pair_sum n Vs S + b \<cdot>\<^sub>m kraus_pair_sum n Vs T) $$ (r, c)" .
qed auto

lemma kraus_pair_sum_one:
  assumes Vs: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
  shows "kraus_pair_sum n Vs (1\<^sub>m (length Vs)) = sum_wdag_w n Vs"
proof (rule eq_matI)
  have Sc: "sum_wdag_w n Vs \<in> carrier_mat n n"
    unfolding sum_wdag_w_def using Vs by (intro foldr_add_mat_carrier) (auto intro!: mult_carrier_mat[of _ n d] dagger_carrier)
  fix r c assume "r < dim_row (sum_wdag_w n Vs)" "c < dim_col (sum_wdag_w n Vs)"
  hence r: "r < n" and c: "c < n" using Sc by auto
  have "kraus_pair_sum n Vs (1\<^sub>m (length Vs)) $$ (r, c)
      = (\<Sum>i<length Vs. \<Sum>j<length Vs. (if i = j then ((Vs ! j)\<^sup>\<dagger> * Vs ! i) $$ (r, c) else 0))"
    by (simp only: kraus_pair_sum_index[OF Vs r c]) (intro sum.cong refl, simp)
  also have "\<dots> = (\<Sum>i<length Vs. ((Vs ! i)\<^sup>\<dagger> * Vs ! i) $$ (r, c))"
    by (intro sum.cong refl) simp
  also have "\<dots> = sum_wdag_w n Vs $$ (r, c)"
  proof -
    have "\<forall>W \<in> set Vs. W\<^sup>\<dagger> * W \<in> carrier_mat n n" using Vs by (auto intro!: mult_carrier_mat[of _ n d] dagger_carrier)
    thus ?thesis unfolding sum_wdag_w_def
      by (simp add: foldr_add_mat_index_rect[OF _ r c] sum_list_sum_nth atLeast0LessThan)
  qed
  finally show "kraus_pair_sum n Vs (1\<^sub>m (length Vs)) $$ (r, c) = sum_wdag_w n Vs $$ (r, c)" .
qed auto

lemma kraus_pair_sum_dagger:
  assumes Vs: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n" and A: "A \<in> carrier_mat (length Vs) (length Vs)"
  shows "kraus_pair_sum n Vs (A\<^sup>\<dagger>) = (kraus_pair_sum n Vs A)\<^sup>\<dagger>"
proof (rule eq_matI)
  fix r c assume "r < dim_row ((kraus_pair_sum n Vs A)\<^sup>\<dagger>)" "c < dim_col ((kraus_pair_sum n Vs A)\<^sup>\<dagger>)"
  hence r: "r < n" and c: "c < n" by (auto simp: dagger_def)
  have e: "((Vs ! j)\<^sup>\<dagger> * Vs ! i) $$ (r, c) = cnj (((Vs ! i)\<^sup>\<dagger> * Vs ! j) $$ (c, r))"
    if "i < length Vs" "j < length Vs" for i j
  proof -
    have Vi: "Vs ! i \<in> carrier_mat d n" and Vj: "Vs ! j \<in> carrier_mat d n"
      using kraus_list_nth(1)[OF Vs] that by auto
    have "(Vs ! j)\<^sup>\<dagger> * Vs ! i = ((Vs ! i)\<^sup>\<dagger> * Vs ! j)\<^sup>\<dagger>"
      using Vi Vj by (simp add: dagger_of_prod dagger_of_dagger_is_id)
    thus ?thesis using Vi Vj r c by (simp add: dagger_def)
  qed
  have Ad_idx: "(A\<^sup>\<dagger>) $$ (i, j) = cnj (A $$ (j, i))" if "i < length Vs" "j < length Vs" for i j
    using A that by (simp add: dagger_def)
  have "kraus_pair_sum n Vs (A\<^sup>\<dagger>) $$ (r, c)
      = (\<Sum>i<length Vs. \<Sum>j<length Vs. cnj (A $$ (j, i)) * cnj (((Vs ! i)\<^sup>\<dagger> * Vs ! j) $$ (c, r)))"
    by (simp only: kraus_pair_sum_index[OF Vs r c]) (intro sum.cong refl, simp add: e Ad_idx)
  also have "\<dots> = cnj (kraus_pair_sum n Vs A $$ (c, r))"
    by (simp only: kraus_pair_sum_index[OF Vs c r] cnj_sum complex_cnj_mult) (subst sum.swap, simp)
  also have "\<dots> = (kraus_pair_sum n Vs A)\<^sup>\<dagger> $$ (r, c)" using r c by (simp add: dagger_def)
  finally show "kraus_pair_sum n Vs (A\<^sup>\<dagger>) $$ (r, c) = (kraus_pair_sum n Vs A)\<^sup>\<dagger> $$ (r, c)" .
qed (auto simp: dagger_def)

lemma Tr_kraus_quad_map:
  assumes Vs: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n" and rho: "\<rho> \<in> carrier_mat n n"
  shows "Tr (kraus_quad_map d Vs T \<rho>) = Tr (kraus_pair_sum n Vs T * \<rho>)"
proof -
  let ?k = "length Vs"
  have cyc: "Tr (Vs ! i * \<rho> * ((Vs ! j)\<^sup>\<dagger>)) = Tr ((Vs ! j)\<^sup>\<dagger> * Vs ! i * \<rho>)"
    if "i < ?k" "j < ?k" for i j
  proof -
    have Vi: "Vs ! i \<in> carrier_mat d n" and Vj: "(Vs ! j)\<^sup>\<dagger> \<in> carrier_mat n d"
      using kraus_list_nth(1)[OF Vs] dagger_carrier that by auto
    have "Tr (Vs ! i * \<rho> * ((Vs ! j)\<^sup>\<dagger>)) = Tr ((Vs ! j)\<^sup>\<dagger> * (Vs ! i * \<rho>))"
      by (rule Tr_cyclic) (use Vi Vj rho in auto)
    also have "\<dots> = Tr ((Vs ! j)\<^sup>\<dagger> * Vs ! i * \<rho>)" by (simp only: assoc_mult_mat[OF Vj Vi rho])
    finally show ?thesis .
  qed
  have "Tr (kraus_quad_map d Vs T \<rho>) = (\<Sum>i<?k. \<Sum>j<?k. T $$ (i, j) * Tr (Vs ! i * \<rho> * ((Vs ! j)\<^sup>\<dagger>)))"
    unfolding kraus_quad_map_def
    by (subst Tr_msum_pairs) (use kraus_quad_term_carrier[OF Vs rho] in \<open>auto intro!: sum.cong simp: Tr_smult\<close>)
  also have "\<dots> = (\<Sum>i<?k. \<Sum>j<?k. T $$ (i, j) * Tr ((Vs ! j)\<^sup>\<dagger> * Vs ! i * \<rho>))"
    by (intro sum.cong refl) (simp add: cyc)
  also have "\<dots> = Tr (kraus_pair_sum n Vs T * \<rho>)"
  proof -
    have eqP: "kraus_pair_sum n Vs T * \<rho>
        = msum n n (\<lambda>(i, j). (T $$ (i, j) \<cdot>\<^sub>m ((Vs ! j)\<^sup>\<dagger> * Vs ! i)) * \<rho>) (List.product [0..<?k] [0..<?k])"
      unfolding kraus_pair_sum_def
      by (rule msum_pairs_mult_right[OF _ rho]) (use kraus_pair_term_carrier[OF Vs] in auto)
    have tc: "(T $$ (i, j) \<cdot>\<^sub>m ((Vs ! j)\<^sup>\<dagger> * Vs ! i)) * \<rho> \<in> carrier_mat n n"
      if "i < ?k" "j < ?k" for i j
      using mult_carrier_mat[OF smult_carrier_mat[OF kraus_pair_term_carrier[OF Vs that]] rho] .
    have te: "Tr ((T $$ (i, j) \<cdot>\<^sub>m ((Vs ! j)\<^sup>\<dagger> * Vs ! i)) * \<rho>) = T $$ (i, j) * Tr ((Vs ! j)\<^sup>\<dagger> * Vs ! i * \<rho>)"
      if "i < ?k" "j < ?k" for i j
      using mult_smult_assoc_mat[OF kraus_pair_term_carrier[OF Vs that] rho] by (simp add: Tr_smult)
    show ?thesis unfolding eqP by (subst Tr_msum_pairs) (use tc te in \<open>auto intro!: sum.cong\<close>)
  qed
  finally show ?thesis .
qed

lemma kraus_quad_map_tp_iff:
  assumes Vs: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
  shows "trace_preserving n (kraus_quad_map d Vs T) \<longleftrightarrow> kraus_pair_sum n Vs T = 1\<^sub>m n"
proof
  assume tp: "trace_preserving n (kraus_quad_map d Vs T)"
  show "kraus_pair_sum n Vs T = 1\<^sub>m n"
  proof (rule mat_trace_pairing_unique)
    fix \<rho> :: "complex Matrix.mat" assume rho: "\<rho> \<in> carrier_mat n n"
    have "Tr (kraus_pair_sum n Vs T * \<rho>) = Tr (kraus_quad_map d Vs T \<rho>)"
      by (rule Tr_kraus_quad_map[OF Vs rho, symmetric])
    also have "\<dots> = Tr \<rho>" using tp rho by (simp add: trace_preserving_def)
    finally show "Tr (kraus_pair_sum n Vs T * \<rho>) = Tr (1\<^sub>m n * \<rho>)" using rho by simp
  qed auto
next
  assume "kraus_pair_sum n Vs T = 1\<^sub>m n"
  thus "trace_preserving n (kraus_quad_map d Vs T)"
    unfolding trace_preserving_def using Tr_kraus_quad_map[OF Vs] by simp
qed

subsubsection \<open>The products of a Kraus list\<close>

text \<open>The products $V_j^*V_i\in M_n$ for all pairs $(i,j)$, the one at position $ik+j$ being
$V_j^*V_i$.  The pair sum is their combination with the coefficients $T_{ij}$: independent products
determine $T$ from $P_T$, and a dependence among them is a non-zero $T$ with $P_T=0$.\<close>

definition kraus_products ::
  "complex Matrix.mat list \<Rightarrow> complex Matrix.mat list"
where
  "kraus_products Vs \<equiv>
     concat (map (\<lambda>i. map (\<lambda>j. (Vs!j)\<^sup>\<dagger> * Vs!i) [0..<length Vs])
                 [0..<length Vs])"

lemma kraus_products_carrier:
  assumes "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
  shows "\<forall>B \<in> set (kraus_products Vs). B \<in> carrier_mat n n"
proof
  fix B assume "B \<in> set (kraus_products Vs)"
  then obtain i j where
    i_lt: "i < length Vs" and j_lt: "j < length Vs"
    and B_eq: "B = (Vs!j)\<^sup>\<dagger> * Vs!i"
    unfolding kraus_products_def by auto
  have Vi_c: "Vs!i \<in> carrier_mat d n"
    using assms i_lt by (simp add: nth_mem)
  have Vj_c: "Vs!j \<in> carrier_mat d n"
    using assms j_lt by (simp add: nth_mem)
  have Vjd_c: "(Vs!j)\<^sup>\<dagger> \<in> carrier_mat n d" using Vj_c by auto
  show "B \<in> carrier_mat n n" using B_eq Vi_c Vjd_c by auto
qed

lemma length_kraus_products:
  "length (kraus_products Vs) = length Vs * length Vs"
proof -
  let ?k = "length Vs"
  let ?L = "map (\<lambda>i. map (\<lambda>j. (Vs!j)\<^sup>\<dagger> * Vs!i) [0..<?k]) [0..<?k]"
  have uniform: "\<forall>xs \<in> set ?L. length xs = ?k" by auto
  have outer_len: "length ?L = ?k" by simp
  have "length (kraus_products Vs) = length (concat ?L)"
    by (simp add: kraus_products_def)
  also have "\<dots> = length ?L * ?k"
    using concat_uniform_length[OF uniform] .
  also have "\<dots> = ?k * ?k"
    using outer_len by simp
  finally show ?thesis .
qed

lemma kraus_products_nth:
  assumes i_lt: "i < length Vs" and j_lt: "j < length Vs"
  shows "kraus_products Vs ! (i * length Vs + j) = (Vs!j)\<^sup>\<dagger> * Vs!i"
proof -
  let ?k = "length Vs"
  let ?L = "map (\<lambda>i. map (\<lambda>j. (Vs!j)\<^sup>\<dagger> * Vs!i) [0..<?k]) [0..<?k]"
  have uniform: "\<forall>xs \<in> set ?L. length xs = ?k" by auto
  have outer_len: "length ?L = ?k" by simp
  have inner_nth: "?L ! i ! j = (Vs!j)\<^sup>\<dagger> * Vs!i"
    using i_lt j_lt by simp
  have i_lt': "i < length ?L" using outer_len i_lt by simp
  have "kraus_products Vs ! (i * ?k + j) = concat ?L ! (i * ?k + j)"
    by (simp add: kraus_products_def)
  also have "\<dots> = ?L ! i ! j"
    using concat_uniform_nth[OF uniform i_lt' j_lt] .
  also have "\<dots> = (Vs!j)\<^sup>\<dagger> * Vs!i"
    using inner_nth .
  finally show ?thesis .
qed

lemma kraus_pair_sum_products:
  assumes Vs: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
  shows "kraus_pair_sum n Vs A
       = msum n n (\<lambda>\<kappa>. A $$ (\<kappa> div length Vs, \<kappa> mod length Vs) \<cdot>\<^sub>m (kraus_products Vs ! \<kappa>))
           [0..<length (kraus_products Vs)]"
proof (rule eq_matI)
  let ?k = "length Vs"
  fix r c assume "r < dim_row (msum n n (\<lambda>\<kappa>. A $$ (\<kappa> div ?k, \<kappa> mod ?k) \<cdot>\<^sub>m (kraus_products Vs ! \<kappa>))
           [0..<length (kraus_products Vs)])" "c < dim_col (msum n n (\<lambda>\<kappa>. A $$ (\<kappa> div ?k, \<kappa> mod ?k) \<cdot>\<^sub>m (kraus_products Vs ! \<kappa>))
           [0..<length (kraus_products Vs)])"
  hence r: "r < n" and c: "c < n" by auto
  have P: "\<And>\<kappa>. \<kappa> < length (kraus_products Vs) \<Longrightarrow> kraus_products Vs ! \<kappa> \<in> carrier_mat n n"
    using kraus_products_carrier[OF Vs] by auto
  have "msum n n (\<lambda>\<kappa>. A $$ (\<kappa> div ?k, \<kappa> mod ?k) \<cdot>\<^sub>m (kraus_products Vs ! \<kappa>)) [0..<length (kraus_products Vs)] $$ (r, c)
      = (\<Sum>\<kappa> = 0..<?k * ?k. A $$ (\<kappa> div ?k, \<kappa> mod ?k) * kraus_products Vs ! \<kappa> $$ (r, c))"
    by (subst msum_upt_index) (use P r c in \<open>auto simp: length_kraus_products atLeast0LessThan carrier_matD[OF P] intro!: sum.cong\<close>)
  also have "\<dots> = (\<Sum>i = 0..<?k. \<Sum>j = 0..<?k. A $$ (i, j) * ((Vs ! j)\<^sup>\<dagger> * Vs ! i) $$ (r, c))"
    by (subst sum_split_prod_atLeastLessThan) (auto intro!: sum.cong simp: kraus_products_nth pair_index_lt(2,3))
  also have "\<dots> = kraus_pair_sum n Vs A $$ (r, c)"
    by (simp add: kraus_pair_sum_index[OF Vs r c] atLeast0LessThan)
  finally show "kraus_pair_sum n Vs A $$ (r, c) = msum n n (\<lambda>\<kappa>. A $$ (\<kappa> div ?k, \<kappa> mod ?k) \<cdot>\<^sub>m (kraus_products Vs ! \<kappa>))
           [0..<length (kraus_products Vs)] $$ (r, c)" ..
qed auto

lemma kraus_pair_sum_eq_zero:
  assumes Vs: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n" and li: "lin_indep_complex_mat n n (kraus_products Vs)"
      and A: "A \<in> carrier_mat (length Vs) (length Vs)" and z: "kraus_pair_sum n Vs A = 0\<^sub>m n n"
  shows "A = 0\<^sub>m (length Vs) (length Vs)"
proof (rule eq_matI)
  let ?k = "length Vs"
  fix i j assume "i < dim_row (0\<^sub>m ?k ?k :: complex Matrix.mat)" "j < dim_col (0\<^sub>m ?k ?k :: complex Matrix.mat)"
  hence i: "i < ?k" and j: "j < ?k" by auto
  have all: "\<forall>\<kappa> < length (kraus_products Vs). A $$ (\<kappa> div ?k, \<kappa> mod ?k) = 0"
    using li z kraus_pair_sum_products[OF Vs, of A] unfolding lin_indep_complex_mat_msum by auto
  have "A $$ ((i * ?k + j) div ?k, (i * ?k + j) mod ?k) = 0"
    using all[unfolded length_kraus_products, rule_format, OF pair_index_lt(1)[OF i j]] .
  thus "A $$ (i, j) = 0\<^sub>m ?k ?k $$ (i, j)" using pair_index_lt[OF i j] i j by simp
qed (use A in auto)

lemma kraus_pair_sum_dependence:
  assumes Vs: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n" and dep: "\<not> lin_indep_complex_mat n n (kraus_products Vs)"
  shows "\<exists>A \<in> carrier_mat (length Vs) (length Vs). A \<noteq> 0\<^sub>m (length Vs) (length Vs) \<and> kraus_pair_sum n Vs A = 0\<^sub>m n n"
proof -
  let ?k = "length Vs" and ?P = "kraus_products Vs"
  obtain c \<kappa>\<^sub>0 where z: "msum n n (\<lambda>\<kappa>. c \<kappa> \<cdot>\<^sub>m (?P ! \<kappa>)) [0..<length ?P] = 0\<^sub>m n n"
    and \<kappa>0: "\<kappa>\<^sub>0 < length ?P" and c0: "c \<kappa>\<^sub>0 \<noteq> 0"
    using dep kraus_products_carrier[OF Vs] unfolding lin_indep_complex_mat_msum by blast
  define A where "A = Matrix.mat ?k ?k (\<lambda>(i, j). c (i * ?k + j))"
  have Ac: "A \<in> carrier_mat ?k ?k" by (simp add: A_def)
  have coeff: "A $$ (\<kappa> div ?k, \<kappa> mod ?k) = c \<kappa>" if "\<kappa> < length ?P" for \<kappa>
  proof -
    have k: "\<kappa> < ?k * ?k" using that by (simp add: length_kraus_products)
    hence "0 < ?k" by (cases "?k") auto
    moreover have "\<kappa> div ?k < ?k" using k by (simp add: less_mult_imp_div_less)
    ultimately show ?thesis by (simp add: A_def)
  qed
  have "kraus_pair_sum n Vs A = msum n n (\<lambda>\<kappa>. c \<kappa> \<cdot>\<^sub>m (?P ! \<kappa>)) [0..<length ?P]"
    unfolding kraus_pair_sum_products[OF Vs] by (rule msum_cong) (simp add: coeff)
  also have "\<dots> = 0\<^sub>m n n" by (rule z)
  finally have PA: "kraus_pair_sum n Vs A = 0\<^sub>m n n" .
  have "A \<noteq> 0\<^sub>m ?k ?k"
  proof
    assume "A = 0\<^sub>m ?k ?k"
    moreover have "\<kappa>\<^sub>0 div ?k < ?k" "\<kappa>\<^sub>0 mod ?k < ?k"
      using \<kappa>0 by (auto simp: length_kraus_products less_mult_imp_div_less intro!: mod_less_divisor
                       intro: Nat.gr0I)
    ultimately have "A $$ (\<kappa>\<^sub>0 div ?k, \<kappa>\<^sub>0 mod ?k) = 0" by simp
    thus False using coeff[OF \<kappa>0] c0 by simp
  qed
  thus ?thesis using Ac PA by blast
qed

subsection \<open>Extreme maps have independent products\<close>

text \<open>The notes' direction ($\Rightarrow$), by contraposition.  A dependence among the products gives a
non-zero Hermitian $H$ with $P_H=0$.  For small $\epsilon>0$ the maps $\Phi_\pm=\psi_{I\pm\epsilon H}$
are completely positive, as $I\pm\epsilon H\ge0$, and trace preserving, as $P_{I\pm\epsilon H}=I$;
they differ from $\Phi=\psi_I$, as $\psi_H\ne0$, and $\Phi=\tfrac12(\Phi_++\Phi_-)$.\<close>

text \<open>A dependence can be taken Hermitian: $P_{A^*}=P_A^*$, and one of $A+A^*$, $i(A-A^*)$ is
non-zero.\<close>

lemma kraus_pair_sum_hermitian_witness:
  assumes Vs: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n" and A: "A \<in> carrier_mat (length Vs) (length Vs)"
      and nz: "A \<noteq> 0\<^sub>m (length Vs) (length Vs)" and z: "kraus_pair_sum n Vs A = 0\<^sub>m n n"
  shows "\<exists>H \<in> carrier_mat (length Vs) (length Vs). hermitian H \<and> H \<noteq> 0\<^sub>m (length Vs) (length Vs)
           \<and> kraus_pair_sum n Vs H = 0\<^sub>m n n"
proof -
  let ?k = "length Vs"
  have Ad: "A\<^sup>\<dagger> \<in> carrier_mat ?k ?k" by (rule dagger_carrier[OF A])
  have zd: "kraus_pair_sum n Vs (A\<^sup>\<dagger>) = 0\<^sub>m n n" by (simp add: kraus_pair_sum_dagger[OF Vs A] z)
  have P: "kraus_pair_sum n Vs (a \<cdot>\<^sub>m A + b \<cdot>\<^sub>m (A\<^sup>\<dagger>)) = 0\<^sub>m n n" for a b
    by (simp add: kraus_pair_sum_coeff[OF Vs A Ad] z zd)
  define H1 where "H1 = 1 \<cdot>\<^sub>m A + 1 \<cdot>\<^sub>m (A\<^sup>\<dagger>)"
  define H2 where "H2 = \<i> \<cdot>\<^sub>m A + (- \<i>) \<cdot>\<^sub>m (A\<^sup>\<dagger>)"
  have H1c: "H1 \<in> carrier_mat ?k ?k" and H2c: "H2 \<in> carrier_mat ?k ?k"
    using A Ad by (simp_all add: H1_def H2_def)
  have h1: "hermitian H1" and h2: "hermitian H2"
    unfolding hermitian_def H1_def H2_def using A by (auto intro!: eq_matI simp: dagger_def algebra_simps)
  have "H1 \<noteq> 0\<^sub>m ?k ?k \<or> H2 \<noteq> 0\<^sub>m ?k ?k"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    hence z1: "H1 = 0\<^sub>m ?k ?k" and z2: "H2 = 0\<^sub>m ?k ?k" by auto
    have "A = 0\<^sub>m ?k ?k"
    proof (rule eq_matI)
      fix i j assume "i < dim_row (0\<^sub>m ?k ?k :: complex Matrix.mat)" "j < dim_col (0\<^sub>m ?k ?k :: complex Matrix.mat)"
      hence i: "i < ?k" and j: "j < ?k" by auto
      have e1: "A $$ (i, j) + cnj (A $$ (j, i)) = 0" using arg_cong[OF z1, of "\<lambda>M. M $$ (i, j)"] A i j
        by (simp add: H1_def dagger_def)
      have e2: "\<i> * A $$ (i, j) - \<i> * cnj (A $$ (j, i)) = 0" using arg_cong[OF z2, of "\<lambda>M. M $$ (i, j)"] A i j
        by (simp add: H2_def dagger_def)
      from e2 have "A $$ (i, j) = cnj (A $$ (j, i))" by (simp add: right_diff_distrib[symmetric])
      with e1 show "A $$ (i, j) = 0\<^sub>m ?k ?k $$ (i, j)" using i j by simp
    qed (use A in auto)
    thus False using nz by simp
  qed
  thus ?thesis using H1c H2c h1 h2 P unfolding H1_def H2_def by blast
qed

text \<open>For Hermitian $H$, $I+tH\ge0$ when $|t|$ is small: if $H=UDU^*$, then $I+tH=U(I+tD)U^*$, and
$\epsilon=1/(1+\sum_i|d_i|)$ works.\<close>

lemma small_eps_psd:
  fixes A :: "complex Matrix.mat"
  assumes A_c: "A \<in> carrier_mat k k" and herm: "hermitian A"
  shows "\<exists>\<epsilon> > 0. \<forall>d :: real. \<bar>d\<bar> \<le> \<epsilon> \<longrightarrow> psd (1\<^sub>m k + complex_of_real d \<cdot>\<^sub>m A)"
proof -
  obtain U D where U: "U \<in> carrier_mat k k" and Uu: "unitary U" and D: "length D = k"
    and spec: "U\<^sup>\<dagger> * A * U = diag_mat_of_real D"
    using hermitian_spectral_decomp[OF A_c herm] by blast
  have A_eq: "A = U * diag_mat_of_real D * (U\<^sup>\<dagger>)" by (rule hermitian_spectral_decomp_eq[OF U A_c Uu spec])
  have Ud: "U\<^sup>\<dagger> \<in> carrier_mat k k" by (rule dagger_carrier[OF U])
  have Dc: "diag_mat_of_real D \<in> carrier_mat k k" using diag_mat_of_real_carrier[of D] D by simp
  have UUd: "U * (U\<^sup>\<dagger>) = 1\<^sub>m k" using Uu U by (simp add: unitary_def)
  define S where "S = (\<Sum>i<k. \<bar>D ! i\<bar>)"
  define \<epsilon> where "\<epsilon> = 1 / (1 + S)"
  have S0: "0 \<le> S" by (simp add: S_def sum_nonneg)
  have \<epsilon>0: "0 < \<epsilon>" using S0 by (simp add: \<epsilon>_def)
  have "psd (1\<^sub>m k + complex_of_real t \<cdot>\<^sub>m A)" if t: "\<bar>t\<bar> \<le> \<epsilon>" for t
  proof -
    define D' where "D' = map (\<lambda>x. 1 + t * x) D"
    have nn: "0 \<le> D' ! i" if i: "i < k" for i
    proof -
      have "\<bar>D ! i\<bar> \<le> S" unfolding S_def using i by (intro member_le_sum) auto
      hence "\<bar>t\<bar> * \<bar>D ! i\<bar> \<le> \<epsilon> * S" using t S0 by (intro mult_mono) auto
      also have "\<epsilon> * S < 1" using S0 by (simp add: \<epsilon>_def field_simps)
      finally have "\<bar>t * D ! i\<bar> < 1" by (simp add: abs_mult)
      thus ?thesis using i D by (simp add: D'_def)
    qed
    have diag: "diag_mat_of_real D' = 1\<^sub>m k + complex_of_real t \<cdot>\<^sub>m diag_mat_of_real D"
      by (rule eq_matI) (auto simp: D'_def D diag_mat_of_real_def mat_diag_def)
    have "U * diag_mat_of_real D' * (U\<^sup>\<dagger>) = U * (U\<^sup>\<dagger>) + complex_of_real t \<cdot>\<^sub>m (U * diag_mat_of_real D * (U\<^sup>\<dagger>))"
      unfolding diag
      by (simp add: mult_add_distrib_mat[OF U one_carrier_mat smult_carrier_mat[OF Dc]]
                    right_mult_one_mat[OF U] mult_smult_distrib[OF U Dc]
                    add_mult_distrib_mat[OF U smult_carrier_mat[OF mult_carrier_mat[OF U Dc]] Ud]
                    mult_smult_assoc_mat[OF mult_carrier_mat[OF U Dc] Ud])
    also have "\<dots> = 1\<^sub>m k + complex_of_real t \<cdot>\<^sub>m A" by (simp add: UUd A_eq[symmetric])
    finally have "1\<^sub>m k + complex_of_real t \<cdot>\<^sub>m A = U * diag_mat_of_real D' * (U\<^sup>\<dagger>)" ..
    thus ?thesis using psd_U_diag_Udag[OF U _ nn] D by (simp add: D'_def)
  qed
  thus ?thesis using \<epsilon>0 by blast
qed

lemma not_extreme_CPTP_of_herm_witness:
  assumes n: "0 < n" and d: "0 < d" and rep: "cptp_kraus_rep n d \<Phi> Vs"
      and li: "lin_indep_complex_mat d n Vs"
      and H: "H \<in> carrier_mat (length Vs) (length Vs)" "hermitian H" "H \<noteq> 0\<^sub>m (length Vs) (length Vs)"
             "kraus_pair_sum n Vs H = 0\<^sub>m n n"
  shows "\<not> extreme_CPTP n d \<Phi>"
proof -
  let ?k = "length Vs" and ?I = "1\<^sub>m (length Vs)"
  note R = cptp_kraus_rep_facts[OF rep]
  have Vs: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n" by (rule R(1))
  obtain \<epsilon> where \<epsilon>: "\<epsilon> > 0" and pos: "\<And>t. \<bar>t\<bar> \<le> \<epsilon> \<Longrightarrow> psd (?I + complex_of_real t \<cdot>\<^sub>m H)"
    using small_eps_psd[OF H(1,2)] by blast
  define T where "T t = ?I + complex_of_real t \<cdot>\<^sub>m H" for t
  have Tc: "T t \<in> carrier_mat ?k ?k" for t using H(1) by (simp add: T_def)
  have psi: "kraus_quad_map d Vs (T t) X = \<Phi> X + complex_of_real t \<cdot>\<^sub>m kraus_quad_map d Vs H X"
    if X: "X \<in> carrier_mat n n" for t X
    using kraus_quad_map_coeff[OF Vs X one_carrier_mat H(1), of 1 "complex_of_real t"]
    by (simp add: T_def one_smult_mat kraus_quad_map_one[OF Vs X] R(3)[OF X])
  have cptp: "kraus_quad_map d Vs (T t) \<in> CPTP n d" if t: "\<bar>t\<bar> \<le> \<epsilon>" for t
  proof -
    have "completely_positive n d (kraus_quad_map d Vs (T t))"
      using kraus_quad_map_cp[OF Vs Tc _ n d] pos[OF t] by (simp add: T_def)
    moreover have "kraus_pair_sum n Vs (T t) = 1\<^sub>m n"
      using kraus_pair_sum_coeff[OF Vs one_carrier_mat H(1), of 1 "complex_of_real t"]
      by (simp add: T_def one_smult_mat kraus_pair_sum_one[OF Vs] R(2) H(4))
    hence "trace_preserving n (kraus_quad_map d Vs (T t))" using kraus_quad_map_tp_iff[OF Vs] by simp
    ultimately show ?thesis by (simp add: CPTP_def)
  qed
  obtain X0 where X0: "X0 \<in> carrier_mat n n" and nz: "kraus_quad_map d Vs H X0 \<noteq> 0\<^sub>m d d"
    using kraus_quad_map_eq_zero[OF Vs li H(1) n d] H(3) by blast
  obtain r c where r: "r < d" and c: "c < d" and nzrc: "kraus_quad_map d Vs H X0 $$ (r, c) \<noteq> 0"
    using nonzero_entry[OF kraus_quad_map_carrier[OF Vs X0] nz] by blast
  have "midpoint_pair n d (CPTP n d) \<Phi> (kraus_quad_map d Vs (T \<epsilon>)) (kraus_quad_map d Vs (T (- \<epsilon>)))"
    unfolding midpoint_pair_def
  proof (intro conjI ballI bexI[of _ X0])
    show "kraus_quad_map d Vs (T \<epsilon>) \<in> CPTP n d" "kraus_quad_map d Vs (T (- \<epsilon>)) \<in> CPTP n d"
      using cptp \<epsilon> by auto
    show "lin_on n d (carrier_mat n n) (kraus_quad_map d Vs (T \<epsilon>))"
      "lin_on n d (carrier_mat n n) (kraus_quad_map d Vs (T (- \<epsilon>)))"
      by (rule kraus_quad_map_lin_on[OF Vs])+
    show "X0 \<in> carrier_mat n n" by (rule X0)
    show "kraus_quad_map d Vs (T \<epsilon>) X0 \<noteq> \<Phi> X0"
    proof
      assume "kraus_quad_map d Vs (T \<epsilon>) X0 = \<Phi> X0"
      hence "(\<Phi> X0 + complex_of_real \<epsilon> \<cdot>\<^sub>m kraus_quad_map d Vs H X0) $$ (r, c) = \<Phi> X0 $$ (r, c)"
        by (simp add: psi[OF X0])
      thus False using R(4)[OF X0] r c nzrc \<epsilon> by simp
    qed
  next
    fix X :: "complex Matrix.mat" assume X: "X \<in> carrier_mat n n"
    show "\<Phi> X = (1/2 :: complex) \<cdot>\<^sub>m kraus_quad_map d Vs (T \<epsilon>) X + (1/2 :: complex) \<cdot>\<^sub>m kraus_quad_map d Vs (T (- \<epsilon>)) X"
      unfolding psi[OF X] using R(4)[OF X]
      by (intro eq_matI) (auto simp: algebra_simps)
  qed
  thus ?thesis unfolding extreme_point_def by blast
qed

theorem extreme_CPTP_imp_products_indep:
  fixes \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
    and Vs :: "complex Matrix.mat list"
  assumes npos: "0 < n" and dpos: "0 < d"
      and \<Phi>_in: "\<Phi> \<in> CPTP n d"
      and rep:  "cptp_kraus_rep n d \<Phi> Vs"
      and minimal: "lin_indep_complex_mat d n Vs"
      and ext: "extreme_CPTP n d \<Phi>"
  shows "lin_indep_complex_mat n n (kraus_products Vs)"
proof (rule ccontr)
  assume dep: "\<not> lin_indep_complex_mat n n (kraus_products Vs)"
  note Vs = cptp_kraus_rep_facts(1)[OF rep]
  obtain A where "A \<in> carrier_mat (length Vs) (length Vs)" "A \<noteq> 0\<^sub>m (length Vs) (length Vs)"
    "kraus_pair_sum n Vs A = 0\<^sub>m n n"
    using kraus_pair_sum_dependence[OF Vs dep] by blast
  then obtain H where "H \<in> carrier_mat (length Vs) (length Vs)" "hermitian H"
    "H \<noteq> 0\<^sub>m (length Vs) (length Vs)" "kraus_pair_sum n Vs H = 0\<^sub>m n n"
    using kraus_pair_sum_hermitian_witness[OF Vs] by blast
  hence "\<not> extreme_CPTP n d \<Phi>" by (rule not_extreme_CPTP_of_herm_witness[OF npos dpos rep minimal])
  thus False using ext by simp
qed

subsection \<open>A CP Radon--Nikodym theorem\<close>

text \<open>The notes prove ($\Leftarrow$) with Choi 2.  Here Choi matrices replace it: if
$0\le P_\Psi\le P_\Phi=VV^*$, then $P_\Psi=VTV^*$ with $T\ge0$, so $\Psi=\psi_T$.  The factorisation of
dominated positive matrices uses the Moore--Penrose pseudoinverse.\<close>

subsubsection \<open>Dominated positive matrices\<close>

text \<open>The pseudoinverse of a real diagonal: $d_i^+=1/d_i$ for $d_i\ne0$ and $d_i^+=0$ otherwise.\<close>

definition pinv_list :: "real list \<Rightarrow> real list" where
  "pinv_list D = map (\<lambda>d. if d = 0 then 0 else 1/d) D"

lemma pinv_list_length [simp]: "length (pinv_list D) = length D"
  unfolding pinv_list_def by simp

lemma pinv_list_index:
  assumes "i < length D"
  shows "pinv_list D ! i = (if D ! i = 0 then 0 else 1 / (D ! i))"
  using assms unfolding pinv_list_def by simp

lemma diag_pinv_diag_eq:
  fixes D :: "real list"
  shows "diag_mat_of_real D * diag_mat_of_real (pinv_list D) * diag_mat_of_real D = diag_mat_of_real D"
  unfolding diag_mat_of_real_def pinv_list_length mat_diag_diag
  by (rule eq_matI) (auto simp: mat_diag_def pinv_list_def)

text \<open>For Hermitian $A=UDU^*$ set $A^+=UD^+U^*$; then $AA^+A=UDD^+DU^*=A$.\<close>

lemma A_Aplus_A_eq:
  fixes U :: "complex Matrix.mat" and D :: "real list"
  assumes Uc: "U \<in> carrier_mat k k"
      and UU: "unitary U"
      and Dlen: "length D = k"
  shows "(U * diag_mat_of_real D * (U\<^sup>\<dagger>))
           * (U * diag_mat_of_real (pinv_list D) * (U\<^sup>\<dagger>))
           * (U * diag_mat_of_real D * (U\<^sup>\<dagger>))
         = U * diag_mat_of_real D * (U\<^sup>\<dagger>)"
proof -
  have Dm: "diag_mat_of_real D \<in> carrier_mat k k" and Pm: "diag_mat_of_real (pinv_list D) \<in> carrier_mat k k"
    using diag_mat_of_real_carrier[of D] diag_mat_of_real_carrier[of "pinv_list D"] Dlen by simp_all
  show ?thesis
    by (simp only: unitary_conj_mult[OF Uc UU Dm Pm] unitary_conj_mult[OF Uc UU mult_carrier_mat[OF Dm Pm] Dm]
                   diag_pinv_diag_eq)
qed

text \<open>If $0\le B\le A$ then $B=AA^+B$: with $Q=A^+A$, $AQ=A$, so $x-Qx\in\ker A\subseteq\ker B$,
whence $B=BQ$, and taking adjoints $B=QB=AA^+B$.\<close>

lemma A_Aplus_B_eq_B:
  fixes U :: "complex Matrix.mat" and D :: "real list" and B :: "complex Matrix.mat"
  assumes Uc: "U \<in> carrier_mat k k"
      and UU: "unitary U"
      and Dlen: "length D = k"
      and Dnn: "\<And>i. i < k \<Longrightarrow> 0 \<le> D ! i"
      and B_c: "B \<in> carrier_mat k k"
      and B_psd: "psd B"
      and dom_psd: "psd ((U * diag_mat_of_real D * (U\<^sup>\<dagger>)) - B)"
  shows "(U * diag_mat_of_real D * (U\<^sup>\<dagger>))
            * (U * diag_mat_of_real (pinv_list D) * (U\<^sup>\<dagger>)) * B = B"
proof -
  let ?Dm  = "diag_mat_of_real D"
  let ?Pm  = "diag_mat_of_real (pinv_list D)"
  let ?Ud  = "U\<^sup>\<dagger>"
  let ?A   = "U * ?Dm * ?Ud"
  let ?Ap  = "U * ?Pm * ?Ud"
  let ?Q   = "?Ap * ?A"

  have Dm_c: "?Dm \<in> carrier_mat k k" using Dlen by auto
  have Pm_c: "?Pm \<in> carrier_mat k k" using Dlen by auto
  have Ud_c: "?Ud \<in> carrier_mat k k" using Uc by auto
  have A_c: "?A \<in> carrier_mat k k" using Uc Dm_c Ud_c by simp
  have Ap_c: "?Ap \<in> carrier_mat k k" using Uc Pm_c Ud_c by simp
  have Q_c: "?Q \<in> carrier_mat k k" using Ap_c A_c by simp
  have BQ_c: "B * ?Q \<in> carrier_mat k k" using B_c Q_c by simp

  have Pnn: "\<And>i. i < k \<Longrightarrow> 0 \<le> pinv_list D ! i"
  proof -
    fix i assume "i < k"
    thus "0 \<le> pinv_list D ! i" using Dnn Dlen by (simp add: pinv_list_index)
  qed
  have A_psd: "psd ?A"
    by (rule psd_U_diag_Udag[OF Uc Dlen]) (use Dnn in auto)
  have Ap_psd: "psd ?Ap"
  proof (rule psd_U_diag_Udag[OF Uc])
    show "length (pinv_list D) = k" using Dlen by simp
  next
    fix i assume "i < k" thus "0 \<le> pinv_list D ! i" by (rule Pnn)
  qed
  have A_herm: "?A\<^sup>\<dagger> = ?A"
    using psd_hermitian[OF A_psd] unfolding hermitian_def .
  have Ap_herm: "?Ap\<^sup>\<dagger> = ?Ap"
    using psd_hermitian[OF Ap_psd] unfolding hermitian_def .
  have B_herm: "B\<^sup>\<dagger> = B"
    using psd_hermitian[OF B_psd] unfolding hermitian_def .

  \<comment> \<open>\<open>A Q = A\<close> from \<open>A A\<^sup>+ A = A\<close>.\<close>
  have AApA: "?A * ?Ap * ?A = ?A" by (rule A_Aplus_A_eq[OF Uc UU Dlen])
  have AQ: "?A * ?Q = ?A"
  proof -
    have "?A * ?Q = ?A * ?Ap * ?A"
      by (rule assoc_mult_mat[OF A_c Ap_c A_c, symmetric])
    also have "\<dots> = ?A" by (rule AApA)
    finally show ?thesis .
  qed

  \<comment> \<open>Pointwise: \<open>B x = B Q x\<close>, since \<open>x - Q x \<in> ker A \<subseteq> ker B\<close>.\<close>
  have pointwise: "\<And>x. x \<in> carrier_vec k \<Longrightarrow> B *\<^sub>v x = (B * ?Q) *\<^sub>v x"
  proof -
    fix x :: "complex Matrix.vec" assume x_c: "x \<in> carrier_vec k"
    let ?y = "x - ?Q *\<^sub>v x"
    have Qx_c: "?Q *\<^sub>v x \<in> carrier_vec k" using Q_c x_c by auto
    have y_c: "?y \<in> carrier_vec k" using x_c Qx_c by auto
    have y_dim: "dim_vec ?y = k" by (rule carrier_vecD[OF y_c])
    have Ax_c: "?A *\<^sub>v x \<in> carrier_vec k" using A_c x_c by auto
    have Ay: "?A *\<^sub>v ?y = 0\<^sub>v k"
    proof -
      have e1: "?A *\<^sub>v (?Q *\<^sub>v x) = (?A * ?Q) *\<^sub>v x"
        by (rule assoc_mult_mat_vec[OF A_c Q_c x_c, symmetric])
      have e2: "(?A * ?Q) *\<^sub>v x = ?A *\<^sub>v x" using AQ by simp
      have "?A *\<^sub>v ?y = ?A *\<^sub>v x - ?A *\<^sub>v (?Q *\<^sub>v x)"
        by (rule mult_minus_distrib_mat_vec[OF A_c x_c Qx_c])
      also have "\<dots> = ?A *\<^sub>v x - ?A *\<^sub>v x" using e1 e2 by simp
      also have "\<dots> = 0\<^sub>v k" using Ax_c by simp
      finally show ?thesis .
    qed
    have By: "B *\<^sub>v ?y = 0\<^sub>v k"
      by (rule loewner_ker_subset[OF A_c B_c B_psd dom_psd y_dim Ay])
    have Bx_c: "B *\<^sub>v x \<in> carrier_vec k" using B_c x_c by auto
    have BQx_c: "B *\<^sub>v (?Q *\<^sub>v x) \<in> carrier_vec k" using B_c Qx_c by auto
    have diff0: "B *\<^sub>v x - B *\<^sub>v (?Q *\<^sub>v x) = 0\<^sub>v k"
      using mult_minus_distrib_mat_vec[OF B_c x_c Qx_c] By by simp
    have "B *\<^sub>v x = B *\<^sub>v (?Q *\<^sub>v x)"
    proof (rule eq_vecI)
      show "dim_vec (B *\<^sub>v x) = dim_vec (B *\<^sub>v (?Q *\<^sub>v x))"
        using Bx_c BQx_c by auto
    next
      fix i assume "i < dim_vec (B *\<^sub>v (?Q *\<^sub>v x))"
      hence ilt: "i < k" using B_c by auto
      have "(B *\<^sub>v x - B *\<^sub>v (?Q *\<^sub>v x)) $ i = 0"
        using diff0 ilt by simp
      moreover have "(B *\<^sub>v x - B *\<^sub>v (?Q *\<^sub>v x)) $ i
                       = (B *\<^sub>v x) $ i - (B *\<^sub>v (?Q *\<^sub>v x)) $ i"
        using ilt B_c by simp
      ultimately show "(B *\<^sub>v x) $ i = (B *\<^sub>v (?Q *\<^sub>v x)) $ i" by simp
    qed
    also have "\<dots> = (B * ?Q) *\<^sub>v x"
      by (rule assoc_mult_mat_vec[OF B_c Q_c x_c, symmetric])
    finally show "B *\<^sub>v x = (B * ?Q) *\<^sub>v x" .
  qed
  have B_eq_BQ: "B = B * ?Q"
    by (rule mat_eq_of_mult_vec_eq[OF B_c BQ_c pointwise])

  \<comment> \<open>Adjoint: \<open>B = B\<^sup>\<dagger> = (B Q)\<^sup>\<dagger> = Q\<^sup>\<dagger> B = A A\<^sup>+ B\<close>.\<close>
  have Q_dag: "?Q\<^sup>\<dagger> = ?A * ?Ap"
  proof -
    have "?Q\<^sup>\<dagger> = ?A\<^sup>\<dagger> * (?Ap\<^sup>\<dagger>)"
      by (rule dagger_of_prod) (use Ap_c A_c in auto)
    also have "\<dots> = ?A * ?Ap" using A_herm Ap_herm by simp
    finally show ?thesis .
  qed
  have "B = B\<^sup>\<dagger>" using B_herm by simp
  also have "\<dots> = (B * ?Q)\<^sup>\<dagger>"
    by (rule arg_cong[where f = dagger, OF B_eq_BQ])
  also have "\<dots> = ?Q\<^sup>\<dagger> * (B\<^sup>\<dagger>)"
    by (rule dagger_of_prod) (use B_c Q_c in auto)
  also have "\<dots> = ?A * ?Ap * B" using Q_dag B_herm by simp
  finally show ?thesis by (rule sym)
qed

text \<open>Dominated positive matrices factor through the dominating frame: if $0\le B\le VV^*$ then
\[ B=VTV^*,\qquad T=V^*A^+BA^+V\ge0,\quad A=VV^*. \]\<close>

lemma dominated_outer_sum_param:
  fixes vs :: "complex Matrix.vec list"
    and B :: "complex Matrix.mat"
  assumes vs_dim: "\<forall>v \<in> set vs. dim_vec v = k"
      and k_pos: "0 < k"
      and B_c: "B \<in> carrier_mat k k"
      and B_psd: "psd B"
      and B_dom: "psd (outer_sum k vs - B)"
  shows "\<exists>T. T \<in> carrier_mat (length vs) (length vs) \<and> psd T \<and>
              B = (mat_of_cols k vs) * T * ((mat_of_cols k vs)\<^sup>\<dagger>)"
proof -
  let ?m = "length vs"
  let ?V = "mat_of_cols k vs"
  let ?Vd = "(mat_of_cols k vs)\<^sup>\<dagger>"
  let ?A = "outer_sum k vs"
  have V_c: "?V \<in> carrier_mat k ?m" by (rule mat_of_cols_carrier(1))
  have Vd_c: "?Vd \<in> carrier_mat ?m k" using V_c by (rule dagger_carrier)
  have A_eq: "?V * ?Vd = ?A" by (simp add: outer_sum_def)
  have A_c: "?A \<in> carrier_mat k k" using V_c Vd_c A_eq by auto
  have A_psd: "psd ?A" by (rule outer_sum_psd[OF refl vs_dim])
  have A_herm: "?A\<^sup>\<dagger> = ?A" by (rule outer_sum_hermitian)
  have B_herm: "B\<^sup>\<dagger> = B"
    using psd_hermitian[OF B_psd] unfolding hermitian_def .

  obtain U :: "complex Matrix.mat" and D :: "real list"
    where Uc: "U \<in> carrier_mat k k" and UU: "unitary U" and Dlen: "length D = k"
      and Dnn0: "\<forall>i < k. 0 \<le> D ! i"
      and A_spec: "?A = U * diag_mat_of_real D * (U\<^sup>\<dagger>)"
    using psd_spectral_decomp_nonneg[OF A_c A_psd] by blast
  have Dnn: "\<And>i. i < k \<Longrightarrow> 0 \<le> D ! i" using Dnn0 by simp

  let ?Pm = "diag_mat_of_real (pinv_list D)"
  let ?Ud = "U\<^sup>\<dagger>"
  let ?Ap = "U * ?Pm * ?Ud"
  have Ud_c: "?Ud \<in> carrier_mat k k" using Uc by auto
  have Pm_c: "?Pm \<in> carrier_mat k k" using Dlen by auto
  have Ap_c: "?Ap \<in> carrier_mat k k" using Uc Pm_c Ud_c by simp
  have Pnn: "\<And>i. i < k \<Longrightarrow> 0 \<le> pinv_list D ! i"
  proof -
    fix i assume "i < k"
    thus "0 \<le> pinv_list D ! i" using Dnn Dlen by (simp add: pinv_list_index)
  qed
  have Ap_psd: "psd ?Ap"
  proof (rule psd_U_diag_Udag[OF Uc])
    show "length (pinv_list D) = k" using Dlen by simp
  next
    fix i assume "i < k" thus "0 \<le> pinv_list D ! i" by (rule Pnn)
  qed
  have Ap_herm: "?Ap\<^sup>\<dagger> = ?Ap"
    using psd_hermitian[OF Ap_psd] unfolding hermitian_def .

  \<comment> \<open>\<open>A A\<^sup>+ B = B\<close> and, by adjoints, \<open>B A\<^sup>+ A = B\<close>.\<close>
  have dom': "psd ((U * diag_mat_of_real D * (U\<^sup>\<dagger>)) - B)"
    using B_dom A_spec by simp
  have AApB: "?A * ?Ap * B = B"
    using A_Aplus_B_eq_B[OF Uc UU Dlen Dnn B_c B_psd dom'] A_spec by simp
  have AAp_c: "?A * ?Ap \<in> carrier_mat k k" using A_c Ap_c by simp
  have BApA: "B * ?Ap * ?A = B"
  proof -
    have "B = (?A * ?Ap * B)\<^sup>\<dagger>" using AApB B_herm by simp
    also have "\<dots> = B\<^sup>\<dagger> * ((?A * ?Ap)\<^sup>\<dagger>)"
      by (rule dagger_of_prod) (use AAp_c B_c in auto)
    also have "(?A * ?Ap)\<^sup>\<dagger> = ?Ap\<^sup>\<dagger> * (?A\<^sup>\<dagger>)"
      by (rule dagger_of_prod) (use A_c Ap_c in auto)
    also have "B\<^sup>\<dagger> * (?Ap\<^sup>\<dagger> * (?A\<^sup>\<dagger>)) = B * (?Ap * ?A)"
      using B_herm Ap_herm A_herm by simp
    also have "\<dots> = B * ?Ap * ?A"
      by (rule assoc_mult_mat[OF B_c Ap_c A_c, symmetric])
    finally show ?thesis by (rule sym)
  qed

  \<comment> \<open>The parameter \<open>T = V\<^sup>\<dagger> A\<^sup>+ B A\<^sup>+ V\<close>.\<close>
  let ?Y1 = "?Vd * ?Ap"
  let ?Y2 = "?Y1 * B"
  let ?Y3 = "?Y2 * ?Ap"
  let ?Tm = "?Y3 * ?V"
  have Y1_c: "?Y1 \<in> carrier_mat ?m k" using Vd_c Ap_c by simp
  have Y2_c: "?Y2 \<in> carrier_mat ?m k" using Y1_c B_c by simp
  have Y3_c: "?Y3 \<in> carrier_mat ?m k" using Y2_c Ap_c by simp
  have Tm_c: "?Tm \<in> carrier_mat ?m ?m" using Y3_c V_c by simp

  have ApV_c: "?Ap * ?V \<in> carrier_mat k ?m" using Ap_c V_c by simp
  have ApV_dag: "(?Ap * ?V)\<^sup>\<dagger> = ?Y1"
  proof -
    have "(?Ap * ?V)\<^sup>\<dagger> = ?Vd * (?Ap\<^sup>\<dagger>)"
      by (rule dagger_of_prod) (use Ap_c V_c in auto)
    also have "\<dots> = ?Y1" using Ap_herm by simp
    finally show ?thesis .
  qed
  have Tm_psd: "psd ?Tm"
  proof -
    have "psd ((?Ap * ?V)\<^sup>\<dagger> * B * (?Ap * ?V))"
      by (rule psd_conjugate[OF B_c B_psd ApV_c])
    also have "(?Ap * ?V)\<^sup>\<dagger> * B * (?Ap * ?V) = ?Y2 * (?Ap * ?V)"
      using ApV_dag by simp
    also have "\<dots> = ?Tm"
      by (rule assoc_mult_mat[OF Y2_c Ap_c V_c, symmetric])
    finally show ?thesis .
  qed

  \<comment> \<open>\<open>V T V\<^sup>\<dagger> = (V V\<^sup>\<dagger>) A\<^sup>+ B A\<^sup>+ (V V\<^sup>\<dagger>) = A A\<^sup>+ B A\<^sup>+ A = B\<close>.\<close>
  have VY1: "?V * ?Y1 = ?A * ?Ap"
  proof -
    have "?V * ?Y1 = ?V * ?Vd * ?Ap"
      by (rule assoc_mult_mat[OF V_c Vd_c Ap_c, symmetric])
    also have "\<dots> = ?A * ?Ap" using A_eq by simp
    finally show ?thesis .
  qed
  have VY2: "?V * ?Y2 = B"
  proof -
    have "?V * ?Y2 = ?V * ?Y1 * B"
      by (rule assoc_mult_mat[OF V_c Y1_c B_c, symmetric])
    also have "\<dots> = ?A * ?Ap * B" using VY1 by simp
    also have "\<dots> = B" by (rule AApB)
    finally show ?thesis .
  qed
  have VY3: "?V * ?Y3 = B * ?Ap"
  proof -
    have "?V * ?Y3 = ?V * ?Y2 * ?Ap"
      by (rule assoc_mult_mat[OF V_c Y2_c Ap_c, symmetric])
    also have "\<dots> = B * ?Ap" using VY2 by simp
    finally show ?thesis .
  qed
  have BAp_c: "B * ?Ap \<in> carrier_mat k k" using B_c Ap_c by simp
  have VTVd: "?V * ?Tm * ?Vd = B"
  proof -
    have "?V * ?Tm = ?V * ?Y3 * ?V"
      by (rule assoc_mult_mat[OF V_c Y3_c V_c, symmetric])
    also have "\<dots> = B * ?Ap * ?V" using VY3 by simp
    finally have VT: "?V * ?Tm = B * ?Ap * ?V" .
    have "?V * ?Tm * ?Vd = B * ?Ap * ?V * ?Vd" using VT by simp
    also have "\<dots> = B * ?Ap * (?V * ?Vd)"
      by (rule assoc_mult_mat[OF BAp_c V_c Vd_c])
    also have "\<dots> = B * ?Ap * ?A" using A_eq by simp
    also have "\<dots> = B" by (rule BApA)
    finally show ?thesis .
  qed
  show ?thesis
    by (intro exI[of _ ?Tm] conjI Tm_c Tm_psd VTVd[symmetric])
qed

subsubsection \<open>Completely positive maps below a Kraus map\<close>

text \<open>If $0\le P_\Psi\le P_\Phi$ for a linear $\Psi$, where $\Phi$ is the Kraus map of the $V_i$, then
$\Psi=\psi_T$ for some $T\ge0$.\<close>

theorem cp_radon_nikodym:
  assumes Vs: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n" and L: "lin_on n d (carrier_mat n n) \<Psi>"
      and P: "psd (choi_matrix n d \<Psi>)" and dom: "psd (choi_matrix n d (kraus_map_dim d Vs) - choi_matrix n d \<Psi>)"
      and n: "0 < n" and d: "0 < d"
  shows "\<exists>T \<in> carrier_mat (length Vs) (length Vs). psd T \<and> (\<forall>X \<in> carrier_mat n n. \<Psi> X = kraus_quad_map d Vs T X)"
proof -
  let ?us = "map (vec_of_kraus d n) Vs"
  have "choi_matrix n d (kraus_map_dim d Vs) = outer_sum (n*d) ?us" by (rule choi_matrix_kraus_eq[OF Vs n d])
  then obtain T where T: "T \<in> carrier_mat (length ?us) (length ?us)" and psdT: "psd T"
    and PT: "choi_matrix n d \<Psi> = mat_of_cols (n*d) ?us * T * ((mat_of_cols (n*d) ?us)\<^sup>\<dagger>)"
    using dominated_outer_sum_param[of ?us "n*d" "choi_matrix n d \<Psi>"] P dom n d by auto
  have T': "T \<in> carrier_mat (length Vs) (length Vs)" using T by simp
  have eqc: "choi_matrix n d \<Psi> = choi_matrix n d (kraus_quad_map d Vs T)"
    using PT choi_matrix_kraus_quad_map[OF Vs T' n d] by (simp add: kraus_vec_mat_def)
  have Lq: "lin_on n d (carrier_mat n n) (kraus_quad_map d Vs T)" by (rule kraus_quad_map_lin_on[OF Vs])
  have "\<Psi> X = kraus_quad_map d Vs T X" if X: "X \<in> carrier_mat n n" for X
    by (rule map_eq_from_choi_when_linear[OF L Lq eqc X])
  thus ?thesis using T' psdT by blast
qed

subsection \<open>Independent products give extreme maps\<close>

text \<open>The notes' direction ($\Leftarrow$).  If $\Phi=\tfrac12(\Phi_1+\Phi_2)$, then
$0\le\tfrac12P_{\Phi_1}\le P_\Phi$, so $\tfrac12\Phi_1=\psi_S$ with $S\ge0$ and $\Phi_1=\psi_{2S}$.  Trace
preservation gives $P_{2S}=I=P_I$, independence of the products $2S=I$, i.e.\ $\Phi_1=\Phi$.\<close>

theorem products_indep_imp_extreme_CPTP:
  fixes \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
    and Vs :: "complex Matrix.mat list"
  assumes npos: "0 < n" and dpos: "0 < d"
      and \<Phi>_in: "\<Phi> \<in> CPTP n d"
      and rep:  "cptp_kraus_rep n d \<Phi> Vs"
      and lin_indep: "lin_indep_complex_mat n n (kraus_products Vs)"
  shows "extreme_CPTP n d \<Phi>"
proof -
  let ?k = "length Vs" and ?I = "1\<^sub>m (length Vs)"
  note R = cptp_kraus_rep_facts[OF rep]
  have Vs: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n" by (rule R(1))
  have "\<not> midpoint_pair n d (CPTP n d) \<Phi> \<Phi>\<^sub>1 \<Phi>\<^sub>2" for \<Phi>\<^sub>1 \<Phi>\<^sub>2
  proof
    assume "midpoint_pair n d (CPTP n d) \<Phi> \<Phi>\<^sub>1 \<Phi>\<^sub>2"
    then obtain X0 where C1: "\<Phi>\<^sub>1 \<in> CPTP n d" and C2: "\<Phi>\<^sub>2 \<in> CPTP n d"
      and L1: "lin_on n d (carrier_mat n n) \<Phi>\<^sub>1" and L2: "lin_on n d (carrier_mat n n) \<Phi>\<^sub>2"
      and X0: "X0 \<in> carrier_mat n n" and ne: "\<Phi>\<^sub>1 X0 \<noteq> \<Phi> X0"
      and mid: "\<And>X. X \<in> carrier_mat n n \<Longrightarrow> \<Phi> X = (1/2 :: complex) \<cdot>\<^sub>m \<Phi>\<^sub>1 X + (1/2 :: complex) \<cdot>\<^sub>m \<Phi>\<^sub>2 X"
      unfolding midpoint_pair_def by blast
    have F1: "\<And>X. X \<in> carrier_mat n n \<Longrightarrow> \<Phi>\<^sub>1 X \<in> carrier_mat d d"
      and F2: "\<And>X. X \<in> carrier_mat n n \<Longrightarrow> \<Phi>\<^sub>2 X \<in> carrier_mat d d"
      using L1 L2 by (auto simp: lin_on_def)
    define \<Psi> where "\<Psi> = (\<lambda>X. (1/2 :: complex) \<cdot>\<^sub>m \<Phi>\<^sub>1 X)"
    have LP: "lin_on n d (carrier_mat n n) \<Psi>" unfolding \<Psi>_def by (rule lin_on_smult[OF L1])
    have PP: "choi_matrix n d \<Psi> = (1/2 :: complex) \<cdot>\<^sub>m choi_matrix n d \<Phi>\<^sub>1"
      unfolding \<Psi>_def by (rule choi_matrix_smult[OF F1 dpos])
    have PPhi: "choi_matrix n d (kraus_map_dim d Vs)
              = (1/2 :: complex) \<cdot>\<^sub>m choi_matrix n d \<Phi>\<^sub>1 + (1/2 :: complex) \<cdot>\<^sub>m choi_matrix n d \<Phi>\<^sub>2"
    proof -
      have "choi_matrix n d (kraus_map_dim d Vs) = choi_matrix n d (\<lambda>X. (1/2 :: complex) \<cdot>\<^sub>m \<Phi>\<^sub>1 X + (1/2 :: complex) \<cdot>\<^sub>m \<Phi>\<^sub>2 X)"
        by (rule choi_matrix_cong) (simp add: mid R(3)[symmetric])
      thus ?thesis by (simp add: choi_matrix_lincomb[OF F1 F2 dpos])
    qed
    have P1: "psd (choi_matrix n d \<Phi>\<^sub>1)" and P2: "psd (choi_matrix n d \<Phi>\<^sub>2)"
      using C1 C2 choi_psd_if_cp[OF npos dpos] by (auto simp: CPTP_def)
    have "psd (choi_matrix n d \<Psi>)"
      using psd_smult_nonneg[of "1/2" "choi_matrix n d \<Phi>\<^sub>1" "n*d"] P1 by (simp add: PP)
    moreover have "psd (choi_matrix n d (kraus_map_dim d Vs) - choi_matrix n d \<Psi>)"
    proof -
      have "choi_matrix n d (kraus_map_dim d Vs) - choi_matrix n d \<Psi> = (1/2 :: complex) \<cdot>\<^sub>m choi_matrix n d \<Phi>\<^sub>2"
        unfolding PPhi PP by (intro eq_matI) (auto simp: choi_matrix_def)
      thus ?thesis using psd_smult_nonneg[of "1/2" "choi_matrix n d \<Phi>\<^sub>2" "n*d"] P2 by simp
    qed
    ultimately obtain S where S: "S \<in> carrier_mat ?k ?k" and psdS: "psd S"
      and PS: "\<And>X. X \<in> carrier_mat n n \<Longrightarrow> \<Psi> X = kraus_quad_map d Vs S X"
      using cp_radon_nikodym[OF Vs LP _ _ npos dpos] by blast
    let ?S2 = "2 \<cdot>\<^sub>m S"
    have S2: "?S2 \<in> carrier_mat ?k ?k" using S by simp
    have F1S: "\<Phi>\<^sub>1 X = kraus_quad_map d Vs ?S2 X" if X: "X \<in> carrier_mat n n" for X
    proof -
      have "\<Phi>\<^sub>1 X = 2 \<cdot>\<^sub>m \<Psi> X" using F1[OF X] by (simp add: \<Psi>_def smult_smult_mat one_smult_mat)
      also have "\<dots> = kraus_quad_map d Vs (2 \<cdot>\<^sub>m S) X" by (simp add: PS[OF X] kraus_quad_map_smult[OF Vs X S])
      finally show ?thesis .
    qed
    have "trace_preserving n (kraus_quad_map d Vs ?S2)"
      using C1 trace_preserving_cong[of n \<Phi>\<^sub>1 "kraus_quad_map d Vs ?S2"] F1S by (simp add: CPTP_def)
    hence P2S: "kraus_pair_sum n Vs ?S2 = 1\<^sub>m n" using kraus_quad_map_tp_iff[OF Vs] by simp
    have "kraus_pair_sum n Vs (1 \<cdot>\<^sub>m ?S2 + (-1) \<cdot>\<^sub>m ?I) = 1 \<cdot>\<^sub>m kraus_pair_sum n Vs ?S2 + (-1) \<cdot>\<^sub>m kraus_pair_sum n Vs ?I"
      by (rule kraus_pair_sum_coeff[OF Vs S2 one_carrier_mat])
    also have "\<dots> = 0\<^sub>m n n"
      by (intro eq_matI) (auto simp: P2S kraus_pair_sum_one[OF Vs] R(2))
    finally have "1 \<cdot>\<^sub>m ?S2 + (-1) \<cdot>\<^sub>m ?I = 0\<^sub>m ?k ?k"
      by (rule kraus_pair_sum_eq_zero[OF Vs lin_indep, rotated]) (use S2 in simp)
    hence "?S2 = ?I"
    proof (intro eq_matI)
      fix i j assume z: "1 \<cdot>\<^sub>m ?S2 + (-1) \<cdot>\<^sub>m ?I = 0\<^sub>m ?k ?k" and i: "i < dim_row ?I" and j: "j < dim_col ?I"
      have "(1 \<cdot>\<^sub>m ?S2 + (-1) \<cdot>\<^sub>m ?I) $$ (i, j) = 0" using z i j by simp
      thus "?S2 $$ (i, j) = ?I $$ (i, j)" using S i j by simp
    qed (use S in auto)
    hence "\<Phi>\<^sub>1 X0 = \<Phi> X0" using F1S[OF X0] kraus_quad_map_one[OF Vs X0] R(3)[OF X0] by simp
    thus False using ne by simp
  qed
  thus ?thesis using \<Phi>_in unfolding extreme_point_def by blast
qed

subsection \<open>Choi's Theorem 3\<close>

text \<open>For a linearly independent Kraus list,
\[ \Phi\ \text{extreme in}\ \mathrm{CPTP}(M_n,M_d)\iff\{V_j^*V_i\}_{i,j}\ \text{linearly independent}. \]
By unitary freedom (\<open>choi_2_unitary_freedom\<close>, Day 21) any two such lists of $\Phi$ differ by a
unitary, so the condition does not depend on the list.\<close>

theorem choi_theorem_3_cptp_iff:
  fixes \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
    and Vs :: "complex Matrix.mat list"
  assumes npos: "0 < n" and dpos: "0 < d"
      and \<Phi>_in: "\<Phi> \<in> CPTP n d"
      and rep:  "cptp_kraus_rep n d \<Phi> Vs"
      and minimal: "lin_indep_complex_mat d n Vs"
  shows "extreme_CPTP n d \<Phi> \<longleftrightarrow> lin_indep_complex_mat n n (kraus_products Vs)"
  using extreme_CPTP_imp_products_indep[OF npos dpos \<Phi>_in rep minimal]
        products_indep_imp_extreme_CPTP[OF npos dpos \<Phi>_in rep]
  by blast

subsubsection \<open>Unital maps (D23-1)\<close>

text \<open>The notes state the theorem for UCP maps.  It follows by the duality of Day 22: $\Gamma(\Phi)=\Phi^*$
carries midpoint decompositions of a UCP map to midpoint decompositions of its adjoint and back,
and the Kraus operators of $\Phi^*$ are the adjoints $W_i^*$, independent with the $W_i$.\<close>

lemma midpoint_pair_adjoint:
  assumes L: "lin_on n d (carrier_mat n n) \<Phi>" and mid: "midpoint_pair n d S \<Phi> \<Phi>\<^sub>1 \<Phi>\<^sub>2"
      and S: "\<And>\<Psi>. lin_on n d (carrier_mat n n) \<Psi> \<Longrightarrow> \<Psi> \<in> S \<Longrightarrow> map_adjoint n d \<Psi> \<in> S'"
  shows "midpoint_pair d n S' (map_adjoint n d \<Phi>) (map_adjoint n d \<Phi>\<^sub>1) (map_adjoint n d \<Phi>\<^sub>2)"
proof -
  obtain X1 where S1: "\<Phi>\<^sub>1 \<in> S" and S2: "\<Phi>\<^sub>2 \<in> S"
    and L1: "lin_on n d (carrier_mat n n) \<Phi>\<^sub>1" and L2: "lin_on n d (carrier_mat n n) \<Phi>\<^sub>2"
    and X1: "X1 \<in> carrier_mat n n" and ne: "\<Phi>\<^sub>1 X1 \<noteq> \<Phi> X1"
    and m: "\<And>X. X \<in> carrier_mat n n \<Longrightarrow> \<Phi> X = (1/2 :: complex) \<cdot>\<^sub>m \<Phi>\<^sub>1 X + (1/2 :: complex) \<cdot>\<^sub>m \<Phi>\<^sub>2 X"
    using mid unfolding midpoint_pair_def by blast
  have diff: "\<exists>Y \<in> carrier_mat d d. map_adjoint n d \<Phi>\<^sub>1 Y \<noteq> map_adjoint n d \<Phi> Y"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    hence "map_adjoint d n (map_adjoint n d \<Phi>\<^sub>1) = map_adjoint d n (map_adjoint n d \<Phi>)"
      by (intro map_adjoint_cong) blast
    from fun_cong[OF this, of X1] have "\<Phi>\<^sub>1 X1 = \<Phi> X1"
      unfolding map_adjoint_adjoint[OF L1 X1] map_adjoint_adjoint[OF L X1] .
    thus False using ne by blast
  qed
  have "map_adjoint n d \<Phi> Y
      = (1/2 :: complex) \<cdot>\<^sub>m map_adjoint n d \<Phi>\<^sub>1 Y + (1/2 :: complex) \<cdot>\<^sub>m map_adjoint n d \<Phi>\<^sub>2 Y"
    if Y: "Y \<in> carrier_mat d d" for Y
  proof -
    have "map_adjoint n d \<Phi> = map_adjoint n d (\<lambda>X. (1/2 :: complex) \<cdot>\<^sub>m \<Phi>\<^sub>1 X + (1/2 :: complex) \<cdot>\<^sub>m \<Phi>\<^sub>2 X)"
      by (rule map_adjoint_cong) (rule m)
    thus ?thesis using map_adjoint_affine[OF L1 L2 Y, of "1/2"] by simp
  qed
  thus ?thesis unfolding midpoint_pair_def using S[OF L1 S1] S[OF L2 S2] map_adjoint_lin diff by blast
qed

theorem extreme_UCP_iff_adjoint:
  assumes L: "lin_on n d (carrier_mat n n) \<Phi>" and U: "\<Phi> \<in> UCP n d" and n: "0 < n" and d: "0 < d"
  shows "extreme_UCP n d \<Phi> \<longleftrightarrow> extreme_CPTP d n (map_adjoint n d \<Phi>)"
proof -
  have toC: "map_adjoint n d \<Psi> \<in> CPTP d n" if "lin_on n d (carrier_mat n n) \<Psi>" "\<Psi> \<in> UCP n d" for \<Psi>
    by (rule adjoint_ucp_imp_cptp[OF that n d])
  have toU: "map_adjoint d n \<Psi> \<in> UCP n d" if "lin_on d n (carrier_mat d d) \<Psi>" "\<Psi> \<in> CPTP d n" for \<Psi>
    by (rule adjoint_cptp_imp_ucp[OF that n d])
  have from_cptp: "midpoint_pair n d (UCP n d) \<Phi> (map_adjoint d n \<Psi>\<^sub>1) (map_adjoint d n \<Psi>\<^sub>2)"
    if "midpoint_pair d n (CPTP d n) (map_adjoint n d \<Phi>) \<Psi>\<^sub>1 \<Psi>\<^sub>2" for \<Psi>\<^sub>1 \<Psi>\<^sub>2
  proof -
    have "midpoint_pair n d (UCP n d) (map_adjoint d n (map_adjoint n d \<Phi>)) (map_adjoint d n \<Psi>\<^sub>1) (map_adjoint d n \<Psi>\<^sub>2)"
      by (rule midpoint_pair_adjoint[OF map_adjoint_lin that toU])
    thus ?thesis using midpoint_pair_cong[of n "map_adjoint d n (map_adjoint n d \<Phi>)" \<Phi>]
        map_adjoint_adjoint[OF L] by blast
  qed
  show ?thesis
    unfolding extreme_point_def
    using U toC[OF L U] midpoint_pair_adjoint[OF L _ toC] from_cptp by blast
qed

text \<open>The adjoints of the Kraus operators of a unital map are Kraus operators of its adjoint.\<close>

lemma kraus_operators_dagger_of_unital:
  assumes Wc: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n" and un: "kraus_map_dim d Ws (1\<^sub>m n) = 1\<^sub>m d"
  shows "kraus_operators d n (map (\<lambda>W. W\<^sup>\<dagger>) Ws)"
  unfolding kraus_operators_def
proof
  show "\<forall>W \<in> set (map (\<lambda>W. W\<^sup>\<dagger>) Ws). W \<in> carrier_mat n d" using Wc by (auto intro: dagger_carrier)
  have "foldr (\<lambda>W acc. W\<^sup>\<dagger> * W + acc) (map (\<lambda>W. W\<^sup>\<dagger>) Ws) (0\<^sub>m d d)
        = foldr (\<lambda>W acc. W * (W\<^sup>\<dagger>) + acc) Ws (0\<^sub>m d d)"
    by (simp add: foldr_map comp_def dagger_of_dagger_is_id)
  also have "\<dots> = 1\<^sub>m d" using un kraus_map_dim_one[OF Wc] by simp
  finally show "foldr (\<lambda>W acc. W\<^sup>\<dagger> * W + acc) (map (\<lambda>W. W\<^sup>\<dagger>) Ws) (0\<^sub>m d d) = 1\<^sub>m d" .
qed

text \<open>Choi's Theorem 3: a unital CP map $\Phi(X)=\sum_iW_iXW_i^*$ with linearly independent $W_i$ is
extreme iff the products $W_jW_i^*$ are linearly independent (\<^const>\<open>kraus_products\<close> of the
adjoints).  The notes write $\Phi(X)=\sum_iV_i^*XV_i$, i.e.\ $V_i=W_i^*$, and the products $V_i^*V_j$.\<close>

theorem choi_theorem_3_ucp:
  assumes n: "0 < n" and d: "0 < d" and U: "\<Phi> \<in> UCP n d"
      and Wc: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
      and rep: "\<And>X. X \<in> carrier_mat n n \<Longrightarrow> \<Phi> X = kraus_map_dim d Ws X"
      and li: "lin_indep_complex_mat d n Ws"
  shows "extreme_UCP n d \<Phi> \<longleftrightarrow> lin_indep_complex_mat d d (kraus_products (map (\<lambda>W. W\<^sup>\<dagger>) Ws))"
proof -
  have L: "lin_on n d (carrier_mat n n) \<Phi>"
    using kraus_lin_on[OF Wc] rep unfolding lin_on_def by (simp add: add_carrier_mat smult_carrier_mat)
  let ?A = "map_adjoint n d \<Phi>" and ?Vs = "map (\<lambda>W. W\<^sup>\<dagger>) Ws"
  have adj: "\<And>Y. Y \<in> carrier_mat d d \<Longrightarrow> ?A Y = kraus_map_dim n ?Vs Y"
  proof -
    fix Y :: "complex Matrix.mat" assume Y: "Y \<in> carrier_mat d d"
    have "?A = map_adjoint n d (kraus_map_dim d Ws)" by (rule map_adjoint_cong) (rule rep)
    hence "?A Y = kraus_adjoint_dim n Ws Y" using map_adjoint_kraus[OF Wc Y] by simp
    thus "?A Y = kraus_map_dim n ?Vs Y" using kraus_adjoint_dim_as_kraus_map_dim[OF Wc Y] by simp
  qed
  have un: "kraus_map_dim d Ws (1\<^sub>m n) = 1\<^sub>m d" using U rep[of "1\<^sub>m n"] by (simp add: UCP_def unital_map_def)
  have krep: "cptp_kraus_rep d n ?A ?Vs"
    unfolding cptp_kraus_rep_def using kraus_operators_dagger_of_unital[OF Wc un] adj by blast
  have "extreme_CPTP d n ?A \<longleftrightarrow> lin_indep_complex_mat d d (kraus_products ?Vs)"
    by (rule choi_theorem_3_cptp_iff[OF d n adjoint_ucp_imp_cptp[OF L U n d] krep lin_indep_complex_mat_dagger[OF li]])
  thus ?thesis using extreme_UCP_iff_adjoint[OF L U n d] by simp
qed

subsubsection \<open>An extreme channel has Choi rank at most $n$ (D22-6)\<close>

text \<open>Corollary to Choi's Theorem 3 (D22-6): an extreme CPTP map $M_n\to M_d$ with a minimal Kraus
representation $(V_i)_{i<r}$ has $r^2\le n^2$, i.e.\ $\mathrm{cr}(\Phi)\le n$.\<close>

corollary extreme_CPTP_kraus_length_le:
  assumes npos: "0 < n" and dpos: "0 < d"
      and \<Phi>_in: "\<Phi> \<in> CPTP n d"
      and rep: "cptp_kraus_rep n d \<Phi> Vs"
      and minimal: "lin_indep_complex_mat d n Vs"
      and ext: "extreme_CPTP n d \<Phi>"
  shows "length Vs \<le> n"
proof -
  have "lin_indep_complex_mat n n (kraus_products Vs)"
    using choi_theorem_3_cptp_iff[OF npos dpos \<Phi>_in rep minimal] ext by simp
  hence "length (kraus_products Vs) \<le> n * n" by (rule lin_indep_mats_length_le)
  thus ?thesis using power2_le_imp_le[of "length Vs" n] by (simp add: power2_eq_square length_kraus_products)
qed

corollary extreme_CPTP_choi_rank_le:
  assumes npos: "0 < n" and dpos: "0 < d"
      and \<Phi>_in: "\<Phi> \<in> CPTP n d"
      and rep: "cptp_kraus_rep n d \<Phi> Vs"
      and minimal: "lin_indep_complex_mat d n Vs"
      and ext: "extreme_CPTP n d \<Phi>"
  shows "choi_rank n d \<Phi> \<le> n"
proof -
  have Vc: "\<forall>A \<in> set Vs. A \<in> carrier_mat d n" and Vr: "\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi> X = kraus_map_dim d Vs X"
    using rep by (auto simp: cptp_kraus_rep_def kraus_operators_def)
  have "length Vs \<in> { length As | As :: complex Matrix.mat list.
             (\<forall>A \<in> set As. A \<in> carrier_mat d n)
             \<and> (\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi> X = kraus_map_dim d As X) }"
    using Vc Vr by blast
  hence "choi_rank n d \<Phi> \<le> length Vs"
    unfolding choi_rank_def by (intro cInf_lower) (auto intro: bdd_belowI[of _ 0])
  thus ?thesis using extreme_CPTP_kraus_length_le[OF assms] by simp
qed

end

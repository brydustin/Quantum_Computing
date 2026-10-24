theory HHL_Sparse_Circuit
  imports HHL_Sparse_Split
begin

section \<open>The sparse simulation circuit\<close>

subsection \<open>Permutation gates\<close>

lemma invol_pmat_unitary: "invol N \<sigma> \<Longrightarrow> unitary (pmat N \<sigma>)"
  by (rule pmat_unitary_invol) (auto simp: invol_lt invol_def)

subsection \<open>Registers\<close>

text \<open>Basis state $\ket{x}\ket{y}\ket{b}$ of the system register, the neighbour register and one
ancilla qubit.\<close>

definition enc :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "enc n x y b = (x * n + y) * 2 + b"

abbreviation (input) bstate :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex Matrix.vec" where
  "bstate n x y b \<equiv> unit_vec (n * n * 2) (enc n x y b)"

lemma reg_lt: "(x::nat) < n \<Longrightarrow> y < n \<Longrightarrow> x * n + y < n * n"
proof -
  assume x: "x < n" and y: "y < n"
  have "x * n + y < x * n + n" using y by simp
  also have "\<dots> = (x + 1) * n" by simp
  also have "\<dots> \<le> n * n" using x by (intro mult_right_mono) simp_all
  finally show ?thesis .
qed

lemma enc_lt:
  assumes "x < n" "y < n" "b < 2"
  shows "enc n x y b < n * n * 2"
proof -
  have "Suc (x * n + y) \<le> n * n" using reg_lt[OF assms(1,2)] by simp
  hence "Suc (x * n + y) * 2 \<le> n * n * 2" by (rule mult_le_mono1)
  thus ?thesis unfolding enc_def using assms(3) by simp
qed

lemma enc_div: "b < 2 \<Longrightarrow> enc n x y b div 2 = x * n + y"
  unfolding enc_def by simp

lemma enc_mod: "b < 2 \<Longrightarrow> enc n x y b mod 2 = b"
  unfolding enc_def using mod_mult_self3[of "x * n + y" 2 b] by simp

lemma enc_decode:
  assumes j: "j < n * n * 2"
  shows "j div 2 div n < n" "j div 2 mod n < n" "j mod 2 < 2"
    "j = enc n (j div 2 div n) (j div 2 mod n) (j mod 2)"
proof -
  have k: "j div 2 < n * n" using j by linarith
  hence n: "0 < n" by (cases n) auto
  show "j div 2 div n < n" using k by (simp add: less_mult_imp_div_less)
  show "j div 2 mod n < n" using n by simp
  show "j mod 2 < 2" by simp
  show "j = enc n (j div 2 div n) (j div 2 mod n) (j mod 2)" unfolding enc_def by simp
qed

lemma enc_eq_iff:
  "y < n \<Longrightarrow> y' < n \<Longrightarrow> b < 2 \<Longrightarrow> b' < 2 \<Longrightarrow>
   enc n x y b = enc n x' y' b' \<longleftrightarrow> x = x' \<and> y = y' \<and> b = b'"
  by (metis enc_div enc_mod mult_index_div_mod)

subsection \<open>The comparator\<close>

text \<open>$\ket x\ket y\ket b\mapsto\ket y\ket x\ket{1-b}$ when ($y<x$, $b=0$) or ($x<y$, $b=1$): it sorts the
pair $\{x,y\}$ and records the order in the ancilla.  A classical reversible involution.\<close>

definition cmp_perm :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "cmp_perm n j = (let x = j div 2 div n; y = j div 2 mod n; b = j mod 2 in
     if j < n * n * 2 \<and> ((y < x \<and> b = 0) \<or> (x < y \<and> b = 1)) then enc n y x (1 - b) else j)"

lemma cmp_perm_enc:
  assumes "x < n" "y < n" "b < 2"
  shows "cmp_perm n (enc n x y b) = (if (y < x \<and> b = 0) \<or> (x < y \<and> b = 1) then enc n y x (1 - b) else enc n x y b)"
  using assms enc_lt[OF assms] by (simp add: cmp_perm_def Let_def enc_div enc_mod mult_index_div_mod)

lemma cmp_perm_invol: "invol (n * n * 2) (cmp_perm n)"
  unfolding invol_def
proof (intro conjI allI impI)
  fix j
  show "cmp_perm n (cmp_perm n j) = j"
  proof (cases "j < n * n * 2")
    case True
    note dj = enc_decode[OF True]
    define x y b where "x = j div 2 div n" and "y = j div 2 mod n" and "b = j mod 2"
    have xyb: "x < n" "y < n" "b < 2" and j: "j = enc n x y b" using dj unfolding x_def y_def b_def by simp_all
    have b1: "1 - b < 2" by simp
    show ?thesis unfolding j cmp_perm_enc[OF xyb]
      using cmp_perm_enc[OF xyb(2,1) b1] cmp_perm_enc[OF xyb] xyb by auto
  next
    case False
    thus ?thesis by (simp add: cmp_perm_def)
  qed
next
  fix j assume "n * n * 2 \<le> j"
  thus "cmp_perm n j = j" by (simp add: cmp_perm_def)
qed

definition cmp_gate :: "nat \<Rightarrow> complex Matrix.mat" where
  "cmp_gate n = pmat (n * n * 2) (cmp_perm n)"

lemma cmp_gate_basis:
  assumes "x < n" "y < n" "b < 2"
  shows "cmp_gate n *\<^sub>v bstate n x y b =
    (if (y < x \<and> b = 0) \<or> (x < y \<and> b = 1) then bstate n y x (1 - b) else bstate n x y b)"
  unfolding cmp_gate_def pmat_unit[where f = "cmp_perm n", OF enc_lt[OF assms] invol_lt[OF cmp_perm_invol enc_lt[OF assms]]] cmp_perm_enc[OF assms] by simp

subsection \<open>The colour oracle\<close>

text \<open>A colour oracle for the matching $q$ is any unitary with $\ket x\ket0\ket b\mapsto\ket x\ket{q(x)}\ket b$.\<close>

definition colour_oracle :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> complex Matrix.mat \<Rightarrow> bool" where
  "colour_oracle n q Or \<longleftrightarrow> Or \<in> carrier_mat (n * n * 2) (n * n * 2) \<and> unitary Or \<and>
     (\<forall>x b. x < n \<longrightarrow> b < 2 \<longrightarrow> Or *\<^sub>v bstate n x 0 b = bstate n x (q x) b)"

lemma colour_oracle_adj:
  assumes O: "colour_oracle n q Or" and x: "x < n" and b: "b < 2" and q: "invol n q"
  shows "Or\<^sup>\<dagger> *\<^sub>v bstate n x (q x) b = bstate n x 0 b"
proof -
  have C: "Or \<in> carrier_mat (n * n * 2) (n * n * 2)" and u: "unitary Or"
    and a: "Or *\<^sub>v bstate n x 0 b = bstate n x (q x) b" using O x b unfolding colour_oracle_def by auto
  have n: "0 < n" using x by simp
  have e: "bstate n x 0 b \<in> carrier_vec (n * n * 2)" using enc_lt[OF x n b] by simp
  have "Or\<^sup>\<dagger> *\<^sub>v bstate n x (q x) b = Or\<^sup>\<dagger> *\<^sub>v (Or *\<^sub>v bstate n x 0 b)" by (simp only: a)
  also have "\<dots> = (Or\<^sup>\<dagger> * Or) *\<^sub>v bstate n x 0 b" by (rule assoc_mult_mat_vec[symmetric, OF dagger_carrier[OF C] C e])
  also have "Or\<^sup>\<dagger> * Or = 1\<^sub>m (n * n * 2)" using u C unfolding unitary_def by simp
  finally show ?thesis using e by simp
qed

text \<open>One implementation: the involution exchanging $\ket x\ket0$ and $\ket x\ket{q(x)}$.\<close>

definition col_perm :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "col_perm n q j = (let x = j div 2 div n; y = j div 2 mod n; b = j mod 2 in
     if j < n * n * 2 then enc n x (if y = 0 then q x else if y = q x then 0 else y) b else j)"

lemma col_perm_enc:
  assumes "x < n" "y < n" "b < 2"
  shows "col_perm n q (enc n x y b) = enc n x (if y = 0 then q x else if y = q x then 0 else y) b"
  using assms enc_lt[OF assms] by (simp add: col_perm_def Let_def enc_div enc_mod mult_index_div_mod)

lemma col_perm_invol:
  assumes q: "invol n q"
  shows "invol (n * n * 2) (col_perm n q)"
  unfolding invol_def
proof (intro conjI allI impI)
  fix j
  show "col_perm n q (col_perm n q j) = j"
  proof (cases "j < n * n * 2")
    case True
    note dj = enc_decode[OF True]
    define x y b where "x = j div 2 div n" and "y = j div 2 mod n" and "b = j mod 2"
    have xyb: "x < n" "y < n" "b < 2" and j: "j = enc n x y b" using dj unfolding x_def y_def b_def by simp_all
    have n: "0 < n" using xyb by simp
    have y': "(if y = 0 then q x else if y = q x then 0 else y) < n" using invol_lt[OF q xyb(1)] xyb n by auto
    show ?thesis unfolding j col_perm_enc[OF xyb] col_perm_enc[OF xyb(1) y' xyb(3)] by auto
  next
    case False
    thus ?thesis by (simp add: col_perm_def)
  qed
next
  fix j assume "n * n * 2 \<le> j"
  thus "col_perm n q j = j" by (simp add: col_perm_def)
qed

lemma colour_oracle_exists:
  assumes q: "invol n q"
  shows "colour_oracle n q (pmat (n * n * 2) (col_perm n q))"
  unfolding colour_oracle_def
proof (intro conjI allI impI)
  show "unitary (pmat (n * n * 2) (col_perm n q))" by (rule invol_pmat_unitary[OF col_perm_invol[OF q]])
  fix x b :: nat assume x: "x < n" and b: "b < 2"
  have n: "0 < n" using x by simp
  show "pmat (n * n * 2) (col_perm n q) *\<^sub>v bstate n x 0 b = bstate n x (q x) b"
    unfolding pmat_unit[where f = "col_perm n q", OF enc_lt[OF x n b] invol_lt[OF col_perm_invol[OF q] enc_lt[OF x n b]]] col_perm_enc[OF x n b] by simp
qed simp

subsection \<open>The entry gate\<close>

text \<open>Controlled on $\ket x\ket y$, the ancilla is rotated by $e^{id\,(\begin{smallmatrix}0&a\\ \bar a&0\end{smallmatrix})}$
with $a=A_{xy}$ ($a=0$ when $x=y$).  This is the only gate that reads entries of $A$.\<close>

definition ent_block :: "real \<Rightarrow> complex Matrix.mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
  "ent_block d A x y = (let a = (if x = y then 0 else A $$ (x, y)); u = a / complex_of_real (cmod a) in
     Matrix.mat 2 2 (\<lambda>(i, j). if i = j then complex_of_real (cos (d * cmod a))
        else if i = 0 then \<i> * complex_of_real (sin (d * cmod a)) * u
        else \<i> * complex_of_real (sin (d * cmod a)) * cnj u))"

definition ent_gate :: "nat \<Rightarrow> real \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "ent_gate n d A = ctrl_blocks (n * n) 2 (\<lambda>k. ent_block d A (k div n) (k mod n))"

lemma ent_gate_carrier [simp]: "ent_gate n d A \<in> carrier_mat (n * n * 2) (n * n * 2)"
  unfolding ent_gate_def by (rule ctrl_blocks_carrier)

lemma ent_gate_basis:
  assumes x: "x < n" and y: "y < n" and b: "b < 2"
  shows "ent_gate n d A *\<^sub>v bstate n x y b =
    ent_block d A x y $$ (0, b) \<cdot>\<^sub>v bstate n x y 0 + ent_block d A x y $$ (1, b) \<cdot>\<^sub>v bstate n x y 1"
proof (rule eq_vecI)
  have j: "enc n x y b < n * n * 2" by (rule enc_lt[OF x y b])
  fix r assume "r < dim_vec (ent_block d A x y $$ (0, b) \<cdot>\<^sub>v bstate n x y 0 + ent_block d A x y $$ (1, b) \<cdot>\<^sub>v bstate n x y 1)"
  hence r: "r < n * n * 2" by simp
  have l: "(ent_gate n d A *\<^sub>v bstate n x y b) $ r =
      (if r div 2 = x * n + y then ent_block d A x y $$ (r mod 2, b) else 0)"
    unfolding mult_unit_vec[OF ent_gate_carrier j] using r j
    by (simp add: ent_gate_def ctrl_blocks_index enc_div[OF b] enc_mod[OF b] mult_index_div_mod[OF y] y)
  have e0: "enc n x y 0 = (x * n + y) * 2" and e1: "enc n x y 1 = (x * n + y) * 2 + 1" by (simp_all add: enc_def)
  show "(ent_gate n d A *\<^sub>v bstate n x y b) $ r =
      (ent_block d A x y $$ (0, b) \<cdot>\<^sub>v bstate n x y 0 + ent_block d A x y $$ (1, b) \<cdot>\<^sub>v bstate n x y 1) $ r"
  proof (cases "r div 2 = x * n + y")
    case True
    have rr: "r = (x * n + y) * 2 + r mod 2" using div_mult_mod_eq[of r 2] True by simp
    have i0: "enc n x y 0 < n * n * 2" and i1: "enc n x y 1 < n * n * 2" using enc_lt[OF x y] by simp_all
    have rhs: "(ent_block d A x y $$ (0, b) \<cdot>\<^sub>v bstate n x y 0 + ent_block d A x y $$ (1, b) \<cdot>\<^sub>v bstate n x y 1) $ r =
        ent_block d A x y $$ (0, b) * (if r = enc n x y 0 then 1 else 0) +
        ent_block d A x y $$ (1, b) * (if r = enc n x y 1 then 1 else 0)"
      using r by (simp add: unit_vec_def)
    show ?thesis
    proof (cases "r mod 2 = 0")
      case True
      hence "r = enc n x y 0" "r \<noteq> enc n x y 1" using rr unfolding e0 e1 by simp_all
      thus ?thesis unfolding l rhs using \<open>r div 2 = x * n + y\<close> True by simp
    next
      case False
      hence m: "r mod 2 = 1" by simp
      hence "r = enc n x y 1" "r \<noteq> enc n x y 0" using rr unfolding e0 e1 by simp_all
      thus ?thesis unfolding l rhs using \<open>r div 2 = x * n + y\<close> m by simp
    qed
  next
    case False
    have "r \<noteq> enc n x y 0" "r \<noteq> enc n x y 1" using False unfolding e0 e1 by auto
    thus ?thesis unfolding l using False r by (simp add: unit_vec_def)
  qed
qed (simp add: ent_gate_def)

subsection \<open>The embedding and the exact 1-sparse evolution\<close>

text \<open>\<open>emb n\<close> maps $\ket x$ to $\ket x\ket0\ket0$.\<close>

definition emb :: "nat \<Rightarrow> complex Matrix.mat" where
  "emb n = Matrix.mat (n * n * 2) n (\<lambda>(r, c). if r = enc n c 0 0 then 1 else 0)"

lemma emb_carrier [simp]: "emb n \<in> carrier_mat (n * n * 2) n"
  by (simp add: emb_def)

lemma emb_unit:
  assumes k: "k < n"
  shows "emb n *\<^sub>v unit_vec n k = bstate n k 0 0"
proof (rule eq_vecI)
  fix r assume "r < dim_vec (bstate n k 0 0)"
  hence r: "r < n * n * 2" by simp
  have "(emb n *\<^sub>v unit_vec n k) $ r = Matrix.row (emb n) r \<bullet> unit_vec n k" using r by (simp add: emb_def)
  also have "\<dots> = Matrix.row (emb n) r $ k" by (rule scalar_prod_right_unit[OF k])
  also have "\<dots> = (if r = enc n k 0 0 then 1 else 0)" using r k by (simp add: emb_def)
  finally show "(emb n *\<^sub>v unit_vec n k) $ r = bstate n k 0 0 $ r" using r enc_lt[OF k _ zero_less_numeral, of 0] k
    by (simp add: unit_vec_def)
qed (simp add: emb_def)

lemma one_sparse_unit:
  assumes q: "invol n q" and k: "k < n"
  shows "one_sparse n q g *\<^sub>v unit_vec n k = g (q k) \<cdot>\<^sub>v unit_vec n (q k)"
proof -
  have "one_sparse n q g *\<^sub>v unit_vec n k = Matrix.vec n (\<lambda>i. g i * unit_vec n k $ q i)"
    by (rule one_sparse_mult_vec[OF q]) simp
  also have "\<dots> = g (q k) \<cdot>\<^sub>v unit_vec n (q k)"
  proof (rule eq_vecI)
    fix i assume "i < dim_vec (g (q k) \<cdot>\<^sub>v unit_vec n (q k))"
    hence i: "i < n" by simp
    have "q i = k \<longleftrightarrow> i = q k" using invol_eq[OF q, of i k] by auto
    thus "Matrix.vec n (\<lambda>i. g i * unit_vec n k $ q i) $ i = (g (q k) \<cdot>\<^sub>v unit_vec n (q k)) $ i"
      using i invol_lt[OF q i] invol_lt[OF q k] by (auto simp: unit_vec_def)
  qed simp
  finally show ?thesis .
qed

definition colour_h :: "complex Matrix.mat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> complex" where
  "colour_h A q i = (if q i = i then 0 else A $$ (i, q i))"

lemma colour_part_eq: "colour_part n A q = one_sparse n q (colour_h A q)"
  by (simp add: colour_part_def colour_h_def[abs_def])

text \<open>$e^{idH}$ for a 1-sparse $H$: $\cos(d|h_i|)$ on the diagonal and
$i\sin(d|h_i|)\,h_i/|h_i|$ at the partner position.\<close>

definition pair_evo :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> complex) \<Rightarrow> real \<Rightarrow> complex Matrix.mat" where
  "pair_evo n q h d = one_sparse n (\<lambda>i. i) (\<lambda>i. complex_of_real (cos (d * cmod (h i)))) +
     one_sparse n q (\<lambda>i. \<i> * complex_of_real (sin (d * cmod (h i))) * (h i / complex_of_real (cmod (h i))))"

lemma pair_evo_carrier [simp]: "pair_evo n q h d \<in> carrier_mat n n"
  by (simp add: pair_evo_def)

lemma pair_evo_unit:
  assumes q: "invol n q" and k: "k < n"
  shows "pair_evo n q h d *\<^sub>v unit_vec n k =
    complex_of_real (cos (d * cmod (h k))) \<cdot>\<^sub>v unit_vec n k +
    (\<i> * complex_of_real (sin (d * cmod (h (q k)))) * (h (q k) / complex_of_real (cmod (h (q k))))) \<cdot>\<^sub>v unit_vec n (q k)"
  unfolding pair_evo_def
  by (simp add: add_mult_distrib_mat_vec[of _ n n] one_sparse_unit[OF q k] one_sparse_unit[OF invol_id k])

subsection \<open>One colour\<close>

text \<open>Query the neighbour, sort the pair, rotate the ancilla, unsort, unquery.\<close>

definition colour_circ :: "nat \<Rightarrow> real \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "colour_circ n d A Or = Or\<^sup>\<dagger> * (cmp_gate n * (ent_gate n d A * (cmp_gate n * Or)))"

lemma cmp_gate_carrier [simp]: "cmp_gate n \<in> carrier_mat (n * n * 2) (n * n * 2)"
  by (simp add: cmp_gate_def)

lemma lin2:
  fixes M :: "complex Matrix.mat"
  assumes M: "M \<in> carrier_mat nr nc" and u: "dim_vec u = nc" and w: "dim_vec w = nc"
  shows "M *\<^sub>v (\<alpha> \<cdot>\<^sub>v u + \<beta> \<cdot>\<^sub>v w) = \<alpha> \<cdot>\<^sub>v (M *\<^sub>v u) + \<beta> \<cdot>\<^sub>v (M *\<^sub>v w)"
proof -
  have u': "u \<in> carrier_vec nc" and w': "w \<in> carrier_vec nc" by (rule carrier_vecI[OF u], rule carrier_vecI[OF w])
  have "M *\<^sub>v (\<alpha> \<cdot>\<^sub>v u + \<beta> \<cdot>\<^sub>v w) = M *\<^sub>v (\<alpha> \<cdot>\<^sub>v u) + M *\<^sub>v (\<beta> \<cdot>\<^sub>v w)"
    by (rule mult_add_distrib_mat_vec[OF M smult_carrier_vec[THEN iffD2, OF u'] smult_carrier_vec[THEN iffD2, OF w']])
  also have "M *\<^sub>v (\<alpha> \<cdot>\<^sub>v u) = \<alpha> \<cdot>\<^sub>v (M *\<^sub>v u)" by (rule mult_mat_vec[OF M u'])
  also have "M *\<^sub>v (\<beta> \<cdot>\<^sub>v w) = \<beta> \<cdot>\<^sub>v (M *\<^sub>v w)" by (rule mult_mat_vec[OF M w'])
  finally show ?thesis .
qed

lemma colour_circ_apply:
  assumes O: "Or \<in> carrier_mat (n * n * 2) (n * n * 2)" and v: "dim_vec v = n * n * 2"
  shows "colour_circ n d A Or *\<^sub>v v = Or\<^sup>\<dagger> *\<^sub>v (cmp_gate n *\<^sub>v (ent_gate n d A *\<^sub>v (cmp_gate n *\<^sub>v (Or *\<^sub>v v))))"
proof -
  let ?N = "n * n * 2"
  have vc: "v \<in> carrier_vec ?N" by (rule carrier_vecI[OF v])
  have C1: "cmp_gate n * Or \<in> carrier_mat ?N ?N" by (rule mult_carrier_mat[OF cmp_gate_carrier O])
  have C2: "ent_gate n d A * (cmp_gate n * Or) \<in> carrier_mat ?N ?N" by (rule mult_carrier_mat[OF ent_gate_carrier C1])
  have C3: "cmp_gate n * (ent_gate n d A * (cmp_gate n * Or)) \<in> carrier_mat ?N ?N" by (rule mult_carrier_mat[OF cmp_gate_carrier C2])
  have "colour_circ n d A Or *\<^sub>v v = Or\<^sup>\<dagger> *\<^sub>v ((cmp_gate n * (ent_gate n d A * (cmp_gate n * Or))) *\<^sub>v v)"
    unfolding colour_circ_def by (rule assoc_mult_mat_vec[OF dagger_carrier[OF O] C3 vc])
  also have "(cmp_gate n * (ent_gate n d A * (cmp_gate n * Or))) *\<^sub>v v = cmp_gate n *\<^sub>v ((ent_gate n d A * (cmp_gate n * Or)) *\<^sub>v v)"
    by (rule assoc_mult_mat_vec[OF cmp_gate_carrier C2 vc])
  also have "(ent_gate n d A * (cmp_gate n * Or)) *\<^sub>v v = ent_gate n d A *\<^sub>v ((cmp_gate n * Or) *\<^sub>v v)"
    by (rule assoc_mult_mat_vec[OF ent_gate_carrier C1 vc])
  also have "(cmp_gate n * Or) *\<^sub>v v = cmp_gate n *\<^sub>v (Or *\<^sub>v v)"
    by (rule assoc_mult_mat_vec[OF cmp_gate_carrier O vc])
  finally show ?thesis .
qed

lemma ent_block_index:
  "ent_block d A x y $$ (0, 0) = complex_of_real (cos (d * cmod (if x = y then 0 else A $$ (x, y))))"
  "ent_block d A x y $$ (1, 1) = complex_of_real (cos (d * cmod (if x = y then 0 else A $$ (x, y))))"
  "ent_block d A x y $$ (0, 1) = \<i> * complex_of_real (sin (d * cmod (if x = y then 0 else A $$ (x, y)))) *
     ((if x = y then 0 else A $$ (x, y)) / complex_of_real (cmod (if x = y then 0 else A $$ (x, y))))"
  "ent_block d A x y $$ (1, 0) = \<i> * complex_of_real (sin (d * cmod (if x = y then 0 else A $$ (x, y)))) *
     cnj ((if x = y then 0 else A $$ (x, y)) / complex_of_real (cmod (if x = y then 0 else A $$ (x, y))))"
  by (simp_all add: ent_block_def Let_def)

lemma lin2':
  fixes M :: "complex Matrix.mat"
  assumes M: "M \<in> carrier_mat nr nc" and u: "dim_vec u = nc" and w: "dim_vec w = nc"
      and Mu: "M *\<^sub>v u = u'" and Mw: "M *\<^sub>v w = w'"
  shows "M *\<^sub>v (\<alpha> \<cdot>\<^sub>v u + \<beta> \<cdot>\<^sub>v w) = \<alpha> \<cdot>\<^sub>v u' + \<beta> \<cdot>\<^sub>v w'"
  using lin2[OF M u w] Mu Mw by simp

text \<open>The circuit for colour $q$, started in $\ket k\ket0\ket0$, outputs $(e^{idH_q}\ket k)\ket0\ket0$.\<close>

lemma colour_circ_basis:
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and q: "invol n q" and O: "colour_oracle n q Or" and k: "k < n"
  shows "colour_circ n d A Or *\<^sub>v bstate n k 0 0 = emb n *\<^sub>v (pair_evo n q (colour_h A q) d *\<^sub>v unit_vec n k)"
proof -
  let ?N = "n * n * 2"
  have Oc: "Or \<in> carrier_mat ?N ?N"
    and Oa: "\<And>x b. x < n \<Longrightarrow> b < 2 \<Longrightarrow> Or *\<^sub>v bstate n x 0 b = bstate n x (q x) b"
    using O unfolding colour_oracle_def by auto
  have Od: "\<And>x b. x < n \<Longrightarrow> b < 2 \<Longrightarrow> Or\<^sup>\<dagger> *\<^sub>v bstate n x (q x) b = bstate n x 0 b"
    by (rule colour_oracle_adj[OF O _ _ q])
  have Odc: "Or\<^sup>\<dagger> \<in> carrier_mat ?N ?N" by (rule dagger_carrier[OF Oc])
  define v where "v = q k"
  have v: "v < n" using invol_lt[OF q k] unfolding v_def .
  have qv: "q v = k" using q unfolding v_def invol_def by simp
  have qk: "q k = v" unfolding v_def ..
  define c where "c = complex_of_real (cos (d * cmod (colour_h A q k)))"
  define s where "s = \<i> * complex_of_real (sin (d * cmod (colour_h A q v))) *
      (colour_h A q v / complex_of_real (cmod (colour_h A q v)))"
  have "pair_evo n q (colour_h A q) d *\<^sub>v unit_vec n k = c \<cdot>\<^sub>v unit_vec n k + s \<cdot>\<^sub>v unit_vec n v"
    unfolding pair_evo_unit[OF q k] c_def s_def v_def ..
  hence rhs: "emb n *\<^sub>v (pair_evo n q (colour_h A q) d *\<^sub>v unit_vec n k) = c \<cdot>\<^sub>v bstate n k 0 0 + s \<cdot>\<^sub>v bstate n v 0 0"
    using lin2'[OF emb_carrier _ _ emb_unit[OF k] emb_unit[OF v], of c s] by simp
  have lhs: "colour_circ n d A Or *\<^sub>v bstate n k 0 0 =
      Or\<^sup>\<dagger> *\<^sub>v (cmp_gate n *\<^sub>v (ent_gate n d A *\<^sub>v (cmp_gate n *\<^sub>v bstate n k v 0)))"
    using colour_circ_apply[OF Oc, of "bstate n k 0 0" d A] Oa[of k 0] k qk by simp
  have hk: "colour_h A q k = A $$ (k, v)" if "k \<noteq> v" using that qk unfolding colour_h_def by simp
  have hv: "colour_h A q v = A $$ (v, k)" if "k \<noteq> v" using that qv unfolding colour_h_def by simp
  have herm: "A $$ (v, k) = cnj (A $$ (k, v))" by (rule hermitian_index_cnj[OF A(2)]) (use A(1) v k in simp_all)
  show ?thesis
  proof (cases "k = v")
    case True
    have h0: "colour_h A q k = 0" "colour_h A q v = 0" using True qk unfolding colour_h_def by simp_all
    have cs: "c = 1" "s = 0" unfolding c_def s_def h0 by simp_all
    have g: "ent_block d A k k $$ (0, 0) = 1" "ent_block d A k k $$ (1, 0) = 0" by (simp_all add: ent_block_def Let_def)
    have s1: "cmp_gate n *\<^sub>v bstate n k k 0 = bstate n k k 0" using cmp_gate_basis[OF k k, of 0] by simp
    have s2: "ent_gate n d A *\<^sub>v bstate n k k 0 = 1 \<cdot>\<^sub>v bstate n k k 0 + 0 \<cdot>\<^sub>v bstate n k k 1"
      using ent_gate_basis[OF k k, of 0 d A] g by simp
    have s3: "cmp_gate n *\<^sub>v (1 \<cdot>\<^sub>v bstate n k k 0 + 0 \<cdot>\<^sub>v bstate n k k 1) = 1 \<cdot>\<^sub>v bstate n k k 0 + 0 \<cdot>\<^sub>v bstate n k k 1"
      by (rule lin2'[OF cmp_gate_carrier]) (simp_all add: cmp_gate_basis k)
    have s4: "Or\<^sup>\<dagger> *\<^sub>v (1 \<cdot>\<^sub>v bstate n k k 0 + 0 \<cdot>\<^sub>v bstate n k k 1) = 1 \<cdot>\<^sub>v bstate n k 0 0 + 0 \<cdot>\<^sub>v bstate n k 0 1"
      by (rule lin2'[OF Odc]) (use Od[of k 0] Od[of k 1] k qk True in simp_all)
    have "colour_circ n d A Or *\<^sub>v bstate n k 0 0 = 1 \<cdot>\<^sub>v bstate n k 0 0 + 0 \<cdot>\<^sub>v bstate n k 0 1"
      unfolding lhs True[symmetric] s1 s2 s3 s4 ..
    thus ?thesis unfolding rhs cs True[symmetric] by (intro eq_vecI) simp_all
  next
    case False
    note hk = hk[OF False] and hv = hv[OF False]
    show ?thesis
    proof (cases "k < v")
      case True
      have g: "ent_block d A k v $$ (0, 0) = c" "ent_block d A k v $$ (1, 0) = s"
        using False unfolding c_def s_def hk hv herm by (simp_all add: ent_block_def Let_def)
      have s1: "cmp_gate n *\<^sub>v bstate n k v 0 = bstate n k v 0" using cmp_gate_basis[OF k v, of 0] True by simp
      have s2: "ent_gate n d A *\<^sub>v bstate n k v 0 = c \<cdot>\<^sub>v bstate n k v 0 + s \<cdot>\<^sub>v bstate n k v 1"
        using ent_gate_basis[OF k v, of 0 d A] g by simp
      have s3: "cmp_gate n *\<^sub>v (c \<cdot>\<^sub>v bstate n k v 0 + s \<cdot>\<^sub>v bstate n k v 1) = c \<cdot>\<^sub>v bstate n k v 0 + s \<cdot>\<^sub>v bstate n v k 0"
        by (rule lin2'[OF cmp_gate_carrier]) (use True in \<open>simp_all add: cmp_gate_basis k v not_less_iff_gr_or_eq\<close>)
      have s4: "Or\<^sup>\<dagger> *\<^sub>v (c \<cdot>\<^sub>v bstate n k v 0 + s \<cdot>\<^sub>v bstate n v k 0) = c \<cdot>\<^sub>v bstate n k 0 0 + s \<cdot>\<^sub>v bstate n v 0 0"
        by (rule lin2'[OF Odc]) (use Od[of k 0] Od[of v 0] k v qk qv in simp_all)
      show ?thesis unfolding rhs lhs s1 s2 s3 s4 ..
    next
      case lt: False
      hence vk: "v < k" using False by simp
      have g: "ent_block d A v k $$ (1, 1) = c" "ent_block d A v k $$ (0, 1) = s"
        using False unfolding c_def s_def hk hv by (simp_all add: ent_block_def Let_def herm)
      have s1: "cmp_gate n *\<^sub>v bstate n k v 0 = bstate n v k 1" using cmp_gate_basis[OF k v, of 0] vk by simp
      have s2: "ent_gate n d A *\<^sub>v bstate n v k 1 = s \<cdot>\<^sub>v bstate n v k 0 + c \<cdot>\<^sub>v bstate n v k 1"
        using ent_gate_basis[OF v k, of 1 d A] g by simp
      have s3: "cmp_gate n *\<^sub>v (s \<cdot>\<^sub>v bstate n v k 0 + c \<cdot>\<^sub>v bstate n v k 1) = s \<cdot>\<^sub>v bstate n v k 0 + c \<cdot>\<^sub>v bstate n k v 0"
        by (rule lin2'[OF cmp_gate_carrier]) (use vk in \<open>simp_all add: cmp_gate_basis k v not_less_iff_gr_or_eq\<close>)
      have s4: "Or\<^sup>\<dagger> *\<^sub>v (s \<cdot>\<^sub>v bstate n v k 0 + c \<cdot>\<^sub>v bstate n k v 0) = s \<cdot>\<^sub>v bstate n v 0 0 + c \<cdot>\<^sub>v bstate n k 0 0"
        by (rule lin2'[OF Odc]) (use Od[of k 0] Od[of v 0] k v qk qv in simp_all)
      have "colour_circ n d A Or *\<^sub>v bstate n k 0 0 = s \<cdot>\<^sub>v bstate n v 0 0 + c \<cdot>\<^sub>v bstate n k 0 0"
        unfolding lhs s1 s2 s3 s4 ..
      thus ?thesis unfolding rhs by (intro eq_vecI) simp_all
    qed
  qed
qed

subsection \<open>The exact evolution of a 1-sparse part\<close>

lemma pair_scalar:
  fixes hi vi vq :: complex and l d :: real
  assumes e1: "hi * vq = complex_of_real l * vi" and e2: "cnj hi * vi = complex_of_real l * vq"
  shows "complex_of_real (cos (d * cmod hi)) * vi +
      \<i> * complex_of_real (sin (d * cmod hi)) * (hi / complex_of_real (cmod hi)) * vq = cis (d * l) * vi"
proof (cases "hi = 0")
  case True
  have "complex_of_real l * vi = 0" using e1 True by simp
  hence "l = 0 \<or> vi = 0" by simp
  thus ?thesis using True by auto
next
  case False
  define a where "a = cmod hi"
  have a: "0 < a" using False unfolding a_def by simp
  have q: "(hi / complex_of_real a) * vq = complex_of_real l * vi / complex_of_real a"
    using e1 by (simp add: field_simps)
  show ?thesis
  proof (cases "vi = 0")
    case True
    hence "vq = 0" using e1 False by simp
    thus ?thesis using True by simp
  next
    case vi: False
    have "complex_of_real l * complex_of_real l * vi = complex_of_real l * (hi * vq)" using e1 by simp
    also have "\<dots> = hi * (cnj hi * vi)" using e2 by (simp add: algebra_simps)
    also have "\<dots> = (hi * cnj hi) * vi" by (simp add: algebra_simps)
    also have "hi * cnj hi = complex_of_real (a\<^sup>2)" unfolding a_def by (rule complex_norm_square[symmetric])
    finally have "complex_of_real (l\<^sup>2) = complex_of_real (a\<^sup>2)" using vi by (simp add: power2_eq_square)
    hence "l\<^sup>2 = a\<^sup>2" by (simp only: of_real_eq_iff)
    hence l: "l = a \<or> l = - a" by (simp add: power2_eq_iff)
    have "complex_of_real (cos (d * a)) * vi + \<i> * complex_of_real (sin (d * a)) * (hi / complex_of_real a) * vq =
        (complex_of_real (cos (d * a)) + \<i> * complex_of_real (sin (d * a)) * complex_of_real (l / a)) * vi"
      using q a by (simp add: algebra_simps)
    also have "\<dots> = cis (d * l) * vi"
      using l a by (auto simp: complex_eq_iff cis.sel)
    finally show ?thesis unfolding a_def .
  qed
qed

lemma colour_h_cnj:
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and q: "invol n q" and i: "i < n"
  shows "colour_h A q (q i) = cnj (colour_h A q i)"
proof (cases "q i = i")
  case True
  thus ?thesis by (simp add: colour_h_def)
next
  case False
  have qq: "q (q i) = i" using q unfolding invol_def by simp
  hence "q (q i) \<noteq> q i" using False by simp
  thus ?thesis using False qq hermitian_index_cnj[OF A(2), of "q i" i] carrier_matD[OF A(1)] invol_lt[OF q i] i by (simp add: colour_h_def)
qed

text \<open>The closed form of $e^{idH}$ for the colour part $H$.\<close>

theorem evolution_colour_part:
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and q: "invol n q"
  shows "evolution (colour_part n A q) d = pair_evo n q (colour_h A q) d"
  unfolding evolution_def
proof (rule mat_fun_eqI)
  show H: "colour_part n A q \<in> carrier_mat n n" "hermitian (colour_part n A q)"
    by (simp add: colour_part_def, rule colour_part_hermitian[OF A q])
  show "pair_evo n q (colour_h A q) d \<in> carrier_mat n n" by simp
  show "pair_evo n q (colour_h A q) d acts_as (\<lambda>x. cis (d * x)) on_eigenvectors_of colour_part n A q"
    unfolding acts_on_eigenvectors_def
  proof (intro allI impI)
    fix v l assume v: "dim_vec v = dim_row (colour_part n A q)"
      and ev: "colour_part n A q *\<^sub>v v = complex_of_real l \<cdot>\<^sub>v v"
    have vn: "dim_vec v = n" using v H(1) by simp
    let ?h = "colour_h A q"
    have Hv: "colour_part n A q *\<^sub>v v = Matrix.vec n (\<lambda>i. ?h i * v $ q i)"
      unfolding colour_part_eq by (rule one_sparse_mult_vec[OF q vn])
    have e: "?h i * v $ q i = complex_of_real l * v $ i" if "i < n" for i
    proof -
      have "(colour_part n A q *\<^sub>v v) $ i = (complex_of_real l \<cdot>\<^sub>v v) $ i" by (simp only: ev)
      thus ?thesis unfolding Hv using that vn by simp
    qed
    have Pv: "pair_evo n q ?h d *\<^sub>v v = Matrix.vec n (\<lambda>i. complex_of_real (cos (d * cmod (?h i))) * v $ i +
        \<i> * complex_of_real (sin (d * cmod (?h i))) * (?h i / complex_of_real (cmod (?h i))) * v $ q i)"
      unfolding pair_evo_def
      using add_mult_distrib_mat_vec[OF one_sparse_carrier one_sparse_carrier carrier_vecI[OF vn]]
        one_sparse_mult_vec[OF q vn] one_sparse_mult_vec[OF invol_id vn]
      by (auto intro!: eq_vecI)
    show "pair_evo n q ?h d *\<^sub>v v = cis (d * l) \<cdot>\<^sub>v v"
    proof (rule eq_vecI)
      fix i assume "i < dim_vec (cis (d * l) \<cdot>\<^sub>v v)"
      hence i: "i < n" using vn by simp
      have qi: "q i < n" by (rule invol_lt[OF q i])
      have qq: "q (q i) = i" using q unfolding invol_def by simp
      have e1: "?h i * v $ q i = complex_of_real l * v $ i" by (rule e[OF i])
      have e2: "cnj (?h i) * v $ i = complex_of_real l * v $ q i"
        using e[OF qi] qq colour_h_cnj[OF A q i] by simp
      show "(pair_evo n q ?h d *\<^sub>v v) $ i = (cis (d * l) \<cdot>\<^sub>v v) $ i"
        unfolding Pv using i vn pair_scalar[OF e1 e2, of d] by simp
    qed (simp add: vn pair_evo_def one_sparse_def)
  qed
qed

subsection \<open>Intertwining\<close>

text \<open>A circuit $C$ that maps $\ket k\ket0\ket0$ to $(E\ket k)\ket0\ket0$ for all $k$ satisfies
$C\,\mathrm{emb}=\mathrm{emb}\,E$.\<close>

lemma emb_intertwine:
  assumes C: "C \<in> carrier_mat (n * n * 2) (n * n * 2)" and E: "E \<in> carrier_mat n n"
      and act: "\<And>k. k < n \<Longrightarrow> C *\<^sub>v bstate n k 0 0 = emb n *\<^sub>v (E *\<^sub>v unit_vec n k)"
  shows "C * emb n = emb n * E"
proof (rule Matrix.mat_col_eqI)
  fix k assume "k < dim_col (emb n * E)"
  hence k: "k < n" using E by simp
  have "Matrix.col (C * emb n) k = C *\<^sub>v Matrix.col (emb n) k" by (rule col_mult2[OF C emb_carrier k])
  also have "Matrix.col (emb n) k = bstate n k 0 0" using mult_unit_vec[OF emb_carrier k] emb_unit[OF k] by simp
  also have "C *\<^sub>v bstate n k 0 0 = emb n *\<^sub>v (E *\<^sub>v unit_vec n k)" by (rule act[OF k])
  also have "E *\<^sub>v unit_vec n k = Matrix.col E k" by (rule mult_unit_vec[OF E k])
  also have "emb n *\<^sub>v Matrix.col E k = Matrix.col (emb n * E) k" by (rule col_mult2[OF emb_carrier E k, symmetric])
  finally show "Matrix.col (C * emb n) k = Matrix.col (emb n * E) k" .
qed (use C E in \<open>simp_all add: emb_def\<close>)

lemma colour_circ_carrier:
  assumes O: "Or \<in> carrier_mat (n * n * 2) (n * n * 2)"
  shows "colour_circ n d A Or \<in> carrier_mat (n * n * 2) (n * n * 2)"
  unfolding colour_circ_def
  by (rule mult_carrier_mat[OF dagger_carrier[OF O] mult_carrier_mat[OF cmp_gate_carrier
        mult_carrier_mat[OF ent_gate_carrier mult_carrier_mat[OF cmp_gate_carrier O]]]])

theorem colour_circ_intertwine:
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and q: "invol n q" and O: "colour_oracle n q Or"
  shows "colour_circ n d A Or * emb n = emb n * evolution (colour_part n A q) d"
proof -
  have Oc: "Or \<in> carrier_mat (n * n * 2) (n * n * 2)" using O unfolding colour_oracle_def by simp
  show ?thesis unfolding evolution_colour_part[OF A q]
    by (rule emb_intertwine[OF colour_circ_carrier[OF Oc] pair_evo_carrier colour_circ_basis[OF A q O]])
qed

subsection \<open>The diagonal\<close>

text \<open>The diagonal part is a phase $e^{idA_{xx}}$ on $\ket x$, one entry query.\<close>

definition dia_gate :: "nat \<Rightarrow> real \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "dia_gate n d A = one_sparse (n * n * 2) (\<lambda>j. j) (\<lambda>j. cis (d * Re (A $$ (j div 2 div n, j div 2 div n))))"

lemma dia_gate_carrier [simp]: "dia_gate n d A \<in> carrier_mat (n * n * 2) (n * n * 2)"
  by (simp add: dia_gate_def)

definition dia_evo :: "nat \<Rightarrow> real \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "dia_evo n d A = one_sparse n (\<lambda>i. i) (\<lambda>i. cis (d * Re (A $$ (i, i))))"

lemma hermitian_diag_real:
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and i: "i < n"
  shows "A $$ (i, i) = complex_of_real (Re (A $$ (i, i)))"
  using hermitian_index_cnj[OF A(2), of i i] carrier_matD[OF A(1)] i by (simp add: complex_eq_iff)

theorem evolution_diag_part:
  assumes A: "A \<in> carrier_mat n n" "hermitian A"
  shows "evolution (diag_part n A) d = dia_evo n d A"
  unfolding evolution_def
proof (rule mat_fun_eqI)
  show H: "diag_part n A \<in> carrier_mat n n" "hermitian (diag_part n A)"
    by (simp add: diag_part_def, rule diag_part_hermitian[OF A])
  show "dia_evo n d A \<in> carrier_mat n n" by (simp add: dia_evo_def)
  show "dia_evo n d A acts_as (\<lambda>x. cis (d * x)) on_eigenvectors_of diag_part n A"
    unfolding acts_on_eigenvectors_def
  proof (intro allI impI)
    fix v l assume v: "dim_vec v = dim_row (diag_part n A)"
      and ev: "diag_part n A *\<^sub>v v = complex_of_real l \<cdot>\<^sub>v v"
    have vn: "dim_vec v = n" using v H(1) by simp
    have e: "A $$ (i, i) * v $ i = complex_of_real l * v $ i" if i: "i < n" for i
    proof -
      have "(diag_part n A *\<^sub>v v) $ i = (complex_of_real l \<cdot>\<^sub>v v) $ i" by (simp only: ev)
      thus ?thesis unfolding diag_part_def one_sparse_mult_vec[OF invol_id vn] using i vn by simp
    qed
    show "dia_evo n d A *\<^sub>v v = cis (d * l) \<cdot>\<^sub>v v"
    proof (rule eq_vecI)
      fix i assume "i < dim_vec (cis (d * l) \<cdot>\<^sub>v v)"
      hence i: "i < n" using vn by simp
      have "cis (d * Re (A $$ (i, i))) * v $ i = cis (d * l) * v $ i"
      proof (cases "v $ i = 0")
        case False
        have "complex_of_real (Re (A $$ (i, i))) = complex_of_real l"
          using e[OF i] False hermitian_diag_real[OF A i] by simp
        thus ?thesis by (simp only: of_real_eq_iff)
      qed simp
      thus "(dia_evo n d A *\<^sub>v v) $ i = (cis (d * l) \<cdot>\<^sub>v v) $ i"
        unfolding dia_evo_def one_sparse_mult_vec[OF invol_id vn] using i vn by simp
    qed (simp add: vn dia_evo_def one_sparse_def)
  qed
qed

theorem dia_gate_intertwine:
  assumes A: "A \<in> carrier_mat n n" "hermitian A"
  shows "dia_gate n d A * emb n = emb n * evolution (diag_part n A) d"
  unfolding evolution_diag_part[OF A]
proof (rule emb_intertwine[OF dia_gate_carrier])
  show "dia_evo n d A \<in> carrier_mat n n" by (simp add: dia_evo_def)
  fix k assume k: "k < n"
  have n: "0 < n" using k by simp
  have j: "enc n k 0 0 < n * n * 2" by (rule enc_lt[OF k n]) simp
  have dk: "enc n k 0 0 div 2 div n = k" using enc_div[of 0 n k 0] mult_index_div_mod(1)[OF n, of k] by simp
  have "dia_gate n d A *\<^sub>v bstate n k 0 0 = cis (d * Re (A $$ (k, k))) \<cdot>\<^sub>v bstate n k 0 0"
    unfolding dia_gate_def one_sparse_unit[OF invol_id j] dk ..
  also have "\<dots> = emb n *\<^sub>v (cis (d * Re (A $$ (k, k))) \<cdot>\<^sub>v unit_vec n k)"
    using mult_mat_vec[OF emb_carrier, where v = "unit_vec n k" and k = "cis (d * Re (A $$ (k, k)))"] emb_unit[OF k] by simp
  also have "cis (d * Re (A $$ (k, k))) \<cdot>\<^sub>v unit_vec n k = dia_evo n d A *\<^sub>v unit_vec n k"
    unfolding dia_evo_def one_sparse_unit[OF invol_id k] ..
  finally show "dia_gate n d A *\<^sub>v bstate n k 0 0 = emb n *\<^sub>v (dia_evo n d A *\<^sub>v unit_vec n k)" .
qed

subsection \<open>The circuit as a gate list\<close>

text \<open>Gates: colour-oracle queries and their inverses, the comparator, the entry gate and the
diagonal phase.  A list is read in time order.\<close>

datatype (plugins del: "quickcheck") sgate = ColQ nat | ColQ_adj nat | Cmp | Ent | DiagQ

fun sgate_mat :: "nat \<Rightarrow> real \<Rightarrow> complex Matrix.mat \<Rightarrow> (nat \<Rightarrow> complex Matrix.mat) \<Rightarrow> sgate \<Rightarrow> complex Matrix.mat" where
  "sgate_mat n d A Os (ColQ c) = Os c"
| "sgate_mat n d A Os (ColQ_adj c) = (Os c)\<^sup>\<dagger>"
| "sgate_mat n d A Os Cmp = cmp_gate n"
| "sgate_mat n d A Os Ent = ent_gate n d A"
| "sgate_mat n d A Os DiagQ = dia_gate n d A"

abbreviation sg_run :: "nat \<Rightarrow> real \<Rightarrow> complex Matrix.mat \<Rightarrow> (nat \<Rightarrow> complex Matrix.mat) \<Rightarrow> sgate list \<Rightarrow> complex Matrix.mat" where
  "sg_run n d A Os gs \<equiv> circuit_mat (n * n * 2) (map (sgate_mat n d A Os) gs)"

fun gate_ok :: "nat \<Rightarrow> sgate \<Rightarrow> bool" where
  "gate_ok K (ColQ c) = (c < K)"
| "gate_ok K (ColQ_adj c) = (c < K)"
| "gate_ok K _ = True"

fun is_query :: "sgate \<Rightarrow> bool" where
  "is_query Cmp = False"
| "is_query _ = True"

definition colour_gates :: "nat \<Rightarrow> sgate list" where
  "colour_gates c = [ColQ c, Cmp, Ent, Cmp, ColQ_adj c]"

definition step_gates :: "nat \<Rightarrow> sgate list" where
  "step_gates K = concat (map colour_gates (rev [0..<K])) @ [DiagQ]"

definition sim_gates :: "nat \<Rightarrow> nat \<Rightarrow> sgate list" where
  "sim_gates K r = concat (replicate r (step_gates K))"

lemma step_gates_ok: "g \<in> set (step_gates K) \<Longrightarrow> gate_ok K g"
  by (auto simp: step_gates_def colour_gates_def)

lemma sim_gates_ok: "g \<in> set (sim_gates K r) \<Longrightarrow> gate_ok K g"
proof -
  assume "g \<in> set (sim_gates K r)"
  hence "g \<in> set (step_gates K)" unfolding sim_gates_def by (cases "r = 0") auto
  thus ?thesis by (rule step_gates_ok)
qed

text \<open>Each Trotter round makes $3K+1$ oracle queries ($2K$ colour, $K+1$ entry) and $2K$
comparisons.\<close>

lemma sim_gates_queries: "length (filter is_query (sim_gates K r)) = r * (3 * K + 1)"
proof -
  have c: "length (filter is_query (colour_gates c)) = 3" for c by (simp add: colour_gates_def)
  have "length (filter is_query (step_gates K)) = 3 * K + 1"
    by (simp add: step_gates_def filter_concat length_concat o_def c sum_list_triv)
  thus ?thesis by (simp add: sim_gates_def filter_concat length_concat o_def sum_list_replicate)
qed

lemma sim_gates_length: "length (sim_gates K r) = r * (5 * K + 1)"
proof -
  have "length (step_gates K) = 5 * K + 1"
    by (simp add: step_gates_def length_concat o_def colour_gates_def sum_list_triv)
  thus ?thesis by (simp add: sim_gates_def length_concat o_def sum_list_replicate)
qed

context
  fixes n :: nat and d :: real and A :: "complex Matrix.mat" and K :: nat and Os :: "nat \<Rightarrow> complex Matrix.mat"
  assumes Oc: "\<And>c. c < K \<Longrightarrow> Os c \<in> carrier_mat (n * n * 2) (n * n * 2)"
begin

lemma sgate_carrier: "gate_ok K g \<Longrightarrow> sgate_mat n d A Os g \<in> carrier_mat (n * n * 2) (n * n * 2)"
  by (cases g) (auto simp: Oc dagger_carrier)

lemma sg_run_carrier: "(\<And>g. g \<in> set gs \<Longrightarrow> gate_ok K g) \<Longrightarrow> sg_run n d A Os gs \<in> carrier_mat (n * n * 2) (n * n * 2)"
  by (rule circuit_mat_carrier) (auto intro: sgate_carrier)

lemma sg_run_append:
  "(\<And>g. g \<in> set xs \<Longrightarrow> gate_ok K g) \<Longrightarrow> (\<And>g. g \<in> set ys \<Longrightarrow> gate_ok K g) \<Longrightarrow>
   sg_run n d A Os (xs @ ys) = sg_run n d A Os ys * sg_run n d A Os xs"
  unfolding map_append by (rule circuit_mat_append) (auto intro: sgate_carrier)

lemma sg_run_colour:
  assumes c: "c < K"
  shows "sg_run n d A Os (colour_gates c) = colour_circ n d A (Os c)"
proof -
  let ?N = "n * n * 2"
  have O: "Os c \<in> carrier_mat ?N ?N" by (rule Oc[OF c])
  have Od: "((Os c)\<^sup>\<dagger>) \<in> carrier_mat ?N ?N" by (rule dagger_carrier[OF O])
  have C: "cmp_gate n \<in> carrier_mat ?N ?N" and G: "ent_gate n d A \<in> carrier_mat ?N ?N" by simp_all
  have "sg_run n d A Os (colour_gates c) = (((1\<^sub>m ?N * ((Os c)\<^sup>\<dagger>)) * cmp_gate n) * ent_gate n d A * cmp_gate n) * Os c"
    by (simp add: colour_gates_def)
  also have "1\<^sub>m ?N * ((Os c)\<^sup>\<dagger>) = ((Os c)\<^sup>\<dagger>)" by (rule left_mult_one_mat[OF Od])
  also have "((Os c)\<^sup>\<dagger>) * cmp_gate n * ent_gate n d A = ((Os c)\<^sup>\<dagger>) * (cmp_gate n * ent_gate n d A)"
    by (rule assoc_mult_mat[OF Od C G])
  also have "((Os c)\<^sup>\<dagger>) * (cmp_gate n * ent_gate n d A) * cmp_gate n = ((Os c)\<^sup>\<dagger>) * (cmp_gate n * ent_gate n d A * cmp_gate n)"
    by (rule assoc_mult_mat[OF Od mult_carrier_mat[OF C G] C])
  also have "((Os c)\<^sup>\<dagger>) * (cmp_gate n * ent_gate n d A * cmp_gate n) * Os c = ((Os c)\<^sup>\<dagger>) * (cmp_gate n * ent_gate n d A * cmp_gate n * Os c)"
    by (rule assoc_mult_mat[OF Od mult_carrier_mat[OF mult_carrier_mat[OF C G] C] O])
  also have "cmp_gate n * ent_gate n d A * cmp_gate n * Os c = cmp_gate n * (ent_gate n d A * (cmp_gate n * Os c))"
  proof -
    have a1: "cmp_gate n * ent_gate n d A * cmp_gate n = cmp_gate n * (ent_gate n d A * cmp_gate n)"
      by (rule assoc_mult_mat[OF C G C])
    have a2: "cmp_gate n * (ent_gate n d A * cmp_gate n) * Os c = cmp_gate n * (ent_gate n d A * cmp_gate n * Os c)"
      by (rule assoc_mult_mat[OF C mult_carrier_mat[OF G C] O])
    have a3: "ent_gate n d A * cmp_gate n * Os c = ent_gate n d A * (cmp_gate n * Os c)"
      by (rule assoc_mult_mat[OF G C O])
    show ?thesis unfolding a1 a2 a3 ..
  qed
  finally show ?thesis unfolding colour_circ_def .
qed

lemma sg_run_replicate:
  "(\<And>g. g \<in> set gs \<Longrightarrow> gate_ok K g) \<Longrightarrow> sg_run n d A Os (concat (replicate r gs)) = sg_run n d A Os gs ^\<^sub>m r"
  unfolding map_concat map_replicate by (rule circuit_mat_concat_replicate) (auto intro: sgate_carrier)

end

subsection \<open>Correctness of the whole circuit\<close>

definition sim_mat :: "nat \<Rightarrow> real \<Rightarrow> complex Matrix.mat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
  "sim_mat n d A K p r = evolution_product n d (sparse_parts n A K p) ^\<^sub>m r"

context
  fixes n :: nat and A :: "complex Matrix.mat" and K :: nat and p :: "nat \<Rightarrow> nat \<Rightarrow> nat"
    and Os :: "nat \<Rightarrow> complex Matrix.mat"
  assumes A: "A \<in> carrier_mat n n" "hermitian A"
      and pinv: "\<And>c. c < K \<Longrightarrow> invol n (p c)"
      and Os: "\<And>c. c < K \<Longrightarrow> colour_oracle n (p c) (Os c)"
begin

lemma Os_carrier: "c < K \<Longrightarrow> Os c \<in> carrier_mat (n * n * 2) (n * n * 2)"
  using Os unfolding colour_oracle_def by blast

lemma colour_part_ok: "c < K \<Longrightarrow> colour_part n A (p c) \<in> carrier_mat n n \<and> hermitian (colour_part n A (p c))"
  using colour_part_hermitian[OF A pinv] by (simp add: colour_part_def)

lemma evolution_product_colours_carrier:
  assumes cs: "set cs \<subseteq> {..<K}"
  shows "evolution_product n d (map (\<lambda>c. colour_part n A (p c)) cs) \<in> carrier_mat n n"
proof (rule evolution_product_carrier)
  fix H assume "H \<in> set (map (\<lambda>c. colour_part n A (p c)) cs)"
  then obtain c where "c \<in> set cs" "H = colour_part n A (p c)" by auto
  thus "H \<in> carrier_mat n n \<and> hermitian H" using colour_part_ok cs by auto
qed

lemma colours_intertwine:
  "set cs \<subseteq> {..<K} \<Longrightarrow>
   sg_run n d A Os (concat (map colour_gates (rev cs))) * emb n = emb n * evolution_product n d (map (\<lambda>c. colour_part n A (p c)) cs)"
proof (induction cs)
  case Nil
  show ?case using left_mult_one_mat[OF emb_carrier, of n] right_mult_one_mat[OF emb_carrier, of n] by simp
next
  case (Cons c cs)
  let ?N = "n * n * 2"
  have c: "c < K" and cs: "set cs \<subseteq> {..<K}" using Cons.prems by auto
  have ok: "\<And>g. g \<in> set (concat (map colour_gates (rev cs))) \<Longrightarrow> gate_ok K g"
    using cs by (auto simp: colour_gates_def)
  have okc: "\<And>g. g \<in> set (colour_gates c) \<Longrightarrow> gate_ok K g" using c by (auto simp: colour_gates_def)
  let ?R = "sg_run n d A Os (concat (map colour_gates (rev cs)))"
  let ?T = "evolution_product n d (map (\<lambda>c. colour_part n A (p c)) cs)"
  have R: "?R \<in> carrier_mat ?N ?N" by (rule sg_run_carrier[where K = K]) (erule Os_carrier, erule ok)
  have Cc: "colour_circ n d A (Os c) \<in> carrier_mat ?N ?N" by (rule colour_circ_carrier[OF Os_carrier[OF c]])
  have T: "?T \<in> carrier_mat n n" by (rule evolution_product_colours_carrier[OF cs])
  have Hc: "colour_part n A (p c) \<in> carrier_mat n n" "hermitian (colour_part n A (p c))"
    by (simp add: colour_part_def, rule colour_part_hermitian[OF A pinv[OF c]])
  have E: "evolution (colour_part n A (p c)) d \<in> carrier_mat n n" by (rule evolution_carrier[OF Hc])
  have "sg_run n d A Os (concat (map colour_gates (rev (c # cs)))) = colour_circ n d A (Os c) * ?R"
  proof -
    have "sg_run n d A Os (concat (map colour_gates (rev cs)) @ colour_gates c) = sg_run n d A Os (colour_gates c) * ?R"
      by (rule sg_run_append[where K = K]) (erule Os_carrier, erule ok, erule okc)
    moreover have "sg_run n d A Os (colour_gates c) = colour_circ n d A (Os c)"
      by (rule sg_run_colour[where K = K]) (erule Os_carrier, rule c)
    ultimately show ?thesis by simp
  qed
  hence "sg_run n d A Os (concat (map colour_gates (rev (c # cs)))) * emb n = (colour_circ n d A (Os c) * ?R) * emb n"
    by simp
  also have "\<dots> = colour_circ n d A (Os c) * (?R * emb n)" by (rule assoc_mult_mat[OF Cc R emb_carrier])
  also have "?R * emb n = emb n * ?T" by (rule Cons.IH[OF cs])
  also have "colour_circ n d A (Os c) * (emb n * ?T) = (colour_circ n d A (Os c) * emb n) * ?T"
    by (rule assoc_mult_mat[OF Cc emb_carrier T, symmetric])
  also have "colour_circ n d A (Os c) * emb n = emb n * evolution (colour_part n A (p c)) d"
    by (rule colour_circ_intertwine[OF A pinv[OF c] Os[OF c]])
  also have "(emb n * evolution (colour_part n A (p c)) d) * ?T = emb n * (evolution (colour_part n A (p c)) d * ?T)"
    by (rule assoc_mult_mat[OF emb_carrier E T])
  finally show ?case by simp
qed

theorem step_intertwine:
  "sg_run n d A Os (step_gates K) * emb n = emb n * evolution_product n d (sparse_parts n A K p)"
proof -
  let ?N = "n * n * 2"
  let ?X = "concat (map colour_gates (rev [0..<K]))"
  let ?T = "evolution_product n d (map (\<lambda>c. colour_part n A (p c)) [0..<K])"
  have ok: "\<And>g. g \<in> set ?X \<Longrightarrow> gate_ok K g" by (auto simp: colour_gates_def)
  have X: "sg_run n d A Os ?X \<in> carrier_mat ?N ?N" by (rule sg_run_carrier[where K = K]) (erule Os_carrier, erule ok)
  have T: "?T \<in> carrier_mat n n" by (rule evolution_product_colours_carrier) auto
  have Dc: "dia_gate n d A \<in> carrier_mat ?N ?N" by simp
  have Hd: "diag_part n A \<in> carrier_mat n n" "hermitian (diag_part n A)"
    by (simp add: diag_part_def, rule diag_part_hermitian[OF A])
  have Ed: "evolution (diag_part n A) d \<in> carrier_mat n n" by (rule evolution_carrier[OF Hd])
  have "sg_run n d A Os (step_gates K) = sg_run n d A Os [DiagQ] * sg_run n d A Os ?X"
    unfolding step_gates_def by (rule sg_run_append[where K = K]) (erule Os_carrier, erule ok, simp)
  also have "sg_run n d A Os [DiagQ] = dia_gate n d A" using left_mult_one_mat[OF Dc] by simp
  finally have "sg_run n d A Os (step_gates K) * emb n = (dia_gate n d A * sg_run n d A Os ?X) * emb n" by simp
  also have "\<dots> = dia_gate n d A * (sg_run n d A Os ?X * emb n)" by (rule assoc_mult_mat[OF Dc X emb_carrier])
  also have "sg_run n d A Os ?X * emb n = emb n * ?T" by (rule colours_intertwine) auto
  also have "dia_gate n d A * (emb n * ?T) = (dia_gate n d A * emb n) * ?T" by (rule assoc_mult_mat[OF Dc emb_carrier T, symmetric])
  also have "dia_gate n d A * emb n = emb n * evolution (diag_part n A) d" by (rule dia_gate_intertwine[OF A])
  also have "(emb n * evolution (diag_part n A) d) * ?T = emb n * (evolution (diag_part n A) d * ?T)"
    by (rule assoc_mult_mat[OF emb_carrier Ed T])
  finally show ?thesis by (simp add: sparse_parts_def)
qed

lemma sparse_parts_tprod_carrier: "evolution_product n d (sparse_parts n A K p) \<in> carrier_mat n n"
proof -
  have Hd: "diag_part n A \<in> carrier_mat n n" "hermitian (diag_part n A)"
    by (simp add: diag_part_def, rule diag_part_hermitian[OF A])
  have "evolution (diag_part n A) d * evolution_product n d (map (\<lambda>c. colour_part n A (p c)) [0..<K]) \<in> carrier_mat n n"
    by (rule mult_carrier_mat[OF evolution_carrier[OF Hd] evolution_product_colours_carrier]) auto
  thus ?thesis by (simp add: sparse_parts_def)
qed

text \<open>$r$ rounds of the gate list act on $\ket x\ket0\ket0$ as $V=(e^{idH_0}\cdots e^{idH_{K}})^r$.\<close>

theorem sim_intertwine:
  "sg_run n d A Os (sim_gates K r) * emb n = emb n * sim_mat n d A K p r"
proof -
  let ?N = "n * n * 2"
  let ?S = "sg_run n d A Os (step_gates K)" and ?T = "evolution_product n d (sparse_parts n A K p)"
  have S: "?S \<in> carrier_mat ?N ?N" by (rule sg_run_carrier[where K = K]) (erule Os_carrier, erule step_gates_ok)
  have T: "?T \<in> carrier_mat n n" by (rule sparse_parts_tprod_carrier)
  have run: "sg_run n d A Os (sim_gates K r) = ?S ^\<^sub>m r"
    unfolding sim_gates_def by (rule sg_run_replicate[where K = K]) (erule Os_carrier, erule step_gates_ok)
  have "?S ^\<^sub>m k * emb n = emb n * ?T ^\<^sub>m k" for k
  proof (induction k)
    case 0
    show ?case using left_mult_one_mat[OF emb_carrier, of n] right_mult_one_mat[OF emb_carrier, of n] using S T by simp
  next
    case (Suc k)
    have Sk: "?S ^\<^sub>m k \<in> carrier_mat ?N ?N" and Tk: "?T ^\<^sub>m k \<in> carrier_mat n n"
      using pow_carrier_mat S T by blast+
    have "?S ^\<^sub>m Suc k * emb n = (?S ^\<^sub>m k * ?S) * emb n" by simp
    also have "\<dots> = ?S ^\<^sub>m k * (?S * emb n)" by (rule assoc_mult_mat[OF Sk S emb_carrier])
    also have "?S * emb n = emb n * ?T" by (rule step_intertwine)
    also have "?S ^\<^sub>m k * (emb n * ?T) = (?S ^\<^sub>m k * emb n) * ?T" by (rule assoc_mult_mat[OF Sk emb_carrier T, symmetric])
    also have "?S ^\<^sub>m k * emb n = emb n * ?T ^\<^sub>m k" by (rule Suc)
    also have "(emb n * ?T ^\<^sub>m k) * ?T = emb n * (?T ^\<^sub>m k * ?T)" by (rule assoc_mult_mat[OF emb_carrier Tk T])
    finally show ?case by simp
  qed
  thus ?thesis unfolding run sim_mat_def .
qed

end

subsection \<open>The simulation oracle\<close>

text \<open>For an $s$-sparse Hermitian $A$ with entries bounded by $L$, any colouring by $2s-1$ matchings
and any colour oracles: the gate list \<open>sim_gates (2s-1) r\<close> with step $d=t/r$ acts on
$\ket x\ket0\ket0$ as a unitary $V$ that is $8(sLt)^2/r$-close to $e^{itA}$, using $r(6s-2)$ oracle
queries.\<close>

theorem sparse_simulation_circuit:
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and s: "1 \<le> s"
      and L: "0 \<le> L" and Lb: "\<And>i j. i < n \<Longrightarrow> j < n \<Longrightarrow> cmod (A $$ (i, j)) \<le> L"
      and cov: "edge_cover n (2 * s - 1) p (edges n A)"
      and Os: "\<And>c. c < 2 * s - 1 \<Longrightarrow> colour_oracle n (p c) (Os c)" and r: "0 < r"
  shows "sg_run n (t / real r) A Os (sim_gates (2 * s - 1) r) * emb n = emb n * sim_mat n (t / real r) A (2 * s - 1) p r"
    and "sim_mat n (t / real r) A (2 * s - 1) p r \<in> carrier_mat n n"
    and "unitary (sim_mat n (t / real r) A (2 * s - 1) p r)"
    and "sim_mat n (t / real r) A (2 * s - 1) p r \<approx>\<^bsub>8 * (real s * L * t)\<^sup>2 / real r\<^esub> evolution A t"
    and "length (filter is_query (sim_gates (2 * s - 1) r)) = r * (6 * s - 2)"
proof -
  have pinv: "\<And>c. c < 2 * s - 1 \<Longrightarrow> invol n (p c)" using cov unfolding edge_cover_def by blast
  have hb: "\<And>H. H \<in> set (sparse_parts n A (2 * s - 1) p) \<Longrightarrow> herm_bounded n L H"
    by (rule sparse_parts_bounded[OF A pinv L Lb])
  show "sg_run n (t / real r) A Os (sim_gates (2 * s - 1) r) * emb n = emb n * sim_mat n (t / real r) A (2 * s - 1) p r"
    by (rule sim_intertwine[OF A pinv Os])
  show "sim_mat n (t / real r) A (2 * s - 1) p r \<in> carrier_mat n n"
    unfolding sim_mat_def by (rule pow_carrier_mat[OF evolution_product_carrier[OF herm_bounded_herm[OF hb]]])
  show "unitary (sim_mat n (t / real r) A (2 * s - 1) p r)"
    unfolding sim_mat_def by (rule unitary_pow[OF evolution_product_carrier[OF herm_bounded_herm[OF hb]] evolution_product_unitary[OF hb]])
  show "sim_mat n (t / real r) A (2 * s - 1) p r \<approx>\<^bsub>8 * (real s * L * t)\<^sup>2 / real r\<^esub> evolution A t"
    unfolding sim_mat_def by (rule sparse_trotter[OF A s L Lb cov r])
  have "3 * (2 * s - 1) + 1 = 6 * s - 2" using s by simp
  thus "length (filter is_query (sim_gates (2 * s - 1) r)) = r * (6 * s - 2)" by (simp add: sim_gates_queries)
qed

text \<open>Colourings and colour oracles always exist.\<close>

corollary sparse_oracles_exist:
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and sp: "sparse n s A" and s: "1 \<le> s"
  shows "\<exists>p Os. edge_cover n (2 * s - 1) p (edges n A) \<and> (\<forall>c < 2 * s - 1. colour_oracle n (p c) (Os c))"
proof -
  obtain p where p: "edge_cover n (2 * s - 1) p (edges n A)" using sparse_split[OF A sp s] by blast
  have o: "\<forall>c < 2 * s - 1. colour_oracle n (p c) (pmat (n * n * 2) (col_perm n (p c)))"
    using p colour_oracle_exists unfolding edge_cover_def by blast
  show ?thesis
  proof (rule exI[of _ p], rule exI[of _ "\<lambda>c. pmat (n * n * 2) (col_perm n (p c))"])
    show "edge_cover n (2 * s - 1) p (edges n A) \<and>
        (\<forall>c<2 * s - 1. colour_oracle n (p c) ((\<lambda>c. pmat (n * n * 2) (col_perm n (p c))) c))"
      using p o by simp
  qed
qed

subsection \<open>Every gate is unitary\<close>

lemma ent_block_unitary: "unitary (ent_block d A x y)"
proof -
  define a where "a = (if x = y then 0 else A $$ (x, y))"
  define c where "c = complex_of_real (cos (d * cmod a))"
  define w where "w = \<i> * complex_of_real (sin (d * cmod a)) * (a / complex_of_real (cmod a))"
  have g: "ent_block d A x y = Matrix.mat 2 2 (\<lambda>(i, j). if i = j then c else if i = 0 then w else - cnj w)"
    unfolding ent_block_def Let_def a_def[symmetric] c_def w_def by (rule eq_matI) auto
  have cc: "cnj c = c" unfolding c_def by simp
  have key: "c * c + w * cnj w = 1"
  proof (cases "a = 0")
    case True
    thus ?thesis unfolding c_def w_def by simp
  next
    case False
    have "cmod w = \<bar>sin (d * cmod a)\<bar>" using False by (simp add: w_def norm_mult norm_divide)
    hence "w * cnj w = complex_of_real ((sin (d * cmod a))\<^sup>2)"
      using complex_norm_square[of w] by simp
    moreover have "c * c = complex_of_real ((cos (d * cmod a))\<^sup>2)" unfolding c_def by (simp add: power2_eq_square)
    ultimately have "c * c + w * cnj w = complex_of_real ((cos (d * cmod a))\<^sup>2 + (sin (d * cmod a))\<^sup>2)"
      by (simp only: of_real_add)
    thus ?thesis by (simp only: sin_cos_squared_add2 of_real_1)
  qed
  let ?g = "Matrix.mat 2 2 (\<lambda>(i, j). if i = j then c else if i = 0 then w else - cnj w) :: complex Matrix.mat"
  have d: "?g\<^sup>\<dagger> = Matrix.mat 2 2 (\<lambda>(i, j). if i = j then c else if i = 0 then - w else cnj w)"
    by (rule eq_matI) (auto simp: dagger_def cc)
  have key2: "cnj w * w + c * c = 1" using key by (simp add: Groups.mult.commute Groups.add.commute)
  have comm: "w * c = c * w" "cnj w * c = c * cnj w" by (simp_all add: Groups.mult.commute)
  have l: "?g\<^sup>\<dagger> * ?g = 1\<^sub>m 2"
    unfolding d
  proof (rule eq_matI)
    fix i j assume "i < dim_row (1\<^sub>m 2 :: complex Matrix.mat)" "j < dim_col (1\<^sub>m 2 :: complex Matrix.mat)"
    hence "i < 2" "j < 2" by simp_all
    thus "(Matrix.mat 2 2 (\<lambda>(i, j). if i = j then c else if i = 0 then - w else cnj w) * ?g) $$ (i, j) = 1\<^sub>m 2 $$ (i, j)"
      using key key2 comm by (auto simp: scalar_prod_def atLeast0LessThan sumof2 less_2_cases_iff)
  qed simp_all
  have r: "?g * (?g\<^sup>\<dagger>) = 1\<^sub>m 2"
    unfolding d
  proof (rule eq_matI)
    fix i j assume "i < dim_row (1\<^sub>m 2 :: complex Matrix.mat)" "j < dim_col (1\<^sub>m 2 :: complex Matrix.mat)"
    hence "i < 2" "j < 2" by simp_all
    thus "(?g * Matrix.mat 2 2 (\<lambda>(i, j). if i = j then c else if i = 0 then - w else cnj w)) $$ (i, j) = 1\<^sub>m 2 $$ (i, j)"
      using key key2 comm by (auto simp: scalar_prod_def atLeast0LessThan sumof2 less_2_cases_iff)
  qed simp_all
  show ?thesis unfolding g unitary_def using l r by simp
qed

lemma ent_block_carrier: "ent_block d A x y \<in> carrier_mat 2 2"
  by (simp add: ent_block_def Let_def)

lemma ent_gate_unitary: "unitary (ent_gate n d A)"
  unfolding ent_gate_def by (rule ctrl_blocks_unitary) (simp_all add: ent_block_unitary ent_block_carrier)

lemma dia_gate_unitary: "unitary (dia_gate n d A)"
proof -
  let ?N = "n * n * 2" and ?g = "\<lambda>j. cis (d * Re (A $$ (j div 2 div n, j div 2 div n)))"
  have D: "(dia_gate n d A)\<^sup>\<dagger> = one_sparse ?N (\<lambda>j. j) (\<lambda>j. cnj (?g j))"
    by (rule eq_matI) (auto simp: dia_gate_def one_sparse_def dagger_def)
  have m: "one_sparse ?N (\<lambda>j. j) f * one_sparse ?N (\<lambda>j. j) h = one_sparse ?N (\<lambda>j. j) (\<lambda>j. f j * h j)" for f h
  proof (rule eq_matI)
    fix i j assume "i < dim_row (one_sparse ?N (\<lambda>j. j) (\<lambda>j. f j * h j))" "j < dim_col (one_sparse ?N (\<lambda>j. j) (\<lambda>j. f j * h j))"
    hence i: "i < ?N" and j: "j < ?N" by (simp_all add: one_sparse_def)
    have "(one_sparse ?N (\<lambda>j. j) f * one_sparse ?N (\<lambda>j. j) h) $$ (i, j) =
        (\<Sum>k = 0..<?N. (if k = i then f i else 0) * (if j = k then h k else 0))"
      using i j by (simp add: one_sparse_def scalar_prod_def atLeast0LessThan)
    also have "\<dots> = (\<Sum>k = 0..<?N. if k = i then (if j = i then f i * h i else 0) else 0)" by (rule sum.cong) auto
    also have "\<dots> = (if j = i then f i * h i else 0)" using i by simp
    finally show "(one_sparse ?N (\<lambda>j. j) f * one_sparse ?N (\<lambda>j. j) h) $$ (i, j) =
        one_sparse ?N (\<lambda>j. j) (\<lambda>j. f j * h j) $$ (i, j)" using i j by (simp add: one_sparse_def)
  qed (simp_all add: one_sparse_def)
  have one: "one_sparse ?N (\<lambda>j. j) (\<lambda>_. 1) = 1\<^sub>m ?N" by (rule eq_matI) (auto simp: one_sparse_def)
  have u1: "cnj (?g j) * ?g j = 1" "?g j * cnj (?g j) = 1" for j
    using complex_norm_square[of "?g j"] by (simp_all add: mult.commute)
  show ?thesis unfolding unitary_def D
    using m[of "\<lambda>j. cnj (?g j)" ?g] m[of ?g "\<lambda>j. cnj (?g j)"] one u1 carrier_matD[OF one_sparse_carrier] by (simp add: dia_gate_def)
qed

lemma sg_run_unitary:
  assumes Os: "\<And>c. c < K \<Longrightarrow> colour_oracle n (p c) (Os c)"
  shows "(\<And>g. g \<in> set gs \<Longrightarrow> gate_ok K g) \<Longrightarrow> unitary (sg_run n d A Os gs)"
proof (induction gs)
  case Nil
  show ?case by simp
next
  case (Cons g gs)
  have Oc: "\<And>c. c < K \<Longrightarrow> Os c \<in> carrier_mat (n * n * 2) (n * n * 2)" using Os unfolding colour_oracle_def by blast
  have g: "gate_ok K g" using Cons.prems by simp
  have ug: "unitary (sgate_mat n d A Os g)"
    using g Os by (cases g) (auto simp: colour_oracle_def unitary_dagger cmp_gate_def invol_pmat_unitary
        cmp_perm_invol ent_gate_unitary dia_gate_unitary)
  have "unitary (sg_run n d A Os gs * sgate_mat n d A Os g)"
    by (rule unitary_mult[OF Cons.IH ug sg_run_carrier[where K = K] sgate_carrier[where K = K]])
      (use Cons.prems Oc g in auto)
  thus ?case by simp
qed

subsection \<open>HHL with the sparse oracle\<close>

text \<open>The HHL window bound of \<open>hhl_sim_window_error\<close> with the oracle realised by the circuit:
total error $(\varepsilon+16(N-1)(sLt_0)^2/r)\norm b$, with $2(N-1)\,r(6s-2)$ oracle queries.\<close>

theorem hhl_sparse_window_error:
  fixes A :: "complex Matrix.mat" and b :: "complex Matrix.vec"
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and t0: "0 < t0" and N: "2 \<le> N"
      and C: "0 < C" and th: "0 < \<theta>" "\<theta> < 1" and lmin: "2 * C / \<theta> \<le> lmin"
      and spec: "\<And>l. l \<in> herm_spectrum A \<Longrightarrow> lmin \<le> l \<and> t0 * l \<le> pi / 2"
      and b: "dim_vec b = n" and e: "0 < \<epsilon>"
      and NQ: "sqrt (8 * pi\<^sup>2 * (2 + pi\<^sup>2) * \<theta> ^ 4 / (t0\<^sup>2 * C\<^sup>2 * (1 - \<theta>\<^sup>2)) + 512 * pi ^ 6 / (t0 ^ 4 * lmin ^ 4)) / \<epsilon> \<le> real N"
      and s: "1 \<le> s" and L: "0 \<le> L" and Lb: "\<And>i j. i < n \<Longrightarrow> j < n \<Longrightarrow> cmod (A $$ (i, j)) \<le> L"
      and cov: "edge_cover n (2 * s - 1) p (edges n A)"
      and Os: "\<And>c. c < 2 * s - 1 \<Longrightarrow> colour_oracle n (p c) (Os c)" and r: "0 < r"
  defines "V \<equiv> sim_mat n (t0 / real r) A (2 * s - 1) p r"
  shows "sg_run n (t0 / real r) A Os (sim_gates (2 * s - 1) r) * emb n = emb n * V"
    and "\<parallel>hhl_sim A t0 N C V *\<^sub>v tensor_vec (win_state N) (tensor_vec b (unit_vec 2 0)) -
           tensor_vec (win_state N)
             (tensor_vec (mat_fun (\<lambda>x. complex_of_real (sqrt (1 - (C / x)\<^sup>2))) A *\<^sub>v b) (unit_vec 2 0) +
              tensor_vec ((complex_of_real C \<cdot>\<^sub>m herm_inv A) *\<^sub>v b) (unit_vec 2 1))\<parallel>
         \<le> (\<epsilon> + 16 * real (N - 1) * (real s * L * t0)\<^sup>2 / real r) * \<parallel>b\<parallel>"
proof -
  note sc = sparse_simulation_circuit(1-4)[where t = t0, OF A s L Lb cov Os r]
  show "sg_run n (t0 / real r) A Os (sim_gates (2 * s - 1) r) * emb n = emb n * V" unfolding V_def by (rule sc(1))
  have eta0: "0 \<le> 8 * (real s * L * t0)\<^sup>2 / real r" by (intro divide_nonneg_nonneg mult_nonneg_nonneg) simp_all
  have c: "\<parallel>hhl_sim A t0 N C V *\<^sub>v tensor_vec (win_state N) (tensor_vec b (unit_vec 2 0)) -
           tensor_vec (win_state N)
             (tensor_vec (mat_fun (\<lambda>x. complex_of_real (sqrt (1 - (C / x)\<^sup>2))) A *\<^sub>v b) (unit_vec 2 0) +
              tensor_vec ((complex_of_real C \<cdot>\<^sub>m herm_inv A) *\<^sub>v b) (unit_vec 2 1))\<parallel>
         \<le> (\<epsilon> + 2 * real (N - 1) * (8 * (real s * L * t0)\<^sup>2 / real r)) * \<parallel>b\<parallel>"
    unfolding V_def by (rule hhl_sim_window_error[OF A t0 N C th lmin spec b e NQ sc(2,3,4) eta0])
  have e: "2 * real (N - 1) * (8 * (real s * L * t0)\<^sup>2 / real r) = 16 * real (N - 1) * (real s * L * t0)\<^sup>2 / real r"
    by simp
  show "\<parallel>hhl_sim A t0 N C V *\<^sub>v tensor_vec (win_state N) (tensor_vec b (unit_vec 2 0)) -
           tensor_vec (win_state N)
             (tensor_vec (mat_fun (\<lambda>x. complex_of_real (sqrt (1 - (C / x)\<^sup>2))) A *\<^sub>v b) (unit_vec 2 0) +
              tensor_vec ((complex_of_real C \<cdot>\<^sub>m herm_inv A) *\<^sub>v b) (unit_vec 2 1))\<parallel>
         \<le> (\<epsilon> + 16 * real (N - 1) * (real s * L * t0)\<^sup>2 / real r) * \<parallel>b\<parallel>" using c unfolding e .
qed

end

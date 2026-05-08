(*
  Title:      Completely_Positive_Maps and Quantum Computing
  Author:     Dustin Bryant (based on notes of Vern Paulsen)
  
  Theory of completely positive maps on finite-dimensional Hilbert spaces.
  We build on the Isabelle Marries Dirac quantum computing library and the
  Quantum Fourier Transform entry.
*)



theory Basic_Math
  imports
    Quantum_Fourier_Transform.QFT
begin

(* ============================================================================
   ABSTRACT LINEAR-SPACE ISOMORPHISMS
   ============================================================================

   Matrix spaces in this development are represented as carrier predicates over
   the single type @{typ "complex Matrix.mat"}, rather than as separate HOL
   types.  These lightweight records give a focused notion of linear
   isomorphism over explicit carriers and operations.  The definition includes
   an explicit inverse linear map, so it can later be shown to imply any more
   general categorical notion of isomorphism without changing project proofs.
   ============================================================================ *)

record ('a, 'v) linear_structure =
  ls_carrier :: "'v set"
  ls_zero :: "'v"
  ls_add :: "'v \<Rightarrow> 'v \<Rightarrow> 'v"
  ls_smul :: "'a \<Rightarrow> 'v \<Rightarrow> 'v"

definition linear_structure_map ::
  "('a, 'v) linear_structure \<Rightarrow> ('a, 'w) linear_structure \<Rightarrow> ('v \<Rightarrow> 'w) \<Rightarrow> bool" where
  "linear_structure_map V W f \<equiv>
     f (ls_zero V) = ls_zero W \<and>
     (\<forall>x \<in> ls_carrier V. f x \<in> ls_carrier W) \<and>
     (\<forall>x \<in> ls_carrier V. \<forall>y \<in> ls_carrier V.
        f (ls_add V x y) = ls_add W (f x) (f y)) \<and>
     (\<forall>c x. x \<in> ls_carrier V \<longrightarrow>
        f (ls_smul V c x) = ls_smul W c (f x))"

definition is_isomorphism_between ::
  "('a, 'v) linear_structure \<Rightarrow> ('a, 'w) linear_structure \<Rightarrow> ('v \<Rightarrow> 'w) \<Rightarrow> bool" where
  "is_isomorphism_between V W f \<equiv>
     linear_structure_map V W f \<and>
     (\<exists>g. linear_structure_map W V g \<and>
          (\<forall>x \<in> ls_carrier V. g (f x) = x) \<and>
          (\<forall>y \<in> ls_carrier W. f (g y) = y))"

definition is_isomorphic_to ::
  "('a, 'v) linear_structure \<Rightarrow> ('a, 'w) linear_structure \<Rightarrow> bool" where
  "is_isomorphic_to V W \<equiv> \<exists>f. is_isomorphism_between V W f"

lemma is_isomorphism_betweenD_map:
  assumes "is_isomorphism_between V W f"
  shows "linear_structure_map V W f"
  using assms by (simp add: is_isomorphism_between_def)

lemma is_isomorphism_betweenD_inverse:
  assumes "is_isomorphism_between V W f"
  obtains g where "linear_structure_map W V g"
    and "\<And>x. x \<in> ls_carrier V \<Longrightarrow> g (f x) = x"
    and "\<And>y. y \<in> ls_carrier W \<Longrightarrow> f (g y) = y"
  using assms by (auto simp: is_isomorphism_between_def)

definition mat_linear_structure :: "nat \<Rightarrow> nat \<Rightarrow> (complex, complex Matrix.mat) linear_structure" where
  "mat_linear_structure m n \<equiv>
     \<lparr> ls_carrier = carrier_mat m n,
       ls_zero = 0\<^sub>m m n,
       ls_add = (\<lambda>x y. x + y),
       ls_smul = (\<lambda>c x. c \<cdot>\<^sub>m x) \<rparr>"

(*Day 1*)

(* ============================================================================
   SECTION 1: The Inner Product on Vectors
   ============================================================================

   Quantum.thy defines:

     inner_prod :: "complex vec \<Rightarrow> complex vec \<Rightarrow> complex"  (\<open>\<langle>_|_\<rangle>\<close>)
     "inner_prod u v \<equiv> \<Sum> i \<in> {0..< dim_vec v}. cnj(u $ i) * (v $ i)"

   That is, \<langle>y|x\<rangle> = \<Sum>_{i=0}^{n-1} \<bar>y_i\<bar> * x_i.

   We restate this as a lemma for clarity. 
   ============================================================================ *)

lemma inner_prod_expand:
  assumes "dim_vec u = n" and "dim_vec v = n"
  shows "\<langle>u|v\<rangle> = (\<Sum> i \<in> {0..< n}. cnj(u $ i) * (v $ i))"
  using assms by (simp add: inner_prod_def)


(* ============================================================================
   SECTION 2: The Inner Product on Matrices (Hilbert-Schmidt Inner Product)
   ============================================================================

   For matrices x, y \<in> M_{m \<times> n}(\<complex>), the Hilbert-Schmidt inner product is:

     \<langle>y | x\<rangle>_{HS} = \<Sum>_i \<Sum>_j  \<bar>Y_{ij}\<bar> * X_{ij}

   This generalises the vector inner product to matrices.  It is also called
   the Frobenius inner product.
   ============================================================================ *)

definition hs_inner_prod :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex" where
  "hs_inner_prod = (\<lambda> y x. 
     \<Sum> i \<in> {0 ..< dim_row x}. 
       \<Sum> j \<in> {0 ..< dim_col x}. 
         cnj (y $$ (i,j)) * (x $$ (i,j)))"

(* Notation: double angle brackets to distinguish from the vector inner product *)
notation hs_inner_prod ("\<langle>\<langle> _ | _ \<rangle>\<rangle>")


(* --- Basic simplification lemma: unfold the definition --- *)

lemma hs_inner_prod_expand:
  assumes "dim_row x = m" and "dim_col x = n"
  shows "\<langle>\<langle> y | x \<rangle>\<rangle> = 
         (\<Sum> i \<in> {0 ..< m}. \<Sum> j \<in> {0 ..< n}. cnj (y $$ (i,j)) * (x $$ (i,j)))"
  using assms by (simp add: hs_inner_prod_def)


(* --- For square matrices --- *)

lemma hs_inner_prod_square:
  assumes "dim_row x = n" and "dim_col x = n"
  shows "\<langle>\<langle> y | x \<rangle>\<rangle> = 
         (\<Sum> i \<in> {0 ..< n}. \<Sum> j \<in> {0 ..< n}. cnj (y $$ (i,j)) * (x $$ (i,j)))"
  using assms by (simp add: hs_inner_prod_def)


(* ============================================================================
   SECTION 3: Basic Properties of the Hilbert-Schmidt Inner Product
   ============================================================================ *)

(* --- Conjugate symmetry: \<langle>\<langle>x|y\<rangle>\<rangle> = cnj(\<langle>\<langle>y|x\<rangle>\<rangle>) --- *)

lemma hs_inner_prod_cnj:
  assumes "dim_row x = dim_row y" and "dim_col x = dim_col y"
  shows "\<langle>\<langle> x | y \<rangle>\<rangle> = cnj (\<langle>\<langle> y | x \<rangle>\<rangle>)"
proof -
  have "\<langle>\<langle> x | y \<rangle>\<rangle> = 
        (\<Sum> i \<in> {0 ..< dim_row y}. \<Sum> j \<in> {0 ..< dim_col y}. cnj (x $$ (i,j)) * (y $$ (i,j)))"
    using assms by (simp add: hs_inner_prod_def)
  also have "\<dots> = (\<Sum> i \<in> {0 ..< dim_row y}. \<Sum> j \<in> {0 ..< dim_col y}. 
                    cnj (cnj (y $$ (i,j)) * (x $$ (i,j))))"
    by (intro sum.cong, auto)
  also have "\<dots> = cnj (\<Sum> i \<in> {0 ..< dim_row y}. \<Sum> j \<in> {0 ..< dim_col y}. 
                    cnj (y $$ (i,j)) * (x $$ (i,j)))"
    by simp
  also have "\<dots> = cnj (\<langle>\<langle> y | x \<rangle>\<rangle>)"
    using assms(1,2) hs_inner_prod_expand by presburger
  finally show ?thesis.
qed


(* --- Linearity in the second argument (right-linearity) --- *)

lemma hs_inner_prod_right_add:
  assumes "dim_row X1 = dim_row y" and "dim_col X1 = dim_col y"
      and "dim_row X2 = dim_row y" and "dim_col X2 = dim_col y"
  shows "\<langle>\<langle> y | X1 + X2 \<rangle>\<rangle> = \<langle>\<langle> y | X1 \<rangle>\<rangle> + \<langle>\<langle> y | X2 \<rangle>\<rangle>"
proof -
  have dims: "dim_row (X1 + X2) = dim_row y" "dim_col (X1 + X2) = dim_col y"
    using assms by auto
  show ?thesis
    unfolding hs_inner_prod_def
    using assms by (auto simp: distrib_left sum.distrib intro!: sum.cong)
qed

lemma hs_inner_prod_right_smult:
  assumes "dim_row x = dim_row y" and "dim_col x = dim_col y"
  shows "\<langle>\<langle> y | c \<cdot>\<^sub>m x \<rangle>\<rangle> = c * \<langle>\<langle> y | x \<rangle>\<rangle>"
  unfolding hs_inner_prod_def using assms
  by (auto simp: mult.assoc sum_distrib_left intro!: sum.cong)

(* --- Conjugate-linearity in the first argument (left-conjugate-linearity) --- *)

lemma hs_inner_prod_left_smult:
  assumes "dim_row x = dim_row y" and "dim_col x = dim_col y"
  shows "\<langle>\<langle> c \<cdot>\<^sub>m y | x \<rangle>\<rangle> = cnj c * \<langle>\<langle> y | x \<rangle>\<rangle>"
  unfolding hs_inner_prod_def using assms 
  by (auto simp: mult.assoc sum_distrib_left intro!: sum.cong)


(* --- Self inner product is real --- *)

lemma hs_inner_prod_self_real:
  shows "\<langle>\<langle> x | x \<rangle>\<rangle> \<in> \<real>"
proof -
  have "\<langle>\<langle> x | x \<rangle>\<rangle> = (\<Sum> i \<in> {0 ..< dim_row x}. \<Sum> j \<in> {0 ..< dim_col x}. 
                              cnj (x $$ (i,j)) * (x $$ (i,j)))"
    by (simp add: hs_inner_prod_def)
  also have "\<dots> = (\<Sum> i \<in> {0 ..< dim_row x}. \<Sum> j \<in> {0 ..< dim_col x}. 
                    (cmod (x $$ (i,j)))^2)"
    by (metis (lifting) ext complex_norm_square mult.commute of_real_hom.hom_sum)
  also have "\<dots> \<in> \<real>"
    by simp
  finally show ?thesis.
qed


(* --- Self inner product is non-negative --- *)

lemma hs_inner_prod_self_nonneg:
  shows "Re (\<langle>\<langle> x | x \<rangle>\<rangle>) \<ge> 0"
proof -
  have "Re (\<langle>\<langle> x | x \<rangle>\<rangle>) = (\<Sum> i \<in> {0 ..< dim_row x}. \<Sum> j \<in> {0 ..< dim_col x}. 
                                   (cmod (x $$ (i,j)))^2)"
    unfolding hs_inner_prod_def 
    by(simp, metis (lifting) ext cmod_power2 power2_eq_square)
  also have "\<dots> \<ge> 0"
    by (intro sum_nonneg, simp)
  finally show ?thesis.
qed


(* --- Positive definiteness: \<langle>\<langle>x|x\<rangle>\<rangle> = 0 implies x = 0 --- *)

lemma hs_inner_prod_eq_zero_imp:
  assumes "\<langle>\<langle> x | x \<rangle>\<rangle> = 0"
      and "i < dim_row x" and "j < dim_col x"
  shows "x $$ (i,j) = 0"
proof -
  define f where "f \<equiv> \<lambda>a b. Re (cnj (x$$(a,b)) * x$$(a,b))"
  (* Each f a b is non-negative *)
  have f_nonneg: "\<And>a b. f a b \<ge> 0"
    by (simp add: f_def)

  (* The double sum of f equals 0.
     We go: sum of f = sum of Re(...) = Re(sum of ...) = Re(0) = 0 *)
  have sum_zero: "(\<Sum>a\<in>{0..<dim_row x}. \<Sum>b\<in>{0..<dim_col x}. f a b) = 0"
  proof -
    have "(\<Sum>a\<in>{0..<dim_row x}. \<Sum>b\<in>{0..<dim_col x}. f a b) =
          Re (\<Sum>a\<in>{0..<dim_row x}. \<Sum>b\<in>{0..<dim_col x}. cnj (x$$(a,b)) * x$$(a,b))"
      unfolding f_def by (simp add: Re_sum[symmetric])
    also have "\<dots> = 0" using assms(1) by (simp add: hs_inner_prod_def)
    finally show ?thesis .
  qed

  (* Each inner sum is non-negative *)
  have inner_nonneg: "\<And>a. 0 \<le> (\<Sum>b\<in>{0..<dim_col x}. f a b)"
    by (intro sum_nonneg) (use f_nonneg in auto)

  (* Peel apart the outer sum — the i-th inner sum must be 0 *)
  have inner_zero: "(\<Sum>b\<in>{0..<dim_col x}. f i b) = 0"
    using sum_nonneg_0[of "{0..<dim_row x}" "\<lambda>a. \<Sum>b\<in>{0..<dim_col x}. f a b" i]
          sum_zero inner_nonneg assms(2) by auto

  (* Peel apart the inner sum — the j-th term must be 0 *)
  have "f i j = 0"
    using sum_nonneg_0[of "{0..<dim_col x}" "\<lambda>b. f i b" j]
          inner_zero f_nonneg assms(3) by auto

  (* f i j = 0 means (cmod(x$$(i,j)))^2 = 0, so x$$(i,j) = 0 *)
  then have "Re (cnj (x$$(i,j)) * x$$(i,j)) = 0" unfolding f_def by simp
  moreover have "cnj (x$$(i,j)) * x$$(i,j) = complex_of_real ((cmod (x$$(i,j)))\<^sup>2)"
    by (simp add: cmod_power2 complex_mult_cnj mult.commute)
  ultimately have "(cmod (x$$(i,j)))\<^sup>2 = 0" 
    by simp
  then have "cmod (x$$(i,j)) = 0" 
    by simp
  then show "x$$(i,j) = 0" 
    by simp
qed

(* ============================================================================
   SECTION 4: Matrix Units E_{i,j}
   ============================================================================

   E_{i,j} is the m \<times> n matrix with 1 in position (i,j) and 0 elsewhere.
   These form an orthonormal basis for M_{m \<times> n}(\<complex>) under the 
   Hilbert-Schmidt inner product.

   Argument order: indices (i,j) first, then dimensions (m,n).
   ============================================================================ *)

definition mat_unit :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
  "mat_unit i j m n = Matrix.mat m n (\<lambda>(r,c). if r = i \<and> c = j then 1 else 0)"

notation mat_unit ("E\<lbrakk>_,_ ; _,_\<rbrakk>" [1000, 1000, 1000, 1000] 999)

lemma mat_unit_dim_row [simp]:
  fixes i j m n :: nat
  shows "dim_row (E\<lbrakk>i,j ; m,n\<rbrakk>) = m"
  by (simp add: mat_unit_def)

lemma mat_unit_dim_col [simp]:
  fixes i j m n :: nat
  shows "dim_col (E\<lbrakk>i,j ; m,n\<rbrakk>) = n"
  by (simp add: mat_unit_def)

lemma mat_unit_index [simp]:
  assumes "r < m" and "c < n"
  shows "(E\<lbrakk>i,j ; m,n\<rbrakk>) $$ (r,c) = (if r = i \<and> c = j then 1 else 0)"
  using assms by (simp add: mat_unit_def)


(* ============================================================================
   SECTION 5: Extraction — \<langle>\<langle>E_{ij} | x\<rangle>\<rangle> = x $$ (i,j)
   ============================================================================

   Taking the Hilbert-Schmidt inner product with the matrix unit E_{ij}
   extracts the (i,j) entry.  This is the matrix analogue of \<langle>e_i | v\<rangle> = v_i.
   ============================================================================ *)

lemma hs_inner_prod_mat_unit_left:
  assumes "i < dim_row x" and "j < dim_col x"
  shows "\<langle>\<langle> E\<lbrakk>i,j ; (dim_row x), (dim_col x)\<rbrakk> | x \<rangle>\<rangle> = x $$ (i,j)"
proof -
  let ?m = "dim_row x"
  let ?n = "dim_col x"

  have "\<langle>\<langle> E\<lbrakk>i,j ; ?m,?n\<rbrakk> | x \<rangle>\<rangle> =
        (\<Sum>r \<in> {0..<?m}. \<Sum>c \<in> {0..<?n}.
          cnj (E\<lbrakk>i,j ; ?m,?n\<rbrakk> $$ (r,c)) * x $$ (r,c))"
    by (simp add: hs_inner_prod_def)
  also have "\<dots> = (\<Sum>r \<in> {0..<?m}. \<Sum>c \<in> {0..<?n}.
          cnj (if r = i \<and> c = j then 1 else 0) * x $$ (r,c))"
    by (intro sum.cong refl) auto
  also have "\<dots> = (\<Sum>r \<in> {0..<?m}. \<Sum>c \<in> {0..<?n}.
          (if r = i \<and> c = j then x $$ (r,c) else 0))"
    by (intro sum.cong refl) simp
  also have "\<dots> = (\<Sum>r \<in> {0..<?m}. if r = i then x $$ (i,j) else 0)"
  proof (intro sum.cong refl)
    fix r
    assume hr: "r \<in> {0..<?m}"
    show "(\<Sum>c \<in> {0..<?n}. if r = i \<and> c = j then x $$ (r,c) else 0) =
          (if r = i then x $$ (i,j) else 0)"
    proof (cases "r = i")
      case True
      then have "(\<Sum>c \<in> {0..<?n}. if r = i \<and> c = j then x $$ (r,c) else 0) =
                 (\<Sum>c \<in> {0..<?n}. if c = j then x $$ (i,j) else 0)"
        by (intro sum.cong) auto
      also have "\<dots> = x $$ (i,j)"
      proof -
        have "(\<Sum>c \<in> {0..<?n}. if c = j then x $$ (i,j) else 0) =
              (\<Sum>c \<in> {0..<?n}. (if c = j then 1 else 0) * x $$ (i,j))"
          by (intro sum.cong) auto
        also have "\<dots> = (\<Sum>c \<in> {0..<?n}. if c = j then 1 else 0) * x $$ (i,j)"
          by (metis sum_distrib_right)
        also have "(\<Sum>c \<in> {0..<?n}. if c = j then 1 else (0::complex)) = 1"
          using assms(2) by simp
        finally show ?thesis by simp
      qed
      finally show ?thesis
        using True by simp
    next
      case False
      then show ?thesis by simp
    qed
  qed
  also have "\<dots> = x $$ (i,j)"
  proof -
    have "(\<Sum>r \<in> {0..<?m}. if r = i then x $$ (i,j) else 0) =
          (\<Sum>r \<in> {0..<?m}. (if r = i then 1 else 0) * x $$ (i,j))"
      by (intro sum.cong) auto
    also have "\<dots> = (\<Sum>r \<in> {0..<?m}. if r = i then 1 else 0) * x $$ (i,j)"
      by (metis sum_distrib_right)
    also have "(\<Sum>r \<in> {0..<?m}. if r = i then 1 else (0::complex)) = 1"
      using assms(1) by simp
    finally show ?thesis by simp
  qed
  finally show ?thesis.
qed


(* ============================================================================
   SECTION 6: Orthonormality of Matrix Units
   ============================================================================

   \<langle>\<langle>E_{ij} | E_{kl}\<rangle>\<rangle> = \<delta>_{ik} \<cdot> \<delta>_{jl}
   ============================================================================ *)

lemma mat_unit_orthonormal:
  assumes i_lt: "i < m"
      and j_lt: "j < n"
      and k_lt: "k < m"
      and l_lt: "l < n"
  shows "\<langle>\<langle> E\<lbrakk>i,j ; m,n\<rbrakk> | E\<lbrakk>k,l ; m,n\<rbrakk> \<rangle>\<rangle> =
         (if i = k \<and> j = l then 1 else 0)"
  by (metis hs_inner_prod_mat_unit_left i_lt j_lt mat_unit_dim_col mat_unit_dim_row mat_unit_index)



(* ============================================================================
   SECTION 7: Expansion of a Matrix in the E_{ij} Basis
   ============================================================================

   x $$ (r,c) = \<Sum>_i \<Sum>_j x $$ (i,j) \<cdot> E_{ij} $$ (r,c)

   Since JNF matrices of different dimensions cannot be added (Matrix.mat is
   not a comm_monoid_add), we state the expansion entrywise.
   ============================================================================ *)

lemma mat_unit_expansion:
  assumes "r < dim_row x" and "c < dim_col x"
  shows "x $$ (r,c) =
         (\<Sum>i \<in> {0..<dim_row x}. \<Sum>j \<in> {0..<dim_col x}.
            x $$ (i,j) * (mat_unit i j (dim_row x) (dim_col x)) $$ (r,c))"
proof -
  let ?m = "dim_row x"
  let ?n = "dim_col x"

  have "(\<Sum>i \<in> {0..<?m}. \<Sum>j \<in> {0..<?n}.
          x $$ (i,j) * (E\<lbrakk>i,j ; ?m,?n\<rbrakk>) $$ (r,c)) =
        (\<Sum>i \<in> {0..<?m}. \<Sum>j \<in> {0..<?n}.
          x $$ (i,j) * (if i = r \<and> j = c then 1 else 0))"
    using assms by (intro sum.cong refl) simp
  also have "\<dots> = (\<Sum>i \<in> {0..<?m}. \<Sum>j \<in> {0..<?n}.
                    (if i = r \<and> j = c then x $$ (i,j) else 0))"
    by (intro sum.cong refl) auto
  also have "\<dots> = (\<Sum>i \<in> {0..<?m}. if i = r then x $$ (r,c) else 0)"
  proof (intro sum.cong refl)
    fix i
    assume hi: "i \<in> {0..<?m}"
    show "(\<Sum>j \<in> {0..<?n}. if i = r \<and> j = c then x $$ (i,j) else 0) =
          (if i = r then x $$ (r,c) else 0)"
    proof (cases "i = r")
      case True
      then have "(\<Sum>j \<in> {0..<?n}. if i = r \<and> j = c then x $$ (i,j) else 0) =
                 (\<Sum>j \<in> {0..<?n}. if j = c then x $$ (r,j) else 0)"
        by (intro sum.cong) auto
      also have "\<dots> = x $$ (r,c)"
      proof -
        have "(\<Sum>j \<in> {0..<?n}. if j = c then x $$ (r,j) else 0) =
              (\<Sum>j \<in> {0..<?n}. (if j = c then 1 else 0) * x $$ (r,c))"
          by (intro sum.cong) auto
        also have "\<dots> = (\<Sum>j \<in> {0..<?n}. if j = c then 1 else 0) * x $$ (r,c)"
          by (metis sum_distrib_right)
        also have "(\<Sum>j \<in> {0..<?n}. if j = c then 1 else (0::complex)) = 1"
          using assms(2) by simp
        finally show ?thesis by simp
      qed
      finally show ?thesis
        using True by simp
    next
      case False
      then show ?thesis by simp
    qed
  qed
  also have "\<dots> = x $$ (r,c)"
  proof -
    have "(\<Sum>i \<in> {0..<?m}. if i = r then x $$ (r,c) else 0) =
          (\<Sum>i \<in> {0..<?m}. (if i = r then 1 else 0) * x $$ (r,c))"
      by (intro sum.cong) auto
    also have "\<dots> = (\<Sum>i \<in> {0..<?m}. if i = r then 1 else 0) * x $$ (r,c)"
      by (metis sum_distrib_right)
    also have "(\<Sum>i \<in> {0..<?m}. if i = r then 1 else (0::complex)) = 1"
      using assms(1) by simp
    finally show ?thesis by simp
  qed
  finally show ?thesis by simp
qed


(* ============================================================================
   SECTION 8: Expansion via Inner Product
   ============================================================================

   x $$ (r,c) = \<Sum>_{ij} \<langle>\<langle>E_{ij} | x\<rangle>\<rangle> \<cdot> E_{ij} $$ (r,c)

   This combines the extraction lemma with the expansion, showing the E_{ij}
   truly act as an orthonormal basis: the coefficients in the expansion are
   exactly the inner products with the basis elements.
   ============================================================================ *)

lemma mat_unit_hs_expansion:
  assumes "r < dim_row x" and "c < dim_col x"
  shows "x $$ (r,c) =
         (\<Sum>i \<in> {0..<dim_row x}. \<Sum>j \<in> {0..<dim_col x}.
            \<langle>\<langle> mat_unit i j (dim_row x) (dim_col x) | x \<rangle>\<rangle> *
            (mat_unit i j (dim_row x) (dim_col x)) $$ (r,c))"
proof -
  let ?m = "dim_row x"
  let ?n = "dim_col x"

  have "(\<Sum>i \<in> {0..<?m}. \<Sum>j \<in> {0..<?n}.
          \<langle>\<langle> E\<lbrakk>i,j ; ?m,?n\<rbrakk> | x \<rangle>\<rangle> * (E\<lbrakk>i,j ; ?m,?n\<rbrakk>) $$ (r,c)) =
        (\<Sum>i \<in> {0..<?m}. \<Sum>j \<in> {0..<?n}.
          x $$ (i,j) * (E\<lbrakk>i,j ; ?m,?n\<rbrakk>) $$ (r,c))"
  proof (intro sum.cong refl)
    fix i
    assume hi: "i \<in> {0..<?m}"
    fix j
    assume hj: "j \<in> {0..<?n}"
    have "\<langle>\<langle> E\<lbrakk>i,j ; ?m,?n\<rbrakk> | x \<rangle>\<rangle> = x $$ (i,j)"
      using hi hj
      by (simp add: hs_inner_prod_mat_unit_left)
    then show "\<langle>\<langle> E\<lbrakk>i,j ; ?m,?n\<rbrakk> | x \<rangle>\<rangle> * (E\<lbrakk>i,j ; ?m,?n\<rbrakk>) $$ (r,c) =
               x $$ (i,j) * (E\<lbrakk>i,j ; ?m,?n\<rbrakk>) $$ (r,c)"
      by simp
  qed
  also have "\<dots> = x $$ (r,c)"
    using mat_unit_expansion[OF assms] by simp
  finally show ?thesis by simp
qed

(* ============================================================================
   SECTION 9: The Trace and Diagonal Matrix Units
   ============================================================================

   Tr x = \<Sum>_r x $$ (r,r)

   The trace records the sum of the diagonal entries.  For the matrix units,
   only the diagonal units E_{ii} contribute to the trace, while off-diagonal
   units E_{ij} with i \<noteq> j have trace 0.

   Using the extraction lemmas above, we can also express the trace as the
   sum of the diagonal Hilbert-Schmidt coefficients.
   ============================================================================ *)

definition Tr :: "complex Matrix.mat \<Rightarrow> complex" where
  "Tr x = (\<Sum>r < dim_row x. if r < dim_col x then x $$ (r,r) else 0)"

lemma Tr_mat_unit:
  assumes i_lt: "i < m"
      and j_lt: "j < n"
  shows "Tr (E\<lbrakk>i,j ; m,n\<rbrakk>) = (if i = j then 1 else 0)"
proof (cases "i = j")
  case True
  have "Tr (E\<lbrakk>i,j ; m,n\<rbrakk>) =
        (\<Sum>r<m. if r < n then (E\<lbrakk>i,j ; m,n\<rbrakk>) $$ (r,r) else 0)"
    by (simp add: Tr_def)
  also have "... =
        (\<Sum>r<m. if r < n then (if r = i \<and> r = j then 1 else 0) else 0)"
    by (intro sum.cong refl) simp
  also have "... = (\<Sum>r<m. if r = i then 1 else 0)"
    by (metis True j_lt)  
  also have "... = 1"
    using i_lt by simp
  finally show ?thesis
    using True by simp
next
  case False
  have "Tr (E\<lbrakk>i,j ; m,n\<rbrakk>) =
        (\<Sum>r<m. if r < n then (E\<lbrakk>i,j ; m,n\<rbrakk>) $$ (r,r) else 0)"
    by (simp add: Tr_def)
  also have "... =
        (\<Sum>r<m. if r < n then (if r = i \<and> r = j then 1 else 0) else 0)"
    by (intro sum.cong refl) simp
  also have "... = 0"
    by (simp add: False sum.neutral)
  finally show ?thesis
    using False by simp
qed

corollary Tr_mat_unit_diag:
  assumes "i < n"
  shows "Tr (E\<lbrakk>i,i ; n,n\<rbrakk>) = 1"
  using assms by (simp add: Tr_mat_unit)

corollary Tr_mat_unit_offdiag:
  assumes "i < m" and "j < n" and "i \<noteq> j"
  shows "Tr (E\<lbrakk>i,j ; m,n\<rbrakk>) = 0"
  by (simp add: Tr_mat_unit assms)



lemma Tr_hs_diagonal_sum:
  shows "Tr x =
         (\<Sum>r < dim_row x.
            if r < dim_col x
            then \<langle>\<langle> E\<lbrakk>r,r ; (dim_row x), (dim_col x)\<rbrakk> | x \<rangle>\<rangle>
            else 0)"
  by (smt (verit, ccfv_threshold) Tr_def hs_inner_prod_mat_unit_left lessThan_iff sum.cong)

corollary Tr_hs_diagonal_sum_square:
  assumes rows: "dim_row x = n"
      and cols: "dim_col x = n"
  shows "Tr x = (\<Sum>r<n. \<langle>\<langle> E\<lbrakk>r,r ; n,n\<rbrakk> | x \<rangle>\<rangle>)"
proof -
  have "Tr x = (\<Sum>r<n. x $$ (r,r))"
    using rows cols by (simp add: Tr_def)
  also have "... = (\<Sum>r<n. \<langle>\<langle> E\<lbrakk>r,r ; n,n\<rbrakk> | x \<rangle>\<rangle>)"
    by (intro sum.cong refl, metis cols hs_inner_prod_mat_unit_left lessThan_iff rows)
  finally show ?thesis.
qed


(* ============================================================================
   SECTION 10: Linearity of the Trace
   ============================================================================

   Tr (x + y) = Tr x + Tr y
   Tr (a \<cdot> x) = a * Tr x

   The trace is linear: it distributes over matrix addition and factors out
   scalar multiplication.  Since our trace was defined entrywise as a sum of
   diagonal entries, both facts follow by simple sum manipulations.
   ============================================================================ *)

lemma Tr_add:
  assumes rows: "dim_row x = dim_row y"
      and cols: "dim_col x = dim_col y"
  shows "Tr (x + y) = Tr x + Tr y"
proof -
  have "Tr (x + y) =
        (\<Sum>r < dim_row x. if r < dim_col x then (x + y) $$ (r,r) else 0)"
    using rows cols by (simp add: Tr_def)
  also have "... =
        (\<Sum>r < dim_row x.
           (if r < dim_col x then x $$ (r,r) else 0) +
           (if r < dim_col x then y $$ (r,r) else 0))"
    by (intro sum.cong refl, simp add: cols rows)
  also have "... =
        (\<Sum>r < dim_row x. if r < dim_col x then x $$ (r,r) else 0) +
        (\<Sum>r < dim_row x. if r < dim_col x then y $$ (r,r) else 0)"
    by (simp add: sum.distrib)
  also have "... = Tr x + Tr y"
    using rows cols by (simp add: Tr_def)
  finally show ?thesis.
qed


lemma Tr_smult: "Tr (a \<cdot>\<^sub>m x) = a * Tr x"
proof -
  have "Tr (a \<cdot>\<^sub>m x) =
        (\<Sum>r < dim_row x. if r < dim_col x then (a \<cdot>\<^sub>m x) $$ (r,r) else 0)"
    by (simp add: Tr_def)
  also have "... =
        (\<Sum>r < dim_row x. a * (if r < dim_col x then x $$ (r,r) else 0))"
    by (intro sum.cong refl) simp
  also have "... =
        a * (\<Sum>r < dim_row x. if r < dim_col x then x $$ (r,r) else 0)"
    by (simp add: sum_distrib_left)
  also have "... = a * Tr x"
    by (simp add: Tr_def)
  finally show ?thesis.
qed

corollary Tr_uminus: "Tr (- x) = - Tr x"
  by (smt (verit, ccfv_threshold) Tr_add add_cancel_right_right add_eq_0_iff carrier_mat_triv 
      index_uminus_mat(2,3) index_zero_mat(2,3)
      right_add_zero_mat uminus_l_inv_mat uminus_uminus_mat)



corollary Tr_diff:
  assumes rows: "dim_row x = dim_row y"
      and cols: "dim_col x = dim_col y"
  shows "Tr (x - y) = Tr x - Tr y"
proof -
  have "Tr (x - y) = Tr (x + (- y))"
    by (metis carrier_mat_triv cols minus_add_uminus_mat rows)
  also have "... = Tr x + Tr (- y)"
    using rows cols by (intro Tr_add) simp_all
  also have "... = Tr x - Tr y"
    by (simp add: Tr_uminus)
  finally show ?thesis.
qed


lemma Tr_zero_mat [simp]:
  shows "Tr (Matrix.mat m n (\<lambda>(r,c). 0)) = 0"
  by (simp add: Tr_def, simp add: sum.neutral)

(* ============================================================================
   SECTION 11: Matrix-Unit Algebra and Cyclicity of Trace
   ============================================================================ *)

lemma mat_unit_dagger:
  shows "(E\<lbrakk>i,j ; m,n\<rbrakk>)\<^sup>\<dagger> = E\<lbrakk>j,i ; n,m\<rbrakk>"
  by (rule eq_matI, simp_all, simp add: dagger_def)



lemma mat_unit_mult_entry:
  assumes r_lt: "r < m"
      and c_lt: "c < p"
      and j_lt: "j < n"
  shows "(E\<lbrakk>i,j ; m,n\<rbrakk> * E\<lbrakk>k,l ; n,p\<rbrakk>) $$ (r,c) =
         (if j = k \<and> r = i \<and> c = l then 1 else 0)"  
proof -
  have "(E\<lbrakk>i,j ; m,n\<rbrakk> * E\<lbrakk>k,l ; n,p\<rbrakk>) $$ (r,c) =
        (\<Sum>t<n. (E\<lbrakk>i,j ; m,n\<rbrakk>) $$ (r,t) * (E\<lbrakk>k,l ; n,p\<rbrakk>) $$ (t,c))"
    using r_lt c_lt by simp
  also have "... =
        (\<Sum>t<n. (if r = i \<and> t = j then 1 else 0) *
               (if t = k \<and> c = l then 1 else 0))"
    using r_lt c_lt by (intro sum.cong refl) simp
  also have "... =
        (if r = i \<and> c = l
         then (\<Sum>t<n. (if t = j then 1 else 0) * (if t = k then 1 else 0))
         else 0)"
    by fastforce
  also have "... = (if r = i \<and> c = l then (if j = k then 1 else 0) else 0)"
    by (smt (verit) Tr_hs_diagonal_sum Tr_mat_unit_diag j_lt lambda_one lambda_zero mat_unit_dim_col
        mat_unit_dim_row mat_unit_orthonormal sum.cong sum.not_neutral_contains_not_neutral)
  also have "... = (if j = k \<and> r = i \<and> c = l then 1 else 0)"
    by auto
  finally show ?thesis.
qed


lemma Tr_cyclic:
  assumes AB: "dim_col A = dim_row B"
      and BA: "dim_row A = dim_col B"
  shows "Tr (A * B) = Tr (B * A)"
proof -
  let ?m = "dim_row A"
  let ?n = "dim_col A"

  have "Tr (A * B) = (\<Sum>i<?m. (A * B) $$ (i,i))"
    using AB BA by (simp add: Tr_def)
  also have "... = (\<Sum>i<?m. \<Sum>k<?n. A $$ (i,k) * B $$ (k,i))"
    using AB BA by (intro sum.cong refl, simp)
  also have "... = (\<Sum>k<?n. \<Sum>i<?m. A $$ (i,k) * B $$ (k,i))"
    by (rule sum.swap)
  also have "... = (\<Sum>k<?n. \<Sum>i<?m. B $$ (k,i) * A $$ (i,k))"
  proof (rule sum.cong[OF refl])
    fix k
    assume "k \<in> {..<dim_col A}"
    then have k_lt: "k < ?n"
      by (metis lessThan_iff)

    show "(\<Sum>i<?m. A $$ (i,k) * B $$ (k,i)) =
          (\<Sum>i<?m. B $$ (k,i) * A $$ (i,k))"
      by (metis mult.commute)
  qed
  also have "... = (\<Sum>k<?n. (B * A) $$ (k,k))"
    using AB BA by (intro sum.cong refl, simp add:  mult.commute)
  also have "... = Tr (B * A)"
    using AB BA by (simp add: Tr_def)
  finally show ?thesis.
qed

lemma Tr_unitary_conjugation:
  assumes Uu: "unitary U"
      and Arow: "dim_row A = dim_row U"
      and Acol: "dim_col A = dim_row U"
  shows "Tr ((U\<^sup>\<dagger>) * A * U) = Tr(A)"
proof -
  have "Tr ((U\<^sup>\<dagger>) * A * U) = Tr (U * ((U\<^sup>\<dagger>) * A))"
    by (metis Acol Tr_cyclic dim_row_of_dagger index_mult_mat(2,3))
  also have "... = Tr (((1\<^sub>m (dim_row U)) * A))"
    by (smt (verit, ccfv_SIG) Arow Uu assoc_mult_mat carrier_mat_triv dagger_of_dagger_is_id dim_row_of_dagger unitary_def)
  finally show ?thesis
    by (metis Arow left_mult_one_mat')
qed


lemma hs_inner_prod_as_trace:
  assumes rows: "dim_row A = dim_row B"
      and cols: "dim_col A = dim_col B"
  shows "\<langle>\<langle> A | B \<rangle>\<rangle> = Tr ((A\<^sup>\<dagger>) * B)"
proof -
  let ?m = "dim_row A" and ?n = "dim_col A"
  have "\<langle>\<langle> A | B \<rangle>\<rangle> = (\<Sum>i<?m. \<Sum>j<?n. cnj (A $$ (i,j)) * B $$ (i,j))"
    using rows cols by (simp add: hs_inner_prod_def atLeast0LessThan)
  also have "\<dots> = (\<Sum>j<?n. \<Sum>i<?m. cnj (A $$ (i,j)) * B $$ (i,j))"
    by (rule sum.swap)
  also have "\<dots> = (\<Sum>j<?n. (A\<^sup>\<dagger> * B) $$ (j,j))"
  proof (intro sum.cong refl)
    fix j 
    assume "j \<in> {..<?n}"
    then have j_lt: "j < ?n" by simp
    have "(A\<^sup>\<dagger> * B) $$ (j,j) = (\<Sum>i<?m. (A\<^sup>\<dagger>) $$ (j,i) * B $$ (i,j))"
      using j_lt rows cols by simp
    also have "\<dots> = (\<Sum>i<?m. cnj (A $$ (i,j)) * B $$ (i,j))"
      by (intro sum.cong refl, metis dagger_def index_mat(1) j_lt lessThan_iff old.prod.case)
    finally show "(\<Sum>i<?m. cnj (A $$ (i,j)) * B $$ (i,j)) = (A\<^sup>\<dagger> * B) $$ (j,j)"
      by simp
  qed
  also have "\<dots> = Tr (A\<^sup>\<dagger> * B)"
    using rows cols by (simp add: Tr_def)
  finally show ?thesis.
qed

corollary hs_inner_prod_self_as_trace:
  shows "\<langle>\<langle> A | A \<rangle>\<rangle> = Tr ((A\<^sup>\<dagger>) * A)"
  by (rule hs_inner_prod_as_trace) simp_all

(* ============================================================================
   SECTION 12: Orthogonal Projections
   ============================================================================

   Given an orthonormal set v_0, ..., v_{k-1} in \<complex>^n (with k \<le> n),
   define the projection matrix

     P = \<Sum>_{l=0}^{k-1} |v_l\<rangle>\<langle>v_l|

   which has (i,j)-entry  \<Sum>_l  (v_l)_i \<sqdot> cnj((v_l)_j).

   The main result is that Px lies in span{v_0, ..., v_{k-1}}, expressed
   entrywise as:

     (Px)_i = \<Sum>_l \<langle>v_l | x\<rangle> \<sqdot> (v_l)_i

   i.e. Px is a linear combination of the v_l with coefficients \<langle>v_l|x\<rangle>.
   ============================================================================ *)

(* ============================================================================
   SECTION 12: Orthogonal Projections and Parseval's Identity
   ============================================================================

   Given an orthonormal list of vectors vs in \<complex>^n, we form the matrix
   V = mat_of_cols n vs (from JNF), whose l-th column is vs ! l.

   The projection is P = V * V\<dagger>.

   We show:
     - V\<dagger>V = I                    (from orthonormality)
     - VV\<dagger> = I when |vs| = n     (full basis \<Longrightarrow> completeness)
     - Px = \<Sum>_l \<langle>v_l|x\<rangle> \<sqdot> v_l   (projection formula)
     - P\<dagger> = P                     (self-adjointness)
     - P² = P                     (idempotence)
     - Parseval's identity
   ============================================================================ *)


(* --- Orthonormality predicate for a list of vectors --- *)

definition orthonormal_list :: "nat \<Rightarrow> complex Matrix.vec list \<Rightarrow> bool" where
  "orthonormal_list n vs \<equiv>
     (\<forall>v \<in> set vs. dim_vec v = n) \<and>
     (\<forall>i < length vs. \<forall>j < length vs.
        \<langle>vs ! i | vs ! j\<rangle> = (if i = j then 1 else 0))"

lemma orthonormal_listD_dim:
  assumes "orthonormal_list n vs" and "i < length vs"
  shows "dim_vec (vs ! i) = n"
  using assms by (simp add: orthonormal_list_def)

lemma orthonormal_listD_inner:
  assumes "orthonormal_list n vs" and "i < length vs" and "j < length vs"
  shows "\<langle>vs ! i | vs ! j\<rangle> = (if i = j then 1 else 0)"
  using assms by (simp add: orthonormal_list_def, force)

lemma orthonormal_listD_carrier:
  assumes "orthonormal_list n vs"
  shows "set vs \<subseteq> carrier_vec n"
  using assms orthonormal_list_def by auto


(* --- The projection matrix P = V * V\<dagger> --- *)
(* --- The outer product sum: V * V\<dagger> = \<Sum>_l |v_l\<rangle>\<langle>v_l| --- *)

definition outer_sum :: "nat \<Rightarrow> complex Matrix.vec list \<Rightarrow> complex Matrix.mat" where
  "outer_sum n vs = mat_of_cols n vs * ((mat_of_cols n vs)\<^sup>\<dagger>)"

lemma outer_sum_dim_row [simp]: "dim_row (outer_sum n vs) = n"
  by (simp add: outer_sum_def)

lemma outer_sum_dim_col [simp]: "dim_col (outer_sum n vs) = n"
  by (simp add: outer_sum_def)

lemma outer_sum_hermitian:
  shows "(outer_sum n vs)\<^sup>\<dagger> = outer_sum n vs"
  unfolding outer_sum_def
  by (simp add: dagger_of_prod dagger_of_dagger_is_id)


(* --- V\<dagger>V = 1\<^sub>m k, from orthonormality --- *)

lemma cols_mat_dagger_left:
  assumes orth: "orthonormal_list n vs"
  shows "(mat_of_cols n vs)\<^sup>\<dagger> * (mat_of_cols n vs) = 1\<^sub>m (length vs)"
proof (rule eq_matI)
  let ?V = "mat_of_cols n vs"
  let ?k = "length vs"
  show "dim_row (?V\<^sup>\<dagger> * ?V) = dim_row (1\<^sub>m ?k)" by simp
  show "dim_col (?V\<^sup>\<dagger> * ?V) = dim_col (1\<^sub>m ?k)" by simp
  fix l1 l2
  assume "l1 < dim_row (1\<^sub>m ?k)" and "l2 < dim_col (1\<^sub>m ?k)"
  then have l12: "l1 < ?k" "l2 < ?k" by simp_all

  have dim1: "dim_vec (vs ! l1) = n" using orth l12(1) by (simp add: orthonormal_listD_dim)
  have dim2: "dim_vec (vs ! l2) = n" using orth l12(2) by (simp add: orthonormal_listD_dim)

  have "(?V\<^sup>\<dagger> * ?V) $$ (l1,l2) = (\<Sum>i<n. (?V\<^sup>\<dagger>) $$ (l1,i) * ?V $$ (i,l2))"
    using l12 by simp
  also have "\<dots> = (\<Sum>i<n. cnj ((vs ! l1) $ i) * (vs ! l2) $ i)"
    using l12 dim1 dim2 by (intro sum.cong refl)
       (simp add: dagger_def mat_of_cols_def)
  also have "\<dots> = \<langle>vs ! l1 | vs ! l2\<rangle>"
    using dim1 dim2 by (simp add: inner_prod_def atLeast0LessThan)
  also have "\<dots> = (if l1 = l2 then 1 else 0)"
    using orth l12 by (simp add: orthonormal_listD_inner)
  also have "\<dots> = (1\<^sub>m ?k) $$ (l1,l2)"
    using l12 by simp
  finally show "(?V\<^sup>\<dagger> * ?V) $$ (l1,l2) = (1\<^sub>m ?k) $$ (l1,l2)" .
qed


(* --- When length vs = n (full basis): VV\<dagger> = I --- *)

lemma cols_mat_dagger_right:
  assumes orth: "orthonormal_list n vs"
      and full: "length vs = n"
  shows "(mat_of_cols n vs) * ((mat_of_cols n vs)\<^sup>\<dagger>) = 1\<^sub>m n"
proof -
  let ?V = "mat_of_cols n vs"
  have left: "?V\<^sup>\<dagger> * ?V = 1\<^sub>m n"
    using cols_mat_dagger_left[OF orth] full by simp
  then have "inverts_mat (?V\<^sup>\<dagger>) ?V"
    by (simp add: full inverts_mat_def)
  then have "inverts_mat ?V (?V\<^sup>\<dagger>)"
    by (metis dim_col_of_dagger full inverts_mat_sym
        mat_of_cols_carrier(2,3) square_mat.elims(3))
  then show ?thesis
    by (simp add: inverts_mat_def full)
qed


(* --- Completeness relation: \<Sum>_l (v_l)_i \<sqdot> cnj((v_l)_j) = \<delta>_{ij} --- *)

lemma completeness_relation:
  assumes orth: "orthonormal_list n vs"
      and full: "length vs = n"
      and i_lt: "i < n" and j_lt: "j < n"
  shows "(\<Sum>l<n. (vs ! l) $ i * cnj ((vs ! l) $ j)) = (if i = j then 1 else 0)"
proof -
  let ?V = "mat_of_cols n vs"
  have "(?V * (?V\<^sup>\<dagger>)) $$ (i,j) = (\<Sum>l<n. ?V $$ (i,l) * (?V\<^sup>\<dagger>) $$ (l,j))"
    using i_lt j_lt full by simp
  also have "\<dots> = (\<Sum>l<n. (vs ! l) $ i * cnj ((vs ! l) $ j))"
    using i_lt j_lt full
    by (intro sum.cong refl, simp add: mat_of_cols_def dagger_def orthonormal_listD_dim[OF orth])
  finally have sum_eq: "(\<Sum>l<n. (vs ! l) $ i * cnj ((vs ! l) $ j)) = (?V * (?V\<^sup>\<dagger>)) $$ (i,j)"
    by simp
  also have "(?V * (?V\<^sup>\<dagger>)) $$ (i,j) = (1\<^sub>m n) $$ (i,j)"
    by (simp add: cols_mat_dagger_right full orth)
  also have "\<dots> = (if i = j then 1 else 0)"
    using i_lt j_lt by simp
  finally show ?thesis using sum_eq by simp
qed


(* --- Outer sum entry formula --- *)

lemma outer_sum_index:
  assumes orth: "orthonormal_list n vs"
      and i_lt: "i < n" and j_lt: "j < n"
  shows "(outer_sum n vs) $$ (i,j) = 
         (\<Sum>l < length vs. (vs ! l) $ i * cnj ((vs ! l) $ j))"
proof -
  let ?V = "mat_of_cols n vs"
  let ?k = "length vs"
  have "(outer_sum n vs) $$ (i,j) = (?V * (?V\<^sup>\<dagger>)) $$ (i,j)"
    by (simp add: outer_sum_def)
  also have "\<dots> = (\<Sum>l<?k. ?V $$ (i,l) * (?V\<^sup>\<dagger>) $$ (l,j))"
    using i_lt j_lt by (simp add: outer_sum_def)
  also have "\<dots> = (\<Sum>l<?k. (vs ! l) $ i * cnj ((vs ! l) $ j))"
    using i_lt j_lt
    by (intro sum.cong refl)
       (simp add: mat_of_cols_def dagger_def orthonormal_listD_dim[OF orth])
  finally show ?thesis.
qed


(* --- Outer sum applies as: (\<Sum>|v_l\<rangle>\<langle>v_l| \<sqdot> x)_i = \<Sum>_l \<langle>v_l|x\<rangle> \<sqdot> (v_l)_i --- *)

lemma outer_sum_apply:
  assumes orth: "orthonormal_list n vs"
      and xdim: "dim_vec x = n"
      and i_lt: "i < n"
  shows "(outer_sum n vs *\<^sub>v x) $ i =  (\<Sum>l < length vs. \<langle>vs ! l | x\<rangle> * (vs ! l) $ i)"
proof -
  let ?V = "mat_of_cols n vs"
  let ?k = "length vs"
  have "(outer_sum n vs *\<^sub>v x) $ i = Matrix.row (outer_sum n vs) i \<bullet> x"
    using i_lt xdim by simp
  also have "\<dots> = (\<Sum>j<n. (outer_sum n vs) $$ (i,j) * x $ j)"
    using i_lt xdim  lessThan_atLeast0 by (simp add: scalar_prod_def)
  also have "\<dots> = (\<Sum>j<n. (\<Sum>l<?k. (vs ! l) $ i * cnj ((vs ! l) $ j)) * x $ j)"
    by (intro sum.cong refl, simp add: outer_sum_index[OF orth i_lt])
  also have "\<dots> = (\<Sum>j<n. \<Sum>l<?k. (vs ! l) $ i * cnj ((vs ! l) $ j) * x $ j)"
    by (intro sum.cong refl) (simp add: sum_distrib_right)
  also have "\<dots> = (\<Sum>l<?k. \<Sum>j<n. (vs ! l) $ i * cnj ((vs ! l) $ j) * x $ j)"
    by (rule sum.swap)
  also have "\<dots> = (\<Sum>l<?k. (vs ! l) $ i * (\<Sum>j<n. cnj ((vs ! l) $ j) * x $ j))"
    by (intro sum.cong refl, 
        metis (mono_tags, lifting) semigroup_mult_class.mult.assoc sum.cong sum_distrib_left)
  also have "\<dots> = (\<Sum>l<?k. (vs ! l) $ i * \<langle>vs ! l | x\<rangle>)"
    using atLeast0LessThan inner_prod_def xdim by (intro sum.cong refl, presburger)   
  also have "\<dots> = (\<Sum>l<?k. \<langle>vs ! l | x\<rangle> * (vs ! l) $ i)"
    by (intro sum.cong refl) (simp add: mult.commute)
  finally show ?thesis.
qed


(* --- Under orthonormality, outer_sum is idempotent (hence a projection) --- *)

lemma outer_sum_idempotent:
  assumes orth: "orthonormal_list n vs"
  shows "outer_sum n vs * outer_sum n vs = outer_sum n vs"
proof -
  let ?V = "mat_of_cols n vs"
  let ?k = "length vs"

  have "outer_sum n vs * outer_sum n vs = (?V * (?V\<^sup>\<dagger>)) * (?V * (?V\<^sup>\<dagger>))"
    by (simp add: outer_sum_def)
  also have "\<dots> = ?V * ((?V\<^sup>\<dagger>) * ?V) * (?V\<^sup>\<dagger>)"
    by (metis (no_types, lifting) assoc_mult_mat carrier_mat_triv dim_col_of_dagger 
        dim_row_of_dagger mat_of_cols_carrier(2) outer_sum_def outer_sum_dim_col)
  also have "\<dots> = ?V * (1\<^sub>m ?k) * (?V\<^sup>\<dagger>)"
    using cols_mat_dagger_left[OF orth] by simp
  also have "\<dots> = ?V * (?V\<^sup>\<dagger>)"
    by simp
  also have "\<dots> = outer_sum n vs"
    by (simp add: outer_sum_def)
  finally show ?thesis .
qed


(* --- Parseval's identity (entrywise) --- *)

lemma parseval:
  assumes orth: "orthonormal_list n vs"
      and full: "length vs = n"
      and vdim: "dim_vec v = n"
      and i_lt: "i < n"
  shows "v $ i = (\<Sum>l<n. \<langle>vs ! l | v\<rangle> * (vs ! l) $ i)"
proof -
  have "(\<Sum>l<n. \<langle>vs ! l | v\<rangle> * (vs ! l) $ i) =
        (\<Sum>l<n. (\<Sum>j<n. cnj ((vs ! l) $ j) * v $ j) * (vs ! l) $ i)"
    using atLeast0LessThan inner_prod_def vdim by (intro sum.cong refl, simp)   
  also have "\<dots> = (\<Sum>l<n. \<Sum>j<n. cnj ((vs ! l) $ j) * v $ j * (vs ! l) $ i)"
    by (intro sum.cong refl, simp add: sum_distrib_right)
  also have "\<dots> = (\<Sum>j<n. \<Sum>l<n. cnj ((vs ! l) $ j) * v $ j * (vs ! l) $ i)"
    by (rule sum.swap)
  also have "\<dots> = (\<Sum>j<n. v $ j * (\<Sum>l<n. (vs ! l) $ i * cnj ((vs ! l) $ j)))"
    by (intro sum.cong refl)
       (simp add: sum_distrib_left mult.assoc mult.commute mult.left_commute)
  also have "\<dots> = (\<Sum>j<n. v $ j * (if i = j then 1 else 0))"
    using orth full i_lt by (intro sum.cong refl, simp add: completeness_relation)
  also have "... = (\<Sum>j<n. if j = i then v $ j else 0)"
    by (intro sum.cong refl) auto
  also have "\<dots> = v $ i"
    using i_lt by simp
  finally show ?thesis 
    by simp
qed

(* --- Parseval's norm identity: \<Parallel>v\<Parallel>² = \<Sum>_l |\<langle>v_l|v\<rangle>|² --- *)

corollary parseval_norm:
  assumes orth: "orthonormal_list n vs"
      and full: "length vs = n"
      and vdim: "dim_vec v = n"
  shows "\<parallel>v\<parallel>\<^sup>2 = (\<Sum>l<n. (cmod (\<langle>vs ! l | v\<rangle>))\<^sup>2)"
proof -
  have "\<parallel>v\<parallel>\<^sup>2 = \<langle>v|v\<rangle>"
    using cpx_vec_length_inner_prod by presburger
  also have "\<dots> = (\<Sum>i<n. cnj (v $ i) * v $ i)"
    using vdim by (simp add: inner_prod_def atLeast0LessThan)
  also have "\<dots> = (\<Sum>i<n. cnj (v $ i) * (\<Sum>l<n. \<langle>vs ! l | v\<rangle> * (vs ! l) $ i))"
    using orth full vdim by (intro sum.cong refl arg_cong[where f = "\<lambda>s. cnj (v $ _) * s"], 
        simp add: parseval) 
  also have "\<dots> = (\<Sum>i<n. \<Sum>l<n. cnj (v $ i) * (\<langle>vs ! l | v\<rangle> * (vs ! l) $ i))"
    by (intro sum.cong refl) (simp add: sum_distrib_left)
  also have "\<dots> = (\<Sum>i<n. \<Sum>l<n. \<langle>vs ! l | v\<rangle> * (cnj (v $ i) * (vs ! l) $ i))"
    by (intro sum.cong refl, simp add: mult.assoc mult.commute mult.left_commute)
  also have "\<dots> = (\<Sum>l<n. \<Sum>i<n. \<langle>vs ! l | v\<rangle> * (cnj (v $ i) * (vs ! l) $ i))"
    by (rule sum.swap)
  also have "\<dots> = (\<Sum>l<n. \<langle>vs ! l | v\<rangle> * (\<Sum>i<n. cnj (v $ i) * (vs ! l) $ i))"
    by (intro sum.cong refl) (simp add: sum_distrib_left)
  also have "\<dots> = (\<Sum>l<n. \<langle>vs ! l | v\<rangle> * \<langle>v | vs ! l\<rangle>)"
    using atLeast0LessThan full inner_prod_def orth orthonormal_listD_dim by force
  also have "\<dots> = (\<Sum>l<n. \<langle>vs ! l | v\<rangle> * cnj (\<langle>vs ! l | v\<rangle>))"
    by (simp add: full inner_prod_cnj orth orthonormal_listD_dim vdim)    
  also have "\<dots> = (\<Sum>l<n. (cmod (\<langle>vs ! l | v\<rangle>))\<^sup>2)"
    using complex_norm_square by force
  finally show ?thesis
    by (meson of_real_eq_iff) 
qed

(* ============================================================================
   SECTION 14: Orthogonality of the Residual
   ============================================================================

   If P = outer_sum n vs = \<Sum>_l |v_l\<rangle>\<langle>v_l| and the v_l are orthonormal, then:

     \<langle>v_l | Px\<rangle> = \<langle>v_l | x\<rangle>       (P reproduces inner products with basis vectors)
     \<langle>v_l | x - Px\<rangle> = 0           (the residual is orthogonal to each v_l)
     x = Px + (x - Px)            (orthogonal decomposition)
   ============================================================================ *)


(* --- Key lemma: \<langle>v_l | Px\<rangle> = \<langle>v_l | x\<rangle> --- *)

lemma inner_prod_outer_sum:
  assumes orth: "orthonormal_list n vs"
      and xdim: "dim_vec x = n"
      and l_lt: "l < length vs"
  shows "\<langle>vs ! l | outer_sum n vs *\<^sub>v x\<rangle> = \<langle>vs ! l | x\<rangle>"
proof -
  let ?k = "length vs"
  have ldim: "dim_vec (vs ! l) = n" 
    using orth l_lt by (simp add: orthonormal_listD_dim)
  have Pdim: "dim_vec (outer_sum n vs *\<^sub>v x) = n" 
    using xdim by simp
  have "\<langle>vs ! l | outer_sum n vs *\<^sub>v x\<rangle> = (\<Sum>i<n. cnj ((vs ! l) $ i) * (outer_sum n vs *\<^sub>v x) $ i)"
    using ldim Pdim by (simp add: inner_prod_def atLeast0LessThan)
  also have "\<dots> = (\<Sum>i<n. cnj ((vs ! l) $ i) * (\<Sum>m<?k. \<langle>vs ! m | x\<rangle> * (vs ! m) $ i))"
    using orth xdim outer_sum_apply 
    by(intro sum.cong refl arg_cong[where f = "\<lambda>s. cnj _ * s"], auto)
  also have "\<dots> = (\<Sum>i<n. \<Sum>m<?k. cnj ((vs ! l) $ i) * (\<langle>vs ! m | x\<rangle> * (vs ! m) $ i))"
    by (intro sum.cong refl) (simp add: sum_distrib_left)
  also have "\<dots> = (\<Sum>i<n. \<Sum>m<?k. \<langle>vs ! m | x\<rangle> * (cnj ((vs ! l) $ i) * (vs ! m) $ i))"
    by (intro sum.cong refl, simp add: mult.assoc mult.commute mult.left_commute)
  also have "\<dots> = (\<Sum>m<?k. \<Sum>i<n. \<langle>vs ! m | x\<rangle> * (cnj ((vs ! l) $ i) * (vs ! m) $ i))"
    by (rule sum.swap)
  also have "\<dots> = (\<Sum>m<?k. \<langle>vs ! m | x\<rangle> * (\<Sum>i<n. cnj ((vs ! l) $ i) * (vs ! m) $ i))"
    by (intro sum.cong refl, simp add: sum_distrib_left)
  also have "\<dots> = (\<Sum>m<?k. \<langle>vs ! m | x\<rangle> * \<langle>vs ! l | vs ! m\<rangle>)"
    using atLeast0LessThan inner_prod_def orth orthonormal_listD_dim by auto    
  also have "\<dots> = (\<Sum>m<?k. \<langle>vs ! m | x\<rangle> * (if l = m then 1 else 0))"
    using orth l_lt by (intro sum.cong refl, simp add: orthonormal_listD_inner)
  also have "\<dots> = (\<Sum>m<?k. if m = l then \<langle>vs ! m | x\<rangle> else 0)"
    by (intro sum.cong refl) auto
  also have "\<dots> = \<langle>vs ! l | x\<rangle>"
    using l_lt by simp
  finally show ?thesis.
qed


(* --- The residual x - Px is orthogonal to each basis vector --- *)

lemma residual_orthogonal:
  assumes orth: "orthonormal_list n vs"
      and xdim: "dim_vec x = n"
      and l_lt: "l < length vs"
  shows "\<langle>vs ! l | x - outer_sum n vs *\<^sub>v x\<rangle> = 0"
proof -
  let ?Px = "outer_sum n vs *\<^sub>v x"
  have ldim: "dim_vec (vs ! l) = n" 
    using orth l_lt by (simp add: orthonormal_listD_dim)
  have Pdim: "dim_vec ?Px = n" 
    using xdim by simp
  have diffdim: "dim_vec (x - ?Px) = n" 
    using xdim Pdim by simp
  have "\<langle>vs ! l | x - ?Px\<rangle> = (\<Sum>i<n. cnj ((vs ! l) $ i) * (x - ?Px) $ i)"
    using ldim diffdim by (simp add: inner_prod_def atLeast0LessThan)
  also have "\<dots> = (\<Sum>i<n. cnj ((vs ! l) $ i) * (x $ i - ?Px $ i))"
    using xdim Pdim by (intro sum.cong refl, simp)
  also have "\<dots> = (\<Sum>i<n. cnj ((vs ! l) $ i) * x $ i - cnj ((vs ! l) $ i) * ?Px $ i)"
    by (intro sum.cong refl, simp add: right_diff_distrib)
  also have "\<dots> = (\<Sum>i<n. cnj ((vs ! l) $ i) * x $ i) -
                  (\<Sum>i<n. cnj ((vs ! l) $ i) * ?Px $ i)"
    by (simp add: sum_subtractf)
  also have "\<dots> = \<langle>vs ! l | x\<rangle> - \<langle>vs ! l | ?Px\<rangle>"
    using ldim xdim Pdim by (simp add: inner_prod_def atLeast0LessThan)
  also have "\<dots> = \<langle>vs ! l | x\<rangle> - \<langle>vs ! l | x\<rangle>"
    using inner_prod_outer_sum[OF orth xdim l_lt] by simp
  also have "\<dots> = 0" 
    by simp
  finally show ?thesis.
qed


(* --- Orthogonal decomposition: x = Px + (x - Px) --- *)

corollary orthogonal_decomposition:
  assumes xdim: "dim_vec x = n"
  shows "x = outer_sum n vs *\<^sub>v x + (x - outer_sum n vs *\<^sub>v x)"
proof -
  have "dim_vec (outer_sum n vs *\<^sub>v x) = n" 
    using xdim by simp
  then show ?thesis using xdim
    by (intro eq_vecI, auto)
qed

(* ============================================================================
   SECTION 15: Uniqueness of the Orthogonal Decomposition
   ============================================================================

   If x = v + w where Pv = v (v is in the image of P) and \<langle>v_l|w\<rangle> = 0
   for all l (w is orthogonal to V), then v = Px and w = x - Px.
   ============================================================================ *)


(* --- Helper: If w is orthogonal to every basis vector, then Pw = 0 --- *)

lemma outer_sum_orthogonal_zero:
  assumes orth: "orthonormal_list n vs"
      and wdim: "dim_vec w = n"
      and ortho: "\<forall>l < length vs. \<langle>vs ! l | w\<rangle> = 0"
  shows "outer_sum n vs *\<^sub>v w = 0\<^sub>v n"
proof (rule eq_vecI)
  show "dim_vec (outer_sum n vs *\<^sub>v w) = dim_vec (0\<^sub>v n)"
    using wdim by simp
next
  fix i assume "i < dim_vec (0\<^sub>v n)"
  then have i_lt: "i < n" by simp
  have "(outer_sum n vs *\<^sub>v w) $ i =
        (\<Sum>l < length vs. \<langle>vs ! l | w\<rangle> * (vs ! l) $ i)"
    using outer_sum_apply[OF orth wdim i_lt] .
  also have "\<dots> = (\<Sum>l < length vs. 0 * (vs ! l) $ i)"
    using ortho by (intro sum.cong refl) simp
  also have "\<dots> = 0" by simp
  finally show "(outer_sum n vs *\<^sub>v w) $ i = (0\<^sub>v n) $ i"
    using i_lt by simp
qed


(* --- Helper: P is linear on vectors (distributes over +) --- *)

lemma outer_sum_add:
  assumes vdim: "dim_vec v = n" and wdim: "dim_vec w = n"
  shows "outer_sum n vs *\<^sub>v (v + w) = 
         outer_sum n vs *\<^sub>v v + outer_sum n vs *\<^sub>v w"
proof -
  have "outer_sum n vs \<in> carrier_mat n n"
    by fastforce

  moreover have "v \<in> carrier_vec n" 
    using vdim carrier_vec_dim_vec by blast
  moreover have "w \<in> carrier_vec n" 
    using wdim carrier_vec_dim_vec by blast
  ultimately show ?thesis
    by (simp add: mult_add_distrib_mat_vec)
qed


(* --- Uniqueness of the decomposition --- *)

lemma orthogonal_decomposition_unique:
  assumes orth: "orthonormal_list n vs"
      and xdim: "dim_vec x = n"
      and vdim: "dim_vec v = n"
      and wdim: "dim_vec w = n"
      and decomp: "x = v + w"
      and v_fixed: "outer_sum n vs *\<^sub>v v = v"
      and w_ortho: "\<forall>l < length vs. \<langle>vs ! l | w\<rangle> = 0"
  shows "v = outer_sum n vs *\<^sub>v x" and "w = x - outer_sum n vs *\<^sub>v x"
proof -
  let ?P = "outer_sum n vs"

  have "v = v + 0\<^sub>v n"
    by (simp add: carrier_vecI vdim)
  also have "\<dots> = ?P *\<^sub>v v + ?P *\<^sub>v w"
    using v_fixed outer_sum_orthogonal_zero[OF orth wdim w_ortho] by simp
  also have "\<dots> = ?P *\<^sub>v (v + w)"
    using outer_sum_add[OF vdim wdim] by simp
  also have "\<dots> = ?P *\<^sub>v x"
    using decomp by simp
  finally show Px_eq: "v = ?P *\<^sub>v x".

  have "w = (v + w) - v"
    using vdim wdim by auto
  also have "\<dots> = x - v"
    using decomp by simp
  also have "\<dots> = x - ?P *\<^sub>v x"
    using Px_eq by simp
  finally show "w = x - ?P *\<^sub>v x".
qed


section \<open> Unitary Algebra \<close>

lemma unitary_square_dim:
  assumes uA: "unitary A"
  shows "dim_row A = dim_col A"
proof -
  let ?m = "dim_row A"
  let ?n = "dim_col A"

  have inv_l: "(A\<^sup>\<dagger>) * A = 1\<^sub>m ?n"
    using uA unfolding unitary_def by auto
  have inv_r: "A * (A\<^sup>\<dagger>) = 1\<^sub>m ?m"
    using uA unfolding unitary_def by auto

  have dim_adj: "dim_row (A\<^sup>\<dagger>) = ?n" "dim_col (A\<^sup>\<dagger>) = ?m"
    by (simp_all add: dagger_def)

  have left_expand:
    "(\<Sum>c=0..<?n. (((A\<^sup>\<dagger>) * A) $$ (c,c))) =
     (\<Sum>c=0..<?n. \<Sum>r=0..<?m. cnj (A $$ (r,c)) * A $$ (r,c))"
  proof (rule sum.cong[OF refl])
    fix c
    assume "c \<in> {0..<dim_col A}"
    then have c_lt: "c < ?n"
      using atLeastLessThan_iff by blast
    have "(((A\<^sup>\<dagger>) * A) $$ (c,c)) =
          (\<Sum>r=0..<?m. (A\<^sup>\<dagger>) $$ (c,r) * A $$ (r,c))"
      by (simp add: atLeast0LessThan c_lt)
    also have "... = (\<Sum>r=0..<?m. cnj (A $$ (r,c)) * A $$ (r,c))"
    proof (rule sum.cong[OF refl])
      fix x 
      assume "x \<in> {0..<dim_row A}"
      then have x_lt: "x < ?m"
        using atLeastLessThan_iff by blast
      show "(A\<^sup>\<dagger>) $$ (c,x) * A $$ (x,c) =
            cnj (A $$ (x,c)) * A $$ (x,c)"
        using c_lt x_lt by (simp add: dagger_def)
    qed
    finally show "(A\<^sup>\<dagger> * A) $$ (c, c) = (\<Sum>r = 0..<dim_row A. cnj (A $$ (r, c)) * A $$ (r, c))" .
  qed

  have right_expand:
    "(\<Sum>r=0..<?m. ((A * (A\<^sup>\<dagger>)) $$ (r,r))) =
     (\<Sum>r=0..<?m. \<Sum>c=0..<?n. A $$ (r,c) * cnj (A $$ (r,c)))"
  proof (rule sum.cong[OF refl])
    fix r
    assume "r \<in> {0..<dim_row A}"
    then have r: "r < ?m"
      using atLeastLessThan_iff by blast
    have "((A * (A\<^sup>\<dagger>)) $$ (r,r)) =
          (\<Sum>c=0..<?n. A $$ (r,c) * (A\<^sup>\<dagger>) $$ (c,r))"
      using r dim_adj atLeast0LessThan
      by (auto simp: scalar_prod_def)
    also have "... = (\<Sum>c=0..<?n. A $$ (r,c) * cnj (A $$ (r,c)))"
    proof (rule sum.cong[OF refl])
      fix c 
      assume "c \<in> {0..<dim_col A}"
      then have c: "c < ?n"
        using atLeast0LessThan by blast
      show "A $$ (r,c) * (A\<^sup>\<dagger>) $$ (c,r) =
            A $$ (r,c) * cnj (A $$ (r,c))"
        using c r by (simp add: dagger_def)
    qed
    finally show "((A * (A\<^sup>\<dagger>)) $$ (r,r)) =
                  (\<Sum>c=0..<?n. A $$ (r,c) * cnj (A $$ (r,c)))" .
  qed
  have left_id: "(\<Sum>c=0..<?n. (((A\<^sup>\<dagger>) * A) $$ (c,c))) = of_nat ?n"
    using inv_l by simp

  have right_id: "(\<Sum>r=0..<?m. ((A * (A\<^sup>\<dagger>)) $$ (r,r))) = of_nat ?m"
    using inv_r by simp
  have "of_nat ?n = (\<Sum>c=0..<?n. \<Sum>r=0..<?m. cnj (A $$ (r,c)) * A $$ (r,c))"
    using left_id left_expand by simp
  also have "... =
        (\<Sum>c=0..<?n. \<Sum>r=0..<?m. A $$ (r,c) * cnj (A $$ (r,c)))"
    by (intro sum.cong[OF refl] sum.cong[OF refl]) (simp add: mult.commute)
  also have "... =
        (\<Sum>r=0..<?m. \<Sum>c=0..<?n. A $$ (r,c) * cnj (A $$ (r,c)))"
    using sum.swap by force
  also have "... = of_nat ?m"
    using right_id right_expand by simp
  finally have "of_nat ?n = of_nat ?m"
    by simp 
  then show "dim_row A = dim_col A"
    by (metis of_nat_eq_iff)
qed

lemma unitary_inv_l_dimcol:
  assumes uA: "unitary A"
  shows "(A\<^sup>\<dagger>) * A = 1\<^sub>m (dim_col A)"
  using uA unfolding unitary_def by auto

lemma unitary_inv_r_dimrow:
  assumes uA: "unitary A"
  shows "A * (A\<^sup>\<dagger>) = 1\<^sub>m (dim_row A)"
  using uA unfolding unitary_def by auto

lemma unitary_inv_l_dimrow:
  assumes uA: "unitary A"
  shows "(A\<^sup>\<dagger>) * A = 1\<^sub>m (dim_row A)"
  by (metis uA unitary_def unitary_square_dim)

lemma unitary_inv_r_dimcol:
  assumes uA: "unitary A"
  shows "A * (A\<^sup>\<dagger>) = 1\<^sub>m (dim_col A)"
  by (metis uA unitary_def unitary_square_dim)

lemma unitary_carrier_square_col:
  assumes uA: "unitary A"
  shows "A \<in> carrier_mat (dim_col A) (dim_col A)"
  using unitary_square_dim uA by blast 

lemma unitary_carrier_square_row:
  assumes uA: "unitary A"
  shows "A \<in> carrier_mat (dim_row A) (dim_row A)"
  using uA unitary_square_dim by auto

lemma unitary_dagger:
  assumes uA: "unitary A"
  shows "unitary (A\<^sup>\<dagger>)"
proof -
  have "(A\<^sup>\<dagger>)\<^sup>\<dagger> * (A\<^sup>\<dagger>) = 1\<^sub>m (dim_col (A\<^sup>\<dagger>))"
    using dagger_of_dagger_is_id uA unitary_def by force
  moreover have "(A\<^sup>\<dagger>) * ((A\<^sup>\<dagger>)\<^sup>\<dagger>) = 1\<^sub>m (dim_row (A\<^sup>\<dagger>))"
    using dagger_of_dagger_is_id uA unitary_def by auto
  ultimately show ?thesis
    unfolding unitary_def
    by (simp add: dagger_def)
qed

lemma unitary_mult:
  assumes UA: "unitary A"
      and UB: "unitary B"
      and dimA: "A \<in> carrier_mat n n"
      and dimB: "B \<in> carrier_mat n n"
  shows "unitary (A * B)"
  by (smt (verit, best) UA UB assoc_mult_mat carrier_matD(1,2) 
      dagger_of_prod dimA dimB dim_col_of_dagger mult_carrier_mat right_mult_one_mat
      unitary_carrier_square_col unitary_dagger unitary_def)

lemma unitary_mult2:
  assumes UA: "unitary A"
      and UB: "unitary B"
      and dims: "dim_row A = dim_row B"
  shows "unitary (A * B)"
  by (metis UA UB dims unitary_carrier_square_row unitary_mult)


section \<open> Tensor Product Infrastructure \<close>

subsection \<open> Tensor of Identities \<close>

lemma tensor_mat_id:
  "Tensor.tensor_mat (1\<^sub>m n) (1\<^sub>m m) = 1\<^sub>m (n * m)"
proof (rule eq_matI)
  show "dim_row (Tensor.tensor_mat (1\<^sub>m n) (1\<^sub>m m)) = dim_row (1\<^sub>m (n * m))"
    by simp
  show "dim_col (Tensor.tensor_mat (1\<^sub>m n) (1\<^sub>m m)) = dim_col (1\<^sub>m (n * m))"
    by simp
  fix i j
  assume "i < dim_row (1\<^sub>m (n * m))" "j < dim_col (1\<^sub>m (n * m))"
  then have ij: "i < n * m" "j < n * m" by simp_all

  show "Tensor.tensor_mat (1\<^sub>m n) (1\<^sub>m m) $$ (i, j) = (1\<^sub>m (n * m)) $$ (i, j)"
  proof (cases "m = 0")
    case True
    then show ?thesis using ij by simp
  next
    case mpos: False
    then have m_pos: "0 < m" by simp
    have div_i: "i div m < n" using ij m_pos by (simp add: less_mult_imp_div_less)
    have div_j: "j div m < n" using ij m_pos by (simp add: less_mult_imp_div_less)
    have mod_i: "i mod m < m" using m_pos by simp
    have mod_j: "j mod m < m" using m_pos by simp

    have "Tensor.tensor_mat (1\<^sub>m n) (1\<^sub>m m) $$ (i, j) =
          (1\<^sub>m n) $$ (i div m, j div m) * (1\<^sub>m m) $$ (i mod m, j mod m)"
      using ij
      by (metis bot_nat_0.not_eq_extremum div_i index_one_mat(2,3) index_tensor_mat m_pos not_less_zero) 
    also have "\<dots> = (if i div m = j div m then 1 else 0) *
                     (if i mod m = j mod m then 1 else 0)"
      using div_i div_j mod_i mod_j by simp
    also have "\<dots> = (if i div m = j div m \<and> i mod m = j mod m then 1 else 0)"
      by simp
    also have "\<dots> = (if i = j then 1 else 0)"
    proof -
      have "i div m = j div m \<and> i mod m = j mod m \<longleftrightarrow> i = j"
      proof
        assume "i div m = j div m \<and> i mod m = j mod m"
        then have "m * (i div m) + i mod m = m * (j div m) + j mod m"
          by simp
        then show "i = j"
          by (simp add: mult_div_mod_eq[symmetric])
      qed simp
      then show ?thesis by simp
    qed
    also have "\<dots> = (1\<^sub>m (n * m)) $$ (i, j)"
      using ij by simp
    finally show ?thesis.
  qed
qed


subsection \<open> Tensor Adjoint \<close>

lemma tensor_mat_adjoint:
  "(Tensor.tensor_mat A B)\<^sup>\<dagger> = Tensor.tensor_mat (A\<^sup>\<dagger>) (B\<^sup>\<dagger>)"
proof (rule eq_matI)
  let ?ra = "dim_row A"  let ?ca = "dim_col A"
  let ?rb = "dim_row B"  let ?cb = "dim_col B"

  show "dim_row ((Tensor.tensor_mat A B)\<^sup>\<dagger>) =
        dim_row (Tensor.tensor_mat (A\<^sup>\<dagger>) (B\<^sup>\<dagger>))"
    by (simp add: dagger_def)
  show "dim_col ((Tensor.tensor_mat A B)\<^sup>\<dagger>) =
        dim_col (Tensor.tensor_mat (A\<^sup>\<dagger>) (B\<^sup>\<dagger>))"
    by (simp add: dagger_def)

  fix i j
  assume "i < dim_row (Tensor.tensor_mat (A\<^sup>\<dagger>) (B\<^sup>\<dagger>))"
         "j < dim_col (Tensor.tensor_mat (A\<^sup>\<dagger>) (B\<^sup>\<dagger>))"
  then have dims:
    "i < ?ca * ?cb" "j < ?ra * ?rb"
    by (simp_all add: dagger_def)

  show "(Tensor.tensor_mat A B)\<^sup>\<dagger> $$ (i, j) =
        Tensor.tensor_mat (A\<^sup>\<dagger>) (B\<^sup>\<dagger>) $$ (i, j)"
  proof (cases "?rb = 0 \<or> ?cb = 0")
    case True
    then show ?thesis using dims by auto
  next
    case False
    then have rb_pos: "0 < ?rb" and cb_pos: "0 < ?cb" by auto

    have div_i_cb: "i div ?cb < ?ca" using dims cb_pos
      by (simp add: less_mult_imp_div_less)
    have mod_i_cb: "i mod ?cb < ?cb" using cb_pos by simp
    have div_j_rb: "j div ?rb < ?ra" using dims rb_pos
      by (simp add: less_mult_imp_div_less)
    have mod_j_rb: "j mod ?rb < ?rb" using rb_pos by simp

    have lhs: "(Tensor.tensor_mat A B)\<^sup>\<dagger> $$ (i, j) =
               cnj (Tensor.tensor_mat A B $$ (j, i))"
      using dims by (simp add: dagger_def)

    have expand_ji: "Tensor.tensor_mat A B $$ (j, i) =
          A $$ (j div ?rb, i div ?cb) * B $$ (j mod ?rb, i mod ?cb)"
      using dims
      by (metis cb_pos div_i_cb index_tensor_mat less_zeroE not_gr0) 

    have lhs_eq: "(Tensor.tensor_mat A B)\<^sup>\<dagger> $$ (i, j) =
          cnj (A $$ (j div ?rb, i div ?cb)) * cnj (B $$ (j mod ?rb, i mod ?cb))"
      using lhs expand_ji by simp

    have rhs_eq: "Tensor.tensor_mat (A\<^sup>\<dagger>) (B\<^sup>\<dagger>) $$ (i, j) =
          (A\<^sup>\<dagger>) $$ (i div ?cb, j div ?rb) * (B\<^sup>\<dagger>) $$ (i mod ?cb, j mod ?rb)"
      using dims by (auto simp: dagger_def, metis bot_nat_0.not_eq_extremum dim_col_mat(1) 
                     dim_row_mat(1) index_tensor_mat mult_eq_0_iff not_less_zero)

    have dagger_A: "(A\<^sup>\<dagger>) $$ (i div ?cb, j div ?rb) =
                    cnj (A $$ (j div ?rb, i div ?cb))"
      using div_i_cb div_j_rb by (simp add: dagger_def)
    have dagger_B: "(B\<^sup>\<dagger>) $$ (i mod ?cb, j mod ?rb) =
                    cnj (B $$ (j mod ?rb, i mod ?cb))"
      using mod_i_cb mod_j_rb by (simp add: dagger_def)
    from lhs_eq rhs_eq dagger_A dagger_B
    show ?thesis by simp
  qed
qed


subsection \<open> Mixed-Product Property \<close>


lemma tensor_mat_mult:
  assumes dimAC: "dim_col A = dim_row C"
      and dimBD: "dim_col B = dim_row D"
  shows "Tensor.tensor_mat A B * Tensor.tensor_mat C D =
         Tensor.tensor_mat (A * C) (B * D)"
proof (rule eq_matI)
  let ?ra = "dim_row A"  let ?ca = "dim_col A"
  let ?rb = "dim_row B"  let ?cb = "dim_col B"
  let ?rc = "dim_row C"  let ?cc = "dim_col C"
  let ?rd = "dim_row D"  let ?cd = "dim_col D"

  from dimAC have rc: "?rc = ?ca" by simp
  from dimBD have rd: "?rd = ?cb" by simp

  show "dim_row (Tensor.tensor_mat A B * Tensor.tensor_mat C D) =
        dim_row (Tensor.tensor_mat (A * C) (B * D))"
    using rc rd by simp

  show "dim_col (Tensor.tensor_mat A B * Tensor.tensor_mat C D) =
        dim_col (Tensor.tensor_mat (A * C) (B * D))"
    using rc rd by simp
  
  fix i j
  assume ij_bounds:
    "i < dim_row (Tensor.tensor_mat (A * C) (B * D))"
    "j < dim_col (Tensor.tensor_mat (A * C) (B * D))"

  then have ij: "i < ?ra * ?rb" "j < ?cc * ?cd"
    using rc rd by simp_all

  show "(Tensor.tensor_mat A B * Tensor.tensor_mat C D) $$ (i, j) =
        Tensor.tensor_mat (A * C) (B * D) $$ (i, j)"
  proof (cases "?cb = 0")
    case True
    then have rd0: "?rd = 0" using rd by simp

    have lhs_zero:
      "(Tensor.tensor_mat A B * Tensor.tensor_mat C D) $$ (i, j) = 0"
    proof -
      have "dim_col (Tensor.tensor_mat A B) = ?ca * ?cb"
        by simp
      then have "dim_col (Tensor.tensor_mat A B) = 0"
        using True by simp
      then show ?thesis
        using ij by (simp add: rc Matrix.col_def rd0)
    qed

    have rhs_zero:
      "Tensor.tensor_mat (A * C) (B * D) $$ (i, j) = 0"
    proof -
      have bd_zero:
        "\<And>r c. r < ?rb \<Longrightarrow> c < ?cd \<Longrightarrow> (B * D) $$ (r, c) = 0"
      proof -
        fix r c assume "r < ?rb" "c < ?cd"
        then have "(B * D) $$ (r, c) =
                   (\<Sum>k=0..<?cb. B $$ (r,k) * D $$ (k,c))"
          using rd by (auto simp: scalar_prod_def atLeast0LessThan)
        also have "\<dots> = 0" using True by simp
        finally show "(B * D) $$ (r, c) = 0" .
      qed
      show ?thesis
        by (metis (mono_tags, lifting) bd_zero ij(1,2) index_mult_mat(2,3)  
            index_tensor_mat mod_less_divisor mult_eq_0_iff not_gr0 not_less_zero)
    qed
    from lhs_zero rhs_zero show ?thesis by simp
  next
    assume "dim_col B \<noteq> 0"
    then have cb_pos: "0 < ?cb" by simp
    show ?thesis
    proof (cases "?rb = 0")
      show "dim_row B = 0 \<Longrightarrow> ((A \<Otimes> B) * (C \<Otimes> D)) $$ (i, j) = (A * C \<Otimes> B * D) $$ (i, j)"
        using ij(1) by presburger
    next
      assume "dim_row B \<noteq> 0"
      then have rb_pos: "0 < ?rb" by simp

      show ?thesis
      proof (cases "?cd = 0")
        show "dim_col D = 0 \<Longrightarrow> ((A \<Otimes> B) * (C \<Otimes> D)) $$ (i, j) = (A * C \<Otimes> B * D) $$ (i, j)"
          using ij(2) by auto
      next
        assume  cd_nonzero: "dim_col D \<noteq> 0"
        then have cd_pos: "0 < ?cd" by simp

        have div_i: "i div ?rb < ?ra"
          using ij rb_pos by (simp add: less_mult_imp_div_less)
        have mod_i: "i mod ?rb < ?rb"
          using rb_pos by simp
        have div_j: "j div ?cd < ?cc"
          using ij cd_pos by (simp add: less_mult_imp_div_less)
        have mod_j: "j mod ?cd < ?cd"
          using cd_pos by simp

        have lhs_sum:
          "(Tensor.tensor_mat A B * Tensor.tensor_mat C D) $$ (i,j) =
           (\<Sum>k=0..<?ca*?cb.
              Tensor.tensor_mat A B $$ (i, k) *
              Tensor.tensor_mat C D $$ (k, j))"
          using ij rc rd
          by (auto simp: scalar_prod_def atLeast0LessThan)

        have lhs_expand:
          "(Tensor.tensor_mat A B * Tensor.tensor_mat C D) $$ (i,j)
           = (A * C) $$ (i div ?rb, j div ?cd) *
             (B * D) $$ (i mod ?rb, j mod ?cd)"
          by (smt (verit, del_insts) Matrix.col_def assms(1) bot_nat_0.not_eq_extremum cb_pos 
              cd_pos dimBD dim_col_tensor_mat dim_row_tensor_mat div_i
              div_j ij(1,2) index_mult_mat(1,2,3) index_tensor_mat lambda_zero 
              mult_distr_tensor not_less_zero sprod_vec_0)
          have rhs_expand:
          "Tensor.tensor_mat (A * C) (B * D) $$ (i, j)
           = (A * C) $$ (i div ?rb, j div ?cd) *
             (B * D) $$ (i mod ?rb, j mod ?cd)"
            using cd_pos div_j ij(1,2) by fastforce
            from lhs_expand rhs_expand show ?thesis
          by simp
      qed
    qed
  qed
qed


subsection \<open> Corollaries of the Mixed-Product Property \<close>

lemma tensor_adjoint_mult:
  "(Tensor.tensor_mat (A\<^sup>\<dagger>) (B\<^sup>\<dagger>)) * (Tensor.tensor_mat A B) =
   Tensor.tensor_mat ((A\<^sup>\<dagger>) * A) ((B\<^sup>\<dagger>) * B)"
  by (rule tensor_mat_mult, simp_all add: dagger_def)

lemma tensor_mult_adjoint:
  "(Tensor.tensor_mat A B) * (Tensor.tensor_mat (A\<^sup>\<dagger>) (B\<^sup>\<dagger>)) =
   Tensor.tensor_mat (A * (A\<^sup>\<dagger>)) (B * (B\<^sup>\<dagger>))"
  by (rule tensor_mat_mult, simp_all add: dagger_def)


subsection \<open> Tensor Unitarity \<close>

lemma tensor_mat_unitary_carrier:
  assumes dimA: "A \<in> carrier_mat n n"
      and dimB: "B \<in> carrier_mat m m"
      and uA:   "unitary A"
      and uB:   "unitary B"
  shows "unitary (Tensor.tensor_mat A B)"
proof -
  have dA: "dim_row A = n" "dim_col A = n"
    using dimA by auto
  have dB: "dim_row B = m" "dim_col B = m"
    using dimB by auto

  have invA_l: "((A\<^sup>\<dagger>) * A) = 1\<^sub>m n"
    using uA dimA unfolding unitary_def by auto
  have invA_r: "(A * (A\<^sup>\<dagger>)) = 1\<^sub>m n"
    using uA dimA unfolding unitary_def by auto
  have invB_l: "((B\<^sup>\<dagger>) * B) = 1\<^sub>m m"
    using uB dimB unfolding unitary_def by auto
  have invB_r: "(B * (B\<^sup>\<dagger>)) = 1\<^sub>m m"
    using uB dimB unfolding unitary_def by auto

  have lhs:
    "(((Tensor.tensor_mat A B)\<^sup>\<dagger>) * (Tensor.tensor_mat A B))
      = 1\<^sub>m (n * m)"
  proof -
    have "((Tensor.tensor_mat A B)\<^sup>\<dagger>) * (Tensor.tensor_mat A B)
        = (Tensor.tensor_mat (A\<^sup>\<dagger>) (B\<^sup>\<dagger>))
          * (Tensor.tensor_mat A B)"
      by (simp add: tensor_mat_adjoint)
    also have "\<dots> =
         Tensor.tensor_mat ((A\<^sup>\<dagger>) * A) ((B\<^sup>\<dagger>) * B)"
      by (rule tensor_adjoint_mult)
    also have "\<dots> =
         Tensor.tensor_mat (1\<^sub>m n) (1\<^sub>m m)"
      using invA_l invB_l by simp
    also have "\<dots> = 1\<^sub>m (n * m)"
      by (rule tensor_mat_id)
    finally show ?thesis .
  qed

  have rhs:
    "((Tensor.tensor_mat A B)
       * ((Tensor.tensor_mat A B)\<^sup>\<dagger>))
      = 1\<^sub>m (n * m)"
  proof -
    have "(Tensor.tensor_mat A B)
          * ((Tensor.tensor_mat A B)\<^sup>\<dagger>)
        = (Tensor.tensor_mat A B)
          * (Tensor.tensor_mat (A\<^sup>\<dagger>) (B\<^sup>\<dagger>))"
      by (simp add: tensor_mat_adjoint)
    also have "\<dots> =
         Tensor.tensor_mat (A * (A\<^sup>\<dagger>))
                           (B * (B\<^sup>\<dagger>))"
      by (rule tensor_mult_adjoint)
    also have "\<dots> =
         Tensor.tensor_mat (1\<^sub>m n) (1\<^sub>m m)"
      using invA_r invB_r by simp
    also have "\<dots> = 1\<^sub>m (n * m)"
      by (rule tensor_mat_id)
    finally show ?thesis .
  qed

  show "unitary (Tensor.tensor_mat A B)"
    unfolding unitary_def
    using lhs rhs dA dB by auto
qed

lemma tensor_mat_unitary:
  assumes uA: "unitary A"
      and uB: "unitary B"
  shows "unitary (Tensor.tensor_mat A B)"
  using tensor_mat_unitary_carrier uA uB unitary_carrier_square_row by blast

lemma tensor_mat_unitary_one_left [simp]:
  assumes uA: "unitary A"
  shows "unitary (Tensor.tensor_mat (1\<^sub>m n) A)"
  using id_is_unitary tensor_mat_unitary uA by blast

lemma tensor_mat_unitary_one_right [simp]:
  assumes uA: "unitary A"
  shows "unitary (Tensor.tensor_mat A (1\<^sub>m n))"
  using id_is_unitary tensor_mat_unitary uA by blast

end

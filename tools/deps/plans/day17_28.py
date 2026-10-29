"""Audit tick 39 (2026-10-28): the one-line metis/smt glue of Days 17, 24 and 28.  Associativity
steps become instances of assoc_mult_mat, Tr_add is applied backwards, the two index-equation
sites take the new bundle lemma mult_index_eq_iff, Day 28's hermitian_tensor_mat reads the
entries through hermitian_index.  `python3 day17_28.py --scratch` writes wip/d23/D28b.thy
(primed copies of every touched lemma, with the replacements applied) for tools/chk.sh;
without the flag it installs."""
import os, re, sys
sys.path.insert(0, os.path.dirname(__file__))
from planlib import *

BUNDLE = r'''lemma mult_index_eq_iff:
  fixes i j k l m :: nat
  assumes "k < m" and "l < m"
  shows "i * m + k = j * m + l \<longleftrightarrow> i = j \<and> k = l"
proof
  assume "i * m + k = j * m + l"
  hence "(i * m + k) div m = (j * m + l) div m" "(i * m + k) mod m = (j * m + l) mod m" by simp_all
  thus "i = j \<and> k = l"
    unfolding mult_index_div_mod[OF assms(1)] mult_index_div_mod[OF assms(2)] by simp
qed simp'''

HTM = r'''lemma hermitian_tensor_mat:
  fixes P Q :: "complex Matrix.mat"
  assumes Pcar: "P \<in> carrier_mat m m" and Qcar: "Q \<in> carrier_mat p p"
      and m_pos: "0 < m" and p_pos: "0 < p"
      and Pherm: "hermitian P" and Qherm: "hermitian Q"
  shows "hermitian (P \<Otimes> Q)"
proof -
  have T: "\<And>a b. a < m * p \<Longrightarrow> b < m * p \<Longrightarrow>
             (P \<Otimes> Q) $$ (a, b) = P $$ (a div p, b div p) * Q $$ (a mod p, b mod p)"
    using index_tensor_mat[OF carrier_matD[OF Pcar] carrier_matD[OF Qcar] _ _ m_pos p_pos] .
  have "(P \<Otimes> Q)\<^sup>\<dagger> = P \<Otimes> Q"
  proof (rule eq_matI)
    fix i j assume "i < dim_row (P \<Otimes> Q)" "j < dim_col (P \<Otimes> Q)"
    hence ij: "i < m * p" "j < m * p" using Pcar Qcar by simp_all
    hence d: "i div p < m" "j div p < m" by (auto intro: less_mult_imp_div_less)
    have e: "i mod p < p" "j mod p < p" using p_pos by simp_all
    show "(P \<Otimes> Q)\<^sup>\<dagger> $$ (i, j) = (P \<Otimes> Q) $$ (i, j)"
      using ij Pcar Qcar
      by (simp add: dagger_def T hermitian_index[OF Pherm, of "j div p" "i div p"]
                    hermitian_index[OF Qherm, of "j mod p" "i mod p"] d e)
  qed (use Pcar Qcar in simp_all)
  thus ?thesis by (simp add: hermitian_def)
qed'''

REPS = {
 "Day17_Quantum_Noise.thy": [
  (r'''  have term_eq: "M * \<rho> * (M\<^sup>\<dagger>) = (M * Q) * ((M * Q)\<^sup>\<dagger>)"
  proof -
    have dagprod: "((M * Q)\<^sup>\<dagger>) = (Q\<^sup>\<dagger>) * (M\<^sup>\<dagger>)"
      using M_c Qc by (simp add: dagger_of_prod)
    have dagprod': "((M * Q)\<^sup>\<dagger>) = Q * (M\<^sup>\<dagger>)"
      using dagprod Qdag by simp
    have a1: "(M * Q) * ((M * Q)\<^sup>\<dagger>) = (M * Q) * (Q * (M\<^sup>\<dagger>))"
      using dagprod' by simp
    have a2: "(M * Q) * (Q * (M\<^sup>\<dagger>)) = M * Q * Q * (M\<^sup>\<dagger>)"
      using M_c Qc Mdag_c
      by (metis assoc_mult_mat mult_carrier_mat)
    have a3: "M * Q * Q * (M\<^sup>\<dagger>) = M * (Q * Q) * (M\<^sup>\<dagger>)"
      using M_c Qc by (metis assoc_mult_mat)
    have a4: "M * (Q * Q) * (M\<^sup>\<dagger>) = M * \<rho> * (M\<^sup>\<dagger>)" using QQ by simp
    show ?thesis using a1 a2 a3 a4 by simp
  qed''',
   r'''  have term_eq: "M * \<rho> * (M\<^sup>\<dagger>) = (M * Q) * ((M * Q)\<^sup>\<dagger>)"
  proof -
    have "((M * Q)\<^sup>\<dagger>) = Q * (M\<^sup>\<dagger>)" using M_c Qc Qdag by (simp add: dagger_of_prod)
    then show ?thesis unfolding QQ[symmetric]
      by (simp add: assoc_mult_mat[OF M_c mult_carrier_mat[OF Qc Qc] Mdag_c] assoc_mult_mat[OF Qc Qc Mdag_c]
                    assoc_mult_mat[OF M_c Qc mult_carrier_mat[OF Qc Mdag_c]])
  qed'''),
  (r'''      using Mdag_c M_c \<rho>_c by (metis assoc_mult_mat)''',
   r'''      by (simp only: assoc_mult_mat[OF Mdag_c M_c \<rho>_c])'''),
  (r'''  case Nil
  have "kraus_map_dim d [] \<rho> = 0\<^sub>m d d" by simp
  hence lhs: "Tr (kraus_map_dim d [] \<rho>) = 0" by simp
  have "sum_wdag_w n [] * \<rho> = 0\<^sub>m n n * \<rho>" by simp
  also have "\<dots> = 0\<^sub>m n n"
    using X_c by (metis left_mult_zero_mat)
  finally have "Tr (sum_wdag_w n [] * \<rho>) = 0" by simp
  thus ?case using lhs by simp''',
   r'''  case Nil
  show ?case by (simp add: left_mult_zero_mat[OF X_c])'''),
  (r'''    using WdWX_c sum_X_c
    by (metis Tr_add carrier_matD(1) carrier_matD(2))''',
   r'''    by (intro Tr_add[symmetric]) (simp_all only: carrier_matD[OF WdWX_c] carrier_matD[OF sum_X_c])'''),
  (r'''      also have "\<dots> = (if c = d \<and> k = l then 1 else 0)"
      proof -
        have "c * p + k = d * p + l \<longleftrightarrow> c = d \<and> k = l"
          using mult_index_div_mod[OF k] mult_index_div_mod[OF l] by metis
        thus ?thesis unfolding UU using mult_index_lt[OF c k] mult_index_lt[OF d l] by simp
      qed''',
   r'''      also have "\<dots> = (if c = d \<and> k = l then 1 else 0)"
        unfolding UU using mult_index_lt[OF c k] mult_index_lt[OF d l] by (simp add: mult_index_eq_iff[OF k l])''')],
 "Day24_Operator_Systems.thy": [
  (r'''  have "a * n + r = b * n + c \<longleftrightarrow> a = b \<and> r = c"
    using mult_index_div_mod[OF r] mult_index_div_mod[OF c] by metis
  thus "block_of_mat n (1\<^sub>m (p * n)) a b $$ (r,c) = (if a = b then 1\<^sub>m n else 0\<^sub>m n n :: complex Matrix.mat) $$ (r,c)"
    using i r c by (simp add: block_of_mat_index)''',
   r'''  show "block_of_mat n (1\<^sub>m (p * n)) a b $$ (r,c) = (if a = b then 1\<^sub>m n else 0\<^sub>m n n :: complex Matrix.mat) $$ (r,c)"
    using i r c by (simp add: block_of_mat_index mult_index_eq_iff[OF r c])''')],
 "Day28_Entanglement_Witnesses.thy": [
  (r'''  by (metis real_vector.scale_zero_left tensor_lmat_scaleR_left)''',
   r'''  using tensor_lmat_scaleR_left[where a = 0 and \<sigma> = "0 :: (complex, 'm, 'm) lmat" and \<tau> = \<tau>] by simp'''),
  (r'''  by (metis real_vector.scale_zero_left tensor_lmat_scaleR_right)''',
   r'''  using tensor_lmat_scaleR_right[where a = 0 and \<sigma> = \<sigma> and \<tau> = "0 :: (complex, 'p, 'p) lmat"] by simp'''),
  (r'''    using c_eq by (metis Re_complex_of_real one_complex.simps(1))''',
   r'''    using c_eq by simp'''),
  (r'''      hence re: "0 \<le> Re (f (Tensor.tensor_mat Q P))" using Wsep unfolding f_def by (metis unwrap_lm_tensor_lmat us ut)''',
   r'''      hence "0 \<le> Re (Tr (W * unwrap_lm (tensor_lmat \<sigma> \<tau>)))" by (rule Wsep[rule_format])
      hence re: "0 \<le> Re (f (Tensor.tensor_mat Q P))" unfolding f_def by (simp add: us ut)''')]}

AFFECTED = {"Day17_Quantum_Noise.thy": ["meas_map_psd", "meas_map_trace_aux", "Tr_kraus_map_dim_as_wdagw", "environment_model"],
            "Day24_Operator_Systems.thy": ["block_of_mat_one"],
            "Day28_Entanglement_Witnesses.thy": ["tensor_lmat_zero_left", "tensor_lmat_zero_right", "hermitian_tensor_mat",
                                                 "separable_density_iff_in_convex_hull_Sprime", "separable_iff_positive_maps"]}

def prime(t): return re.sub(r"^(lemma|theorem|corollary) (\S+?):", r"\1 \2':", t, count=1)

if "--scratch" in sys.argv:
    out = ["theory D28b", "  imports Quantum_Computing_by_VP.Day17_Quantum_Noise Quantum_Computing_by_VP.Day24_Operator_Systems",
           "    Quantum_Computing_by_VP.Day28_Entanglement_Witnesses", "begin", "", prime(BUNDLE), ""]
    used = {old: 0 for reps in REPS.values() for old, _ in reps}
    for f, names in AFFECTED.items():
        blocks = {b["name"]: "\n".join(b["lines"]).rstrip("\n") for b in B.split(head(f)) if b["name"]}
        for n in names:
            t = HTM if n == "hermitian_tensor_mat" else blocks[n]
            for old, new in REPS[f]:
                if old in t:
                    assert t.count(old) == 1, (f, n); t = t.replace(old, new); used[old] += 1
            out += [prime(t).replace("mult_index_eq_iff", "mult_index_eq_iff'"), ""]
    assert all(v == 1 for v in used.values()), used
    out.append("end\n")
    open(os.path.join(P, "wip/d23/D28b.thy"), "w").write("\n".join(out)); print("scratch written")
else:
    edit("Matrix_Analysis_Prerequisites/Unitary_Tensor_Algebra.thy", insert_after=[("mult_index_div_mod", [BUNDLE])])
    edit("Day17_Quantum_Noise.thy", replace=REPS["Day17_Quantum_Noise.thy"])
    edit("Day24_Operator_Systems.thy", replace=REPS["Day24_Operator_Systems.thy"])
    edit("Day28_Entanglement_Witnesses.thy", remove=["hermitian_tensor_mat"], insert_after=[("hermitian_tensor_mat", [HTM])],
         replace=REPS["Day28_Entanglement_Witnesses.thy"])
    print("installed")

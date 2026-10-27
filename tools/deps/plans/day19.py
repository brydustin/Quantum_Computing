"""Audit tick 4 (2026-10-27): Day 19's Choi theorem from the pieces that already exist (the Choi
matrix is the block matrix (Phi(E_ij)), a linear map is its values on matrix units, a positive
matrix is a sum of rank ones), instead of 800 lines of entrywise bookkeeping.
  day19.py scratch   writes wip/d23/D19.thy (theory D19 on Day18) for the scratch session;
  day19.py           installs: Day19, and the helpers in Matrix_Lemmas, Day 17, 20, 22, 23."""
import os, sys
sys.path.insert(0, os.path.dirname(__file__))
from planlib import *

SCRATCH = len(sys.argv) > 1 and sys.argv[1] == "scratch"
H = B.split(head("Day19_Choi_Theorem.thy"))
def blk(key):
    if isinstance(key, int): return "\n".join(H[key]["lines"]).rstrip("\n")
    k = [b for b in H if b["name"] == key]; assert len(k) == 1, key
    return "\n".join(k[0]["lines"]).rstrip("\n")
def hd(kind, t): return f"{kind} \\<open>{t}\\<close>"

# ---- general helpers (Matrix_Lemmas, Day 17) ------------------------------------------------
ML_NEW = [txt(r"Sums of matrices over a list: congruence, additivity, scalars, concatenation."), r"""lemma msum_cong: "(\<And>x. x \<in> set xs \<Longrightarrow> g x = h x) \<Longrightarrow> msum r c g xs = msum r c h xs"
  by (induction xs) auto""", r"""lemma msum_add:
  assumes g: "\<forall>x \<in> set xs. g x \<in> carrier_mat r c" and h: "\<forall>x \<in> set xs. h x \<in> carrier_mat r c"
  shows "msum r c (\<lambda>x. g x + h x) xs = msum r c g xs + msum r c h xs"
proof (rule eq_matI)
  fix i j assume "i < dim_row (msum r c g xs + msum r c h xs)" "j < dim_col (msum r c g xs + msum r c h xs)"
  hence i: "i < r" and j: "j < c" by auto
  have gh: "\<forall>x \<in> set xs. g x + h x \<in> carrier_mat r c" using h by (auto intro: add_carrier_mat)
  have e: "(g x + h x) $$ (i, j) = g x $$ (i, j) + h x $$ (i, j)" if "x \<in> set xs" for x
    using h that i j by auto
  show "msum r c (\<lambda>x. g x + h x) xs $$ (i, j) = (msum r c g xs + msum r c h xs) $$ (i, j)"
    using i j by (simp add: msum_index[OF gh i j] msum_index[OF g i j] msum_index[OF h i j] sum_list_addf e cong: map_cong)
qed auto""", r"""lemma msum_smult:
  assumes g: "\<forall>x \<in> set xs. g x \<in> carrier_mat r c"
  shows "msum r c (\<lambda>x. a \<cdot>\<^sub>m g x) xs = a \<cdot>\<^sub>m msum r c g xs"
proof (rule eq_matI)
  fix i j assume "i < dim_row (a \<cdot>\<^sub>m msum r c g xs)" "j < dim_col (a \<cdot>\<^sub>m msum r c g xs)"
  hence i: "i < r" and j: "j < c" by auto
  have ag: "\<forall>x \<in> set xs. a \<cdot>\<^sub>m g x \<in> carrier_mat r c" using g by auto
  have e: "(a \<cdot>\<^sub>m g x) $$ (i, j) = a * g x $$ (i, j)" if "x \<in> set xs" for x using g that i j by auto
  show "msum r c (\<lambda>x. a \<cdot>\<^sub>m g x) xs $$ (i, j) = (a \<cdot>\<^sub>m msum r c g xs) $$ (i, j)"
    using i j by (simp add: msum_index[OF ag i j] msum_index[OF g i j] sum_list_const_mult e cong: map_cong)
qed auto""", r"""lemma msum_append:
  assumes g: "\<forall>x \<in> set xs. g x \<in> carrier_mat r c" and g': "\<forall>x \<in> set ys. g x \<in> carrier_mat r c"
  shows "msum r c g (xs @ ys) = msum r c g xs + msum r c g ys"
proof (rule eq_matI)
  fix i j assume "i < dim_row (msum r c g xs + msum r c g ys)" "j < dim_col (msum r c g xs + msum r c g ys)"
  hence i: "i < r" and j: "j < c" by auto
  have ga: "\<forall>x \<in> set (xs @ ys). g x \<in> carrier_mat r c" using g g' by auto
  show "msum r c g (xs @ ys) $$ (i, j) = (msum r c g xs + msum r c g ys) $$ (i, j)"
    using i j by (simp add: msum_index[OF ga i j] msum_index[OF g i j] msum_index[OF g' i j])
qed auto"""]
D17_NEW_K = [r'''lemma kraus_map_dim_msum: "kraus_map_dim d Ws \<rho> = msum d d (\<lambda>W. W * \<rho> * (W\<^sup>\<dagger>)) Ws"
  by (simp add: kraus_map_dim_def msum_def)''']
D17_NEW_S = [r'''lemma sum_wdag_w_msum: "sum_wdag_w n Ws = msum n n (\<lambda>W. (W\<^sup>\<dagger>) * W) Ws"
  by (simp add: sum_wdag_w_def msum_def)''']
D17_APPEND = r'''lemma kraus_map_dim_append:
  fixes Ws Vs :: "complex Matrix.mat list"
  assumes Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
      and Vs_c: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
      and \<rho>_c: "\<rho> \<in> carrier_mat n n"
  shows "kraus_map_dim d (Ws @ Vs) \<rho>
         = kraus_map_dim d Ws \<rho> + kraus_map_dim d Vs \<rho>"
  unfolding kraus_map_dim_msum
  by (rule msum_append) (use Ws_c Vs_c \<rho>_c in \<open>auto intro!: mult_carrier_mat dagger_carrier\<close>)'''

# ---- Day 19: the new proofs ------------------------------------------------------------------
MAP_EQ = r'''lemma map_eq_from_choi_when_linear:
  assumes L: "lin_on n d (carrier_mat n n) Phi" and L': "lin_on n d (carrier_mat n n) Psi"
      and choi_eq: "choi_matrix n d Phi = choi_matrix n d Psi" and A: "A \<in> carrier_mat n n"
  shows "Phi A = Psi A"
proof -
  have "Phi (E\<lbrakk>i,j ; n,n\<rbrakk>) = Psi (E\<lbrakk>i,j ; n,n\<rbrakk>)" if "i < n" "j < n" for i j
    using choi_block[OF _ that, of Phi d] choi_block[OF _ that, of Psi d] L L' choi_eq
    unfolding lin_on_def by simp
  thus ?thesis unfolding lin_expansion[OF L A] lin_expansion[OF L' A] by (intro msum_cong) auto
qed'''
SEED_BLOCK = r'''lemma choi_seed_block:
  assumes a: "a < n" and b: "b < n"
  shows "block_of_mat n (choi_seed n) a b = mat_unit a b n n"
  using unit_blocks_block[OF a b, of id] a b by (simp add: choi_seed_unit_blocks)'''
AS_AMP = r'''lemma choi_matrix_as_amplification:
  assumes npos: "n > 0"
      and dpos: "d > 0"
  shows "choi_matrix n d \<Phi> = amplification n d n \<Phi> (choi_seed n)"
proof (rule eq_matI)
  fix i j assume "i < dim_row (amplification n d n \<Phi> (choi_seed n))" "j < dim_col (amplification n d n \<Phi> (choi_seed n))"
  hence "i < n*d" "j < n*d" by simp_all
  hence "i div d < n" "j div d < n" by (simp_all add: less_mult_imp_div_less)
  thus "choi_matrix n d \<Phi> $$ (i, j) = amplification n d n \<Phi> (choi_seed n) $$ (i, j)"
    using \<open>i < n*d\<close> \<open>j < n*d\<close> by (simp add: choi_matrix_def amplification_index choi_seed_block)
qed (simp_all add: choi_matrix_def)'''
PSD_IF_CP = r'''lemma choi_psd_if_cp:
  assumes npos: "n > 0"
      and dpos: "d > 0"
      and cp: "completely_positive n d \<Phi>"
  shows "psd (choi_matrix n d \<Phi>)"
  using cp npos by (simp add: completely_positive_def choi_psd_if_n_positive[OF npos dpos])'''
KM_ADD = r'''lemma kraus_map_dim_add:
  assumes A_c: "A \<in> carrier_mat n n" and B_c: "B \<in> carrier_mat n n"
      and Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
  shows "kraus_map_dim d Ws (A + B) =
         kraus_map_dim d Ws A + kraus_map_dim d Ws B"
proof -
  have "W * (A + B) * (W\<^sup>\<dagger>) = W * A * (W\<^sup>\<dagger>) + W * B * (W\<^sup>\<dagger>)" if "W \<in> set Ws" for W
  proof -
    have W: "W \<in> carrier_mat d n" using Ws_c that by blast
    show ?thesis
      by (simp add: mult_add_distrib_mat[OF W A_c B_c]
                    add_mult_distrib_mat[OF mult_carrier_mat[OF W A_c] mult_carrier_mat[OF W B_c] dagger_carrier[OF W]])
  qed
  thus ?thesis unfolding kraus_map_dim_msum
    by (subst msum_add[symmetric]) (use Ws_c A_c B_c in \<open>auto intro!: msum_cong mult_carrier_mat dagger_carrier\<close>)
qed'''
KM_SMULT = r'''lemma kraus_map_dim_smult:
  assumes A_c: "A \<in> carrier_mat n n"
      and Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
  shows "kraus_map_dim d Ws (c \<cdot>\<^sub>m A) = c \<cdot>\<^sub>m kraus_map_dim d Ws A"
proof -
  have "W * (c \<cdot>\<^sub>m A) * (W\<^sup>\<dagger>) = c \<cdot>\<^sub>m (W * A * (W\<^sup>\<dagger>))" if "W \<in> set Ws" for W
  proof -
    have W: "W \<in> carrier_mat d n" using Ws_c that by blast
    show ?thesis
      by (simp add: mult_smult_distrib[OF W A_c] mult_smult_assoc_mat[OF mult_carrier_mat[OF W A_c] dagger_carrier[OF W]])
  qed
  thus ?thesis unfolding kraus_map_dim_msum
    by (subst msum_smult[symmetric]) (use Ws_c A_c in \<open>auto intro!: msum_cong mult_carrier_mat dagger_carrier\<close>)
qed'''
KM_ZERO = r'''lemma kraus_map_dim_zero [simp]:
  assumes Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
  shows "kraus_map_dim d Ws (0\<^sub>m n n) = 0\<^sub>m d d"
proof -
  have "W * 0\<^sub>m n n * (W\<^sup>\<dagger>) = 0\<^sub>m d d" if "W \<in> set Ws" for W
  proof -
    have W: "W \<in> carrier_mat d n" using Ws_c that by blast
    show ?thesis by (simp add: right_mult_zero_mat[OF W] left_mult_zero_mat[OF dagger_carrier[OF W]])
  qed
  thus ?thesis unfolding kraus_map_dim_msum
    by (subst msum_cong[of Ws _ "\<lambda>_. 0\<^sub>m d d"]) (simp_all add: msum_def foldr_add_mat_zero)
qed'''
SW_APPEND = r'''lemma sum_wdag_w_append:
  fixes Ws Vs :: "complex Matrix.mat list"
  assumes Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
      and Vs_c: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
  shows "sum_wdag_w n (Ws @ Vs)
         = sum_wdag_w n Ws + sum_wdag_w n Vs"
  unfolding sum_wdag_w_msum
  by (rule msum_append) (use Ws_c Vs_c in \<open>auto intro!: mult_carrier_mat dagger_carrier\<close>)'''
KRAUS_OF_VEC = [txt(r"Conversely a vector in $\C^{nd}$ folds into a $d\times n$ matrix."), r'''definition kraus_of_vec :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.vec \<Rightarrow> complex Matrix.mat" where
  "kraus_of_vec d n v = Matrix.mat d n (\<lambda>(i, a). v $ (a * d + i))"''', r'''lemma kraus_of_vec_carrier [simp]: "kraus_of_vec d n v \<in> carrier_mat d n"
  by (simp add: kraus_of_vec_def)''', r'''lemma vec_of_kraus_of_vec:
  assumes v: "dim_vec v = n * d" and d: "0 < d"
  shows "vec_of_kraus d n (kraus_of_vec d n v) = v"
proof (rule eq_vecI)
  fix r assume "r < dim_vec v"
  hence r: "r < n * d" using v by simp
  hence "r div d < n" "r mod d < d" using d by (simp_all add: less_mult_imp_div_less)
  thus "vec_of_kraus d n (kraus_of_vec d n v) $ r = v $ r"
    using r by (simp add: vec_of_kraus_index kraus_of_vec_def div_mult_mod_eq)
qed (use v in simp)''']
UNIT_ENTRY = r'''lemma kraus_map_dim_mat_unit_entry:
  assumes Vs_c: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
      and a_lt: "a < n" and b_lt: "b < n"
      and i_lt: "i < d" and j_lt: "j < d"
  shows "(kraus_map_dim d Vs (mat_unit a b n n)) $$ (i, j)
           = (\<Sum>k<length Vs. Vs!k $$ (i, a) * cnj (Vs!k $$ (j, b)))"
proof -
  have "(\<Sum>V\<leftarrow>Vs. (V * mat_unit a b n n * (V\<^sup>\<dagger>)) $$ (i, j)) = (\<Sum>V\<leftarrow>Vs. V $$ (i, a) * cnj (V $$ (j, b)))"
    by (rule arg_cong[where f = sum_list, OF map_cong[OF refl]])
       (use Vs_c in \<open>simp add: sandwich_mat_unit_entry[OF _ _ a_lt b_lt i_lt j_lt]\<close>)
  thus ?thesis
    by (simp add: kraus_map_dim_entry_sum_list[OF Vs_c mat_unit_carrier i_lt j_lt] sum_list_sum_nth atLeast0LessThan)
qed'''
CHOI_KRAUS = r'''lemma choi_matrix_kraus_eq:
  assumes Vs_c: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
      and npos: "0 < n" and dpos: "0 < d"
  shows "choi_matrix n d (kraus_map_dim d Vs)
           = outer_sum (n*d) (map (vec_of_kraus d n) Vs)"
proof (rule eq_matI)
  let ?M = "mat_of_cols (n*d) (map (vec_of_kraus d n) Vs)"
  fix r c assume "r < dim_row (outer_sum (n*d) (map (vec_of_kraus d n) Vs))"
    "c < dim_col (outer_sum (n*d) (map (vec_of_kraus d n) Vs))"
  hence r: "r < n*d" and c: "c < n*d" by simp_all
  have rd: "r div d < n" "r mod d < d" and cd: "c div d < n" "c mod d < d"
    using r c dpos by (simp_all add: less_mult_imp_div_less)
  have "choi_matrix n d (kraus_map_dim d Vs) $$ (r, c)
      = (\<Sum>k<length Vs. Vs!k $$ (r mod d, r div d) * cnj (Vs!k $$ (c mod d, c div d)))"
    using r c by (simp add: choi_matrix_def kraus_map_dim_mat_unit_entry[OF Vs_c rd(1) cd(1) rd(2) cd(2)])
  also have "\<dots> = (?M * (?M\<^sup>\<dagger>)) $$ (r, c)"
    using r c
    by (simp add: mat_mult_entry[OF mat_of_cols_carrier(1) dagger_carrier[OF mat_of_cols_carrier(1)] r c]
                  dagger_def mat_of_cols_index vec_of_kraus_index)
  finally show "choi_matrix n d (kraus_map_dim d Vs) $$ (r, c) = outer_sum (n*d) (map (vec_of_kraus d n) Vs) $$ (r, c)"
    by (simp add: outer_sum_def)
qed (simp_all add: choi_matrix_def outer_sum_def)'''
KRAUS_REP = r'''lemma kraus_rep_of_psd_choi:
  fixes \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes linear: "\<And>A B. A \<in> carrier_mat n n \<Longrightarrow> B \<in> carrier_mat n n \<Longrightarrow>
                   \<Phi> (A + B) = \<Phi> A + \<Phi> B"
      and smult:  "\<And>c A. A \<in> carrier_mat n n \<Longrightarrow> \<Phi> (c \<cdot>\<^sub>m A) = c \<cdot>\<^sub>m \<Phi> A"
      and range:  "\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A \<in> carrier_mat d d"
      and npos: "n > 0"
      and dpos: "d > 0"
      and psdP: "psd (choi_matrix n d \<Phi>)"
  shows "\<exists>Ws :: complex Matrix.mat list.
           length Ws = n * d \<and>
           (\<forall>W \<in> set Ws. W \<in> carrier_mat d n) \<and>
           (\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A = kraus_map_dim d Ws A)"
proof -
  have L: "lin_on n d (carrier_mat n n) \<Phi>" unfolding lin_on_def using linear smult range by auto
  obtain vs :: "complex Matrix.vec list" where len: "length vs = n * d"
    and dim: "\<forall>v \<in> set vs. dim_vec v = n * d" and P: "outer_sum (n * d) vs = choi_matrix n d \<Phi>"
    using psd_kraus_decomp[OF choi_matrix_carrier psdP] by blast
  define Ws where "Ws = map (kraus_of_vec d n) vs"
  have Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n" by (simp add: Ws_def)
  have "map (vec_of_kraus d n) Ws = vs"
    unfolding Ws_def map_map using dim dpos by (intro map_idI) (simp add: vec_of_kraus_of_vec)
  hence "choi_matrix n d (kraus_map_dim d Ws) = choi_matrix n d \<Phi>"
    by (simp add: choi_matrix_kraus_eq[OF Ws_c npos dpos] P)
  hence eq: "\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A = kraus_map_dim d Ws A"
    using map_eq_from_choi_when_linear[OF L kraus_lin_on[OF Ws_c]] by simp
  show ?thesis using len Ws_c eq by (intro exI[of _ Ws]) (simp add: Ws_def)
qed'''
CHOI_THM = r'''theorem choi_theorem:
  fixes \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes linear: "\<And>A B. A \<in> carrier_mat n n \<Longrightarrow> B \<in> carrier_mat n n \<Longrightarrow>
                   \<Phi> (A + B) = \<Phi> A + \<Phi> B"
      and smult:  "\<And>c A. A \<in> carrier_mat n n \<Longrightarrow> \<Phi> (c \<cdot>\<^sub>m A) = c \<cdot>\<^sub>m \<Phi> A"
      and range:  "\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A \<in> carrier_mat d d"
      and npos: "n > 0"
      and dpos: "d > 0"
  shows "completely_positive n d \<Phi> \<longleftrightarrow>
         psd (choi_matrix n d \<Phi>)"
proof
  assume "completely_positive n d \<Phi>"
  thus "psd (choi_matrix n d \<Phi>)" by (rule choi_psd_if_cp[OF npos dpos])
next
  assume "psd (choi_matrix n d \<Phi>)"
  then obtain Ws where Ws: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
    and eq: "\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A = kraus_map_dim d Ws A"
    using kraus_rep_of_psd_choi[OF linear smult range npos dpos] by blast
  thus "completely_positive n d \<Phi>"
    using kraus_cp_no_tp[OF Ws npos dpos] completely_positive_cong[of n \<Phi> "kraus_map_dim d Ws" d] by simp
qed'''
CHOI_CPTP = r'''theorem choi_kraus_cptp:
  fixes \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes linear: "\<And>A B. A \<in> carrier_mat n n \<Longrightarrow> B \<in> carrier_mat n n \<Longrightarrow>
                   \<Phi> (A + B) = \<Phi> A + \<Phi> B"
      and smult:  "\<And>c A. A \<in> carrier_mat n n \<Longrightarrow> \<Phi> (c \<cdot>\<^sub>m A) = c \<cdot>\<^sub>m \<Phi> A"
      and range:  "\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A \<in> carrier_mat d d"
      and npos: "n > 0"
      and dpos: "d > 0"
  shows "(completely_positive n d \<Phi> \<and> trace_preserving n \<Phi>) \<longleftrightarrow>
         (\<exists>Ws :: complex Matrix.mat list.
            kraus_operators n d Ws \<and>
            (\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi> X = kraus_map_dim d Ws X))"
proof
  assume "\<exists>Ws :: complex Matrix.mat list. kraus_operators n d Ws \<and>
            (\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi> X = kraus_map_dim d Ws X)"
  then obtain Ws where K: "kraus_operators n d Ws"
    and eq: "\<And>X. X \<in> carrier_mat n n \<Longrightarrow> \<Phi> X = kraus_map_dim d Ws X" by blast
  have "completely_positive n d \<Phi> = completely_positive n d (kraus_map_dim d Ws)"
    by (rule completely_positive_cong) (rule eq)
  thus "completely_positive n d \<Phi> \<and> trace_preserving n \<Phi>"
    using kraus_is_cp[OF K npos dpos] kraus_is_trace_preserving[OF K] by (simp add: trace_preserving_def eq)
next
  assume "completely_positive n d \<Phi> \<and> trace_preserving n \<Phi>"
  hence cp: "completely_positive n d \<Phi>" and tp: "trace_preserving n \<Phi>" by auto
  obtain Ws where Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
    and eq: "\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi> X = kraus_map_dim d Ws X"
    using kraus_rep_of_psd_choi[OF linear smult range npos dpos choi_psd_if_cp[OF npos dpos cp]] by blast
  have "sum_wdag_w n Ws = 1\<^sub>m n"
  proof (rule mat_trace_pairing_unique[OF sum_wdag_w_carrier[OF Ws_c] one_carrier_mat])
    fix \<rho> :: "complex Matrix.mat" assume \<rho>: "\<rho> \<in> carrier_mat n n"
    have "Tr (sum_wdag_w n Ws * \<rho>) = Tr (kraus_map_dim d Ws \<rho>)"
      by (rule Tr_kraus_map_dim_as_wdagw[OF Ws_c \<rho>, symmetric])
    also have "\<dots> = Tr \<rho>" using eq tp \<rho> by (simp add: trace_preserving_def)
    finally show "Tr (sum_wdag_w n Ws * \<rho>) = Tr (1\<^sub>m n * \<rho>)" using \<rho> by simp
  qed
  thus "\<exists>Ws :: complex Matrix.mat list. kraus_operators n d Ws \<and>
          (\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi> X = kraus_map_dim d Ws X)"
    using Ws_c eq by (auto simp: kraus_operators_altdef)
qed'''

INTRO = blk(3).replace(
 "The step (2)$\\Rightarrow$(3) is the observation that $P_\\Phi=\\Phi^{(n)}((E_{ij}))$ with\n$(E_{ij})\\ge0$ (\\<open>choi_matrix_as_amplification\\<close>).",
 "The step (2)$\\Rightarrow$(3) is the observation that $P_\\Phi=\\Phi^{(n)}((E_{ij}))$ with\n$(E_{ij})\\ge0$ (\\<open>choi_matrix_as_amplification\\<close>); (3)$\\Rightarrow$(4) is the notes' proof,\nthrough the vectorisation of Kraus operators (\\<open>choi_matrix_kraus_eq\\<close>: the Choi matrix of a\nKraus map is $\\sum_k v_kv_k^*$, $v_k=\\mathrm{vec}(V_k)$).")
assert INTRO != blk(3)

P19 = [blk(0), blk(1) if not SCRATCH else "theory D19\n  imports Quantum_Computing_by_VP.Day18_CP_Maps\nbegin", blk(2), INTRO]
if SCRATCH: P19 += ML_NEW + D17_NEW_K + D17_NEW_S + [D17_APPEND.replace("lemma kraus_map_dim_append:", "lemma kraus_map_dim_append':")]
P19 += [hd("subsection", "The Choi matrix"),
        txt(r"$P_\Phi\in M_n(M_d)$ is the block matrix with $(a,b)$ block $\Phi(E_{ab})$.  It is linear in $\Phi$."),
        blk("choi_matrix"), blk(5), blk("choi_matrix_carrier"), blk("choi_block"), blk("choi_matrix_cong"),
        blk("choi_matrix_smult"), blk("choi_matrix_lincomb")]
P19 += [hd("subsection", "A linear map is its values on the matrix units"),
        blk(95), blk("unit_expansion"), blk("id_expansion"), blk("lin_expansion"),
        txt(r"So two linear maps with the same Choi matrix agree on $M_n$."), MAP_EQ]
P19 += [hd("subsection", "The Choi matrix as an amplification"),
        blk(78), blk("unit_blocks"), blk("unit_blocks_block"), blk("unit_blocks_vec"), blk(82),
        blk("unit_blocks_outer"), blk("unit_blocks_psd"), blk("choi_seed_unit_blocks"), blk("choi_seed_psd"),
        SEED_BLOCK, blk(6), AS_AMP, blk("choi_psd_if_n_positive"), PSD_IF_CP]
P19 += [hd("subsection", "Kraus maps"),
        txt(r"A Kraus map is linear in its argument, completely positive, and trace preserving when its operators are Kraus operators."),
        KM_ADD, KM_SMULT, KM_ZERO, blk("kraus_lin_on"), blk(13), blk("kraus_cp_no_tp"), SW_APPEND,
        blk("kraus_is_trace_preserving"), blk(40), blk("kraus_map_dim_density_matrix")]
P19 += [blk(55), blk(56), blk("vec_of_kraus"), blk("vec_of_kraus_dim"), blk("vec_of_kraus_index"), blk(60),
        blk("vec_of_kraus_combined_index")] + KRAUS_OF_VEC
P19 += [blk(62), blk(63), UNIT_ENTRY, CHOI_KRAUS]
P19 += [hd("subsection", "Choi's theorem"), blk(12), KRAUS_REP, CHOI_THM,
        txt(r"The trace-preserving case: CPTP maps are exactly the Kraus maps of Kraus operators."), CHOI_CPTP,
        txt(r"Condition (2), $n$-positivity, isolated (D19-1)."), blk("choi_four_conditions")]
P19 += [blk(i) for i in range(42, 55)]                       # composition of Kraus maps
P19 += [blk(89), blk(90), blk("Tr_msum"), blk("Tr_msum_pairs")] + [blk(i) for i in range(99, 107)] + ["end"]
assert all(H[i]["kind"] == "notation" for i in (5,)), H[5]["kind"]

if SCRATCH:
    open(os.path.join(P, "wip/d23/D19.thy"), "w").write("\n\n".join(P19) + "\n")
    print("scratch written")
else:
    open(os.path.join(P, "Day19_Choi_Theorem.thy"), "w").write("\n\n".join(P19) + "\n")
    edit("Essential_Functional_Analysis/Matrix_Lemmas.thy", insert_after=[("msum_mult_left", ML_NEW)])
    edit("Day17_Quantum_Noise.thy", remove=["kraus_map_dim_append"],
         insert_after=[("kraus_map_dim_single", D17_NEW_K), ("sum_wdag_w_two", D17_NEW_S),
                       ("kraus_map_dim_entry_sum_list", [D17_APPEND])])
    edit("Day20_Positive_Functionals.thy",
         replace=[("        using Tr_mult_mat_unit[OF M_c jd id].", "        using Tr_mat_unit_mult[OF M_c id jd] ."),
                  (head("Day20_Positive_Functionals.thy")[head("Day20_Positive_Functionals.thy").index("proof -\n  have ps_valid:"):
                                                          head("Day20_Positive_Functionals.thy").index("theorem positive_scalar_is_cp:")],
                   r'''proof -
  have L: "lin_on n d (carrier_mat n n) \<phi>" unfolding lin_on_def using f_add f_smult f_car by auto
  show ?thesis
    unfolding lin_expansion[OF L M_c]
    by (subst msum_pairs_index)
       (use r_lt c_lt in \<open>auto intro!: sum.cong simp: f_car[OF mat_unit_carrier] carrier_matD[OF f_car[OF mat_unit_carrier]]\<close>)
qed

''')])
    edit("Day22_Minimal_Kraus.thy",
         replace=[(r'''    by (rule map_eq_from_choi_when_linear[OF _ _ _ _ _ _ choi npos dpos Xc])
       (auto intro: kraus_map_dim_add[OF _ _ Ws_c] kraus_map_dim_smult[OF _ Ws_c] kraus_map_dim_carrier[OF Ws_c]
                    kraus_map_dim_add[OF _ _ Vs_c] kraus_map_dim_smult[OF _ Vs_c] kraus_map_dim_carrier[OF Vs_c])''',
                   r'''    by (rule map_eq_from_choi_when_linear[OF kraus_lin_on[OF Ws_c] kraus_lin_on[OF Vs_c] choi Xc])''')])
    edit("Day23_Choi_Extreme_Points.thy",
         replace=[(r'''    by (rule map_eq_from_choi_when_linear[OF lin_on_choi_hyps(1,2)[OF L] _ lin_on_choi_hyps(1,2)[OF Lq] _ eqc n d X])
       (use L Lq in \<open>auto simp: lin_on_def\<close>)''',
                   r'''    by (rule map_eq_from_choi_when_linear[OF L Lq eqc X])''')])
    print("installed")

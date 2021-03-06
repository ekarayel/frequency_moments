section \<open>Frequency Moment $0$\<close>

theory Frequency_Moment_0
  imports Main Primes_Ext Float_Ext Median K_Smallest Universal_Hash_Families_Nat Encoding
  Frequency_Moments Landau_Ext
begin

text \<open>This section contains a formalization of the algorithm for the zero-th frequency moment.
It is a KMV-type ($k$-minimum value) algorithm with a rounding method to match the space complexity 
of the best algorithm described in \cite{baryossef2002}.\<close>

text \<open>In addition ot the Isabelle proof here, there is also an informal hand-writtend proof in
Appendix~\ref{sec:f0_proof}.\<close>

type_synonym f0_state = "nat \<times> nat \<times> nat \<times> nat \<times> (nat \<Rightarrow> (int set list)) \<times> (nat \<Rightarrow> float set)"

fun f0_init :: "rat \<Rightarrow> rat \<Rightarrow> nat \<Rightarrow> f0_state pmf" where
  "f0_init \<delta> \<epsilon> n =
    do {
      let s = nat \<lceil>-18 * ln (real_of_rat \<epsilon>)\<rceil>;
      let t = nat \<lceil>80 / (real_of_rat \<delta>)\<^sup>2\<rceil>;
      let p = find_prime_above (max n 19);
      let r = nat (4 * \<lceil>log 2 (1 / real_of_rat \<delta>)\<rceil> + 24); 
      h \<leftarrow> prod_pmf {0..<s} (\<lambda>_. pmf_of_set (bounded_degree_polynomials (ZFact (int p)) 2));
      return_pmf (s, t, p, r, h, (\<lambda>_ \<in> {0..<s}. {}))
    }"

fun f0_update :: "nat \<Rightarrow> f0_state \<Rightarrow> f0_state pmf" where
  "f0_update x (s, t, p, r, h, sketch) = 
    return_pmf (s, t, p, r, h, \<lambda>i \<in> {0..<s}.
      least t (insert (float_of (truncate_down r (hash p x (h i)))) (sketch i)))"

fun f0_result :: "f0_state \<Rightarrow> rat pmf" where
  "f0_result (s, t, p, r, h, sketch) = return_pmf (median s (\<lambda>i \<in> {0..<s}.
      (if card (sketch i) < t then of_nat (card (sketch i)) else
        rat_of_nat t* rat_of_nat p / rat_of_float  (Max (sketch i)))
    ))"

definition f0_sketch where 
  "f0_sketch p r t h xs = least t ((\<lambda>x. float_of (truncate_down r (hash p x h))) ` (set xs))"

lemma f0_alg_sketch:
  fixes n :: nat
  fixes as :: "nat list"
  assumes "\<epsilon> \<in> {0<..<1}"
  assumes "\<delta> \<in> {0<..<1}"
  defines "sketch \<equiv> fold (\<lambda>a state. state \<bind> f0_update a) as (f0_init \<delta> \<epsilon> n)"
  defines "t \<equiv> nat \<lceil>80 / (real_of_rat \<delta>)\<^sup>2\<rceil>"
  defines "s \<equiv> nat \<lceil>-(18 * ln (real_of_rat \<epsilon>))\<rceil>"
  defines "p \<equiv> find_prime_above (max n 19)"
  defines "r \<equiv> nat (4 * \<lceil>log 2 (1 / real_of_rat \<delta>)\<rceil> + 24)"
  shows "sketch = map_pmf (\<lambda>x. (s,t,p,r, x, \<lambda>i \<in> {0..<s}. f0_sketch p r t (x i) as))
    (prod_pmf {0..<s} (\<lambda>_. pmf_of_set (bounded_degree_polynomials (ZFact (int p)) 2)))" 
proof (subst sketch_def, induction as rule:rev_induct)
  case Nil
  then show ?case
    apply (simp add:s_def[symmetric] p_def[symmetric] map_pmf_def[symmetric] t_def[symmetric] r_def[symmetric])
    apply (rule arg_cong2[where f="map_pmf"])
     apply (rule ext)
     apply simp
    by (rule ext, simp add:f0_sketch_def least_def, simp)
next
  case (snoc x xs)
  then show ?case
    apply (simp add:map_pmf_def)
    apply (subst bind_assoc_pmf)
    apply (subst bind_return_pmf)
    apply (rule arg_cong2[where f="bind_pmf"], simp)
    apply (simp)
    apply (rule ext, rule arg_cong[where f="return_pmf"], simp)
    apply (rule ext)
    apply (simp add:f0_sketch_def)
    by (subst least_insert, simp, simp)
qed


lemma abs_ge_iff: "((x::real) \<le> abs y) = (x \<le> y \<or> x \<le> -y)"
  by linarith

lemma two_powr_0: "2 powr (0::real) = 1"
  by simp

lemma count_nat_abs_diff_2:
  fixes x :: nat
  fixes q :: real
  assumes "q \<ge> 0"
  defines "A \<equiv> {(k::nat). abs (real x - real k) \<le> q \<and> k \<noteq> x}"
  shows "real (card A) \<le> 2 * q" and "finite A"
proof -
  have a: "of_nat x \<in> {\<lceil>real x-q\<rceil>..\<lfloor>real x+q\<rfloor>}"
    using assms 
    by (simp add: ceiling_le_iff)
  
  have "card A = card (int ` A)"
    by (rule card_image[symmetric], simp)
  also have "... \<le> card ({\<lceil>real x-q\<rceil>..\<lfloor>real x+q\<rfloor>} - {of_nat x})"
    apply (rule card_mono, simp)
    apply (rule image_subsetI)
    apply (simp add:A_def abs_le_iff)
    by linarith
  also have "... = card {\<lceil>real x-q\<rceil>..\<lfloor>real x+q\<rfloor>} - 1"
    by (rule card_Diff_singleton, rule a)
  also have "... = int (card {\<lceil>real x-q\<rceil>..\<lfloor>real x+q\<rfloor>}) - int 1"
    apply (rule of_nat_diff)
    by (metis a card_0_eq empty_iff finite_atLeastAtMost_int less_one linorder_not_le)
  also have "... \<le> \<lfloor>q+real x\<rfloor>+1 -\<lceil>real x-q\<rceil> - 1"
    using assms
    apply simp
    by linarith
  also have "... \<le> 2*q"
    by linarith
  finally show "card A \<le> 2 * q"
    by simp
  show "finite A"
    apply (simp add:A_def)
    apply (rule finite_subset[where B="{0..x+nat \<lceil>q\<rceil>}"])
    apply (rule subsetI, simp add:abs_le_iff)
    using assms apply linarith by simp
qed

lemma f0_collision_prob:
  fixes p :: nat
  assumes "Factorial_Ring.prime p"
  defines "\<Omega> \<equiv> pmf_of_set (bounded_degree_polynomials (ZFact (int p)) 2)"
  assumes "M \<subseteq> {0..<p}"
  assumes "c \<ge> 1"
  assumes "r \<ge> 1"
  shows "\<P>(\<omega> in measure_pmf \<Omega>. 
    \<exists>x \<in> M. \<exists>y \<in> M.
    x \<noteq> y \<and>
    truncate_down r (hash p x \<omega>) \<le> c \<and>
    truncate_down r (hash p x \<omega>) = truncate_down r (hash p y \<omega>)) \<le> 
    6 * (real (card M))\<^sup>2 * c\<^sup>2 * 2 powr -r / (real p) \<^sup>2 + 1/real p" (is "\<P>(\<omega> in _. ?l \<omega>) \<le> ?r1 + ?r2")
proof -
  have p_ge_0: "p > 0"
    using assms prime_gt_0_nat by blast

  have c_ge_0: "c\<ge>0" using assms by simp
  
  have two_pow_r_le_1: "2 powr (-real r) \<le> 1" 
    by (subst two_powr_0[symmetric], rule powr_mono, simp, simp)

  have f_M: "finite M"
    by (rule finite_subset[where B="{0..<p}"], metis assms(3), simp)

  have a2: "\<And>\<omega> x. x < p \<Longrightarrow> \<omega> \<in> bounded_degree_polynomials (ZFact p) 2 \<Longrightarrow> hash p x \<omega> < p" 
    using hash_range[OF p_ge_0] by simp
  have "\<And>\<omega>. degree \<omega> \<ge> 1 \<Longrightarrow> \<omega> \<in> bounded_degree_polynomials (ZFact p) 2 \<Longrightarrow> degree \<omega> = 1"
    apply (simp add:bounded_degree_polynomials_def) 
    by (metis One_nat_def Suc_1 le_less_Suc_eq less_imp_diff_less list.size(3) pos2)
  hence a3: "\<And>\<omega> x y. x < p \<Longrightarrow> y < p \<Longrightarrow>  x \<noteq> y \<Longrightarrow> degree \<omega> \<ge> 1 \<Longrightarrow> 
    \<omega> \<in> bounded_degree_polynomials (ZFact p) 2 \<Longrightarrow> 
    hash p x \<omega> \<noteq> hash p y \<omega>" 
    using hash_inj_if_degree_1[OF assms(1)] 
    by (meson atLeastLessThan_iff inj_on_def less_nat_zero_code linorder_not_less)

  have a1: 
    "\<And>x y. x < y \<Longrightarrow> x \<in> M \<Longrightarrow> y \<in> M \<Longrightarrow> measure \<Omega> 
    {\<omega>. degree \<omega> \<ge> 1 \<and> truncate_down r (hash p x \<omega>) \<le> c \<and>
    truncate_down r (hash p x \<omega>) = truncate_down r (hash p y \<omega>)} \<le> 
    12 * c\<^sup>2 * 2 powr (-real r) /(real p)\<^sup>2"
  proof -
    fix x y
    assume a1_1: "x \<in> M"
    assume a1_2: "y \<in> M"
    assume a1_3: "x < y"

    have a1_4: "\<And>u v. truncate_down r (real u) \<le> c \<Longrightarrow> 
        truncate_down r (real u) = truncate_down r (real v) \<Longrightarrow>
        real u \<le> 2 * c \<and> \<bar>real u - real v\<bar> \<le> 2 * c * 2 powr (-real r)"
    proof -
      fix u v
      assume a_1:"truncate_down r (real u) \<le> c"
      assume a_2:"truncate_down r (real u) = truncate_down r (real v)"
      have a_3: "2 * 2 powr (- real r) = 2 powr (1 -real r)"
        by (simp add: divide_powr_uminus powr_diff)

      have a_4_1: "1 \<le> 2 * (1 - 2 powr (- real r))"
        apply (simp, subst a_3, subst (2) two_powr_0[symmetric])
        apply (rule powr_mono)
        using assms(5) by simp+

      have a_4: "(c*1) / (1 - 2 powr (-real r)) \<le> c * 2" 
        apply (subst pos_divide_le_eq, simp)
         apply (subst two_powr_0[symmetric])
         apply (rule powr_less_mono) using assms(5) apply simp
         apply simp
        using a_4_1 
        by (metis (no_types, opaque_lifting) c_ge_0 mult.left_commute mult.right_neutral mult_left_mono)

      have a_5: "\<And>x. truncate_down r (real x) \<le>  c  \<Longrightarrow> real x \<le> c * 2"
        apply (rule order_trans[OF _ a_4])
        apply (subst pos_le_divide_eq)
         apply (simp, subst two_powr_0[symmetric])
         apply (rule powr_less_mono) using assms(5) apply simp
        apply simp
        using  truncate_down_pos[OF of_nat_0_le_iff] order_trans apply simp by blast

      have a_6: "real u \<le> c * 2"
        using a_1 a_5 by simp
      have a_7: "real v \<le> c * 2" 
        using a_1 a_2 a_5 by simp
      have " \<bar>real u - real v\<bar> \<le> (max \<bar>real u\<bar> \<bar>real v\<bar>) * 2 powr (-real r)"
        apply (rule truncate_down_eq) using a_2 by simp 
      also have "... \<le> (c * 2) * 2 powr (-real r)"
        apply (rule mult_right_mono) using a_6 a_7 by simp+
      finally have a_8: "\<bar>real u - real v\<bar> \<le> 2 * c * 2 powr (-real r)"
        by simp

      show "real u \<le> 2* c \<and> \<bar>real u - real v\<bar> \<le> 2 * c * 2 powr (-real r)" 
        using a_6 a_8 by simp
    qed

    have "measure \<Omega> {\<omega>. degree \<omega> \<ge> 1 \<and> truncate_down r (hash p x \<omega>) \<le> c \<and>
      truncate_down r (hash p x \<omega>) = truncate_down r (hash p y \<omega>)} \<le>
      measure \<Omega> (\<Union> i \<in> {(u,v) \<in> {0..<p} \<times> {0..<p}. u \<noteq> v \<and>
      truncate_down r u \<le> c \<and> truncate_down r u = truncate_down r v}.
      {\<omega>.  hash p x \<omega> = fst i \<and> hash p y \<omega> = snd i})"
      apply (rule pmf_mono_1)
      apply (simp add: \<Omega>_def)
      apply (subst (asm) set_pmf_of_set)
        apply (rule ne_bounded_degree_polynomials)
      apply (rule fin_bounded_degree_polynomials[OF p_ge_0])
      by (metis assms(3) a2 a3 a1_1 a1_2 a1_3  One_nat_def less_not_refl3 atLeastLessThan_iff subset_eq)
    also have "... \<le> (\<Sum> i\<in> {(u,v) \<in> {0..<p} \<times> {0..<p}. u \<noteq> v \<and>
      truncate_down r u \<le> c \<and> truncate_down r u = truncate_down r v}. 
      measure \<Omega>  {\<omega>. hash p x \<omega> = fst i \<and> hash p y \<omega> = snd i})"
      apply (rule measure_UNION_le)
       apply (rule finite_subset[where B="{0..<p} \<times> {0..<p}"], rule subsetI, simp add:case_prod_beta mem_Times_iff, simp)
      by simp
    also have "... \<le> (\<Sum> i\<in> {(u,v) \<in> {0..<p} \<times> {0..<p}. u \<noteq> v \<and>
      truncate_down r u \<le> c \<and> truncate_down r u = truncate_down r v}. 
      \<P>(\<omega> in \<Omega>. (\<forall>u \<in> UNIV. hash p (if u then x else y) \<omega> = (if u then (fst i) else (snd i)))))" 
      apply (rule sum_mono)
      apply (rule pmf_mono_1)
      by (simp add:case_prod_beta)
    also have "... \<le> (\<Sum> i\<in> {(u,v) \<in> {0..<p} \<times> {0..<p}. u \<noteq> v \<and>
      truncate_down r u \<le> c \<and> truncate_down r u = truncate_down r v}. 1/(real p)\<^sup>2)"
      apply (rule sum_mono)
      apply (simp only:\<Omega>_def)
      apply (subst hash_prob_2[OF assms(1)])
          using a1_3 apply (simp add: inj_on_def)
         using a1_1 assms(3) a1_3 a1_2 apply auto[1]
         by force+
    also have "... = 1/(real p)\<^sup>2 * 
      card {(u,v) \<in> {0..<p} \<times> {0..<p}. u \<noteq> v \<and> truncate_down r u \<le> c \<and> truncate_down r u = truncate_down r v}"
      by simp
    also have "... \<le> 1/(real p)\<^sup>2 * 
      card {(u,v) \<in> {0..<p} \<times> {0..<p}. u \<noteq> v \<and> real u \<le> 2 * c \<and> abs (real u - real v) \<le> 2 * c * 2 powr (-real r)}"
      apply (rule mult_left_mono, rule of_nat_mono, rule card_mono)
        apply (rule finite_subset[where B="{0..<p}\<times>{0..<p}"], rule subsetI, simp add:mem_Times_iff case_prod_beta, simp)
       apply (rule subsetI, simp add:case_prod_beta)
      by (metis a1_4, simp)
    also have "... \<le> 1/(real p)\<^sup>2 * card (\<Union>u' \<in> {u. u < p \<and> real u \<le> 2 * c}.
        {(u::nat,v::nat). u = u' \<and> abs (real u - real v) \<le> 2 * c * 2 powr (-real r) \<and> v < p \<and> v \<noteq> u'})"
      apply (rule mult_left_mono)
       apply (rule of_nat_mono)
       apply (rule card_mono, simp add:case_prod_beta)
        apply (rule allI, rule impI)
      apply (rule finite_subset[where B="{0..<p}\<times>{0..<p}"], rule subsetI, simp add:case_prod_beta mem_Times_iff, simp)
       apply (rule subsetI, simp add:case_prod_beta)
      by simp
    also have "... \<le> 1/(real p)\<^sup>2 * (\<Sum> u' \<in> {u. u < p \<and> real u \<le> 2 * c}.
      card  {(u::nat,v::nat). u = u' \<and> abs (real u - real v) \<le> 2 * c * 2 powr (-real r) \<and> v < p \<and> v \<noteq> u'})"
      apply (rule mult_left_mono)
       apply (rule of_nat_mono)
      by (rule card_UN_le, simp, simp)
    also have "... = 1/(real p)\<^sup>2 * (\<Sum> u' \<in> {u. u < p \<and>  real u \<le> 2 * c}.
      card ((\<lambda>x. (u' ,x)) ` {(v::nat). abs (real u' - real v) \<le> 2 * c * 2 powr (-real r) \<and> v < p \<and> v \<noteq> u'}))"
      apply (simp, rule disjI2, rule sum.cong, simp)
      apply (simp, rule arg_cong[where f="card"], subst set_eq_iff)
      by blast
    also have "... \<le> 1/(real p)\<^sup>2 * (\<Sum> u' \<in> {u. u < p \<and> real u \<le> 2 * c}.
      card {(v::nat). abs (real u' - real v) \<le> 2 * c * 2 powr (-real r) \<and> v < p \<and> v \<noteq> u'})"
      apply (rule mult_left_mono)
       apply (rule of_nat_mono, rule sum_mono, rule card_image_le, simp)
      by simp
    also have "... \<le> 1/(real p)\<^sup>2 * (\<Sum> u' \<in> {u. u < p \<and> real u \<le> 2 * c}.
      card {(v::nat). abs (real u' - real v) \<le> 2 * c * 2 powr (-real r) \<and> v \<noteq> u'})"
      apply (rule mult_left_mono)
       apply (rule of_nat_mono, rule sum_mono, rule card_mono)
        apply (rule count_nat_abs_diff_2(2), simp)
      by (rule subsetI, simp, simp)
    also have "... \<le> 1/(real p)\<^sup>2 * (\<Sum> u' \<in> {u. u < p \<and> real u \<le> 2 * c}.
      2 * (2 * c * 2 powr (-real r)))"
      apply (rule mult_left_mono)
       apply (subst of_nat_sum)
       apply (rule sum_mono)
       apply (rule count_nat_abs_diff_2(1), simp)
      by simp
    also have "... \<le>  1/(real p)\<^sup>2 * (real (card {u. u \<le> nat (\<lfloor>2 * c \<rfloor>)}) * (2 * (2 * c * 2 powr (-real r))))"
      apply (rule mult_left_mono)
       apply (subst sum_constant)
       apply (rule mult_right_mono)
        apply (rule of_nat_mono, rule card_mono, simp)
        apply (rule subsetI, simp) using c_ge_0 le_nat_floor apply blast
       apply (simp add: c_ge_0)
      by simp
    also have "... \<le>  1/(real p)\<^sup>2 * ((3 * c) * (2 * (2 * c * 2 powr (-real r))))"
      apply (rule mult_left_mono)
       apply (rule mult_right_mono)
      apply simp using assms(4) apply linarith
      by (simp add: c_ge_0)+
    also have "... = 12  * c\<^sup>2 * 2 powr (-real r) /(real p)\<^sup>2"
      by (simp add:ac_simps power2_eq_square) 
    finally show "measure \<Omega> {\<omega>. degree \<omega> \<ge> 1 \<and> truncate_down r (hash p x \<omega>) \<le> c \<and>
      truncate_down r (hash p x \<omega>) = truncate_down r (hash p y \<omega>)} \<le>  12  * c\<^sup>2 * 2 powr (-real r) /(real p)\<^sup>2"
      by simp
  qed

  have "\<P>(\<omega> in measure_pmf \<Omega>. ?l \<omega> \<and> degree \<omega> \<ge> 1) \<le> 
    measure \<Omega> (\<Union> i \<in> {(x,y) \<in> M \<times> M. x < y}. {\<omega>. 
    degree \<omega> \<ge> 1 \<and> truncate_down r (hash p (fst i) \<omega>) \<le> c \<and>
    truncate_down r (hash p (fst i) \<omega>) = truncate_down r (hash p (snd i) \<omega>)})"
    apply (rule pmf_mono_1)
    apply (simp) 
    by (metis linorder_neqE_nat)
  also have "... \<le> (\<Sum> i \<in> {(x,y) \<in> M \<times> M. x < y}. measure \<Omega> 
    {\<omega>. degree \<omega> \<ge> 1 \<and> truncate_down r (hash p (fst i) \<omega>) \<le> c \<and>
    truncate_down r (hash p (fst i) \<omega>) = truncate_down r (hash p (snd i) \<omega>)})"
    apply (rule measure_UNION_le)
     apply (rule finite_subset[where B="M \<times> M"], rule subsetI, simp add:case_prod_beta mem_Times_iff)
     apply (rule finite_cartesian_product[OF f_M f_M])
    by simp
  also have "... \<le> (\<Sum> i \<in> {(x,y) \<in> M \<times> M. x < y}. 12  * c\<^sup>2 * 2 powr (-real r) /(real p)\<^sup>2)"
    apply (rule sum_mono)
    using a1 by (simp add:case_prod_beta)
  also have "... =  (12 * c\<^sup>2  * 2 powr (-real r) /(real p)\<^sup>2) * card  {(x,y) \<in> M \<times> M. x < y}"
    by simp
  also have "... \<le> (12 * c\<^sup>2 * 2 powr (-real r) /(real p)\<^sup>2) * ((real (card M))\<^sup>2/real 2)"
    apply (rule mult_left_mono)
     apply (subst pos_le_divide_eq, simp)
     apply (subst mult.commute)
     apply (subst of_nat_mult[symmetric])
     apply (subst card_ordered_pairs, rule finite_subset[OF assms(3)], simp)
     apply (subst of_nat_power[symmetric], rule of_nat_mono)
     apply (simp add:power2_eq_square)
    by (simp add:c_ge_0)
  also have "... = 6 * (real (card M))\<^sup>2 * c\<^sup>2 * 2 powr (-real r) /(real p)\<^sup>2"
    by (simp add:algebra_simps)
  finally have a:"\<P>(\<omega> in measure_pmf \<Omega>. ?l \<omega> \<and> degree \<omega> \<ge> 1) \<le> ?r1" by simp

  have b1: "bounded_degree_polynomials (ZFact (int p)) 2 \<inter> {\<omega>. length \<omega> \<le> Suc 0}
    = bounded_degree_polynomials (ZFact (int p)) 1"
    apply (rule order_antisym)
     apply (rule subsetI, simp add:bounded_degree_polynomials_def) 
    by (rule subsetI, simp add:bounded_degree_polynomials_def, fastforce) 

  have b: " \<P>(\<omega> in measure_pmf \<Omega>. degree \<omega> < 1) \<le> ?r2" 
    apply (simp add:\<Omega>_def)
    apply (subst measure_pmf_of_set) 
        apply (rule ne_bounded_degree_polynomials)
      apply (rule fin_bounded_degree_polynomials[OF p_ge_0])
    apply (subst card_bounded_degree_polynomials[OF p_ge_0], subst b1)
    apply (subst card_bounded_degree_polynomials[OF p_ge_0]) 
    apply (simp add:zfact_card[OF p_ge_0])
    by (subst pos_divide_le_eq, simp add:p_ge_0, simp add:power2_eq_square)

  have "\<P>(\<omega> in measure_pmf \<Omega>. ?l \<omega>) \<le>
    \<P>(\<omega> in measure_pmf \<Omega>. ?l \<omega> \<and> degree \<omega> \<ge> 1) + \<P>(\<omega> in measure_pmf \<Omega>. degree \<omega> < 1)"
    by (rule pmf_add, simp, linarith)
  also have "... \<le> ?r1 + ?r2" by (rule add_mono, metis a, metis b)
  finally show ?thesis by simp
qed

lemma inters_compr: "A \<inter> {x. P x} = {x \<in> A. P x}"
  by blast

lemma of_bool_square: "(of_bool x)\<^sup>2 = ((of_bool x)::real)"
  by (cases x, simp, simp)

theorem f0_alg_correct:
  assumes "\<epsilon> \<in> {0<..<1}"
  assumes "\<delta> \<in> {0<..<1}"
  assumes "set as \<subseteq> {0..<n}"
  defines "M \<equiv> fold (\<lambda>a state. state \<bind> f0_update a) as (f0_init \<delta> \<epsilon> n) \<bind> f0_result"
  shows "\<P>(\<omega> in measure_pmf M. \<bar>\<omega> - F 0 as\<bar> \<le> \<delta> * F 0 as) \<ge> 1 - of_rat \<epsilon>"
proof -
  define s where "s = nat \<lceil>-(18* ln (real_of_rat \<epsilon>))\<rceil>"
  define t where "t = nat \<lceil>80 / (real_of_rat \<delta>)\<^sup>2\<rceil>"
  define p where "p = find_prime_above (max n 19)"
  define r where "r = nat (4 * \<lceil>log 2 (1 / real_of_rat \<delta>)\<rceil> + 24)"
  define g where "g = (\<lambda>S. if card S < t then rat_of_nat (card S) else of_nat t * rat_of_nat p / rat_of_float (Max S))"
  define g' where "g' = (\<lambda>S. if card S < t then real (card S) else real t * real p / Max S)"
  define h where "h = (\<lambda>\<omega>. least t ((\<lambda>x. truncate_down r (hash p x \<omega>)) ` set as))"
  define \<Omega>\<^sub>0 where "\<Omega>\<^sub>0 = prod_pmf {0..<s} (\<lambda>_. pmf_of_set (bounded_degree_polynomials (ZFact (int p)) 2))"
  define \<Omega>\<^sub>1 where "\<Omega>\<^sub>1 = pmf_of_set (bounded_degree_polynomials (ZFact (int p)) 2)"
  define m where "m = card (set as)"

  define f where "f = (\<lambda>r \<omega>. card {x \<in> set as. int (hash p x \<omega>) \<le> r})"
  define \<delta>' where "\<delta>' = 3* real_of_rat \<delta> /4"
  define a where "a = \<lfloor>real t * p / (m * (1+\<delta>'))\<rfloor>"
  define b where "b = \<lceil>real t * p / (m * (1-\<delta>'))-1\<rceil>"

  define has_no_collision where "has_no_collision = (\<lambda>\<omega>. \<forall>x\<in> set as. \<forall>y \<in> set as.
    (truncate_down r (hash p x \<omega>) = truncate_down r (hash p y \<omega>) \<longrightarrow> x = y) \<or> 
    truncate_down r (hash p x \<omega>) > b)"

  have s_ge_0: "s > 0" 
    using assms(1) by (simp add:s_def)

  have t_ge_0: "t > 0"
    using assms by (simp add:t_def)

  have \<delta>_ge_0: "\<delta> > 0" using assms by simp
  have \<delta>_le_1: "\<delta> < 1" using assms by simp

  have r_bound: "4 * log 2 (1 / real_of_rat \<delta>) + 24 \<le> r"
    apply (simp add:r_def)                              
    apply (subst of_nat_nat)
     apply (rule add_nonneg_nonneg)
      apply (rule mult_nonneg_nonneg, simp)
      apply (subst zero_le_ceiling, subst log_divide, simp, simp, simp, simp add:\<delta>_ge_0, simp)
      apply (subst log_less_one_cancel_iff, simp, simp add:\<delta>_ge_0)
    by (rule order_less_le_trans[where y="1"], simp add:\<delta>_le_1, simp+)

  have "1 \<le> 0 + (24::real)" by simp
  also have "... \<le> 4 * log 2 (1 / real_of_rat \<delta>) + 24"
    apply (rule add_mono, simp)
    apply (subst zero_le_log_cancel_iff)
    using assms by simp+
  also have "... \<le> r" using r_bound by simp
  finally have r_ge_0: "1 \<le> r" by simp

  have "2 powr (-real r) \<le> 2 powr (-(4 * log 2 (1 / real_of_rat \<delta>) + 24))"
    apply (rule powr_mono) using r_bound apply linarith by simp
  also have "... = 2 powr (-4 * log 2 (1 /real_of_rat \<delta>) -24)"
    by (rule arg_cong2[where f="(powr)"], simp, simp add:algebra_simps)
  also have "... \<le> 2 powr ( -1 * log 2 (1 /real_of_rat \<delta>) -4)"
    apply (rule powr_mono)
     apply (rule diff_mono)
    using assms(2) by simp+
  also have "... = real_of_rat \<delta> / 16"
    apply (subst powr_diff)
    apply (subst log_divide, simp, simp, simp, simp add:\<delta>_ge_0, simp)
    by (subst powr_log_cancel, simp, simp, simp add:\<delta>_ge_0, simp)
  also have "... < real_of_rat \<delta> / 8"
    by (subst pos_divide_less_eq, simp, simp add:\<delta>_ge_0)
  finally have r_le_\<delta>: "2 powr (-real r) < (real_of_rat \<delta>)/ 8"
    by simp

  have r_le_t2: "18 * 96 * (real t)\<^sup>2 * 2 powr (-real r) \<le> 
    18 * 96 * (80 / (real_of_rat \<delta>)\<^sup>2+1)\<^sup>2 * 2 powr (-4 * log 2 (1 / real_of_rat \<delta>) - 24)"
    apply (rule mult_mono)
       apply (rule mult_left_mono)
        apply (rule power_mono)
         apply (simp add:t_def) using t_def t_ge_0 apply linarith
        apply simp
       apply simp
      apply (rule powr_mono) using r_bound apply linarith
    by simp+
  also have "... \<le> 18 * 96 * (80 / (real_of_rat \<delta>)\<^sup>2 + 1 /  (real_of_rat \<delta>)\<^sup>2)\<^sup>2 * (2 powr (-4 * log 2 (1 / real_of_rat \<delta>)) * 2 powr (-24))"
    apply (rule mult_mono)
       apply (rule mult_left_mono)
        apply (rule power_mono)
         apply (rule add_mono, simp) using assms(2) apply (simp add: power_le_one)
    by (simp add:powr_diff)+
  also have "... = 18 * 96 * (81\<^sup>2 / (real_of_rat \<delta>)^4) * (2 powr (log 2 ((real_of_rat \<delta>)^4))  * 2 powr (-24))"
    apply (rule arg_cong2[where f="(*)"])
     apply (rule arg_cong2[where f="(*)"], simp)
    apply (simp add:power2_eq_square power4_eq_xxxx)
    apply (rule arg_cong2[where f="(*)"])
     apply (rule arg_cong2[where f="(powr)"], simp)
     apply (subst log_nat_power, simp add:\<delta>_ge_0)
     apply (subst log_divide, simp, simp, simp, simp add:\<delta>_ge_0) 
    by simp+
  also have "... = 18 * 96 * 81\<^sup>2 * 2 powr (-24)"
    apply (subst powr_log_cancel, simp, simp, simp) using \<delta>_ge_0 apply blast
    apply (simp add:algebra_simps) using \<delta>_ge_0 by blast
  also have "... \<le> 1"
    by simp
  finally have r_le_t2: "18 * 96 * (real t)\<^sup>2 * 2 powr (-real r) \<le> 1"
    by simp

  have \<delta>'_ge_0: "\<delta>' > 0" using assms by (simp add:\<delta>'_def)
  have \<delta>'_le_1: "\<delta>' < 1"
    apply (rule order_less_le_trans[where y="3/4"])
    using assms by (simp add:\<delta>'_def)+
 
  have "t \<le> 80 / (real_of_rat \<delta>)\<^sup>2 + 1"
    using t_def t_ge_0 by linarith
  also have "... = 45 / (\<delta>')\<^sup>2 + 1"
    by (simp add:\<delta>'_def algebra_simps power2_eq_square)
  also have "... \<le> 45 / \<delta>'\<^sup>2 + 1 / \<delta>'\<^sup>2"
    apply (rule add_mono, simp)
    apply (subst pos_le_divide_eq, simp add:\<delta>'_def)
    using assms apply force
    apply (simp add: \<delta>'_def algebra_simps)
    apply (subst power_le_one_iff)
    using assms apply simp
    apply (subst pos_divide_le_eq, simp, simp)
    apply (rule order_trans[where y="3"])
    using assms(2) by simp+
  also have "... = 46/ \<delta>'\<^sup>2"
    by simp
  finally have t_le_\<delta>': "t \<le> 46/ \<delta>'\<^sup>2" by simp

  have "45 / \<delta>'\<^sup>2 = 80/ (real_of_rat \<delta>)\<^sup>2"
    by (simp add:\<delta>'_def power2_eq_square)
  also have "... \<le> t"
    using t_ge_0 t_def of_nat_ceiling by blast
  finally have t_ge_\<delta>': " 45 / \<delta>'\<^sup>2 \<le> t" by simp

  have p_prime: "Factorial_Ring.prime p" 
    using p_def find_prime_above_is_prime by simp
  have p_ge_18: "p \<ge> 18" 
    apply (rule order_trans[where y="19"], simp)
    using p_def find_prime_above_lower_bound max.bounded_iff by blast
  hence p_ge_0: "p > 0" by simp

  have "m \<le> card {0..<n}" 
    apply (subst m_def)
    by (rule card_mono, simp, simp add:assms(3))
  also have "... \<le> p"
    by (metis p_def find_prime_above_lower_bound card_atLeastLessThan diff_zero max_def order_trans)
  finally have m_le_p: "m \<le> p" by simp

  have xs_le_p: "\<And>x. x \<in> set as \<Longrightarrow> x < p" 
    apply (rule order_less_le_trans[where y="n"])
    using assms(3) atLeastLessThan_iff apply blast
    by (metis p_def find_prime_above_lower_bound max_def order_trans)

  have m_eq_F_0: "real m = of_rat (F 0 as)"
    by (simp add:m_def F_def)

  have fin_omega_1: "finite (set_pmf \<Omega>\<^sub>1)"
    apply (simp add:\<Omega>\<^sub>1_def)
    by (metis fin_bounded_degree_polynomials[OF p_ge_0] ne_bounded_degree_polynomials set_pmf_of_set)

  have exp_var_f: "\<And>a. a \<ge> -1 \<Longrightarrow> a < int p \<Longrightarrow> 
    prob_space.expectation \<Omega>\<^sub>1 (\<lambda>\<omega>. real (f a \<omega>)) = real m * (real_of_int a+1) / p \<and>
    prob_space.variance \<Omega>\<^sub>1 (\<lambda>\<omega>. real (f a \<omega>)) \<le> real m * (real_of_int a+1) / p"
  proof -
    fix a :: int
    assume a_ge_m1: "a \<ge> -1"
    assume a_le_p: "a < int p"
    have xs_subs_p: "set as \<subseteq> {0..<p}"
      using xs_le_p  
      by (simp add: subset_iff)

    have exp_single: "\<And>x. x \<in> set as \<Longrightarrow> prob_space.expectation \<Omega>\<^sub>1 (\<lambda>\<omega>. of_bool (int (hash p x \<omega>) \<le> a)) = 
      (real_of_int a+1)/real p"
    proof -
      fix x
      assume "x \<in> set as"
      hence x_le_p: "x < p" using xs_le_p by simp
      have "prob_space.expectation \<Omega>\<^sub>1 (\<lambda>\<omega>. of_bool (int (hash p x \<omega>) \<le> a)) = 
        measure \<Omega>\<^sub>1 ({\<omega>. int (hash p x \<omega>) \<le> a} \<inter> space \<Omega>\<^sub>1)"
        apply (subst Bochner_Integration.integral_indicator[where M="measure_pmf \<Omega>\<^sub>1", symmetric])
        apply (rule arg_cong2[where f="integral\<^sup>L"], simp)
        by (rule ext, simp)
      also have "... = \<P>(\<omega> in \<Omega>\<^sub>1. hash p x \<omega> \<in> {k. int k \<le> a})"
        by simp
      also have "... = card ({k. int k \<le> a} \<inter> {0..<p}) / real p"
        apply (simp only:\<Omega>\<^sub>1_def)
        by (rule hash_prob_range[OF p_prime x_le_p], simp)
      also have "... = card {0..<nat (a+1)} / real p"
        apply (rule arg_cong2[where f="(/)"])
         apply (rule arg_cong[where f="real"], rule arg_cong[where f="card"])
         apply (subst set_eq_iff, rule allI)
         apply (cases "a \<ge> 0")
          using a_le_p apply (simp, linarith) 
        by simp+
      also have "... =  (real_of_int a+1)/real p"
        using a_ge_m1 by simp
      finally show "prob_space.expectation \<Omega>\<^sub>1 (\<lambda>\<omega>. of_bool (int (hash p x \<omega>) \<le> a)) = 
        (real_of_int a+1)/real p"
        by simp
    qed
    have "prob_space.expectation \<Omega>\<^sub>1 (\<lambda>\<omega>. real (f a \<omega>)) = 
      prob_space.expectation \<Omega>\<^sub>1 (\<lambda>\<omega>. (\<Sum>x \<in> set as. of_bool (int (hash p x \<omega>) \<le> a)))"
      by (simp add:f_def inters_compr)
    also have "... =  (\<Sum>x \<in> set as. prob_space.expectation \<Omega>\<^sub>1 (\<lambda>\<omega>. of_bool (int (hash p x \<omega>) \<le> a)))"
      apply (rule Bochner_Integration.integral_sum)
      by (rule integrable_measure_pmf_finite[OF fin_omega_1])
    also have "... = (\<Sum> x \<in> set as. (a+1)/real p)"
      by (rule sum.cong, simp, subst exp_single, simp, simp)
    also have "... = real m * (real_of_int a + 1) /real p"
      by (simp add:m_def)
    finally have r_1: "prob_space.expectation \<Omega>\<^sub>1 (\<lambda>\<omega>. real (f a \<omega>)) = real m * (real_of_int a+1) / p"
      by simp

    have "prob_space.variance \<Omega>\<^sub>1 (\<lambda>\<omega>. real (f a \<omega>)) = 
      prob_space.variance \<Omega>\<^sub>1 (\<lambda>\<omega>. (\<Sum>x \<in> set as. of_bool (int (hash p x \<omega>) \<le> a)))"
      by (simp add:f_def inters_compr)
    also have "... = (\<Sum>x \<in> set as. prob_space.variance \<Omega>\<^sub>1 (\<lambda>\<omega>. of_bool (int (hash p x \<omega>) \<le> a)))"
      apply (rule prob_space.var_sum_pairwise_indep_2, simp add:prob_space_measure_pmf, simp, simp)
       apply (rule integrable_measure_pmf_finite[OF fin_omega_1])
      apply (rule prob_space.indep_vars_compose2[where Y="\<lambda>i x. of_bool (int x \<le> a)" and M'="\<lambda>_. measure_pmf (pmf_of_set {0..<p})"])
        apply (simp add:prob_space_measure_pmf)
       using hash_k_wise_indep[OF p_prime, where n="2"] xs_subs_p
       apply (simp add:measure_pmf.k_wise_indep_vars_def \<Omega>\<^sub>1_def) 
       apply (metis le_refl order_trans subset_eq_atLeast0_lessThan_finite) 
      by simp
    also have "... \<le> (\<Sum> x \<in> set as. (a+1)/real p)"
      apply (rule sum_mono)
      apply (subst prob_space.variance_eq[OF prob_space_measure_pmf])
       apply (rule integrable_measure_pmf_finite[OF fin_omega_1])
       apply (rule integrable_measure_pmf_finite[OF fin_omega_1])
      apply (simp add:of_bool_square)
      apply (subst exp_single, simp)
      by simp
    also have "... = real m * (real_of_int a + 1) /real p"
      by (simp add:m_def)
    finally have r_2: "prob_space.variance \<Omega>\<^sub>1 (\<lambda>\<omega>. real (f a \<omega>)) \<le> real m * (real_of_int a+1) / p"
      by simp
    show
      "prob_space.expectation \<Omega>\<^sub>1 (\<lambda>\<omega>. real (f a \<omega>)) = real m * (real_of_int a+1) / p \<and>
       prob_space.variance \<Omega>\<^sub>1 (\<lambda>\<omega>. real (f a \<omega>)) \<le> real m * (real_of_int a+1) / p"
      using r_1 r_2 by auto
  qed

  have exp_f: "\<And>a.  a \<ge> -1 \<Longrightarrow> a < int p \<Longrightarrow> prob_space.expectation \<Omega>\<^sub>1 (\<lambda>\<omega>. real (f a \<omega>)) =
    real m * (real_of_int a+1) / p" using exp_var_f by blast

  have var_f: "\<And>a. a \<ge> -1 \<Longrightarrow> a < int p \<Longrightarrow> prob_space.variance \<Omega>\<^sub>1 (\<lambda>\<omega>. real (f a \<omega>)) \<le>
    real m * (real_of_int a+1) / p" using exp_var_f by blast

  have b: "\<P>(\<omega> in measure_pmf \<Omega>\<^sub>1. 
    of_rat \<delta> * real_of_rat (F 0 as) < \<bar>g' (h \<omega>) - of_rat (F 0 as)\<bar>) \<le> 1/3"
  proof (cases "card (set as) \<ge> t")
    case True
    hence t_le_m: "t \<le> card (set as)" by simp
    have m_ge_0: "real m > 0"
      using m_def True t_ge_0 by simp
  
    have b_le_tpm :"b \<le> real t * real p / (real m * (1 - \<delta>'))"
      by (simp add:b_def)
    also have "... \<le> real t * real p / (real m * (1/4))"
      apply (rule divide_left_mono)
        apply (rule mult_left_mono)
        using assms apply (simp add:\<delta>'_def)
      using m_ge_0 \<delta>'_le_1 by (auto intro!:mult_pos_pos)
    finally have b_le_tpm: "b \<le> 4 * real t * real p / real m"
      by (simp add:algebra_simps)

    have a_ge_0: "a \<ge> 0" 
      apply (simp add:a_def)
      apply (rule divide_nonneg_nonneg, simp)
      using \<delta>'_ge_0 by simp
    have b_ge_0: "b > 0" 
      apply (simp add:b_def)
      apply (subst pos_less_divide_eq)
       apply (rule mult_pos_pos)
      using True m_def t_ge_0 apply simp
      using \<delta>'_le_1 apply simp
      apply simp
      apply (subst mult.commute)
      apply (rule order_less_le_trans[where y="real m"]) using \<delta>'_ge_0 m_ge_0 apply simp
      apply (rule order_trans[where y="1 * real p"]) using m_le_p apply simp
      apply (rule mult_right_mono) using t_ge_0 apply simp
      by simp
    hence b_ge_1: "real_of_int b \<ge> 1"
      by linarith

    have a_le_p: "a < real p"
      apply (rule order_le_less_trans[where y="real t * real p / (real m * (1 + \<delta>'))"])
       apply (simp add:a_def)
      apply (subst pos_divide_less_eq) using m_ge_0 \<delta>'_ge_0 apply force
      apply (subst mult.commute)
      apply (rule mult_strict_left_mono)
       apply (rule order_le_less_trans[where y="real m"]) using True m_def apply linarith
      using \<delta>'_ge_0 m_ge_0 apply force
      using p_ge_0 by simp
    hence a_le_p: "a < int p"
      by linarith

    have "\<P>(\<omega> in measure_pmf \<Omega>\<^sub>1. f a \<omega> \<ge> t) \<le> 
      \<P>(\<omega> in measure_pmf \<Omega>\<^sub>1. abs (real (f a \<omega>) - prob_space.expectation (measure_pmf \<Omega>\<^sub>1) (\<lambda>\<omega>. real (f a \<omega>))) 
      \<ge> 3 * sqrt (m *(real_of_int a+1)/p))"
    proof (rule pmf_mono_2)
      fix \<omega>
      assume "\<omega> \<in> set_pmf \<Omega>\<^sub>1"
      assume t_le: "t \<le> f a \<omega>"
      have "real m * (of_int a + 1) / p = real m * (of_int a) / p + real m / p"
        by (simp add:algebra_simps add_divide_distrib)
      also have "... \<le>  real m * (real t * real p / (real m * (1+\<delta>'))) / real p + 1"
        apply (rule add_mono)
         apply (rule divide_right_mono)
          apply (rule mult_mono, simp, simp add:a_def, simp, simp add:a_ge_0)
         apply (simp)
        using m_le_p by (simp add: p_ge_0)
      also have "... \<le> real t / (1+\<delta>') + 1"
        apply (rule add_mono)
         apply (subst pos_le_divide_eq) using \<delta>'_ge_0 apply simp
        by simp+
      finally have a_le_1: "real m * (of_int a + 1) / p \<le> t / (1+ \<delta>') + 1"
        by simp
      have a_le: "3 * sqrt (real m * (of_int a + 1) / real p) + real m * (of_int a + 1) / real p \<le> 
        3 * sqrt (t / (1+\<delta>') + 1) + (t / (1+\<delta>') + 1)"
        apply (rule add_mono)
         apply (rule mult_left_mono)
          apply (subst real_sqrt_le_iff, simp add:a_le_1)
         apply simp
        by (simp add:a_le_1)
      also have "... \<le> 3 * sqrt (real t+1) + ((t - \<delta>' * t / (1+\<delta>')) + 1)"
        apply (rule add_mono)
         apply (rule mult_left_mono)
          apply (subst real_sqrt_le_iff, simp)
          apply (subst pos_divide_le_eq) using \<delta>'_ge_0 apply simp
          using \<delta>'_ge_0 apply (simp add: t_ge_0)
         apply simp
        apply (rule add_mono)
         apply (subst pos_divide_le_eq) using \<delta>'_ge_0 apply simp
         apply (subst left_diff_distrib, simp, simp add:algebra_simps)
        using \<delta>'_ge_0 by simp+
      also have "... \<le> 3 * sqrt (46 / \<delta>'\<^sup>2 + 1 / \<delta>'\<^sup>2) + (t - \<delta>' * t/2) + 1 / \<delta>'"
        apply (subst add.assoc[symmetric])
        apply (rule add_mono)
         apply (rule add_mono)
          apply (rule mult_left_mono)
           apply (subst real_sqrt_le_iff)
           apply (rule add_mono, metis t_le_\<delta>')
           apply (subst pos_le_divide_eq) using \<delta>'_ge_0 apply simp
           apply (metis  \<delta>'_le_1 \<delta>'_ge_0  less_eq_real_def mult_1 power_le_one)
          apply simp
         apply simp
         apply (subst pos_le_divide_eq) using \<delta>'_ge_0 apply simp
         using \<delta>'_le_1 \<delta>'_ge_0 
         apply (metis add_mono less_eq_real_def mult_eq_0_iff mult_left_mono of_nat_0_le_iff one_add_one)
        using \<delta>'_le_1 \<delta>'_ge_0 by simp
      also have "... \<le> (21 / \<delta>' + (t - 45 / (2*\<delta>'))) + 1 / \<delta>'" 
        apply (rule add_mono)
         apply (rule add_mono)
          apply (simp add:real_sqrt_divide, subst abs_of_nonneg) using \<delta>'_ge_0 apply linarith
        using \<delta>'_ge_0 apply (simp add: divide_le_cancel)
          apply (rule real_le_lsqrt, simp, simp, simp)
         apply simp
         apply (metis \<delta>'_ge_0 t_ge_\<delta>' less_eq_real_def mult_left_mono power2_eq_square real_divide_square_eq times_divide_eq_right)
        by simp
      also have "... \<le> t" using \<delta>'_ge_0 by simp
      also have "... \<le> f a \<omega>" using t_le by simp
      finally have t_le: "3 * sqrt (real m * (of_int a + 1) / real p) \<le> f a \<omega> - real m * (of_int a + 1) / real p"
        by (simp add:algebra_simps)
      show " 3 * sqrt (real m * (real_of_int a + 1) / real p) \<le> 
        \<bar>real (f a \<omega>) - measure_pmf.expectation \<Omega>\<^sub>1 (\<lambda>\<omega>. real (f a \<omega>))\<bar>"
        apply (subst exp_f) using a_ge_0 a_le_p True apply (simp, simp)
        apply (subst abs_ge_iff)
        using t_le by blast
    qed
    also have "... \<le> prob_space.variance (measure_pmf \<Omega>\<^sub>1) (\<lambda>\<omega>. real (f a \<omega>)) 
      / (3 * sqrt (real m * (of_int a + 1) / real p))\<^sup>2"
      apply (rule prob_space.Chebyshev_inequality)
         apply (metis prob_space_measure_pmf)
        apply simp
       apply (rule integrable_measure_pmf_finite[OF fin_omega_1])
       apply simp
      using t_ge_0 a_ge_0 p_ge_0 m_ge_0 m_eq_F_0 by auto
    also have "... \<le> 1/9"
      apply (subst pos_divide_le_eq) using a_ge_0 p_ge_0 m_ge_0 m_eq_F_0 apply force
      apply simp
      apply (subst real_sqrt_pow2) using a_ge_0 p_ge_0 m_ge_0 m_eq_F_0 apply force
      apply (rule var_f) using a_ge_0 apply linarith
      using a_le_p by simp
    finally have case_1: "\<P>(\<omega> in measure_pmf \<Omega>\<^sub>1. f a \<omega> \<ge> t) \<le> 1/9"
      by simp

    have case_2: "\<P>(\<omega> in measure_pmf \<Omega>\<^sub>1. f b \<omega> < t) \<le> 1/9"
    proof (cases "b < p")
      case True
      have "\<P>(\<omega> in measure_pmf \<Omega>\<^sub>1. f b \<omega> < t) \<le> 
        \<P>(\<omega> in measure_pmf \<Omega>\<^sub>1. abs (real (f b \<omega>) - prob_space.expectation (measure_pmf \<Omega>\<^sub>1) (\<lambda>\<omega>. real (f b \<omega>))) 
        \<ge> 3 * sqrt (m *(real_of_int b+1)/p))"
      proof (rule pmf_mono_2)
        fix \<omega>
        assume "\<omega> \<in> set_pmf \<Omega>\<^sub>1"
        have aux: "(real t + 3 * sqrt (real t / (1 - \<delta>') + 1)) * (1 - \<delta>') =
           real t - \<delta>' * t + 3 * ((1-\<delta>') * sqrt( real t / (1-\<delta>') + 1))"
          by (simp add:algebra_simps)
        also have "... = real t - \<delta>' * t + 3 * sqrt (  (1-\<delta>')\<^sup>2 * (real t /  (1-\<delta>') +  1))"
          apply (subst real_sqrt_mult)
          apply (subst real_sqrt_abs)
          apply (subst abs_of_nonneg)
          using \<delta>'_le_1 by simp+
        also have "... = real t - \<delta>' * t + 3 * sqrt ( real t * (1- \<delta>') + (1-\<delta>')\<^sup>2)"
          by (simp add:power2_eq_square distrib_left)
        also have "... \<le> real t - 45/ \<delta>' + 3 * sqrt ( real t  + 1)"
          apply (rule add_mono, simp)
           apply (subst mult.commute, subst pos_divide_le_eq[symmetric])
            using \<delta>'_ge_0 apply blast
           using t_ge_\<delta>' apply (simp add:power2_eq_square)
          apply simp
          apply (rule add_mono)
           using \<delta>'_le_1 \<delta>'_ge_0 by (simp add: power_le_one t_ge_0)+
        also have "... \<le> real t - 45/ \<delta>' + 3 * sqrt ( 46 / \<delta>'\<^sup>2 + 1 / \<delta>'\<^sup>2)"
          apply (rule add_mono, simp)
          apply (rule mult_left_mono)
           apply (subst real_sqrt_le_iff)
           apply (rule add_mono, metis t_le_\<delta>')
           apply (meson \<delta>'_ge_0 \<delta>'_le_1 le_divide_eq_1_pos less_eq_real_def power_le_one_iff zero_less_power)
          by simp
        also have "... = real t + (3 * sqrt(47) - 45)/ \<delta>'"
          apply (simp add:real_sqrt_divide)
          apply (subst abs_of_nonneg)
          using \<delta>'_ge_0 by (simp add: diff_divide_distrib)+
        also have "... \<le> t"
          apply simp
          apply (subst pos_divide_le_eq)
          using \<delta>'_ge_0 apply simp 
          apply simp
          by (rule real_le_lsqrt, simp+)
        finally have aux: "(real t + 3 * sqrt (real t / (1 - \<delta>') + 1)) * (1 - \<delta>') \<le> real t "
          by simp
        assume t_ge: "f b \<omega> < t"
        have "real (f b \<omega>) + 3 * sqrt (real m * (real_of_int b + 1) / real p) 
          \<le> real t + 3 * sqrt (real m * real_of_int b / real p + 1)"
          apply (rule add_mono)
          using t_ge apply linarith
          using m_le_p by (simp add: algebra_simps add_divide_distrib p_ge_0)
        also have "... \<le> real t + 3 * sqrt (real m * (real t * real p / (real m * (1- \<delta>'))) / real p + 1)"
          apply (rule add_mono, simp)
          apply (rule mult_left_mono)
           apply (subst real_sqrt_le_iff)
           apply (rule add_mono)
            apply (rule divide_right_mono)
             apply (rule mult_left_mono)
          apply (simp add:b_def)
          by simp+ 
        also have "... \<le> real t + 3 * sqrt(real t / (1-\<delta>') + 1)"
          apply (simp add:p_ge_0)
          using t_ge_0 t_le_m m_def by linarith
        also have "... \<le> real t / (1-\<delta>')" 
          apply (subst pos_le_divide_eq) using \<delta>'_le_1 aux by simp+
        also have "... = real m * (real t * real p / (real m * (1-\<delta>'))) / real p" 
          apply (simp add:p_ge_0)
          using t_ge_0 t_le_m m_def by linarith
        also have "... \<le>  real m * (real_of_int b + 1) / real p"      
          apply (rule divide_right_mono)
           apply (rule mult_left_mono)
          by (simp add:b_def)+
        finally have t_ge: "real (f b \<omega>) + 3 * sqrt (real m * (real_of_int b + 1) / real p) 
          \<le> real m * (real_of_int b + 1) / real p"
          by simp
        show " 3 * sqrt (real m * (real_of_int b + 1) / real p) \<le> 
          \<bar>real (f b \<omega>) - measure_pmf.expectation \<Omega>\<^sub>1 (\<lambda>\<omega>. real (f b \<omega>))\<bar>"  
          apply (subst exp_f) using b_ge_0 True apply (simp, simp)
          apply (subst abs_ge_iff)
          using t_ge by force
      qed
      also have "... \<le> prob_space.variance (measure_pmf \<Omega>\<^sub>1) (\<lambda>\<omega>. real (f b \<omega>)) 
        / (3 * sqrt (real m * (real_of_int b + 1) / real p))\<^sup>2" 
        apply (rule prob_space.Chebyshev_inequality)
           apply (metis prob_space_measure_pmf)
          apply simp
         apply (rule integrable_measure_pmf_finite[OF fin_omega_1])
         apply simp
        using t_ge_0 b_ge_0 p_ge_0 m_ge_0 m_eq_F_0 by auto
      also have "... \<le> 1/9"
        apply (subst pos_divide_le_eq) 
        using b_ge_0 p_ge_0 m_ge_0 m_eq_F_0 apply force
        apply simp
        apply (subst real_sqrt_pow2)
        using b_ge_0 p_ge_0 m_ge_0 m_eq_F_0 apply force
        apply (rule var_f) using b_ge_0 apply linarith
        using True by simp
      finally show ?thesis
        by simp
    next
      case False
      have "\<P>(\<omega> in \<Omega>\<^sub>1. f b \<omega> < t) \<le> \<P>(\<omega> in \<Omega>\<^sub>1. False)"
      proof (rule pmf_mono_1)
        fix \<omega>
        assume a_1:"\<omega> \<in> {\<omega> \<in> space (measure_pmf \<Omega>\<^sub>1). f b \<omega> < t}"
        assume a_2:"\<omega> \<in> set_pmf \<Omega>\<^sub>1"
        have a:"\<And>x. x < p \<Longrightarrow> hash p x \<omega> < p" 
          using hash_range[OF p_ge_0]  a_2
          by (simp add:\<Omega>\<^sub>1_def set_pmf_of_set[OF ne_bounded_degree_polynomials fin_bounded_degree_polynomials[OF p_ge_0]])
        have "t \<le> card (set as)"
          using True by simp
        also have "... \<le> f b \<omega>"
          apply (simp add:f_def)
          apply (rule card_mono, simp)
          apply (rule subsetI)
          by (metis (no_types, lifting) False a xs_le_p  linorder_linear mem_Collect_eq of_nat_less_iff order_le_less_trans)
        also have "... < t" using a_1 by simp
        finally have "False" by auto
        thus "\<omega> \<in> {\<omega> \<in> space (measure_pmf \<Omega>\<^sub>1). False}"
          by simp
      qed
      also have "... = 0" by auto
      finally show ?thesis by simp
    qed

    have "\<P>(\<omega> in measure_pmf \<Omega>\<^sub>1. \<not>has_no_collision \<omega>) \<le>
      \<P>(\<omega> in measure_pmf \<Omega>\<^sub>1. \<exists>x \<in> set as. \<exists>y \<in> set as. x \<noteq> y \<and> 
      truncate_down r (real (hash p x \<omega>)) \<le> real_of_int b \<and> 
      truncate_down r (real (hash p x \<omega>)) = truncate_down r (real (hash p y \<omega>)))" 
      apply (rule pmf_mono_1)
      apply (simp add:has_no_collision_def \<Omega>\<^sub>1_def) 
      by force
    also have "... \<le> 6 * (real (card (set as)))\<^sup>2 * (real_of_int b)\<^sup>2 
       * 2 powr - real r / (real p)\<^sup>2 + 1 / real p"
      apply (simp only: \<Omega>\<^sub>1_def)
      apply (rule f0_collision_prob[where c="real_of_int b"])
        apply (metis p_prime)
       apply (rule subsetI, simp add:xs_le_p)
       apply ( metis b_ge_1)
      by (metis r_ge_0)
    also have "... \<le> 6 * (real m)\<^sup>2 * (real_of_int b)\<^sup>2 * 2 powr - real r / (real p)\<^sup>2 + 1 / real p"
      apply (rule add_mono)
       apply (rule divide_right_mono)
        apply (rule mult_right_mono)
         apply (rule mult_mono)
            apply (simp add:m_def)
           apply (rule power_mono, simp)
      using b_ge_0 by simp+
    also have "... \<le> 6 * (real m)\<^sup>2 * (4 * real t * real p / real m)\<^sup>2 * (2 powr - real r) / (real p)\<^sup>2 + 1 / real p"
      apply (rule add_mono)
       apply (rule divide_right_mono)
        apply (rule mult_right_mono)
        apply (rule mult_left_mono)
      apply (simp add:b_def) 
      using b_def b_ge_1 b_le_tpm apply force
         apply simp
        apply simp
       apply simp
      by simp 
    also have "... = 96 * (real t)\<^sup>2 * (2 powr -real r) + 1 / real p"
      using p_ge_0 m_ge_0 t_ge_0 by (simp add:algebra_simps power2_eq_square)
    also have "... \<le> 1/18 + 1/18"
      apply (rule add_mono)
      apply (subst pos_le_divide_eq, simp)
      using r_le_t2 apply simp
      using p_ge_18 by simp
    also have "... = 1/9" by (simp)
    finally have case_3: "\<P>(\<omega> in measure_pmf \<Omega>\<^sub>1. \<not>has_no_collision \<omega>) \<le> 1/9" 
      by simp

    have "\<P>(\<omega> in measure_pmf \<Omega>\<^sub>1.
        real_of_rat \<delta> * real_of_rat (F 0 as) < \<bar>g' (h \<omega>) - real_of_rat (F 0 as)\<bar>) \<le> 
      \<P>(\<omega> in measure_pmf \<Omega>\<^sub>1. f a \<omega> \<ge> t \<or> f b \<omega> < t \<or> \<not>(has_no_collision \<omega>))"
    proof (rule pmf_mono_2, rule ccontr)
      fix \<omega>
      assume "\<omega> \<in> set_pmf \<Omega>\<^sub>1"
      assume est: "real_of_rat \<delta> * real_of_rat (F 0 as) < \<bar>g' (h \<omega>) - real_of_rat (F 0 as)\<bar>"
      assume "\<not>( t \<le> f a \<omega> \<or> f b \<omega> < t \<or> \<not> has_no_collision \<omega>)"
      hence lb: "f a \<omega> < t" and ub: "f b \<omega> \<ge> t" and no_col: "has_no_collision \<omega>" by simp+

      define y where "y =  nth_mset (t-1) {#int (hash p x \<omega>). x \<in># mset_set (set as)#}"
      define y' where "y' =  nth_mset (t-1) {#truncate_down r (hash p x \<omega>). x \<in># mset_set (set as)#}"

      have "a < y" 
        apply (subst y_def, rule nth_mset_bound_left_excl)
         apply (simp)
        using True t_ge_0 apply linarith
        using lb 
        by (simp add:f_def swap_filter_image count_le_def)
      hence rank_t_lb: "a + 1 \<le> y" 
        by linarith
    
      have rank_t_ub: "y \<le> b" 
        apply (subst y_def, rule nth_mset_bound_right)
         apply simp using True t_ge_0 apply linarith
        using ub t_ge_0
        by (simp add:f_def swap_filter_image count_le_def)

      have y_ge_0: "real_of_int y \<ge> 0" using rank_t_lb a_ge_0 by linarith
      have y'_eq: "y' = truncate_down r y"
        apply (subst y_def, subst y'_def, subst nth_mset_commute_mono[where f="(\<lambda>x. truncate_down r (of_int x))"]) 
          apply (metis truncate_down_mono mono_def of_int_le_iff)
         apply simp using True t_ge_0 apply linarith
        by (simp add: multiset.map_comp comp_def)
      have "real_of_int (a+1) * (1 - 2 powr -real r) \<le> real_of_int y * (1 - 2 powr (-real r))"
        apply (rule mult_right_mono)
        using rank_t_lb of_int_le_iff apply blast
        apply simp
        apply (subst two_powr_0[symmetric])
        by (rule powr_mono, simp, simp)
      also have "... \<le> y'"
        apply (subst y'_eq)
        using truncate_down_pos[OF y_ge_0] by simp
      finally have rank_t_lb': "(a+1) * (1 - 2 powr (-real r)) \<le> y'" by simp

      have "y' \<le> real_of_int y"
        by (subst y'_eq, rule truncate_down_le, simp)
      also have "... \<le> real_of_int b"
        using rank_t_ub of_int_le_iff by blast
      finally have rank_t_ub': "y' \<le> b"
        by simp

      have "0 < (a+1) * (1-2 powr (-real r))"
        apply (rule mult_pos_pos)
        using a_ge_0 apply linarith
        apply simp
        apply (subst two_powr_0[symmetric])
        apply (rule powr_less_mono)
        using r_ge_0 by auto
      hence y'_pos: "y' > 0" using rank_t_lb' by linarith

      have no_col': "\<And>x. x \<le> y' \<Longrightarrow> count {#truncate_down r (real (hash p x \<omega>)). x \<in># mset_set (set as)#} x \<le> 1"
        apply (subst count_image_mset, simp add:vimage_def card_le_Suc0_iff_eq)
        using  rank_t_ub' no_col apply (subst (asm) has_no_collision_def)
        by force

      have h_1: "Max (h \<omega>) = y'"
        apply (simp add:h_def y'_def)
        apply (subst nth_mset_max)
        using True t_ge_0 apply simp
        using no_col' apply (simp add:y'_def)
        using t_ge_0
        by simp

      have "card (h \<omega>) = card (least ((t-1)+1) (set_mset {#truncate_down r (hash p x \<omega>). x \<in># mset_set (set as)#}))"
        using t_ge_0
        by (simp add:h_def)
      also have "... = (t-1) +1"
        apply (rule nth_mset_max(2))
         using True t_ge_0 apply simp
        using no_col' by (simp add:y'_def)
      also have "... = t" using t_ge_0 by simp
      finally have h_2: "card (h \<omega>) = t"
        by simp
      have h_3: "g' (h \<omega>) = real t * real p / y'"
        using h_2 h_1 by (simp add:g'_def)

      have "(real t) * real p \<le>  (1 + \<delta>') * real m * ((real t) * real p / (real m * (1 + \<delta>')))" 
        apply (simp)
        using \<delta>'_le_1 m_def True t_ge_0 \<delta>'_ge_0 by linarith
      also have "... \<le> (1+\<delta>') * m * (a+1)"
        apply (rule mult_left_mono)
         apply (simp add:a_def)
        using \<delta>'_ge_0 by simp
      also have "... < ((1 + real_of_rat \<delta>)*(1-real_of_rat \<delta>/8)) * m * (a+1)"
        apply (rule mult_strict_right_mono)
         apply (rule mult_strict_right_mono)
          apply (simp add:\<delta>'_def distrib_left distrib_right left_diff_distrib right_diff_distrib)
        using True m_def t_ge_0 a_ge_0 assms(2) by auto
      also have "... \<le> ((1 + real_of_rat \<delta>)*(1-2 powr (-r))) * m * (a+1)"
        apply (rule mult_right_mono)
         apply (rule mult_right_mono)
          apply (rule mult_left_mono)
        using r_le_\<delta> assms(2) a_ge_0 by auto
      also have "... = (1 + real_of_rat \<delta>) * m * ((a+1) * (1-2 powr (-real r)))" 
        by simp
      also have "... \<le> (1 + real_of_rat \<delta>) * m * y'"
        apply (rule mult_left_mono, metis rank_t_lb')
        using assms by simp
      finally have "real t * real p < (1 + real_of_rat \<delta>) * m * y'" by simp
      hence f_1: "g' (h \<omega>) < (1 + real_of_rat \<delta>) * m"
        apply (simp add: h_3)
        by (subst pos_divide_less_eq, metis y'_pos, simp)
      have "(1 - real_of_rat \<delta>) * m * y' \<le> (1 - real_of_rat \<delta>) * m * b" 
        apply (rule mult_left_mono, metis rank_t_ub')
        using assms by simp
      also have "... = ((1-real_of_rat \<delta>))  * (real m * b)"
        by simp
      also have "... < (1-\<delta>') * (real m * b)" 
        apply (rule mult_strict_right_mono)
         apply (simp add: \<delta>'_def algebra_simps)
        using assms apply simp
        using r_le_\<delta> m_eq_F_0 m_ge_0 b_ge_0 by simp
      also have "... \<le> (1-\<delta>') * (real m * (real t * real p / (real m * (1-\<delta>'))))"
        apply (rule mult_left_mono)
        apply (rule mult_left_mono)
          apply (simp add:b_def, simp)
        using \<delta>'_ge_0 \<delta>'_le_1 by force
      also have "... = real t * real p"
        apply (simp)
        using \<delta>'_ge_0 \<delta>'_le_1 t_ge_0 p_ge_0 apply simp
        using True m_def order_less_le_trans by blast
      finally have "(1 - real_of_rat \<delta>) * m * y' < real t * real p" by simp
      hence f_2: "g' (h \<omega>) > (1 - real_of_rat \<delta>) * m"
        apply (simp add: h_3)
        by (subst pos_less_divide_eq, metis y'_pos, simp)
      have "abs (g' (h \<omega>) - real_of_rat (F 0 as)) < real_of_rat \<delta> * (real_of_rat (F 0 as))"
        apply (subst abs_less_iff) using f_1 f_2
        by (simp add:algebra_simps m_eq_F_0)
      thus "False"
        using est by linarith
    qed
    also have "... \<le> 1/9 + (1/9 + 1/9)"
      apply (rule pmf_add_2, rule case_1)
      by (rule pmf_add_2, rule case_2, rule case_3)
    also have "... = 1/3" by simp
    finally show ?thesis by simp
  next
    case False
    have "\<P>(\<omega> in measure_pmf \<Omega>\<^sub>1. real_of_rat \<delta> * real_of_rat (F 0 as) < \<bar>g' (h \<omega>) - real_of_rat (F 0 as)\<bar>) \<le>
      \<P>(\<omega> in measure_pmf \<Omega>\<^sub>1. \<exists>x \<in> set as. \<exists>y \<in> set as. x \<noteq> y \<and> 
      truncate_down r (real (hash p x \<omega>)) \<le> real p \<and> 
      truncate_down r (real (hash p x \<omega>)) = truncate_down r (real (hash p y \<omega>)))" 
    proof (rule pmf_mono_1)
      fix \<omega>
      assume a:"\<omega> \<in> {\<omega> \<in> space (measure_pmf \<Omega>\<^sub>1).
              real_of_rat \<delta> * real_of_rat (F 0 as) < \<bar>g' (h \<omega>) - real_of_rat (F 0 as)\<bar>}"
      assume b:"\<omega> \<in> set_pmf \<Omega>\<^sub>1" 
      have a_1: "card (set as) < t" using False by auto
      have a_2:"card (h \<omega>) = card ((\<lambda>x. truncate_down r (real (hash p x \<omega>))) ` (set as))"
        apply (simp add:h_def)
        apply (subst card_least, simp)
        apply (rule min.absorb4)
        using card_image_le a_1 order_le_less_trans[OF _ a_1] by blast
      have "card (h \<omega>) < t"
        by (metis List.finite_set  a_1 a_2 card_image_le  order_le_less_trans)
      hence "g' (h \<omega>) = card (h \<omega>)" by (simp add:g'_def)
      hence "card (h \<omega>) \<noteq> real_of_rat (F 0 as)"
        using a assms(2) apply simp 
        by (metis abs_zero cancel_comm_monoid_add_class.diff_cancel of_nat_less_0_iff pos_prod_lt zero_less_of_rat_iff)
      hence "card (h \<omega>) \<noteq> card (set as)"
        using m_def m_eq_F_0 by linarith
      hence "\<not>inj_on (\<lambda>x. truncate_down r (real (hash p x \<omega>))) (set as)"
        apply (simp add:a_2) 
        using card_image by blast
      moreover have "\<And>x. x \<in> set as \<Longrightarrow> truncate_down r (real (hash p x \<omega>)) \<le> real p"
      proof -
        fix x
        assume a:"x \<in> set as"
        show "truncate_down r (real (hash p x \<omega>)) \<le> real p"
          apply (rule truncate_down_le)
          using hash_range[OF p_ge_0 _ xs_le_p[OF a]]  b
          apply (simp add:\<Omega>\<^sub>1_def set_pmf_of_set[OF ne_bounded_degree_polynomials fin_bounded_degree_polynomials[OF p_ge_0]])
          using le_eq_less_or_eq by blast
      qed
     ultimately show "\<omega> \<in> {\<omega> \<in> space (measure_pmf \<Omega>\<^sub>1). \<exists>x \<in> set as. \<exists>y \<in> set as. x \<noteq> y \<and>
        truncate_down r (real (hash p x \<omega>)) \<le> real p \<and> 
        truncate_down r (real (hash p x \<omega>)) = truncate_down r (real (hash p y \<omega>))}"
       apply (simp add:inj_on_def) by blast
    qed
    also have "... \<le> 6 * (real (card (set as)))\<^sup>2 * (real p)\<^sup>2 * 2 powr - real r / (real p)\<^sup>2 + 1 / real p"
      apply (simp only:\<Omega>\<^sub>1_def)
      apply (rule f0_collision_prob)
        apply (metis p_prime)
       apply (rule subsetI, simp add:xs_le_p)
      using p_ge_0 r_ge_0 by simp+
    also have "... = 6 * (real (card (set as)))\<^sup>2 * 2 powr (- real r) + 1 / real p"
      apply (simp add:ac_simps power2_eq_square)
      using p_ge_0 by blast
    also have "... \<le> 6 * (real t)\<^sup>2 * 2 powr (-real r) + 1 / real p"
      apply (rule add_mono)
       apply (rule mult_right_mono)
        apply (rule mult_left_mono)
         apply (rule power_mono) using False apply simp
      by simp+
    also have "... \<le> 1/6 + 1/6"
      apply (rule add_mono)
      apply (subst pos_le_divide_eq, simp)
      using r_le_t2 apply simp
      using p_ge_18 by simp
    also have "... \<le> 1/3" by simp
    finally show ?thesis by simp
  qed

  have f0_result_elim: "\<And>x. f0_result (s, t, p, r, x, \<lambda>i\<in>{0..<s}. f0_sketch p r t (x i) as) =
    return_pmf (median s (\<lambda>i. g (f0_sketch p r t (x i) as)))"
    apply (simp add:g_def)
    apply (rule median_cong)
    by simp

  have real_g_2:"\<And>\<omega>. real_of_float ` f0_sketch p r t \<omega> as = h \<omega>" 
    apply (simp add:g_def g'_def h_def f0_sketch_def)
    apply (subst least_mono_commute, simp)
     apply (meson less_float.rep_eq strict_mono_onI)
    by (simp add:image_comp float_of_inverse[OF truncate_down_float])

  have card_eq: "\<And>\<omega>. card (f0_sketch p r t \<omega> as) = card (h \<omega>)" 
    apply (subst real_g_2[symmetric]) 
    apply (rule card_image[symmetric]) 
    using inj_on_def real_of_float_inject by blast

  have real_g: "\<And>\<omega>. real_of_rat (g (f0_sketch p r t \<omega> as)) = g' (h \<omega>)"
    apply (simp add:g_def g'_def card_eq of_rat_divide of_rat_mult of_rat_add real_of_rat_of_float)
    apply (rule impI)
    apply (subst mono_Max_commute[where f="real_of_float"])
    using less_eq_float.rep_eq mono_def apply blast
      apply (simp add:f0_sketch_def, simp add:least_def)
    using card_eq[symmetric] card_gt_0_iff t_ge_0 apply (simp, force) 
    by (simp add:real_g_2)
 
  have "1-real_of_rat \<epsilon> \<le> \<P>(\<omega> in measure_pmf \<Omega>\<^sub>0.
      \<bar>median s (\<lambda>i. g' (h (\<omega> i))) - real_of_rat (F 0 as)\<bar> \<le>  real_of_rat \<delta> * real_of_rat (F 0 as))"
    apply (rule prob_space.median_bound_2, simp add:prob_space_measure_pmf)
       using assms apply simp 
      apply (subst \<Omega>\<^sub>0_def)
      apply (rule indep_vars_restrict_intro [where f="\<lambda>j. {j}"], simp, simp add:disjoint_family_on_def, simp add: s_ge_0, simp, simp, simp)
     apply (simp add:s_def) using of_nat_ceiling apply blast
    apply simp
    apply (subst \<Omega>\<^sub>0_def)
    apply (subst prob_prod_pmf_slice, simp, simp)
    using b by (simp add:\<Omega>\<^sub>1_def) 
  also have "... = \<P>(\<omega> in measure_pmf \<Omega>\<^sub>0. 
      \<bar>median s (\<lambda>i. g (f0_sketch p r t (\<omega> i) as)) - F 0 as\<bar> \<le>  \<delta> * F 0 as)"
    apply (rule arg_cong2[where f="measure"], simp)
    apply (rule Collect_cong, simp, subst real_g[symmetric])
    apply (subst of_rat_mult[symmetric], subst median_rat[OF s_ge_0, symmetric])
    apply (subst of_rat_diff[symmetric], simp)
    using of_rat_less_eq by blast
  finally have a:"\<P>(\<omega> in measure_pmf \<Omega>\<^sub>0.  
      \<bar>median s (\<lambda>i. g (f0_sketch p r t (\<omega> i) as)) - F 0 as\<bar> \<le> \<delta> * F 0 as) \<ge> 1-real_of_rat \<epsilon>"
    by blast

  show ?thesis
    apply (subst M_def)
    apply (subst f0_alg_sketch[OF assms(1) assms(2)], simp)
    apply (simp add:t_def[symmetric] p_def[symmetric] r_def[symmetric] s_def[symmetric] map_pmf_def)
    apply (subst bind_assoc_pmf)
    apply (subst bind_return_pmf)
    apply (subst f0_result_elim)
    apply (subst map_pmf_def[symmetric])
    using a by (simp add:\<Omega>\<^sub>0_def[symmetric])
qed

fun f0_space_usage :: "(nat \<times> rat \<times> rat) \<Rightarrow> real" where
  "f0_space_usage (n, \<epsilon>, \<delta>) = (
    let s = nat \<lceil>-18 * ln (real_of_rat \<epsilon>)\<rceil> in 
    let r = nat (4 * \<lceil>log 2 (1 / real_of_rat \<delta>)\<rceil> + 24) in
    let t = nat \<lceil>80 / (real_of_rat \<delta>)\<^sup>2 \<rceil> in
    8 +
    2 * log 2 (real s + 1) +
    2 * log 2 (real t + 1) +
    2 * log 2 (real n + 10) +
    2 * log 2 (real r + 1) +
    real s * (12 + 4 * log 2 (10 + real n) +
    real t * (11 + 4 * r + 2 * log 2 (log 2 (real n + 9)))))"

definition encode_f0_state :: "f0_state \<Rightarrow> bool list option" where
  "encode_f0_state = 
    N\<^sub>S \<times>\<^sub>D (\<lambda>s. 
    N\<^sub>S \<times>\<^sub>S (
    N\<^sub>S \<times>\<^sub>D (\<lambda>p. 
    N\<^sub>S \<times>\<^sub>S ( 
    ([0..<s] \<rightarrow>\<^sub>S (list\<^sub>S (zfact\<^sub>S p))) \<times>\<^sub>S
    ([0..<s] \<rightarrow>\<^sub>S (set\<^sub>S F\<^sub>S))))))"

lemma "inj_on encode_f0_state (dom encode_f0_state)"
  apply (rule encoding_imp_inj)
  apply (simp add: encode_f0_state_def)
  apply (rule dependent_encoding, metis nat_encoding)
  apply (rule prod_encoding, metis nat_encoding)
  apply (rule dependent_encoding, metis nat_encoding)
  apply (rule prod_encoding, metis nat_encoding)
  apply (rule prod_encoding, metis encode_extensional list_encoding zfact_encoding)
  by (rule encode_extensional, rule encode_set, rule encode_float)

lemma f_subset:
  assumes "g ` A \<subseteq> h ` B"
  shows "(\<lambda>x. f (g x)) ` A \<subseteq> (\<lambda>x. f (h x)) ` B"
  using assms by auto

theorem f0_exact_space_usage:
  assumes "\<epsilon> \<in> {0<..<1}"
  assumes "\<delta> \<in> {0<..<1}"
  assumes "set as \<subseteq> {0..<n}"
  defines "M \<equiv> fold (\<lambda>a state. state \<bind> f0_update a) as (f0_init \<delta> \<epsilon> n)"
  shows "AE \<omega> in M. bit_count (encode_f0_state \<omega>) \<le> f0_space_usage (n, \<epsilon>, \<delta>)"
proof -
  define s where "s = nat \<lceil>-(18* ln (real_of_rat \<epsilon>))\<rceil>"
  define t where "t = nat \<lceil>80 / (real_of_rat \<delta>)\<^sup>2\<rceil>"
  define p where "p = find_prime_above (max n 19)"
  define r where "r = nat (4 * \<lceil>log 2 (1 / real_of_rat \<delta>)\<rceil> + 24)"

  have n_le_p: "n \<le> p" 
    apply (rule order_trans[where y="max n 19"], simp)
    apply (subst p_def)
    by (rule find_prime_above_lower_bound)

  have p_ge_0: "p > 0"
    apply (rule prime_gt_0_nat)
    by (simp add:p_def find_prime_above_is_prime)

  have p_le_n: "p \<le> 2*n + 19"
    apply (simp add:p_def)
    apply (cases "n \<le> 19", simp add:find_prime_above.simps) 
    apply (rule order_trans[where y="2*n+2"], simp add:find_prime_above_upper_bound[simplified])
    by simp

  have log_2_4: "log 2 4 = 2" 
    by (metis log2_of_power_eq mult_2 numeral_Bit0 of_nat_numeral power2_eq_square)

  have b_4_22: "\<And>y. y \<in> {0..<p} \<Longrightarrow> bit_count (F\<^sub>S (float_of (truncate_down r y))) \<le> 
    ereal (10 + 4 * real r + 2 * log 2 (log 2 (n+9)))" 
  proof -
    fix y
    assume a:"y \<in> {0..<p}"

    show " bit_count (F\<^sub>S (float_of (truncate_down r y))) \<le> ereal (10 + 4 * real r + 2 * log 2 (log 2 (n+9)))" 
    proof (cases "y \<ge> 1")
      case True

      have b_4_23: "0 < 2 + log 2 (real p)" 
       apply (rule order_less_le_trans[where y="2+log 2 1"], simp)
       using p_ge_0 by simp

      have "bit_count (F\<^sub>S (float_of (truncate_down r y))) \<le>  ereal (8 + 4 * real r + 2 * log 2 (2 + \<bar>log 2 \<bar>real y\<bar>\<bar>))"
        by (rule truncate_float_bit_count)
      also have "... \<le> ereal (8 + 4 * real r + 2 * log 2 (2 + log 2 p))"
        apply (simp)
        apply (subst log_le_cancel_iff, simp, simp, simp add:b_4_23)
        apply (subst abs_of_nonneg) using True apply simp
        apply (simp, subst log_le_cancel_iff, simp, simp) using True apply simp
         apply (simp add:p_ge_0)
        using a by simp
      also have "... \<le> ereal (8 + 4 * real r + 2 * log 2 (log 2 4 + log 2 (2 * n + 19)))"
        apply simp
        apply (subst log_le_cancel_iff, simp, simp add:_b_4_23)
         apply (rule add_pos_pos, simp, simp)
        apply (rule add_mono)
         apply (metis dual_order.refl log2_of_power_eq mult_2 numeral_Bit0 of_nat_numeral power2_eq_square)
        apply (subst log_le_cancel_iff, simp, simp add:p_ge_0, simp)
        using p_le_n by simp
      also have "... \<le> ereal (8 + 4 * real r + 2 * log 2 (log 2 ((n+9) powr 2)))"
        apply simp
        apply (subst log_le_cancel_iff, simp, rule add_pos_pos, simp, simp, simp)
        apply (subst log_mult[symmetric], simp, simp, simp, simp)
        by (subst log_le_cancel_iff, simp, simp, simp, simp add:power2_eq_square algebra_simps)
      also have "... = ereal (10 +  4 * real r + 2 * log 2 (log 2 (n + 9)))"
        apply (subst log_powr, simp)
        apply (simp)
        apply (subst (3) log_2_4[symmetric]) 
        by (subst log_mult, simp, simp, simp, simp, simp add:log_2_4)
      finally show ?thesis by simp
    next
      case False
      hence "y = 0" using a by simp
      then show ?thesis by (simp add:float_bit_count_zero)
    qed
  qed

  have b: 
    "\<And>x. x \<in> ({0..<s} \<rightarrow>\<^sub>E bounded_degree_polynomials (ZFact (int p)) 2) \<Longrightarrow>
        bit_count (encode_f0_state (s, t, p, r, x, \<lambda>i\<in>{0..<s}. f0_sketch p r t (x i) as)) \<le> 
        f0_space_usage (n, \<epsilon>, \<delta>)"
  proof -
    fix x
    assume b_1:"x \<in> {0..<s} \<rightarrow>\<^sub>E bounded_degree_polynomials (ZFact (int p)) 2"
    have b_2: "x \<in> extensional {0..<s}" using b_1 by (simp add:PiE_def) 

    have "\<And>y. y \<in> {0..<s} \<Longrightarrow> card (f0_sketch p r t (x y) as) \<le> t "
      apply (simp add:f0_sketch_def)
      apply (subst card_least, simp)
      by simp

    hence b_3: "\<And>y. y \<in> (\<lambda>z. f0_sketch p r t (x z) as) ` {0..<s} \<Longrightarrow> card y \<le> t"
      by force

    have "\<And>y. y \<in> {0..<s} \<Longrightarrow> f0_sketch p r t (x y) as \<subseteq> (\<lambda>k. float_of (truncate_down r k)) ` {0..<p} "
      apply (simp add:f0_sketch_def)
      apply (rule order_trans[OF least_subset])
      apply (rule f_subset[where f="\<lambda>x. float_of (truncate_down r (real x))"])
      apply (rule image_subsetI, simp)
      apply (rule hash_range[OF p_ge_0, where n="2"])
       using b_1 apply (simp add: PiE_iff)
      by (metis assms(3) n_le_p order_less_le_trans atLeastLessThan_iff subset_eq)
    hence b_4: "\<And>y. y \<in> (\<lambda>z. f0_sketch p r t (x z) as) ` {0..<s} \<Longrightarrow> 
      y \<subseteq> (\<lambda>k. float_of (truncate_down r k)) ` {0..<p}"
      by force

    have b_4_1: "\<And>y z . y \<in> (\<lambda>z. f0_sketch p r t (x z) as) ` {0..<s} \<Longrightarrow> z \<in> y \<Longrightarrow> 
      bit_count (F\<^sub>S z) \<le> ereal (10 + 4 * real r + 2 * log 2 (log 2 (n+9)))"
      using b_4_22 b_4 by blast

    have "\<And>y. y \<in> {0..<s} \<Longrightarrow> finite (f0_sketch p r t (x y) as)"
      apply (simp add:f0_sketch_def)
      by (rule finite_subset[OF least_subset], simp)
    hence b_5: "\<And>y. y \<in> (\<lambda>z. f0_sketch p r t (x z) as) ` {0..<s} \<Longrightarrow> finite y" by force

    have "bit_count (encode_f0_state (s, t, p, r, x, \<lambda>i\<in>{0..<s}. f0_sketch p r t (x i) as)) =
      bit_count (N\<^sub>S s) + bit_count (N\<^sub>S t) +  bit_count (N\<^sub>S p) + bit_count (N\<^sub>S r) +
      bit_count (list\<^sub>S (list\<^sub>S (zfact\<^sub>S p)) (map x [0..<s])) +
      bit_count (list\<^sub>S (set\<^sub>S F\<^sub>S) (map (\<lambda>i\<in>{0..<s}. f0_sketch p r t (x i) as) [0..<s]))"
      apply (simp add:b_2 encode_f0_state_def dependent_bit_count prod_bit_count
        s_def[symmetric] t_def[symmetric] p_def[symmetric] r_def[symmetric] fun\<^sub>S_def
        del:N\<^sub>S.simps encode_prod.simps encode_dependent_sum.simps)
      by (simp add:ac_simps del:N\<^sub>S.simps encode_prod.simps encode_dependent_sum.simps)
    also have "... \<le> ereal (2* log 2 (real s + 1) + 1) + ereal  (2* log 2 (real t + 1) + 1)
      + ereal (2* log 2 (real p + 1) + 1) + ereal (2 * log 2 (real r + 1) + 1)
      + (ereal (real s) * (ereal (real 2 * (2 * log 2 (real p) + 2) + 1) + 1) + 1) 
      + (ereal (real s) * ((ereal (real t) * (ereal (10 + 4 * real r + 2 * log 2 (log 2 (real (n + 9))))
           + 1) + 1) + 1) + 1)"
      apply (rule add_mono, rule add_mono, rule add_mono, rule add_mono, rule add_mono)
           apply (metis nat_bit_count)
          apply (metis nat_bit_count)
         apply (metis nat_bit_count)
        apply (metis nat_bit_count)
       apply (rule list_bit_count_est[where xs="map x [0..<s]", simplified])
       apply (rule bounded_degree_polynomial_bit_count[OF p_ge_0]) using b_1 apply blast
      apply (rule list_bit_count_est[where xs="map (\<lambda>i\<in>{0..<s}. f0_sketch p r t (x i) as) [0..<s]", simplified])
      apply (rule set_bit_count_est, metis b_5, metis b_3)
      apply simp 
      by (metis b_4_1)
    also have "... = ereal ( 6 + 2 * log 2 (real s + 1) + 2 * log 2 (real t + 1) + 
      2 * log 2 (real p + 1) + 2 * log 2 (real r + 1) + real s * (8 + 4 * log 2 (real p) + 
      real t * (11 + (4 * real r + 2 * log 2 (log 2 (real n + 9))))))"
      apply (simp)
      by (subst distrib_left[symmetric], simp) 
    also have "... \<le> ereal ( 6 + 2 * log 2 (real s + 1)  + 2 * log 2 (real t + 1) + 
      2 * log 2 (2 * (10 + real n)) + 2 * log 2 (real r + 1) + real s * (8 + 4 * log 2 (2 * (10 + real n)) + 
      real t * (11 + (4 * real r + 2 * log 2 (log 2 (real n + 9))))))"
      apply (simp, rule add_mono, simp) using p_le_n apply simp
      apply (rule mult_left_mono, simp)
       apply (subst log_le_cancel_iff, simp, simp add:p_ge_0, simp)
       using p_le_n apply simp
      by simp
    also have "... \<le> f0_space_usage (n, \<epsilon>, \<delta>)"
      apply (subst log_mult, simp, simp, simp)
      apply (subst log_mult, simp, simp, simp)
      apply (simp add:s_def[symmetric] r_def[symmetric] t_def[symmetric])
      by (simp add:algebra_simps)
    finally show "bit_count (encode_f0_state (s, t, p, r, x, \<lambda>i\<in>{0..<s}. f0_sketch p r t (x i) as)) \<le> 
        f0_space_usage (n, \<epsilon>, \<delta>)" by simp
  qed
  
  have a:"\<And>y. y \<in> (\<lambda>x. (s, t, p, r, x, \<lambda>i\<in>{0..<s}. f0_sketch p r t (x i) as)) `
             ({0..<s} \<rightarrow>\<^sub>E bounded_degree_polynomials (ZFact (int p)) 2) \<Longrightarrow>
         bit_count (encode_f0_state y) \<le> f0_space_usage (n, \<epsilon>, \<delta>)"
    using b apply (simp add:image_def del:f0_space_usage.simps) by blast

  show ?thesis
    apply (subst AE_measure_pmf_iff, rule ballI)
    apply (subst (asm) M_def)
    apply (subst (asm) f0_alg_sketch[OF assms(1) assms(2)], simp)
    apply (simp add:s_def[symmetric] t_def[symmetric] p_def[symmetric] r_def[symmetric])
    apply (subst (asm) set_prod_pmf, simp)
    apply (simp add:comp_def)
    apply (subst (asm) set_pmf_of_set)
      apply (metis ne_bounded_degree_polynomials)
     apply (metis fin_bounded_degree_polynomials[OF p_ge_0])
    using a
    by (simp add:s_def[symmetric] t_def[symmetric] p_def[symmetric] r_def[symmetric])
qed

lemma f0_asympotic_space_complexity:
  "f0_space_usage \<in> O[at_top \<times>\<^sub>F at_right 0 \<times>\<^sub>F at_right 0](\<lambda>(n, \<epsilon>, \<delta>). ln (1 / of_rat \<epsilon>) * 
  (ln (real n) + 1 / (of_rat \<delta>)\<^sup>2 * (ln (ln (real n)) + ln (1 / of_rat \<delta>))))"
  (is "_ \<in> O[?F](?rhs)")
proof -
  define n_of :: "nat \<times> rat \<times> rat \<Rightarrow> nat" where "n_of = (\<lambda>(n, \<epsilon>, \<delta>). n)"
  define \<epsilon>_of :: "nat \<times> rat \<times> rat \<Rightarrow> rat" where "\<epsilon>_of = (\<lambda>(n, \<epsilon>, \<delta>). \<epsilon>)"
  define \<delta>_of :: "nat \<times> rat \<times> rat \<Rightarrow> rat" where "\<delta>_of = (\<lambda>(n, \<epsilon>, \<delta>). \<delta>)"

  define g where "g = (\<lambda>x. ln (1 / of_rat (\<epsilon>_of x)) * 
    (ln (real (n_of x)) + 1 / (of_rat (\<delta>_of x))\<^sup>2 * (ln (ln (real (n_of x))) + ln (1 / of_rat (\<delta>_of x)))))"

  have n_inf: "\<And>c. eventually (\<lambda>x. c \<le> (real (n_of x))) ?F" 
    apply (simp add:n_of_def case_prod_beta')
    apply (subst eventually_prod1', simp add:prod_filter_eq_bot)
    by (meson eventually_at_top_linorder nat_ceiling_le_eq)

  have delta_inf: "\<And>c. eventually (\<lambda>x. c \<le> 1 / (real_of_rat (\<delta>_of x))) ?F"
    apply (simp add:\<delta>_of_def case_prod_beta')
    apply (subst eventually_prod2', simp)
    apply (subst eventually_prod2', simp)
    by (rule inv_at_right_0_inf)

  have eps_inf: "\<And>c. eventually (\<lambda>x. c \<le> 1 / (real_of_rat (\<epsilon>_of x))) ?F"
    apply (simp add:\<epsilon>_of_def case_prod_beta')
    apply (subst eventually_prod2', simp)
    apply (subst eventually_prod1', simp)
    by (rule inv_at_right_0_inf)

  have zero_less_eps: "eventually (\<lambda>x. 0 < (real_of_rat (\<epsilon>_of x))) ?F"
    apply (simp add:\<epsilon>_of_def case_prod_beta')
    apply (subst eventually_prod2', simp)
    apply (subst eventually_prod1', simp)
    by (rule eventually_at_rightI[where b="1"], simp, simp)

  have zero_less_delta: "eventually (\<lambda>x. 0 < (real_of_rat (\<delta>_of x))) ?F"
    apply (simp add:\<delta>_of_def case_prod_beta')
    apply (subst eventually_prod2', simp)
    apply (subst eventually_prod2', simp)
    by (rule eventually_at_rightI[where b="1"], simp, simp)

  have l1: "\<forall>\<^sub>F x in ?F. 0 \<le> (ln (ln (real (n_of x))) + ln (1 / real_of_rat (\<delta>_of x))) / (real_of_rat (\<delta>_of x))\<^sup>2"
    apply (rule eventually_nonneg_div)
     apply (rule eventually_nonneg_add)
     apply (rule eventually_ln_ge_iff, rule eventually_ln_ge_iff[OF n_inf])
    apply (rule eventually_ln_ge_iff[OF delta_inf])
    by (rule eventually_mono[OF zero_less_delta], simp)

  have unit_1: "(\<lambda>_. 1) \<in> O[?F](\<lambda>x. 1 / (real_of_rat (\<delta>_of x))\<^sup>2)" 
    apply (rule landau_o.big_mono, simp)
    apply (rule eventually_mono[OF eventually_conj[OF delta_inf[where c="1"] zero_less_delta]])
    by (metis one_le_power power_one_over)

  have unit_2: "(\<lambda>_. 1) \<in> O[?F](\<lambda>x. ln (1 / real_of_rat (\<delta>_of x)))"
    apply (rule landau_o.big_mono, simp)
    apply (rule eventually_mono[OF eventually_conj[OF delta_inf[where c="exp 1"] zero_less_delta]])
    apply (subst abs_of_nonneg)
     apply (rule ln_ge_zero)
    apply (meson dual_order.trans one_le_exp_iff rel_simps(44))
    by (simp add: ln_ge_iff)

  have unit_3: "(\<lambda>_. 1) \<in> O[?F](\<lambda>x. real (n_of x))"
    by (rule landau_o.big_mono, simp, rule n_inf)

  have unit_4: "(\<lambda>_. 1) \<in> O[?F](\<lambda>x. ln (1 / real_of_rat (\<epsilon>_of x)))"
    apply (rule landau_o.big_mono, simp)
    apply (rule eventually_mono[OF eventually_conj[OF eps_inf[where c="exp 1"] zero_less_eps]])
    apply (subst abs_of_nonneg)
     apply (rule ln_ge_zero)
    using one_le_exp_iff order_trans_rules(23) apply blast
    by (simp add: ln_ge_iff)

  have unit_5: "(\<lambda>_. 1) \<in> O[?F](\<lambda>x. 1 / real_of_rat (\<epsilon>_of x))"
    apply (rule landau_o.big_mono, simp)
    apply (rule eventually_mono[OF eventually_conj[OF eps_inf[where c="1"] zero_less_eps]])
    by simp

  have unit_6: "(\<lambda>_. 1) \<in> O[?F](\<lambda>x. ln (real (n_of x)))" 
    apply (rule landau_o.big_mono, simp)
    apply (rule eventually_mono[OF n_inf[where c="exp 1"]])
    apply (subst abs_of_nonneg)
    apply (rule ln_ge_zero)
     apply (metis less_one not_exp_le_zero not_le of_nat_eq_0_iff of_nat_ge_1_iff)
    by (metis less_eq_real_def ln_ge_iff not_exp_le_zero of_nat_0_le_iff)

  have unit_7: "(\<lambda>_. 1) \<in> O[?F](\<lambda>x. ln (real (n_of x)) + (ln (ln (real (n_of x))) + ln (1 / real_of_rat (\<delta>_of x))) / (real_of_rat (\<delta>_of x))\<^sup>2)"
    apply (rule landau_sum_1)
      apply (rule eventually_ln_ge_iff[OF n_inf])
     apply (rule l1)
    by (rule unit_6)

  have unit_8: "(\<lambda>_. 1) \<in> O[?F](g)" 
    apply (simp add:g_def)
    apply (rule landau_o.big_mult_1[OF unit_4])
    by (rule unit_7)

  have l2: "(\<lambda>x. ln (real (nat \<lceil>- (18 * ln (real_of_rat (\<epsilon>_of x)))\<rceil>) + 1)) \<in> O[?F](g)" 
    apply (simp add:g_def)
    apply (rule landau_o.big_mult_1)
     apply (rule landau_ln_2[where a="2"], simp, simp)
      apply (rule eps_inf)
    apply (rule sum_in_bigo)
      apply (rule landau_nat_ceil[OF unit_5])
    apply (subst minus_mult_right)
      apply (subst cmult_in_bigo_iff, rule disjI2)
      apply (subst landau_o.big.in_cong[where f="\<lambda>x. - ln (real_of_rat (\<epsilon>_of x))" and g="\<lambda>x. ln (1 / real_of_rat (\<epsilon>_of x))"])
       apply (rule eventually_mono[OF zero_less_eps], simp add:ln_div)
      apply (rule landau_ln_3[OF eps_inf], simp, rule unit_5)
    by (rule unit_7)

  have l3: "(\<lambda>x. ln (real (nat \<lceil>80 / (real_of_rat (\<delta>_of x))\<^sup>2\<rceil>) + 1)) \<in> O[?F](g)"
    apply (simp add:g_def)
    apply (rule landau_o.big_mult_1'[OF unit_4])
    apply (rule landau_sum_2)
      apply (rule eventually_ln_ge_iff[OF n_inf])
    apply (rule l1)
    apply (subst (3) div_commute)
    apply (rule landau_o.big_mult_1)
     apply (rule landau_ln_3, simp)
     apply (rule sum_in_bigo)
      apply (rule landau_nat_ceil[OF unit_1])
     apply (rule landau_const_inv, simp, simp, rule unit_1)
    apply (rule landau_sum_2)
      apply (rule eventually_ln_ge_iff[OF eventually_ln_ge_iff[OF n_inf]])
     apply (rule eventually_ln_ge_iff[OF delta_inf])
    by (rule unit_2)

  have unit_9: "(\<lambda>_. 1) \<in> O[?F](\<lambda>x. ln (real (n_of x)))" 
    apply (rule landau_o.big_mono, simp)
    apply (rule eventually_mono[OF n_inf[where c="exp 1"]])
    by (metis abs_ge_self less_eq_real_def ln_ge_iff not_exp_le_zero of_nat_0_le_iff order.trans)

  have l4: "(\<lambda>x. ln (10 + real (n_of x))) \<in> O[?F](\<lambda>x. ln (real (n_of x)))"
    apply (rule landau_ln_2[where a="2"], simp, simp, rule n_inf)
    by (rule sum_in_bigo, simp add:unit_3, simp)

  have l5: "(\<lambda>x. ln (real (n_of x) + 10)) \<in> O[?F](g)"
    apply (simp add:g_def)
    apply (rule landau_o.big_mult_1'[OF unit_4])
    apply (rule landau_sum_1)
      apply (rule eventually_ln_ge_iff[OF n_inf])
     apply (rule l1)
    apply (rule landau_ln_2[where a="2"], simp, simp, rule n_inf)
    by (rule sum_in_bigo, simp, simp add:unit_3)
  
  have l6: "(\<lambda>x. log 2 (real (nat (4 * \<lceil>log 2 (1 / real_of_rat (\<delta>_of x))\<rceil> + 24)) + 1)) \<in> O[?F](g)"
    apply (simp add:g_def log_def, rule landau_o.big_mult_1'[OF unit_4], rule landau_sum_2)
      apply (rule eventually_ln_ge_iff[OF n_inf])
     apply (rule l1)
    apply (subst (4) div_commute)
    apply (rule landau_o.big_mult_1)
     apply (rule landau_ln_3, simp)
     apply (rule sum_in_bigo)
      apply (rule landau_real_nat, simp)
      apply (rule sum_in_bigo)
       apply (simp, rule landau_ceil[OF unit_1], simp, rule landau_ln_3[OF delta_inf])
       apply (rule landau_o.big_mono)
       apply (rule eventually_mono[OF eventually_conj[OF delta_inf[where c="1"] zero_less_delta]])
       apply (simp, metis pos2 power_one_over self_le_power)
      apply (simp add:unit_1)
     apply (simp add:unit_1)
    apply (rule landau_sum_2)
      apply (rule eventually_ln_ge_iff, rule eventually_ln_ge_iff[OF n_inf])
     apply (rule eventually_ln_ge_iff[OF delta_inf])
    by (rule unit_2)

  have l7: "(\<lambda>x. real (nat \<lceil>- (18 * ln (real_of_rat (\<epsilon>_of x)))\<rceil>)) \<in> O[?F](\<lambda>x. ln (1 / real_of_rat (\<epsilon>_of x)))"
    apply (rule landau_nat_ceil, rule unit_4)
    apply (subst minus_mult_right)
    apply (subst cmult_in_bigo_iff, rule disjI2)
    apply (rule landau_o.big_mono)
    apply (rule eventually_mono[OF zero_less_eps])
    by (subst ln_div, simp, simp, simp)

  have l8: "(\<lambda>x. real (nat \<lceil>80 / (real_of_rat (\<delta>_of x))\<^sup>2\<rceil>) * 
    (11 + 4 * real (nat (4 * \<lceil>log 2 (1 / real_of_rat (\<delta>_of x))\<rceil> + 24)) + 
    2 * log 2 (log 2 (real (n_of x) + 9))))
    \<in> O[?F](\<lambda>x. (ln (ln (real (n_of x))) + ln (1 / real_of_rat (\<delta>_of x))) / (real_of_rat (\<delta>_of x))\<^sup>2)"
    apply (subst (4) div_commute)
    apply (rule landau_o.mult)
     apply (rule landau_nat_ceil[OF unit_1], rule landau_const_inv, simp, simp)
    apply (subst (3) add.commute)
    apply (rule landau_sum)
       apply (rule eventually_ln_ge_iff, rule eventually_ln_ge_iff, rule n_inf)
      apply (rule eventually_ln_ge_iff, rule delta_inf, simp add:log_def)
     apply (rule landau_ln_2[where a="2"], simp)
       apply (subst pos_le_divide_eq, simp, simp)
      apply (rule eventually_mono[OF n_inf[where c="exp 2"]])
      apply (subst ln_ge_iff, metis less_eq_real_def not_exp_le_zero of_nat_0_le_iff)
      apply simp
     apply (simp, rule landau_ln_2[where a="2"], simp, simp, rule n_inf)
     apply (rule sum_in_bigo, simp, simp add:unit_3)
    apply (rule sum_in_bigo, simp add:unit_2)
    apply (simp, rule landau_real_nat, simp)
    apply (rule sum_in_bigo, simp)
    by (rule landau_ceil[OF unit_2], simp add:log_def, simp add:unit_2)

  have "f0_space_usage = (\<lambda>x. f0_space_usage (n_of x, \<epsilon>_of x, \<delta>_of x))"
    apply (rule ext)
    by (simp add:case_prod_beta' n_of_def \<epsilon>_of_def \<delta>_of_def)
  also have "... \<in>  O[?F](g)"
    apply (simp add:Let_def)
    apply (rule sum_in_bigo_r) 
     apply (simp add:g_def)
     apply (rule landau_o.mult, simp add:l7)
     apply (rule landau_sum)
        apply (rule eventually_ln_ge_iff[OF n_inf])
       apply (rule l1)
      apply (rule sum_in_bigo_r, simp add:log_def l4, simp add:unit_9)
     apply (simp add:l8)
    apply (rule sum_in_bigo_r, simp add:l6)
    apply (rule sum_in_bigo_r, simp add:log_def l5)
    apply (rule sum_in_bigo_r, simp add:log_def l3)
    apply (rule sum_in_bigo_r, simp add:log_def l2)
    by (simp add:unit_8)
  also have "... = O[?F](?rhs)"
    apply (rule arg_cong2[where f="bigo"], simp)
    apply (rule ext)
    by (simp add:case_prod_beta' g_def n_of_def \<epsilon>_of_def \<delta>_of_def)
  finally show ?thesis
    by simp
qed

end

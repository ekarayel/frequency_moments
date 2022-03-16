section \<open>Frequency Moment $0$\<close>

theory Frequency_Moment_0
  imports Main Primes_Ext Float_Ext Median_Method.Median K_Smallest 
    Universal_Hash_Families.Carter_Wegman_Hash_Family Encoding
    Frequency_Moments Landau_Ext Product_PMF_Ext
    Universal_Hash_Families.Field
begin

text \<open>This section contains a formalization of the algorithm for the zero-th frequency moment.
It is a KMV-type ($k$-minimum value) algorithm with a rounding method to match the space complexity 
of the best algorithm described in \cite{baryossef2002}.\<close>

text \<open>In addition to the Isabelle proof here, there is also an informal hand-writtend proof in
Appendix~\ref{sec:f0_proof}.\<close>

type_synonym f0_state = "nat \<times> nat \<times> nat \<times> nat \<times> (nat \<Rightarrow> nat list) \<times> (nat \<Rightarrow> float set)"

definition hash where "hash p = ring.hash (mod_ring p)"

fun f0_init :: "rat \<Rightarrow> rat \<Rightarrow> nat \<Rightarrow> f0_state pmf" where
  "f0_init \<delta> \<epsilon> n =
    do {
      let s = nat \<lceil>-18 * ln (real_of_rat \<epsilon>)\<rceil>;
      let t = nat \<lceil>80 / (real_of_rat \<delta>)\<^sup>2\<rceil>;
      let p = find_prime_above (max n 19);
      let r = nat (4 * \<lceil>log 2 (1 / real_of_rat \<delta>)\<rceil> + 23); 
      h \<leftarrow> prod_pmf {..<s} (\<lambda>_. pmf_of_set (bounded_degree_polynomials (mod_ring p) 2));
      return_pmf (s, t, p, r, h, (\<lambda>_ \<in> {0..<s}. {}))
    }"

fun f0_update :: "nat \<Rightarrow> f0_state \<Rightarrow> f0_state pmf" where
  "f0_update x (s, t, p, r, h, sketch) = 
    return_pmf (s, t, p, r, h, \<lambda>i \<in> {..<s}.
      least t (insert (float_of (truncate_down r (hash p x (h i)))) (sketch i)))"

fun f0_result :: "f0_state \<Rightarrow> rat pmf" where
  "f0_result (s, t, p, r, h, sketch) = return_pmf (median s (\<lambda>i \<in> {..<s}.
      (if card (sketch i) < t then of_nat (card (sketch i)) else
        rat_of_nat t* rat_of_nat p / rat_of_float (Max (sketch i)))
    ))"

fun f0_space_usage :: "(nat \<times> rat \<times> rat) \<Rightarrow> real" where
  "f0_space_usage (n, \<epsilon>, \<delta>) = (
    let s = nat \<lceil>-18 * ln (real_of_rat \<epsilon>)\<rceil> in 
    let r = nat (4 * \<lceil>log 2 (1 / real_of_rat \<delta>)\<rceil> + 23) in
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
    ([0..<s] \<rightarrow>\<^sub>S (list\<^sub>S N\<^sub>S)) \<times>\<^sub>S
    ([0..<s] \<rightarrow>\<^sub>S (set\<^sub>S F\<^sub>S))))))"

lemma "inj_on encode_f0_state (dom encode_f0_state)"
proof -
  have "is_encoding encode_f0_state" 
    unfolding encode_f0_state_def
    by (intro dependent_encoding nat_encoding encode_extensional list_encoding encode_set encode_float)
  thus ?thesis  by (rule encoding_imp_inj)
qed

context
  fixes \<epsilon> \<delta> :: rat
  fixes n :: nat
  fixes as :: "nat list"
  fixes result
  assumes \<epsilon>_range: "\<epsilon> \<in> {0<..<1}"
  assumes \<delta>_range: "\<delta> \<in> {0<..<1}"
  assumes as_range: "set as \<subseteq> {..<n}"
  defines "result \<equiv> fold (\<lambda>a state. state \<bind> f0_update a) as (f0_init \<delta> \<epsilon> n) \<bind> f0_result"
begin  

private definition t where "t = nat \<lceil>80 / (real_of_rat \<delta>)\<^sup>2\<rceil>"
private lemma t_ge_0: "t > 0" using \<delta>_range by (simp add:t_def)

private definition s where "s = nat \<lceil>-(18 * ln (real_of_rat \<epsilon>))\<rceil>"
private lemma s_ge_0: "s > 0" using \<epsilon>_range by (simp add:s_def)

private definition p where "p = find_prime_above (max n 19)"

private lemma p_prime:"Factorial_Ring.prime p"
  using p_def find_prime_above_is_prime by presburger

private lemma p_ge_18: "p \<ge> 18"
proof -
  have "p \<ge> 19" 
    by (metis p_def find_prime_above_lower_bound max.bounded_iff)
  thus ?thesis by simp
qed

private lemma p_ge_0: "p > 0" using p_ge_18 by simp
private lemma p_ge_1: "p > 1" using p_ge_18 by simp

private lemma n_le_p: "n \<le> p"
proof -
  have "n \<le> max n 19" by simp
  also have "... \<le> p"
    unfolding p_def by (rule find_prime_above_lower_bound)
  finally show ?thesis by simp
qed

private lemma p_le_n: "p \<le> 2*n + 19"
proof (cases "n \<le> 19")
  case True
  then show ?thesis by (simp add:p_def find_prime_above.simps)
next
  case False
  hence "p \<le> 2*n + 2"
    using find_prime_above_upper_bound
    by (simp add:p_def)
  also have "... \<le> 2*n+19"
    by simp
  finally show ?thesis by simp
qed

private lemma as_lt_p: "\<And>x. x \<in> set as \<Longrightarrow> x < p" 
  using as_range atLeastLessThan_iff
  by (intro order_less_le_trans[OF _ n_le_p]) blast

private lemma as_subset_p: "set as \<subseteq> {..<p}"
   using as_lt_p  by (simp add: subset_iff)

private definition r where "r = nat (4 * \<lceil>log 2 (1 / real_of_rat \<delta>)\<rceil> + 23)"

private lemma r_bound: "4 * log 2 (1 / real_of_rat \<delta>) + 23 \<le> r"
proof -
  have "0 \<le> log 2 (1 / real_of_rat \<delta>)" using \<delta>_range by simp 
  hence "0 \<le> \<lceil>log 2 (1 / real_of_rat \<delta>)\<rceil>" by simp
  hence "0 \<le> 4 * \<lceil>log 2 (1 / real_of_rat \<delta>)\<rceil> + 23"
    by (intro add_nonneg_nonneg mult_nonneg_nonneg, auto)
  thus ?thesis by (simp add:r_def)
qed

private lemma r_ge_23: "r \<ge> 23"
proof -
  have "(23::real) = 0 + 23" by simp
  also have "... \<le> 4 * log 2 (1 / real_of_rat \<delta>) + 23" 
    using \<delta>_range by (intro add_mono mult_nonneg_nonneg, auto) 
  also have "... \<le> r" using r_bound by simp
  finally show "23 \<le> r" by simp
qed

private lemma two_pow_r_le_1: "0 < 1 - 2 powr - real r"
proof -
  have a: "2 powr (0::real) = 1"
    by simp
  show ?thesis using r_ge_23 
    by (simp, subst a[symmetric], intro powr_less_mono, auto)
qed

interpretation carter_wegman_hash_family "mod_ring p" 2
  rewrites "ring.hash (mod_ring p) = Frequency_Moment_0.hash p"
  using carter_wegman_hash_familyI[OF mod_ring_is_field mod_ring_finite]
  using hash_def p_prime by auto

private definition tr_hash where "tr_hash x \<omega> = truncate_down r (hash x \<omega>)"

private definition f0_sketch where (* Rename to sketch_rv *)
  "f0_sketch \<omega> = least t ((\<lambda>x. float_of (tr_hash x \<omega>)) ` set as)"

private definition estimate (* Should be directly applied to f0_sketch - abstract over type! *)
   where "estimate S = (if card S < t then of_nat (card S) else of_nat t * of_nat p / rat_of_float (Max S))"

private definition sketch_rv' where "sketch_rv' \<omega> = least t ((\<lambda>x. tr_hash x \<omega>) ` set as)"
private definition estimate' where "estimate' S = (if card S < t then real (card S) else real t * real p / Max S)"

private definition \<Omega>\<^sub>0 where "\<Omega>\<^sub>0 = prod_pmf {..<s} (\<lambda>_. pmf_of_set space)"

private lemma f0_alg_sketch:
  defines "sketch \<equiv> fold (\<lambda>a state. state \<bind> f0_update a) as (f0_init \<delta> \<epsilon> n)"
  shows "sketch = map_pmf (\<lambda>x. (s,t,p,r, x, \<lambda>i \<in> {..<s}. f0_sketch (x i))) \<Omega>\<^sub>0" 
  unfolding f0_sketch_def 
proof (subst sketch_def, induction as rule:rev_induct)
  case Nil
  then show ?case
    by (simp add:s_def p_def[symmetric] map_pmf_def t_def r_def Let_def least_def restrict_def space_def \<Omega>\<^sub>0_def)
next
  case (snoc x xs)
  let ?sketch = "\<lambda>\<omega> xs. least t ((\<lambda>a. float_of (tr_hash a \<omega>)) ` set xs)"
  have "fold (\<lambda>a state. state \<bind> f0_update a) (xs @ [x]) (f0_init \<delta> \<epsilon> n) =
     (map_pmf (\<lambda>\<omega>. (s, t, p, r, \<omega>, \<lambda>i \<in> {..<s}. ?sketch (\<omega> i) xs)) \<Omega>\<^sub>0) \<bind> f0_update x"
    by (simp add: restrict_def snoc del:f0_init.simps)
  also have "... = \<Omega>\<^sub>0 \<bind> (\<lambda>\<omega>. f0_update x (s, t, p, r, \<omega>, \<lambda>i\<in>{..<s}. ?sketch (\<omega> i) xs)) "
    by (simp add:map_pmf_def bind_assoc_pmf bind_return_pmf del:f0_update.simps)
  also have "... = map_pmf (\<lambda>\<omega>. (s, t, p, r, \<omega>, \<lambda>i\<in>{..<s}. ?sketch (\<omega> i) (xs@[x]))) \<Omega>\<^sub>0"
    by (simp add:least_insert map_pmf_def tr_hash_def cong:restrict_cong)
  finally show ?case by blast
qed

private lemma abs_ge_iff: "((x::real) \<le> abs y) = (x \<le> y \<or> x \<le> -y)"
  by linarith

private lemma card_nat_in_ball:
  fixes x :: nat
  fixes q :: real
  assumes "q \<ge> 0"
  defines "A \<equiv> {k. abs (real x - real k) \<le> q \<and> k \<noteq> x}"
  shows "real (card A) \<le> 2 * q" and "finite A"
proof -
  have a: "of_nat x \<in> {\<lceil>real x-q\<rceil>..\<lfloor>real x+q\<rfloor>}"
    using assms 
    by (simp add: ceiling_le_iff)
  have "card A = card (int ` A)"
    by (rule card_image[symmetric], simp)
  also have "... \<le> card ({\<lceil>real x-q\<rceil>..\<lfloor>real x+q\<rfloor>} - {of_nat x})"
    by (intro card_mono image_subsetI, simp_all add:A_def abs_le_iff, linarith)
  also have "... = card {\<lceil>real x-q\<rceil>..\<lfloor>real x+q\<rfloor>} - 1"
    by (rule card_Diff_singleton, rule a)
  also have "... = int (card {\<lceil>real x-q\<rceil>..\<lfloor>real x+q\<rfloor>}) - int 1"
    by (intro of_nat_diff)
     (metis a card_0_eq empty_iff finite_atLeastAtMost_int less_one linorder_not_le)
  also have "... \<le> \<lfloor>q+real x\<rfloor>+1 -\<lceil>real x-q\<rceil> - 1"
    using assms by (simp, linarith)
  also have "... \<le> 2*q"
    by linarith
  finally show "card A \<le> 2 * q"
    by simp
  have "A \<subseteq> {..x + nat \<lceil>q\<rceil>}"
    by (rule subsetI, simp add:A_def abs_le_iff, linarith)
  thus "finite A"
    by (rule finite_subset, simp)
qed

private lemma prob_degree_lt_1:
   "prob {\<omega>. degree \<omega> < 1} \<le> 1/real p" 
proof -
  have "space \<inter> {\<omega>. length \<omega> \<le> Suc 0} = bounded_degree_polynomials (mod_ring p) 1"
    by (auto simp:set_eq_iff bounded_degree_polynomials_def space_def)
  moreover have "field_size = p" by (simp add:mod_ring_def)
  hence "real (card (bounded_degree_polynomials (mod_ring p) (Suc 0))) / real (card space) = 1 / real p"
    by (simp add:space_def bounded_degree_polynomials_card power2_eq_square)
  ultimately show ?thesis
    by (simp add:M_def measure_pmf_of_set)
qed

private lemma collision_prob:
  assumes "c \<ge> 1"
  shows "prob {\<omega>. \<exists>x \<in> set as. \<exists>y \<in> set as. x \<noteq> y \<and> tr_hash x \<omega> \<le> c \<and> tr_hash x \<omega> = tr_hash y \<omega>} \<le> 
    (5/2) * (real (card (set as)))\<^sup>2 * c\<^sup>2 * 2 powr -(real r) / (real p)\<^sup>2 + 1/real p" (is "prob {\<omega>. ?l \<omega>} \<le> ?r1 + ?r2")
proof -
  define \<rho> :: real where "\<rho> = 9/8"

  have rho_c_ge_0: "\<rho> * c \<ge> 0" unfolding \<rho>_def using assms by simp 

  have c_ge_0: "c\<ge>0" using assms by simp
  
  have "degree \<omega> \<ge> 1 \<Longrightarrow> \<omega> \<in> space \<Longrightarrow> degree \<omega> = 1" for \<omega>
    by (simp add:bounded_degree_polynomials_def space_def) 
     (metis One_nat_def Suc_1 le_less_Suc_eq less_imp_diff_less list.size(3) pos2)
  hence a: "\<And>\<omega> x y. x < p \<Longrightarrow> y < p \<Longrightarrow>  x \<noteq> y \<Longrightarrow> degree \<omega> \<ge> 1 \<Longrightarrow> \<omega> \<in> space \<Longrightarrow>  hash x \<omega> \<noteq> hash y \<omega>" 
    using inj_onD[OF inj_if_degree_1]  mod_ring_carr by blast 

  have b: "prob {\<omega>. degree \<omega> \<ge> 1 \<and> tr_hash x \<omega> \<le> c \<and> tr_hash x \<omega> = tr_hash y \<omega>} \<le> 5 * c\<^sup>2 * 2 powr (-real r) /(real p)\<^sup>2"
    if b_assms: "x \<in> set as"  "y \<in> set as"  "x < y" for x y
  proof -
    have c: "real u \<le> \<rho> * c \<and> \<bar>real u - real v\<bar> \<le> \<rho> * c * 2 powr (-real r)"
      if c_assms:"truncate_down r (real u) \<le> c" "truncate_down r (real u) = truncate_down r (real v)" for u v
    proof -
      have "9 * 2 powr - real r \<le> 9 * 2 powr (- real 23)" 
        using r_ge_23 by (intro mult_left_mono powr_mono, auto)
      also have "... \<le> 1" by simp
      finally have "9 * 2 powr - real r \<le> 1" by simp

      hence "1 \<le> \<rho> * (1 - 2 powr (- real r))" 
        by (simp add:\<rho>_def)

      hence d: "(c*1) / (1 - 2 powr (-real r)) \<le> c * \<rho>" 
        using assms two_pow_r_le_1 by (simp add: pos_divide_le_eq)

      have "\<And>x. truncate_down r (real x) \<le> c \<Longrightarrow> real x * (1 - 2 powr - real r) \<le> c * 1" 
        using  truncate_down_pos[OF of_nat_0_le_iff] order_trans by (simp, blast)
      hence "\<And>x. truncate_down r (real x) \<le>  c  \<Longrightarrow> real x \<le> c * \<rho>"
        using two_pow_r_le_1 by (intro order_trans[OF _ d], simp add: pos_le_divide_eq) 

      hence e: "real u \<le> c * \<rho>" "real v \<le> c * \<rho>" 
        using c_assms by auto
      have " \<bar>real u - real v\<bar> \<le> (max \<bar>real u\<bar> \<bar>real v\<bar>) * 2 powr (-real r)"
        using c_assms by (intro truncate_down_eq, simp) 
      also have "... \<le> (c * \<rho>) * 2 powr (-real r)"
        using e by (intro mult_right_mono, auto)
      finally have "\<bar>real u - real v\<bar> \<le> \<rho> * c * 2 powr (-real r)"
        by (simp add:algebra_simps)
      thus ?thesis using e by (simp add:algebra_simps)
    qed

    have "prob {\<omega>. degree \<omega> \<ge> 1 \<and> tr_hash x \<omega> \<le> c \<and> tr_hash x \<omega> = tr_hash y \<omega>} \<le>
      prob (\<Union> i \<in> {(u,v) \<in> {..<p} \<times> {..<p}. u \<noteq> v \<and> truncate_down r u \<le> c \<and> truncate_down r u = truncate_down r v}.
      {\<omega>.  hash x \<omega> = fst i \<and> hash y \<omega> = snd i})"
      using a by (intro pmf_mono'[OF M_def], simp add:tr_hash_def) 
       (metis hash_range mod_ring_carr b_assms as_subset_p lessThan_iff nat_neq_iff subset_eq) 
    also have "... \<le> (\<Sum> i\<in> {(u,v) \<in> {..<p} \<times> {..<p}. u \<noteq> v \<and>
      truncate_down r u \<le> c \<and> truncate_down r u = truncate_down r v}. 
      prob {\<omega>. hash x \<omega> = fst i \<and> hash  y \<omega> = snd i})"
      by (intro measure_UNION_le finite_cartesian_product finite_subset[where B="{0..<p} \<times> {0..<p}"])
       (auto simp add:M_def)
    also have "... \<le> (\<Sum> i\<in> {(u,v) \<in> {..<p} \<times> {..<p}. u \<noteq> v \<and>
      truncate_down r u \<le> c \<and> truncate_down r u = truncate_down r v}. 
      prob {\<omega>. (\<forall>u \<in> {x,y}. hash u \<omega> = (if u = x then (fst i) else (snd i)))})" 
      by (intro sum_mono  pmf_mono'[OF M_def]) force
    also have "... \<le> (\<Sum> i\<in> {(u,v) \<in> {..<p} \<times> {..<p}. u \<noteq> v \<and>
      truncate_down r u \<le> c \<and> truncate_down r u = truncate_down r v}. 1/(real p)\<^sup>2)"
      using assms as_subset_p b_assms
      by (intro sum_mono, subst hash_prob)  (auto simp add: mod_ring_def power2_eq_square)
    also have "... = 1/(real p)\<^sup>2 * 
      card {(u,v) \<in> {0..<p} \<times> {0..<p}. u \<noteq> v \<and> truncate_down r u \<le> c \<and> truncate_down r u = truncate_down r v}"
      by simp
    also have "... \<le> 1/(real p)\<^sup>2 * 
      card {(u,v) \<in> {..<p} \<times> {..<p}. u \<noteq> v \<and> real u \<le> \<rho> * c \<and> abs (real u - real v) \<le> \<rho> * c * 2 powr (-real r)}"
      using c
      by (intro mult_mono of_nat_mono card_mono finite_cartesian_product finite_subset[where B="{..<p}\<times>{..<p}"])
        auto
    also have "... \<le> 1/(real p)\<^sup>2 * card (\<Union>u' \<in> {u. u < p \<and> real u \<le> \<rho> * c}.
        {(u::nat,v::nat). u = u' \<and> abs (real u - real v) \<le> \<rho> * c * 2 powr (-real r) \<and> v < p \<and> v \<noteq> u'})"
      by (intro mult_left_mono of_nat_mono card_mono finite_cartesian_product finite_subset[where B="{..<p}\<times>{..<p}"])
       auto
    also have "... \<le> 1/(real p)\<^sup>2 * (\<Sum> u' \<in> {u. u < p \<and> real u \<le> \<rho> * c}.
      card  {(u,v). u = u' \<and> abs (real u - real v) \<le> \<rho> * c * 2 powr (-real r) \<and> v < p \<and> v \<noteq> u'})"
      by (intro mult_left_mono of_nat_mono card_UN_le, auto)
    also have "... = 1/(real p)\<^sup>2 * (\<Sum> u' \<in> {u. u < p \<and>  real u \<le> \<rho> * c}.
      card ((\<lambda>x. (u' ,x)) ` {v. abs (real u' - real v) \<le> \<rho> * c * 2 powr (-real r) \<and> v < p \<and> v \<noteq> u'}))"
      by (intro arg_cong2[where f="(*)"] arg_cong[where f="real"] sum.cong arg_cong[where f="card"])
       (auto simp add:set_eq_iff)
    also have "... \<le> 1/(real p)\<^sup>2 * (\<Sum> u' \<in> {u. u < p \<and> real u \<le> \<rho> * c}.
      card {v. abs (real u' - real v) \<le> \<rho> * c * 2 powr (-real r) \<and> v < p \<and> v \<noteq> u'})"
      by (intro mult_left_mono of_nat_mono sum_mono card_image_le, auto)
    also have "... \<le> 1/(real p)\<^sup>2 * (\<Sum> u' \<in> {u. u < p \<and> real u \<le> \<rho> * c}.
      card {v. abs (real u' - real v) \<le> \<rho> * c * 2 powr (-real r) \<and> v \<noteq> u'})"
      by (intro mult_left_mono sum_mono of_nat_mono card_mono card_nat_in_ball subsetI)  auto
    also have "... \<le> 1/(real p)\<^sup>2 * (\<Sum> u' \<in> {u. u < p \<and> real u \<le> \<rho> * c}.
      real (card {v. abs (real u' - real v) \<le> \<rho> * c * 2 powr (-real r) \<and> v \<noteq> u'}))"
      by simp
    also have "... \<le> 1/(real p)\<^sup>2 * (\<Sum> u' \<in> {u. u < p \<and> real u \<le> \<rho> * c}. 2 * (\<rho> * c * 2 powr (-real r)))"
      by (intro mult_left_mono sum_mono card_nat_in_ball(1), auto)
    also have "... =  1/(real p)\<^sup>2 * (real (card {u. u < p \<and> real u \<le> \<rho> * c}) * (2 * (\<rho> * c * 2 powr (-real r))))"
      by simp
    also have "... \<le>  1/(real p)\<^sup>2 * (real (card {u. u \<le> nat (\<lfloor>\<rho> * c \<rfloor>)}) * (2 * (\<rho> * c * 2 powr (-real r))))"
      using rho_c_ge_0 le_nat_floor
      by (intro mult_left_mono mult_right_mono of_nat_mono card_mono subsetI) auto
    also have "... \<le>  1/(real p)\<^sup>2 * ((1+\<rho> * c) * (2 * (\<rho> * c * 2 powr (-real r))))"
      using rho_c_ge_0 by (intro mult_left_mono mult_right_mono, auto)
    also have "... \<le>  1/(real p)\<^sup>2 * (((1+\<rho>) * c) * (2 * (\<rho> * c * 2 powr (-real r))))" 
      using assms by (intro mult_mono, auto simp add:distrib_left distrib_right \<rho>_def)
    also have "... = (\<rho> * (2 + \<rho> * 2)) * c\<^sup>2 * 2 powr (-real r) /(real p)\<^sup>2"
      by (simp add:ac_simps power2_eq_square) 
    also have "... \<le> 5 * c\<^sup>2 *  2 powr (-real r) /(real p)\<^sup>2"
      by (intro divide_right_mono mult_right_mono) (auto simp add:\<rho>_def)
    finally show ?thesis by simp
  qed

  have "prob {\<omega>. ?l \<omega> \<and> degree \<omega> \<ge> 1} \<le> 
    prob (\<Union> i \<in> {(x,y) \<in> (set as) \<times> (set as). x < y}. {\<omega>. degree \<omega> \<ge> 1 \<and> tr_hash (fst i) \<omega> \<le> c \<and>
    tr_hash (fst i) \<omega> = tr_hash (snd i) \<omega>})"
    by (rule pmf_mono'[OF M_def], simp, metis linorder_neqE_nat)
  also have "... \<le> (\<Sum> i \<in> {(x,y) \<in> (set as) \<times> (set as). x < y}. prob 
    {\<omega>. degree \<omega> \<ge> 1 \<and> tr_hash  (fst i) \<omega> \<le> c \<and> tr_hash (fst i) \<omega> = tr_hash (snd i) \<omega>})"
    unfolding M_def
    by (intro measure_UNION_le finite_cartesian_product finite_subset[where B="(set as) \<times> (set as)"])
      auto
  also have "... \<le> (\<Sum> i \<in> {(x,y) \<in> (set as) \<times> (set as). x < y}. 5  * c\<^sup>2 * 2 powr (-real r) /(real p)\<^sup>2)"
    using b by (intro sum_mono, simp add:case_prod_beta)
  also have "... =  ((5/2) * c\<^sup>2  * 2 powr (-real r) /(real p)\<^sup>2) * (2 * card  {(x,y) \<in> (set as) \<times> (set as). x < y})"
    by simp
  also have "... =  ((5/2) * c\<^sup>2  * 2 powr (-real r) /(real p)\<^sup>2) * (card (set as) * (card (set as) - 1))"
    by (subst card_ordered_pairs, auto) 
  also have "... \<le> ((5/2) * c\<^sup>2 * 2 powr (-real r) /(real p)\<^sup>2) * (real (card (set as)))\<^sup>2"
    by (intro mult_left_mono) (auto simp add:power2_eq_square mult_left_mono)
  also have "... = (5/2) * (real (card (set as)))\<^sup>2 * c\<^sup>2 * 2 powr (-real r) /(real p)\<^sup>2"
    by (simp add:algebra_simps)
  finally have a':"prob {\<omega>. ?l \<omega> \<and> degree \<omega> \<ge> 1} \<le> ?r1" by simp

  have "prob {\<omega>. ?l \<omega>} \<le> prob {\<omega>. ?l \<omega> \<and> degree \<omega> \<ge> 1} + prob {\<omega>. degree \<omega> < 1}"
    by (rule pmf_add[OF M_def], auto)
  also have "... \<le> ?r1 + ?r2" by (intro add_mono a' prob_degree_lt_1)
  finally show ?thesis by simp
qed

lemma of_bool_square: "(of_bool x)\<^sup>2 = ((of_bool x)::real)"
  by (cases x, simp, simp)

private definition Q where "Q y \<omega> = card {x \<in> set as. int (hash x \<omega>) \<le> y}"

private definition m where "m = card (set as)"

private lemma
  assumes "a \<ge> -1"
  assumes "a < int p"
  shows exp_Q: "expectation (\<lambda>\<omega>. real (Q a \<omega>)) = real m * (of_int a+1) / p"
  and var_Q: "variance (\<lambda>\<omega>. real (Q a \<omega>)) \<le> real m * (of_int a+1) / p"
proof -
  have exp_single: "expectation (\<lambda>\<omega>. of_bool (int (hash x \<omega>) \<le> a)) = (real_of_int a+1)/real p"
    if a:"x \<in> set as" for x
  proof -
    have x_le_p: "x < p" using a as_lt_p by simp
    have "expectation (\<lambda>\<omega>. of_bool (int (hash x \<omega>) \<le> a)) = expectation (indicat_real {\<omega>. int (Frequency_Moment_0.hash p x \<omega>) \<le> a})"
      by (intro arg_cong2[where f="integral\<^sup>L"] ext, simp_all)
    also have "... = prob {\<omega>. hash x \<omega> \<in> {k. int k \<le> a}}"
      by (simp add:M_def)
    also have "... = card ({k. int k \<le> a} \<inter> {..<p}) / real p"
      by (subst prob_range, simp_all add: x_le_p mod_ring_def)
    also have "... = card {..<nat (a+1)} / real p"
      using assms by (intro arg_cong2[where f="(/)"] arg_cong[where f="real"] arg_cong[where f="card"])
       (auto simp add:set_eq_iff) 
    also have "... =  (real_of_int a+1)/real p"
      using assms by simp
    finally show "expectation (\<lambda>\<omega>. of_bool (int (hash x \<omega>) \<le> a)) = (real_of_int a+1)/real p"
      by simp
  qed

  have "expectation(\<lambda>\<omega>. real (Q a \<omega>)) = expectation (\<lambda>\<omega>. (\<Sum>x \<in> set as. of_bool (int (hash x \<omega>) \<le> a)))"
    by (simp add:Q_def Int_def)
  also have "... =  (\<Sum>x \<in> set as. expectation (\<lambda>\<omega>. of_bool (int (hash x \<omega>) \<le> a)))"
    by (rule Bochner_Integration.integral_sum, simp)
  also have "... = (\<Sum> x \<in> set as. (a+1)/real p)"
    by (rule sum.cong, simp, subst exp_single, simp, simp)
  also have "... = real m * (real_of_int a + 1) /real p"
    by (simp add:m_def)
  finally show "expectation (\<lambda>\<omega>. real (Q a \<omega>)) = real m * (real_of_int a+1) / p" by simp

  have indep: "J \<subseteq> set as \<Longrightarrow> card J = 2 \<Longrightarrow> indep_vars (\<lambda>_. borel) (\<lambda>i x. of_bool (int (hash i x) \<le> a)) J" for J
    using as_subset_p mod_ring_carr
    by (intro indep_vars_compose2[where Y="\<lambda>i x. of_bool (int x \<le> a)" and M'="\<lambda>_. discrete"]
        k_wise_indep_vars_subset[OF k_wise_indep] finite_subset[OF _ finite_set]) auto

  have rv: "\<And>x. x \<in> set as \<Longrightarrow> random_variable borel (\<lambda>\<omega>. of_bool (int (hash x \<omega>) \<le> a))"
     by (simp add:M_def)

  have "variance (\<lambda>\<omega>. real (Q a \<omega>)) = variance (\<lambda>\<omega>. (\<Sum>x \<in> set as. of_bool (int (hash x \<omega>) \<le> a)))"
    by (simp add:Q_def Int_def)
  also have "... = (\<Sum>x \<in> set as. variance (\<lambda>\<omega>. of_bool (int (hash x \<omega>) \<le> a)))"
    by (intro var_sum_pairwise_indep_2 indep rv) auto
  also have "... \<le> (\<Sum> x \<in> set as. (a+1)/real p)"
    by (rule sum_mono, simp add: variance_eq of_bool_square, simp add: exp_single)
  also have "... = real m * (real_of_int a + 1) /real p"
    by (simp add:m_def)
  finally show "variance (\<lambda>\<omega>. real (Q a \<omega>)) \<le> real m * (real_of_int a+1) / p"
    by simp
qed

lemma estimate'_bounds:
  "prob {\<omega>. of_rat \<delta> * real_of_rat (F 0 as) < \<bar>estimate' (sketch_rv' \<omega>) - of_rat (F 0 as)\<bar>} \<le> 1/3"
proof -
  define \<delta>' where "\<delta>' = 3* real_of_rat \<delta> /4"
  define a where "a = \<lfloor>real t * p / (m * (1+\<delta>'))\<rfloor>"
  define b where "b = \<lceil>real t * p / (m * (1-\<delta>'))-1\<rceil>"

  define has_no_collision where 
    "has_no_collision = (\<lambda>\<omega>. \<forall>x\<in> set as. \<forall>y \<in> set as. (tr_hash x \<omega> = tr_hash y \<omega> \<longrightarrow> x = y) \<or> tr_hash x \<omega> > b)"

  have \<delta>_ge_0: "\<delta> > 0" using \<delta>_range by simp
  have \<delta>_le_1: "\<delta> < 1" using \<delta>_range by simp

  have r_ge_0: "1 \<le> r" using r_ge_23 by simp

  have "2 powr (-real r) \<le> 2 powr (-(4 * log 2 (1 / real_of_rat \<delta>) + 23))"
    using r_bound by (intro powr_mono, linarith, simp)
  also have "... = 2 powr (-4 * log 2 (1 /real_of_rat \<delta>) -23)"
    by (rule arg_cong2[where f="(powr)"], auto simp add:algebra_simps)
  also have "... \<le> 2 powr ( -1 * log 2 (1 /real_of_rat \<delta>) -4)"
    using \<delta>_range by (intro powr_mono diff_mono, auto)
  also have "... = 2 powr ( -1 * log 2 (1 /real_of_rat \<delta>)) /  16"
    by (simp add: powr_diff)
  also have "... = real_of_rat \<delta> / 16"
    using \<delta>_ge_0 by (simp add:log_divide)
  also have "... < real_of_rat \<delta> / 8"
    by (subst pos_divide_less_eq, simp, simp add:\<delta>_ge_0)
  finally have r_le_\<delta>: "2 powr (-real r) < real_of_rat \<delta> / 8"
    by simp

  have "t \<le> 80 / (real_of_rat \<delta>)\<^sup>2 + 1" using t_def t_ge_0 by linarith
  also have "... \<le> 80 / (real_of_rat \<delta>)\<^sup>2 + 1 /  (real_of_rat \<delta>)\<^sup>2"
    using \<delta>_range by (intro add_mono, simp, simp add:power_le_one)
  also have "... = 81 / (real_of_rat \<delta>)\<^sup>2" by simp
  finally have t_le_\<delta>: "t \<le> 81 / (real_of_rat \<delta>)\<^sup>2" by simp

  have \<delta>'_ge_0: "\<delta>' > 0" using \<delta>_range by (simp add:\<delta>'_def)
  have "\<delta>' < 3/4" using \<delta>_range by (simp add:\<delta>'_def)+
  also have "... < 1" by simp
  finally have \<delta>'_le_1: "\<delta>' < 1" by simp

  have "t \<le> 81 / (real_of_rat \<delta>)\<^sup>2"
    using t_le_\<delta> by simp
  also have "... = (81*9/16) / (\<delta>')\<^sup>2"
    by (simp add:\<delta>'_def power2_eq_square)
  also have "... \<le> 46 / \<delta>'\<^sup>2"
    by (intro divide_right_mono, simp, simp)
  finally have t_le_\<delta>': "t \<le> 46/ \<delta>'\<^sup>2" by simp

  have "720 * (real t)\<^sup>2 * 2 powr (-real r) \<le> 720 * (81 / (real_of_rat \<delta>)\<^sup>2)\<^sup>2 * 2 powr (-4 * log 2 (1 / real_of_rat \<delta>) - 23)"
    using r_bound t_le_\<delta>
    by (intro mult_left_mono mult_mono power_mono powr_mono, auto)
  also have "... \<le> 720 * (81 / (real_of_rat \<delta>)\<^sup>2)\<^sup>2 * (2 powr (-4 * log 2 (1 / real_of_rat \<delta>)) * 2 powr (-23))"
    using \<delta>_range by (intro mult_left_mono mult_mono power_mono add_mono)
     (simp_all add:power_le_one powr_diff)
  also have "... = 720 * (81\<^sup>2 / (real_of_rat \<delta>)^4) * (2 powr (log 2 ((real_of_rat \<delta>)^4))  * 2 powr (-23))"
    using \<delta>_ge_0 by (intro arg_cong2[where f="(*)"])
      (simp_all add:power2_eq_square power4_eq_xxxx log_divide log_powr[symmetric])
  also have "... = 720 * 81\<^sup>2 * 2 powr (-23)" using \<delta>_ge_0 by simp
  also have "... \<le> 1" by simp
  finally have r_le_t2: "18 * 40 * (real t)\<^sup>2 * 2 powr (-real r) \<le> 1" by simp

  have "80 \<le> (real_of_rat \<delta>)\<^sup>2 * (80 / (real_of_rat \<delta>)\<^sup>2)" using \<delta>_range by simp
  also have "... \<le> (real_of_rat \<delta>)\<^sup>2 * t"
    by (intro mult_left_mono, simp add:t_def of_nat_ceiling, simp)
  finally have "80 \<le> (real_of_rat \<delta>)\<^sup>2 * t" by simp
  hence t_ge_\<delta>': "45 \<le> t * \<delta>' * \<delta>'" by (simp add:\<delta>'_def power2_eq_square)

  have "m \<le> card {..<n}" unfolding m_def using as_range by (intro card_mono, auto)
  also have "... \<le> p" using n_le_p by simp
  finally have m_le_p: "m \<le> p" by simp

  have m_eq_F_0: "real m = of_rat (F 0 as)"
    by (simp add:m_def F_def)

  show "prob {\<omega>. of_rat \<delta> * real_of_rat (F 0 as) < \<bar>estimate' (sketch_rv' \<omega>) - of_rat (F 0 as)\<bar>} \<le> 1/3"
  proof (cases "card (set as) \<ge> t")
    case True
    hence t_le_m: "t \<le> card (set as)" by simp
    have m_ge_0: "real m > 0" using m_def True t_ge_0 by simp
  
    have b_le_tpm :"b \<le> real t * real p / (real m * (1 - \<delta>'))" by (simp add:b_def)
    also have "... \<le> real t * real p / (real m * (1/4))"
      using \<delta>'_le_1 m_ge_0 \<delta>_range
      by (intro divide_left_mono mult_left_mono mult_nonneg_nonneg mult_pos_pos, simp_all add:\<delta>'_def)
    finally have b_le_tpm: "b \<le> 4 * real t * real p / real m" by (simp add:algebra_simps)

    have a_ge_0: "a \<ge> 0" using \<delta>'_ge_0 by (simp add:a_def)
    have "real m * (1 - \<delta>') < real m" using \<delta>'_ge_0 m_ge_0 by simp
    also have "... \<le> 1 * real p" using m_le_p by simp
    also have "... \<le> real t * real p" using t_ge_0 by (intro mult_right_mono, auto)
    finally have " real m * (1 - \<delta>') < real t * real p" by simp
    hence b_ge_0: "b > 0" using mult_pos_pos m_ge_0 \<delta>'_le_1 by (simp add:b_def)
    hence b_ge_1: "real_of_int b \<ge> 1" by linarith

    have "real t \<le> real m" using True m_def by linarith
    also have "... < (1 + \<delta>') * real m" using \<delta>'_ge_0 m_ge_0 by force
    finally have a_le_p_aux: "real t < (1 + \<delta>') * real m"  by simp

    have "a \<le> real t * real p / (real m * (1 + \<delta>'))" by (simp add:a_def)
    also have "... < real p" 
      using m_ge_0 \<delta>'_ge_0 a_le_p_aux  a_le_p_aux p_ge_0
      by (simp add: pos_divide_less_eq ac_simps) 
    finally have a_le_p: "a < real p" by simp
    hence a_le_p: "a < int p" by linarith

    have "prob {\<omega>. Q a \<omega> \<ge> t} \<le> 
      prob {\<omega> \<in> Sigma_Algebra.space M. abs (real (Q a \<omega>) - expectation (\<lambda>\<omega>. real (Q a \<omega>))) \<ge> 3 * sqrt (m *(real_of_int a+1)/p)}"
    proof (rule pmf_mono'[OF M_def])
      fix \<omega>
      assume "\<omega> \<in> {\<omega>. t \<le> Q a \<omega>}"
      hence t_le: "t \<le> Q a \<omega>" by simp
      have "real m * (of_int a + 1) / p = real m * (of_int a) / p + real m / p"
        by (simp add:algebra_simps add_divide_distrib)
      also have "... \<le>  real m * (real t * real p / (real m * (1+\<delta>'))) / real p + 1"
        using m_le_p p_ge_0 a_ge_0
        by (intro add_mono divide_right_mono mult_mono, simp_all add:a_def)
      also have "... \<le> real t / (1+\<delta>') + 1"
        using \<delta>'_ge_0
        by (intro add_mono, auto simp: pos_le_divide_eq)
      finally have a_le_1: "real m * (of_int a + 1) / p \<le> t / (1+ \<delta>') + 1"
        by simp
      have a_le: "3 * sqrt (real m * (of_int a + 1) / real p) + real m * (of_int a + 1) / real p \<le> 
        3 * sqrt (t / (1+\<delta>') + 1) + (t / (1+\<delta>') + 1)"
        using a_le_1 by (intro add_mono mult_left_mono, auto)
      also have "... \<le> 3 * sqrt (real t+1) + ((t - \<delta>' * t / (1+\<delta>')) + 1)"
        using \<delta>'_ge_0 t_ge_0
        apply (intro add_mono mult_left_mono)
         apply (simp add: pos_divide_le_eq left_diff_distrib)+ 
        by (simp add:algebra_simps)+
      also have "... = 3 * sqrt (real t+1) + (t - \<delta>' * t / (1+\<delta>')) + 1" by simp
      also have "... \<le> 3 * sqrt (46 / \<delta>'\<^sup>2 + 1 / \<delta>'\<^sup>2) + (t - \<delta>' * t/2) + 1 / \<delta>'"
        using \<delta>'_ge_0 t_ge_0 \<delta>'_le_1 add_pos_pos  t_le_\<delta>'
        by (intro add_mono mult_left_mono real_sqrt_le_mono add_mono)
         (simp_all add: power_le_one pos_le_divide_eq)
      also have "... \<le> (21 / \<delta>' + (t - 45 / (2*\<delta>'))) + 1 / \<delta>'" 
        using \<delta>'_ge_0 t_ge_\<delta>'
        by (intro add_mono)
           (simp_all add:real_sqrt_divide divide_le_cancel real_le_lsqrt pos_divide_le_eq ac_simps)
      also have "... \<le> t" using \<delta>'_ge_0 by simp
      also have "... \<le> Q a \<omega>" using t_le by simp
      finally have t_le: "3 * sqrt (real m * (of_int a + 1) / real p) \<le> Q a \<omega> - real m * (of_int a + 1) / real p"
        by (simp add:algebra_simps)
      have " 3 * sqrt (real m * (real_of_int a + 1) / real p) \<le> 
        \<bar>real (Q a \<omega>) - expectation (\<lambda>\<omega>. real (Q a \<omega>))\<bar>"
        using a_ge_0 a_le_p True t_le by (simp add:exp_Q abs_ge_iff)
      thus "\<omega> \<in> {\<omega> \<in> Sigma_Algebra.space M. 3 * sqrt (real m * (real_of_int a + 1) / real p) \<le> \<bar>real (Q a \<omega>) -expectation (\<lambda>\<omega>. real (Q a \<omega>))\<bar>}"
        by (simp add: M_def)
    qed
    also have "... \<le> variance  (\<lambda>\<omega>. real (Q a \<omega>)) / (3 * sqrt (real m * (of_int a + 1) / real p))\<^sup>2"
      using t_ge_0 a_ge_0 p_ge_0 m_ge_0 m_eq_F_0 
      by (intro Chebyshev_inequality, simp add:M_def)  auto
    also have "... \<le> (real m * (real_of_int a + 1) / real p) / (3 * sqrt (real m * (of_int a + 1) / real p))\<^sup>2"
      using a_ge_0 a_le_p by (intro divide_right_mono var_Q, auto)
    also have "... \<le> 1/9" using a_ge_0 by simp
    finally have case_1: "prob {\<omega>. Q a \<omega> \<ge> t} \<le> 1/9" by simp

    have case_2: "prob {\<omega>. Q b \<omega> < t} \<le> 1/9"
    proof (cases "b < p")
      case True
      have "prob {\<omega>. Q b \<omega> < t} \<le> prob {\<omega> \<in> Sigma_Algebra.space M. abs (real (Q b \<omega>) - expectation (\<lambda>\<omega>. real (Q b \<omega>))) 
        \<ge> 3 * sqrt (m *(real_of_int b+1)/p)}"
      proof (rule pmf_mono'[OF M_def])
        fix \<omega>
        assume "\<omega> \<in> set_pmf (pmf_of_set space)"
        have "(real t + 3 * sqrt (real t / (1 - \<delta>') + 1)) * (1 - \<delta>') = real t - \<delta>' * t + 3 * ((1-\<delta>') * sqrt( real t / (1-\<delta>') + 1))"
          by (simp add:algebra_simps)
        also have "... = real t - \<delta>' * t + 3 * sqrt (  (1-\<delta>')\<^sup>2 * (real t /  (1-\<delta>') +  1))"
          using \<delta>'_le_1 by (simp add:real_sqrt_mult)
        also have "... = real t - \<delta>' * t + 3 * sqrt ( real t * (1- \<delta>') + (1-\<delta>')\<^sup>2)"
          by (simp add:power2_eq_square distrib_left)
        also have "... \<le> real t - 45/ \<delta>' + 3 * sqrt ( real t  + 1)"
          using \<delta>'_ge_0 t_ge_\<delta>' \<delta>'_le_1
          by (intro add_mono mult_left_mono real_sqrt_le_mono)
           (simp_all add:pos_divide_le_eq ac_simps left_diff_distrib power_le_one)
         also have "... \<le> real t - 45/ \<delta>' + 3 * sqrt ( 46 / \<delta>'\<^sup>2 + 1 / \<delta>'\<^sup>2)"
           using  t_le_\<delta>' \<delta>'_le_1 \<delta>'_ge_0
           by (intro add_mono mult_left_mono real_sqrt_le_mono, simp_all add:pos_divide_le_eq power_le_one)
        also have "... = real t + (3 * sqrt(47) - 45)/ \<delta>'"
          using \<delta>'_ge_0 by (simp add:real_sqrt_divide diff_divide_distrib)
        also have "... \<le> t"
          using \<delta>'_ge_0 by (simp add:pos_divide_le_eq real_le_lsqrt)
        finally have aux: "(real t + 3 * sqrt (real t / (1 - \<delta>') + 1)) * (1 - \<delta>') \<le> real t "
          by simp
        assume "\<omega> \<in> {\<omega>. Q b \<omega> < t}"
        hence "Q b \<omega> < t" by simp
        hence "real (Q b \<omega>) + 3 * sqrt (real m * (real_of_int b + 1) / real p) 
          \<le> real t + 3 * sqrt (real m * real_of_int b / real p + 1)"
          using m_le_p p_ge_0 
          by (intro add_mono, auto simp add: algebra_simps add_divide_distrib)
        also have "... \<le> real t + 3 * sqrt (real m * (real t * real p / (real m * (1- \<delta>'))) / real p + 1)"
          by (intro add_mono mult_left_mono real_sqrt_le_mono divide_right_mono)
           (auto simp add:b_def)
        also have "... \<le> real t + 3 * sqrt(real t / (1-\<delta>') + 1)"
          using m_ge_0 p_ge_0 by simp
        also have "... \<le> real t / (1-\<delta>')" 
          using \<delta>'_le_1 aux by (simp add: pos_le_divide_eq) 
        also have "... = real m * (real t * real p / (real m * (1-\<delta>'))) / real p" 
          using t_ge_0 t_le_m m_ge_0 p_ge_0 \<delta>'_le_1 by simp
        also have "... \<le>  real m * (real_of_int b + 1) / real p"      
          by (intro  divide_right_mono mult_left_mono) (simp_all add:b_def)
        finally have "real (Q b \<omega>) + 3 * sqrt (real m * (real_of_int b + 1) / real p) 
          \<le> real m * (real_of_int b + 1) / real p" by simp
        hence " 3 * sqrt (real m * (real_of_int b + 1) / real p) \<le> \<bar>real (Q b \<omega>) -expectation (\<lambda>\<omega>. real (Q b \<omega>))\<bar>"  
          using b_ge_0 True by (simp add: exp_Q abs_ge_iff)
        thus "\<omega> \<in> {\<omega>\<in> Sigma_Algebra.space M. 3 * sqrt (real m * (real_of_int b + 1) / real p) \<le> \<bar>real (Q b \<omega>) - expectation (\<lambda>\<omega>. real (Q b \<omega>))\<bar>}" 
          by (simp add:M_def)
      qed
      also have "... \<le> variance (\<lambda>\<omega>. real (Q b \<omega>)) / (3 * sqrt (real m * (real_of_int b + 1) / real p))\<^sup>2" 
        using t_ge_0 b_ge_0 p_ge_0 m_ge_0 m_eq_F_0
        by (intro Chebyshev_inequality, simp add:M_def, auto)
      also have "... \<le> (real m * (real_of_int b + 1) / real p) / (3 * sqrt (real m * (real_of_int b + 1) / real p))\<^sup>2"
        using  b_ge_0 True  by (intro divide_right_mono var_Q, auto)
      also have "... = 1/9"
        using p_ge_0 b_ge_0 m_ge_0 by (simp add:power2_eq_square)
      finally show ?thesis
        by simp
    next
      case False
      have "prob {\<omega>. Q b \<omega> < t} \<le> prob {\<omega>. False}"
      proof (rule pmf_mono'[OF M_def])
        fix \<omega>
        assume a:"\<omega> \<in> {\<omega>. Q b \<omega> < t}"
        assume "\<omega> \<in> set_pmf (pmf_of_set space)"
        hence b:"\<And>x. x < p \<Longrightarrow> hash x \<omega> < p" 
          using hash_range mod_ring_carr by (simp add:M_def measure_pmf_inverse) 
        have "t \<le> card (set as)" using True by simp
        also have "... \<le> Q b \<omega>"
          unfolding Q_def  using b False as_lt_p
          by (intro card_mono subsetI, simp, force) 
        also have "... < t" using a by simp
        finally have "False" by auto
        thus "\<omega> \<in> {\<omega>. False}" by simp
      qed
      also have "... = 0" by auto
      finally show ?thesis by simp
    qed

    have "prob {\<omega>. \<not>has_no_collision \<omega>} \<le>
      prob {\<omega>. \<exists>x \<in> set as. \<exists>y \<in> set as. x \<noteq> y \<and> tr_hash x \<omega> \<le> real_of_int b \<and> tr_hash x \<omega> = tr_hash y \<omega>}"
      by (rule pmf_mono'[OF M_def]) (simp add:has_no_collision_def M_def, force) 
    also have "... \<le> (5/2) * (real (card (set as)))\<^sup>2 * (real_of_int b)\<^sup>2 * 2 powr - real r / (real p)\<^sup>2 + 1 / real p"
      using collision_prob  b_ge_1 by blast
    also have "... \<le> (5/2) * (real m)\<^sup>2 * (real_of_int b)\<^sup>2 * 2 powr - real r / (real p)\<^sup>2 + 1 / real p"
      by (intro divide_right_mono add_mono mult_right_mono mult_mono power_mono, simp_all add:m_def)
    also have "... \<le> (5/2) * (real m)\<^sup>2 * (4 * real t * real p / real m)\<^sup>2 * (2 powr - real r) / (real p)\<^sup>2 + 1 / real p"
      using b_def b_ge_1 b_le_tpm
      by (intro add_mono divide_right_mono  mult_right_mono  mult_left_mono, auto)
    also have "... = 40 * (real t)\<^sup>2 * (2 powr -real r) + 1 / real p"
      using p_ge_0 m_ge_0 t_ge_0 by (simp add:algebra_simps power2_eq_square)
    also have "... \<le> 1/18 + 1/18"
      using r_le_t2 p_ge_18 by (intro add_mono, simp_all add: pos_le_divide_eq)
    also have "... = 1/9" by (simp)
    finally have case_3: "prob {\<omega>. \<not>has_no_collision \<omega>} \<le> 1/9" 
      by simp

    have "prob {\<omega>. real_of_rat \<delta> * of_rat (F 0 as) < \<bar>estimate' (sketch_rv' \<omega>) - of_rat (F 0 as)\<bar>} \<le> 
      prob {\<omega>. Q a \<omega> \<ge> t \<or> Q b \<omega> < t \<or> \<not>(has_no_collision \<omega>)}"
    proof (rule pmf_mono'[OF M_def], rule ccontr)
      fix \<omega>
      assume "\<omega> \<in> set_pmf (pmf_of_set space)"
      assume "\<omega> \<in> {\<omega>. real_of_rat \<delta> * real_of_rat (F 0 as) < \<bar>estimate' (sketch_rv' \<omega>) - real_of_rat (F 0 as)\<bar>}"
      hence est: "real_of_rat \<delta> * real_of_rat (F 0 as) < \<bar>estimate' (sketch_rv' \<omega>) - real_of_rat (F 0 as)\<bar>" by simp
      assume "\<omega> \<notin> {\<omega>. t \<le> Q a \<omega> \<or> Q b \<omega> < t \<or> \<not> has_no_collision \<omega>}"
      hence "\<not>( t \<le> Q a \<omega> \<or> Q b \<omega> < t \<or> \<not> has_no_collision \<omega>)" by simp
      hence lb: "Q a \<omega> < t" and ub: "Q b \<omega> \<ge> t" and no_col: "has_no_collision \<omega>" by simp+

      define y where "y =  nth_mset (t-1) {#int (hash x \<omega>). x \<in># mset_set (set as)#}"
      define y' where "y' = nth_mset (t-1) {#tr_hash x \<omega>. x \<in># mset_set (set as)#}"

      have "a < y" 
        apply (subst y_def, rule nth_mset_bound_left_excl)
         apply (simp)
        using True t_ge_0 apply linarith
        using lb 
        by (simp add:Q_def swap_filter_image count_le_def)
      hence rank_t_lb: "a + 1 \<le> y" 
        by linarith
    
      have rank_t_ub: "y \<le> b" 
        apply (subst y_def, rule nth_mset_bound_right)
         apply simp using True t_ge_0 apply linarith
        using ub t_ge_0
        by (simp add:Q_def swap_filter_image count_le_def)

      have y_ge_0: "real_of_int y \<ge> 0" using rank_t_lb a_ge_0 by linarith
      have y'_eq: "y' = truncate_down r y"
        apply (subst y_def, subst y'_def, subst nth_mset_commute_mono[where f="(\<lambda>x. truncate_down r (of_int x))"]) 
          apply (metis truncate_down_mono mono_def of_int_le_iff)
         apply simp using True t_ge_0 apply linarith
        by (simp add: multiset.map_comp comp_def tr_hash_def)
      have "real_of_int (a+1) * (1 - 2 powr -real r) \<le> real_of_int y * (1 - 2 powr (-real r))"
        using rank_t_lb of_int_le_iff two_pow_r_le_1
        by (intro mult_right_mono, auto)
      also have "... \<le> y'"
        using y'_eq truncate_down_pos[OF y_ge_0] by simp
      finally have rank_t_lb': "(a+1) * (1 - 2 powr (-real r)) \<le> y'" by simp

      have "y' \<le> real_of_int y"
        by (subst y'_eq, rule truncate_down_le, simp)
      also have "... \<le> real_of_int b"
        using rank_t_ub of_int_le_iff by blast
      finally have rank_t_ub': "y' \<le> b"
        by simp

      have "0 < (a+1) * (1-2 powr (-real r))"
        using a_ge_0 two_pow_r_le_1 by (intro mult_pos_pos, auto)
      hence y'_pos: "y' > 0" using rank_t_lb' by linarith

      have no_col': "\<And>x. x \<le> y' \<Longrightarrow> count {#tr_hash x \<omega>. x \<in># mset_set (set as)#} x \<le> 1"
        apply (subst count_image_mset, simp add:vimage_def card_le_Suc0_iff_eq)
        using  rank_t_ub' no_col apply (subst (asm) has_no_collision_def)
        by force

      have h_1: "Max (sketch_rv' \<omega>) = y'"
        apply (simp add:sketch_rv'_def y'_def)
        apply (subst nth_mset_max)
        using True t_ge_0 apply simp
        using no_col' apply (simp add:y'_def)
        using t_ge_0
        by simp

      have "card (sketch_rv' \<omega>) = card (least ((t-1)+1) (set_mset {#tr_hash x \<omega>. x \<in># mset_set (set as)#}))"
        using t_ge_0 by (simp add:sketch_rv'_def)
      also have "... = (t-1) +1"
        apply (rule nth_mset_max(2))
         using True t_ge_0 apply simp
        using no_col' by (simp add:y'_def)
      also have "... = t" using t_ge_0 by simp
      finally have h_2: "card (sketch_rv' \<omega>) = t" by simp
      have h_3: "estimate' (sketch_rv' \<omega>) = real t * real p / y'"
        using h_2 h_1 by (simp add:estimate'_def)

      have "(real t) * real p \<le>  (1 + \<delta>') * real m * ((real t) * real p / (real m * (1 + \<delta>')))" 
        using \<delta>'_le_1 m_def True t_ge_0 \<delta>'_ge_0 by auto
      also have "... \<le> (1+\<delta>') * m * (a+1)"
        using \<delta>'_ge_0 by (intro mult_left_mono, simp_all add:a_def)
      also have "... < ((1 + real_of_rat \<delta>)*(1-real_of_rat \<delta>/8)) * m * (a+1)"
        using True m_def t_ge_0 a_ge_0 \<delta>_range
        by (intro mult_strict_right_mono, auto simp add:\<delta>'_def right_diff_distrib)
      also have "... \<le> ((1 + real_of_rat \<delta>)*(1-2 powr (-r))) * m * (a+1)"
        using r_le_\<delta> \<delta>_range a_ge_0 by (intro mult_right_mono mult_left_mono, auto)
      also have "... = (1 + real_of_rat \<delta>) * m * ((a+1) * (1-2 powr (-real r)))" 
        by simp
      also have "... \<le> (1 + real_of_rat \<delta>) * m * y'"
       using \<delta>_range by (intro mult_left_mono rank_t_lb', simp)
      finally have "real t * real p < (1 + real_of_rat \<delta>) * m * y'" by simp
      hence f_1: "estimate' (sketch_rv' \<omega>) < (1 + real_of_rat \<delta>) * m"
        apply (simp add: h_3)
        by (subst pos_divide_less_eq, metis y'_pos, simp)
      have "(1 - real_of_rat \<delta>) * m * y' \<le> (1 - real_of_rat \<delta>) * m * b" 
        using \<delta>_range by (intro mult_left_mono rank_t_ub', simp)
      also have "... = ((1-real_of_rat \<delta>))  * (real m * b)"
        by simp
      also have "... < (1-\<delta>') * (real m * b)" 
        using \<delta>_range r_le_\<delta> m_eq_F_0 m_ge_0 b_ge_0
        by (intro mult_strict_right_mono, simp_all add: \<delta>'_def algebra_simps)
      also have "... \<le> (1-\<delta>') * (real m * (real t * real p / (real m * (1-\<delta>'))))"
        using \<delta>'_ge_0 \<delta>'_le_1 by (intro mult_left_mono, auto simp add:b_def)
      also have "... = real t * real p"
        using \<delta>'_ge_0 \<delta>'_le_1 t_ge_0 p_ge_0 m_ge_0 by auto
      finally have "(1 - real_of_rat \<delta>) * m * y' < real t * real p" by simp
      hence f_2: "estimate' (sketch_rv' \<omega>) > (1 - real_of_rat \<delta>) * m"
        apply (simp add: h_3)
        by (subst pos_less_divide_eq, metis y'_pos, simp)
      have "abs (estimate' (sketch_rv' \<omega>) - real_of_rat (F 0 as)) < real_of_rat \<delta> * (real_of_rat (F 0 as))"
        using f_1 f_2 by (simp add:abs_less_iff algebra_simps m_eq_F_0)
      thus "False" using est by linarith
    qed
    also have "... \<le> 1/9 + (1/9 + 1/9)"
      by (intro prob_add case_1 case_2 case_3, auto simp add:M_def)
    also have "... = 1/3" by simp
    finally show ?thesis by simp
  next
    case False
    have "prob {\<omega>. real_of_rat \<delta> * of_rat (F 0 as) < \<bar>estimate' (sketch_rv' \<omega>) - of_rat (F 0 as)\<bar>} \<le>
      prob {\<omega>. \<exists>x \<in> set as. \<exists>y \<in> set as. x \<noteq> y \<and> tr_hash x \<omega> \<le> real p \<and> tr_hash x \<omega> = tr_hash y \<omega>}" 
    proof (rule pmf_mono'[OF M_def])
      fix \<omega>
      assume a:"\<omega> \<in> {\<omega>. real_of_rat \<delta> * real_of_rat (F 0 as) < \<bar>estimate' (sketch_rv' \<omega>) - real_of_rat (F 0 as)\<bar>}"
      assume b:"\<omega> \<in> set_pmf (pmf_of_set space)" 
      have a_1: "card (set as) < t" using False by auto
      have a_2:"card (sketch_rv' \<omega>) = card ((\<lambda>x. tr_hash x \<omega>) ` (set as))"
        apply (simp add:sketch_rv'_def)
        apply (subst card_least, simp)
        apply (rule min.absorb4)
        using card_image_le a_1 order_le_less_trans[OF _ a_1] by blast
      have "card (sketch_rv' \<omega>) < t"
        by (metis List.finite_set  a_1 a_2 card_image_le  order_le_less_trans)
      hence "estimate' (sketch_rv' \<omega>) = card (sketch_rv' \<omega>)" by (simp add:estimate'_def)
      hence "card (sketch_rv' \<omega>) \<noteq> real_of_rat (F 0 as)"
        using a \<delta>_range apply simp 
        by (metis abs_zero cancel_comm_monoid_add_class.diff_cancel of_nat_less_0_iff pos_prod_lt zero_less_of_rat_iff)
      hence "card (sketch_rv' \<omega>) \<noteq> card (set as)"
        using m_def m_eq_F_0 by linarith
      hence "\<not>inj_on (\<lambda>x. tr_hash x \<omega>) (set as)"
        using card_image a_2 by auto
      moreover have "tr_hash x \<omega> \<le> real p" if a:"x \<in> set as" for x
      proof -
        have "hash x \<omega> < p" 
          using hash_range as_lt_p a  b
          by (simp add:mod_ring_carr M_def)
        thus "tr_hash x \<omega> \<le> real p" using truncate_down_le by (simp add:tr_hash_def)
      qed
     ultimately show "\<omega> \<in> {\<omega>. \<exists>x \<in> set as. \<exists>y \<in> set as. x \<noteq> y \<and> tr_hash x \<omega> \<le> real p \<and> tr_hash x \<omega> = tr_hash y \<omega>}"
       by (simp add:inj_on_def, blast)
    qed
    also have "... \<le> (5/2) * (real (card (set as)))\<^sup>2 * (real p)\<^sup>2 * 2 powr - real r / (real p)\<^sup>2 + 1 / real p"
      using p_ge_0 by (intro collision_prob, auto)
    also have "... = (5/2) * (real (card (set as)))\<^sup>2 * 2 powr (- real r) + 1 / real p"
      using p_ge_0 by (simp add:ac_simps power2_eq_square)
    also have "... \<le> (5/2) * (real t)\<^sup>2 * 2 powr (-real r) + 1 / real p"
      using False by (intro add_mono mult_right_mono mult_left_mono power_mono, auto)
    also have "... \<le> 1/6 + 1/6"
      using r_le_t2  p_ge_18 by (intro add_mono, simp_all)
    also have "... \<le> 1/3" by simp
    finally show ?thesis by simp
  qed
qed

lemma median_bounds:
  "\<P>(\<omega> in measure_pmf \<Omega>\<^sub>0. \<bar>median s (\<lambda>i. estimate (f0_sketch (\<omega> i))) - F 0 as\<bar> \<le> \<delta> * F 0 as) \<ge> 1 - real_of_rat \<epsilon>"
proof -
  have "strict_mono_on real_of_float A" for A by (meson less_float.rep_eq strict_mono_onI)
  hence real_g_2: "\<And>\<omega>.  sketch_rv' \<omega> = real_of_float ` f0_sketch \<omega>" 
    by (simp add: sketch_rv'_def f0_sketch_def tr_hash_def least_mono_commute image_comp)

  moreover have "inj_on real_of_float A" for A
    using  real_of_float_inject by (simp add:inj_on_def)
  ultimately have card_eq: "\<And>\<omega>. card (f0_sketch \<omega>) = card (sketch_rv' \<omega>)" 
    using real_g_2 by (auto intro!: card_image[symmetric])

  have real_g: "\<And>\<omega>. estimate' (sketch_rv' \<omega>) = real_of_rat (estimate (f0_sketch \<omega>))"
    apply (simp add:estimate_def estimate'_def card_eq of_rat_divide of_rat_mult of_rat_add real_of_rat_of_float)
    apply (rule impI)
    apply (subst mono_Max_commute[where f="real_of_float"])
    using less_eq_float.rep_eq mono_def apply blast
      apply (simp add:f0_sketch_def, simp add:least_def)
    using card_eq[symmetric] card_gt_0_iff t_ge_0 apply (simp, force) 
    by (simp add:real_g_2)
 
  have "1-real_of_rat \<epsilon> \<le> \<P>(\<omega> in measure_pmf \<Omega>\<^sub>0.
      \<bar>median s (\<lambda>i. estimate' (sketch_rv' (\<omega> i))) - real_of_rat (F 0 as)\<bar> \<le>  real_of_rat \<delta> * real_of_rat (F 0 as))"
    apply (rule prob_space.median_bound_2, simp add:prob_space_measure_pmf)
       using \<epsilon>_range apply simp 
       apply (subst \<Omega>\<^sub>0_def)
       apply (rule indep_vars_restrict_intro'[where f="id"], simp, simp, simp add:restrict_dfl_def, simp add:lessThan_atLeast0, simp)
     apply (simp add:s_def) using of_nat_ceiling apply blast
    apply simp
    apply (subst \<Omega>\<^sub>0_def)
    apply (subst prob_prod_pmf_slice, simp, simp)
    using estimate'_bounds by (simp add:M_def) 
  also have "... = \<P>(\<omega> in measure_pmf \<Omega>\<^sub>0. 
      \<bar>median s (\<lambda>i. estimate (f0_sketch (\<omega> i))) - F 0 as\<bar> \<le>  \<delta> * F 0 as)"
    using s_ge_0 median_rat[symmetric] real_g by (intro arg_cong2[where f="measure"]) 
      (simp_all add:of_rat_diff[symmetric] of_rat_mult[symmetric] of_rat_less_eq)
  finally show "\<P>(\<omega> in measure_pmf \<Omega>\<^sub>0. \<bar>median s (\<lambda>i. estimate (f0_sketch (\<omega> i))) - F 0 as\<bar> \<le> \<delta> * F 0 as) \<ge> 1-real_of_rat \<epsilon>"
    by blast
qed

lemma f0_alg_correct':
  "\<P>(\<omega> in measure_pmf result. \<bar>\<omega> - F 0 as\<bar> \<le> \<delta> * F 0 as) \<ge> 1 - of_rat \<epsilon>"
proof -
  have f0_result_elim: "\<And>x. f0_result (s, t, p, r, x, \<lambda>i\<in>{..<s}. f0_sketch (x i)) =
    return_pmf (median s (\<lambda>i. estimate (f0_sketch (x i))))"
    apply (simp add:estimate_def)
    apply (rule median_cong)
    by simp

  show ?thesis
    apply (subst result_def)
    apply (subst f0_alg_sketch, simp)
    apply (simp add:t_def[symmetric] p_def[symmetric] r_def[symmetric] s_def[symmetric] map_pmf_def)
    apply (subst bind_assoc_pmf)
    apply (subst bind_return_pmf)
    apply (subst f0_result_elim)
    apply (subst map_pmf_def[symmetric])
    using median_bounds by simp
qed

lemma f_subset:
  assumes "g ` A \<subseteq> h ` B"
  shows "(\<lambda>x. f (g x)) ` A \<subseteq> (\<lambda>x. f (h x)) ` B"
  using assms by auto

lemma f0_exact_space_usage':
  defines "\<Omega> \<equiv> fold (\<lambda>a state. state \<bind> f0_update a) as (f0_init \<delta> \<epsilon> n)"
  shows "AE \<omega> in \<Omega>. bit_count (encode_f0_state \<omega>) \<le> f0_space_usage (n, \<epsilon>, \<delta>)"
proof -
  
  have log_2_4: "log 2 4 = 2" 
    by (metis log2_of_power_eq mult_2 numeral_Bit0 of_nat_numeral power2_eq_square)

  have b_4_22: "\<And>y. y \<in> {..<p} \<Longrightarrow> bit_count (F\<^sub>S (float_of (truncate_down r y))) \<le> 
    ereal (10 + 4 * real r + 2 * log 2 (log 2 (n+9)))" 
  proof -
    fix y
    assume a:"y \<in> {..<p}"

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
    "\<And>x. x \<in> ({..<s} \<rightarrow>\<^sub>E space) \<Longrightarrow>
        bit_count (encode_f0_state (s, t, p, r, x, \<lambda>i\<in>{..<s}. f0_sketch (x i))) \<le> 
        f0_space_usage (n, \<epsilon>, \<delta>)"
  proof -
    fix x
    assume b_1:"x \<in> {..<s} \<rightarrow>\<^sub>E space"
    have b_2: "x \<in> extensional {..<s}" using b_1 by (simp add:PiE_def) 

    have "\<And>y. y \<in> {..<s} \<Longrightarrow> card (f0_sketch (x y)) \<le> t "
      apply (simp add:f0_sketch_def)
      apply (subst card_least, simp)
      by simp

    hence b_3: "\<And>y. y \<in> (\<lambda>z. f0_sketch (x z)) ` {..<s} \<Longrightarrow> card y \<le> t"
      by force

    have "\<And>y. y \<in> {..<s} \<Longrightarrow> f0_sketch (x y) \<subseteq> (\<lambda>k. float_of (truncate_down r k)) ` {..<p} "
      apply (simp add:f0_sketch_def tr_hash_def)
      apply (rule order_trans[OF least_subset])
      apply (rule f_subset[where f="\<lambda>x. float_of (truncate_down r (real x))"])
      apply (rule image_subsetI, simp) 
      using hash_range
      using b_1 apply (simp add: PiE_iff mod_ring_carr )
      using as_range n_le_p
      by (meson lessThan_iff order_less_le_trans subset_code(1) zero_le)
    hence b_4: "\<And>y. y \<in> (\<lambda>z. f0_sketch (x z)) ` {..<s} \<Longrightarrow> 
      y \<subseteq> (\<lambda>k. float_of (truncate_down r k)) ` {..<p}"
      by force

    have b_4_1: "\<And>y z . y \<in> (\<lambda>z. f0_sketch (x z)) ` {..<s} \<Longrightarrow> z \<in> y \<Longrightarrow> 
      bit_count (F\<^sub>S z) \<le> ereal (10 + 4 * real r + 2 * log 2 (log 2 (n+9)))"
      using b_4_22 b_4 by blast

    have "\<And>y. y \<in> {..<s} \<Longrightarrow> finite (f0_sketch (x y))"
      apply (simp add:f0_sketch_def)
      by (rule finite_subset[OF least_subset], simp)
    hence b_5: "\<And>y. y \<in> (\<lambda>z. f0_sketch (x z)) ` {..<s} \<Longrightarrow> finite y" by force

    have "bit_count (encode_f0_state (s, t, p, r, x, \<lambda>i\<in>{..<s}. f0_sketch (x i))) =
      bit_count (N\<^sub>S s) + bit_count (N\<^sub>S t) +  bit_count (N\<^sub>S p) + bit_count (N\<^sub>S r) +
      bit_count (list\<^sub>S (list\<^sub>S N\<^sub>S) (map x [0..<s])) +
      bit_count (list\<^sub>S (set\<^sub>S F\<^sub>S) (map (\<lambda>i\<in>{..<s}. f0_sketch (x i)) [0..<s]))"
      using b_2
      apply (simp add:encode_f0_state_def dependent_bit_count lessThan_atLeast0
        s_def[symmetric] t_def[symmetric] p_def[symmetric] r_def[symmetric] fun\<^sub>S_def)
      by (simp add:ac_simps  lessThan_atLeast0)
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
       apply (rule bounded_degree_polynomial_bit_count[OF p_ge_0]) using b_1 space_def lessThan_atLeast0 apply blast
      apply (rule list_bit_count_est[where xs="map (\<lambda>i\<in>{..<s}. f0_sketch (x i)) [0..<s]", simplified])
         apply (rule set_bit_count_est)
      using  b_5 b_3 b_4_1  by (simp add:lessThan_atLeast0)+
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
      apply (simp add:s_def[symmetric] r_def[symmetric] t_def[symmetric] Let_def)
      by (simp add:algebra_simps)
    finally show "bit_count (encode_f0_state (s, t, p, r, x, \<lambda>i\<in>{..<s}. f0_sketch (x i))) \<le> 
        f0_space_usage (n, \<epsilon>, \<delta>)" by simp
  qed
  
  have a:"\<And>y. y \<in> (\<lambda>x. (s, t, p, r, x, \<lambda>i\<in>{..<s}. f0_sketch (x i))) `
             ({..<s} \<rightarrow>\<^sub>E space) \<Longrightarrow>
         bit_count (encode_f0_state y) \<le> f0_space_usage (n, \<epsilon>, \<delta>)"
    using b apply (simp add:image_def del:f0_space_usage.simps) by blast

  show ?thesis
    apply (subst AE_measure_pmf_iff, rule ballI)
    apply (subst (asm) \<Omega>_def)
    apply (subst (asm) f0_alg_sketch, simp)
    apply (simp add:s_def[symmetric] t_def[symmetric] p_def[symmetric] r_def[symmetric] Let_def \<Omega>\<^sub>0_def)
    apply (subst (asm) set_prod_pmf, simp)
    apply (simp add:comp_def space_def[symmetric])
    using a
    by (simp add:s_def[symmetric] t_def[symmetric] p_def[symmetric] r_def[symmetric] Let_def)
qed

end

theorem f0_alg_correct:
  assumes "\<epsilon> \<in> {0<..<1}"
  assumes "\<delta> \<in> {0<..<1}"
  assumes "set as \<subseteq> {..<n}"
  defines "\<Omega> \<equiv> fold (\<lambda>a state. state \<bind> f0_update a) as (f0_init \<delta> \<epsilon> n) \<bind> f0_result"
  shows "\<P>(\<omega> in measure_pmf \<Omega>. \<bar>\<omega> - F 0 as\<bar> \<le> \<delta> * F 0 as) \<ge> 1 - of_rat \<epsilon>"
  using f0_alg_correct'[OF assms(1,2,3)] unfolding \<Omega>_def by blast

theorem f0_exact_space_usage:
  assumes "\<epsilon> \<in> {0<..<1}"
  assumes "\<delta> \<in> {0<..<1}"
  assumes "set as \<subseteq> {..<n}"
  defines "\<Omega> \<equiv> fold (\<lambda>a state. state \<bind> f0_update a) as (f0_init \<delta> \<epsilon> n)"
  shows "AE \<omega> in \<Omega>. bit_count (encode_f0_state \<omega>) \<le> f0_space_usage (n, \<epsilon>, \<delta>)"
  using f0_exact_space_usage'[OF assms(1,2,3)] unfolding \<Omega>_def by blast

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
  
  have l6: "(\<lambda>x. log 2 (real (nat (4 * \<lceil>log 2 (1 / real_of_rat (\<delta>_of x))\<rceil> + 23)) + 1)) \<in> O[?F](g)"
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
    (11 + 4 * real (nat (4 * \<lceil>log 2 (1 / real_of_rat (\<delta>_of x))\<rceil> + 23)) + 
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

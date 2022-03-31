section \<open>Frequency Moment $k$\<close>

theory Frequency_Moment_k
  imports Main Median_Method.Median Product_PMF_Ext Lp.Lp List_Ext Frequency_Moments Landau_Ext
begin

text \<open>This section contains a formalization of the algorithm for the $k$-th frequency moment.
It is based on the algorithm described in \cite[\textsection 2.1]{alon1999}.\<close>

type_synonym fk_state = "nat \<times> nat \<times> nat \<times> nat \<times> (nat \<times> nat \<Rightarrow> (nat \<times> nat))"

fun fk_init :: "nat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> nat \<Rightarrow> fk_state pmf" where
  "fk_init k \<delta> \<epsilon> n =
    do {
      let s\<^sub>1 = nat \<lceil>3*real k*(real n) powr (1-1/ real k)/ (real_of_rat \<delta>)\<^sup>2\<rceil>;
      let s\<^sub>2 = nat \<lceil>-18 * ln (real_of_rat \<epsilon>)\<rceil>;
      return_pmf (s\<^sub>1, s\<^sub>2, k, 0, (\<lambda>_ \<in> {0..<s\<^sub>1} \<times> {0..<s\<^sub>2}. (0,0)))
    }"

fun fk_update :: "nat \<Rightarrow> fk_state \<Rightarrow> fk_state pmf" where
  "fk_update a (s\<^sub>1, s\<^sub>2, k, m, r) = 
    do {
      coins \<leftarrow> prod_pmf ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) (\<lambda>_. bernoulli_pmf (1/(real m+1)));
      return_pmf (s\<^sub>1, s\<^sub>2, k, m+1, \<lambda>i \<in> {0..<s\<^sub>1} \<times> {0..<s\<^sub>2}. 
        if coins i then 
          (a,0) 
        else (
          let (x,l) = r i in (x, l + of_bool (x=a))
        )
      )
    }"

fun fk_result :: "fk_state \<Rightarrow> rat pmf" where
  "fk_result (s\<^sub>1, s\<^sub>2, k, m, r) = 
    return_pmf (median s\<^sub>2 (\<lambda>i\<^sub>2 \<in> {0..<s\<^sub>2}.
      (\<Sum>i\<^sub>1\<in>{0..<s\<^sub>1}. rat_of_nat (let t = snd (r (i\<^sub>1, i\<^sub>2)) + 1 in m * (t^k - (t - 1)^k))) / (rat_of_nat s\<^sub>1))
    )"

lemma bernoulli_pmf_1: "bernoulli_pmf 1 = return_pmf True"
  by (rule pmf_eqI, simp add:indicator_def)

fun fk_space_usage :: "(nat \<times> nat \<times> nat \<times> rat \<times> rat) \<Rightarrow> real" where
  "fk_space_usage (k, n, m, \<epsilon>, \<delta>) = (
    let s\<^sub>1 = nat \<lceil>3*real k*(real n) powr (1-1/ real k) / (real_of_rat \<delta>)\<^sup>2 \<rceil> in
    let s\<^sub>2 = nat \<lceil>-(18 * ln (real_of_rat \<epsilon>))\<rceil> in 
    4 +
    2 * log 2 (s\<^sub>1 + 1) +
    2 * log 2 (s\<^sub>2 + 1) +
    2 * log 2 (real k + 1) +
    2 * log 2 (real m + 1) +
    s\<^sub>1 * s\<^sub>2 * (2 + 2 * log 2 (real n+1) + 2 * log 2 (real m+1)))"

definition encode_fk_state :: "fk_state \<Rightarrow> bool list option" where
  "encode_fk_state = 
    N\<^sub>S \<times>\<^sub>D (\<lambda>s\<^sub>1. 
    N\<^sub>S \<times>\<^sub>D (\<lambda>s\<^sub>2. 
    N\<^sub>S \<times>\<^sub>S  
    N\<^sub>S \<times>\<^sub>S  
    (List.product [0..<s\<^sub>1] [0..<s\<^sub>2] \<rightarrow>\<^sub>S (N\<^sub>S \<times>\<^sub>S N\<^sub>S))))"

lemma "inj_on encode_fk_state (dom encode_fk_state)"
proof -
  have "is_encoding encode_fk_state"
    by (simp add:encode_fk_state_def)
     (intro dependent_encoding exp_goloumb_encoding fun_encoding)

  thus ?thesis by (rule encoding_imp_inj)
qed


context
  fixes \<epsilon> \<delta> :: rat
  fixes n k :: nat
  fixes as
  assumes k_ge_1: "k \<ge> 1"
  assumes \<epsilon>_range: "\<epsilon> \<in> {0<..<1}"
  assumes \<delta>_range: "\<delta> > 0"
  assumes as_range: "set as \<subseteq> {..<n}"
begin

definition s\<^sub>1 where "s\<^sub>1 = nat \<lceil>3*real k*(real n) powr (1-1/ real k)/ (real_of_rat \<delta>)\<^sup>2\<rceil>"
definition s\<^sub>2 where "s\<^sub>2 = nat \<lceil>-(18 * ln (real_of_rat \<epsilon>))\<rceil>"

fun fk_update_1 :: "'a \<Rightarrow> nat \<Rightarrow> (nat \<times> nat \<Rightarrow> ('a \<times> nat)) \<Rightarrow> (nat \<times> nat \<Rightarrow> ('a \<times> nat)) pmf" where
  "fk_update_1 a m r = 
    do {
      coins \<leftarrow> prod_pmf ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) (\<lambda>_. bernoulli_pmf (1/(real m+1)));
      return_pmf (\<lambda>i \<in> {0..<s\<^sub>1} \<times> {0..<s\<^sub>2}. 
        if coins i then 
          (a,0) 
        else (
          let (x,l) = r i in (x, l + of_bool (x=a))
        )
      )
    }"

fun fk_update_2 :: "'a \<Rightarrow> nat \<Rightarrow> ('a \<times> nat) \<Rightarrow> (('a \<times> nat)) pmf" where
  "fk_update_2 a m (x,l) = 
    do {
      coin \<leftarrow> bernoulli_pmf (1/(real m+1));
      return_pmf (if coin then (a,0) else (x, l + of_bool (x=a)))
    }"

abbreviation "S \<equiv> {(u, v). v < count_list as u}"

lemma split_space:
  "(\<Sum>a\<in>S. f (snd a)) = (\<Sum>u \<in> set as. (\<Sum>v \<in>{0..<count_list as u}. f v))"
proof -
  define A where "A = (\<lambda>u. {u} \<times> {v. v < count_list as u})"

  have a: "inj_on snd (A x)" for x 
    by (simp add:A_def inj_on_def) 

  have "\<And>u v. u < count_list as v \<Longrightarrow> v \<in> set as"
    by (subst count_list_gr_1, force)
  hence "S = \<Union> (A ` set as)"
    by (auto simp add:set_eq_iff A_def)
  hence "(\<Sum>a\<in>S. f (snd a)) = sum (f \<circ> snd)  (\<Union> (A ` set as))"
    by (intro sum.cong, auto)
  also have "... = sum (\<lambda>x. sum (f \<circ> snd) (A x)) (set as)"
    by (rule sum.UNION_disjoint, simp, simp add:A_def, simp add:A_def, blast) 
  also have "... = sum (\<lambda>x. sum f (snd ` A x)) (set as)"
    by (intro sum.cong, auto simp add:sum.reindex[OF a])
  also have "... = (\<Sum>u \<in> set as. (\<Sum>v \<in>{0..<count_list as u}. f v))"
    unfolding A_def by (intro sum.cong, auto)
  finally show ?thesis by blast
qed

lemma
  assumes "as \<noteq> []"
  shows fin_space: "finite S" 
    and non_empty_space: "S \<noteq> {}"
    and card_space: "card S = length as"
proof -
  have "S \<subseteq> set as \<times> {k. k < length as}"
  proof (rule subsetI)
    fix x
    assume a:"x \<in> S"
    have "fst x \<in> set as"
      using a by (simp add:case_prod_beta count_list_gr_1)
    moreover have "snd x < length as"
      using a count_le_length order_less_le_trans
      by (simp add:case_prod_beta) fast
    ultimately show "x \<in> set as \<times> {k. k < length as}"
      by (simp add:mem_Times_iff)
  qed
  thus fin_space: "finite  S"
    using finite_subset by blast

  have "(as ! 0, 0) \<in> S" 
    using assms(1) 
    by (simp, metis count_list_gr_1 gr0I length_greater_0_conv not_one_le_zero nth_mem)
  thus "S \<noteq> {}" by blast

  show "card S = length as"
    using fin_space split_space[where f="\<lambda>_. (1::nat)"]
    by (simp add:sum_count_set[where X="set as" and xs="as", simplified])
qed

text \<open>Returns the i-th element from the list and the number of occurences of it after
the i-th element. The following result establishes that the distribution of sketch is S.\<close> 
definition sketch where "sketch i = (as ! i, count_list (drop (i+1) as) (as ! i))"

lemma sketch_samples_from_S:
  assumes "as \<noteq> []"
  shows "pmf_of_set {..<length as} \<bind> (\<lambda>k. return_pmf (sketch k)) = pmf_of_set S"
proof -
  have "x < y \<Longrightarrow> y < length as \<Longrightarrow> 
    count_list (drop (y+1) as) (as ! y) < count_list (drop (x+1) as) (as ! y)" for x y
    by (intro count_list_lt_suffix suffix_drop_drop, simp_all)
     (metis Suc_diff_Suc diff_Suc_Suc diff_add_inverse lessI less_natE)
  hence a1: "inj_on sketch {k. k < length as}"
    unfolding sketch_def by (intro inj_onI) (metis Pair_inject mem_Collect_eq nat_neq_iff)

  have "x < length as \<Longrightarrow> count_list (drop (x+1) as) (as ! x) < count_list as (as ! x)" for x
    by (rule count_list_lt_suffix, auto simp add:suffix_drop)
  hence "sketch ` {k. k < length as} \<subseteq> S"
    by (intro image_subsetI, simp add:sketch_def)
  moreover have "card S \<le> card (sketch ` {k. k < length as})"
    by (simp add: card_space[OF assms(1)] card_image[OF a1])
  ultimately have "sketch ` {k. k < length as} = S"
    using fin_space[OF assms(1)] by (intro card_seteq, simp_all)
  hence "bij_betw sketch {k. k < length as} S"
    using a1 by (simp add:bij_betw_def)
  hence "map_pmf sketch (pmf_of_set {k. k < length as}) = pmf_of_set S"
    using assms by (intro map_pmf_of_set_bij_betw, auto)
  thus ?thesis by (simp add: sketch_def map_pmf_def lessThan_def)
qed

text \<open>This result establishes that fk_update_2 simulates uniformly selecting an element from 
  the list without knowing its length in advance.\<close>

lemma fk_update_2_distr:
  assumes "as \<noteq> []"
  shows "fold (\<lambda>x (c,state). (c+1, state \<bind> fk_update_2 x c)) as (0, return_pmf (0,0)) =
  (length as, pmf_of_set {..<length as} \<bind> (\<lambda>k. return_pmf (sketch k)))"
  unfolding sketch_def using assms
proof (induction as rule:rev_nonempty_induct)
  case (single x)
  show ?case using single 
    by (simp add:bind_return_pmf pmf_of_set_singleton bernoulli_pmf_1 lessThan_def) 
next
  case (snoc x xs)
  (* Because the result is established using induction over the stream. The definition for 
  sketch in the context is not usefule. The following is an abbreviaton for sketch that is 
  parameterized over the sequence. *)
  let ?sketch = "(\<lambda>xs k. return_pmf (xs ! k, count_list (drop (Suc k) xs) (xs ! k)))"

  have non_empty: " {..<Suc (length xs)} \<noteq> {}" " {..<length xs} \<noteq> {}" using snoc by auto

  have fk_update_2_eta:"\<And>c. fk_update_2 x c = (\<lambda>a. fk_update_2 x c (fst a,snd a))" 
    by auto
  have a: "\<And>y. pmf_of_set {..<length xs} \<bind> (\<lambda>k. ?sketch xs k \<bind>
          (\<lambda>xa. return_pmf (if y then (x, 0) else (fst xa, snd xa + (of_bool (fst xa = x))))))
      = pmf_of_set {..<length xs} \<bind> (\<lambda>k. return_pmf (if y then (length xs) else k) \<bind> ?sketch (xs@[x]))"
    using non_empty
    by (intro bind_pmf_cong) (simp_all add:bind_return_pmf nth_append count_list_append)

  have b: "bernoulli_pmf (1 / (real (length xs) + 1)) \<bind> (\<lambda>y. pmf_of_set {..<length xs} \<bind>
    (\<lambda>k. return_pmf (if y then length xs else k))) = pmf_of_set {..<length xs + 1}"
    using snoc(1) non_empty
    by (intro pmf_eqI, simp add: pmf_bind measure_pmf_of_set)
     (simp add:indicator_def algebra_simps frac_eq_eq)

  have "pmf_of_set {..<length xs} \<bind> ?sketch xs \<bind> fk_update_2 x (length xs) = 
    pmf_of_set {..<length xs} \<bind> ?sketch xs \<bind> (\<lambda>a. bernoulli_pmf (1 / (real (length xs) + 1)) \<bind>
       (\<lambda>coin. return_pmf (if coin then (x, 0) else (fst a, snd a + of_bool (fst a = x)))))"
    by (subst fk_update_2_eta, subst fk_update_2.simps, simp)
  also have "... = bernoulli_pmf (1 / (real (length xs) + 1)) \<bind> (\<lambda>coin. pmf_of_set {..<length xs} \<bind>
       (\<lambda>k. ?sketch xs k \<bind> (\<lambda>a. return_pmf (if coin then (x, 0) else (fst a, snd a + of_bool (fst a = x))))))"
    by (subst bind_commute_pmf, subst bind_assoc_pmf, simp)
  also have "... = bernoulli_pmf (1 / (real (length xs) + 1)) \<bind> (\<lambda>y. pmf_of_set {..<length xs} \<bind> 
    (\<lambda>k. return_pmf (if y then length xs else k))) \<bind> ?sketch (xs@[x])"
    by (simp add:a del:drop_append)  (simp add: bind_assoc_pmf[symmetric])
  also have "... = pmf_of_set {..<length (xs @ [x])} \<bind> ?sketch (xs@[x])"
    by (subst b, simp)
  finally have d:"pmf_of_set {..<length xs} \<bind> ?sketch xs \<bind> fk_update_2 x (length xs) = 
    pmf_of_set {..<length (xs @ [x])} \<bind> ?sketch (xs@[x])" 
    by simp

  have "fold (\<lambda>x (c,state). (c+1, state \<bind> fk_update_2 x c)) (xs@[x]) (0, return_pmf (0,0)) = 
    (length  xs + 1, pmf_of_set {..<length xs} \<bind> ?sketch xs \<bind> fk_update_2 x (length xs))"
    using snoc by (simp add:case_prod_beta')
  also have "... = (length (xs@[x]), pmf_of_set {..<length (xs @ [x])} \<bind> ?sketch (xs@[x]))"
    by (subst d, simp)
  finally show ?case by simp
qed

definition if_then_else where "if_then_else p q r = (if p then q else r)"

text \<open>This definition is introduced to be able to temporarily substitute @{term "(if p then q else r)"}
with @{term "if_then_else p q r"}, which unblocks the simplifier to process @{term "q"} and @{term "r"}.\<close>

lemma lift_eval_to_prod_pmf:
  "fold (\<lambda>x (c, state). (c+1, state \<bind> fk_update_1 x c)) as (0, return_pmf (\<lambda>i \<in> {0..<s\<^sub>1} \<times> {0..<s\<^sub>2}. (0,0)))
  = (length as, prod_pmf ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) 
  (\<lambda>_. (snd (fold (\<lambda>x (c,state). (c+1, state \<bind> fk_update_2 x c)) as (0, return_pmf (0,0))))))"
proof (induction as rule:rev_induct)
  case Nil
  show ?case
    by simp
next
  case (snoc x xs)
  obtain t1 t2 where t_def: 
    "(t1,t2) = fold (\<lambda>x (c, state). (Suc c, state \<bind> fk_update_2 x c)) xs (0, return_pmf (0,0))"
    by (metis (no_types, lifting) surj_pair)
  have a:"fk_update_1 x (length xs) = (\<lambda>a. fk_update_1 x (length xs) a)" 
    by auto
  have c:"\<And>c. fk_update_2 x c = (\<lambda>a. fk_update_2 x c (fst a,snd a))" 
    by auto
  have "fst (fold (\<lambda>x (c, state). (Suc c, state \<bind> fk_update_2 x c)) xs (0, return_pmf (0,0))) = length xs"
    by (induction xs rule:rev_induct, simp, simp add:case_prod_beta)
  hence d:"t1 = length xs" 
    by (metis t_def fst_conv)


  show ?case using snoc
    apply (simp del:fk_update_2.simps fk_update_1.simps)
    apply (simp add:t_def[symmetric])
    apply (subst a[simplified])
    apply (subst pair_pmfI)
    apply (subst pair_pmf_ptw, simp)
    apply (subst bind_assoc_pmf)
    apply (subst bind_return_pmf)
    apply (subst if_then_else_def[symmetric])
    apply (simp add:comp_def cong:restrict_cong)
    apply (subst map_ptw, simp)
    apply (subst if_then_else_def)
    apply (rule arg_cong2[where f="prod_pmf"], simp)
    apply (rule ext)
    apply (subst c, subst fk_update_2.simps, simp)
    apply (simp add:d)
    apply (subst pair_pmfI)
    apply (rule arg_cong2[where f="bind_pmf"], simp)
    by force
qed

lemma fk_alg_aux_1:
  assumes "as \<noteq> []"
  shows "fold (\<lambda>a state. state \<bind> fk_update a) as (fk_init k \<delta> \<epsilon> n)  = 
    map_pmf (\<lambda>x. (s\<^sub>1,s\<^sub>2,k,length as, x)) 
    (snd (fold (\<lambda>x (c, state). (c+1, state \<bind> fk_update_1 x c)) as (0, return_pmf (\<lambda>i \<in> {0..<s\<^sub>1} \<times> {0..<s\<^sub>2}. (0,0)))))"
  using assms(1)
proof (induction as rule:rev_nonempty_induct)
  case (single x)
  then show ?case 
    by (simp add: map_bind_pmf bind_return_pmf s\<^sub>1_def s\<^sub>2_def Let_def restrict_def)
next
  case (snoc x xs)
  obtain t1 t2 where t:
    "fold (\<lambda>x (c, state). (Suc c, state \<bind> fk_update_1 x c)) xs (0, return_pmf (\<lambda>i. if i \<in> {0..<s\<^sub>1} \<times> {0..<s\<^sub>2} then (0,0) else undefined)) 
    = (t1,t2)"
    by fastforce

  have "fst (fold (\<lambda>x (c, state). (Suc c, state \<bind> fk_update_1 x c)) xs (0, return_pmf (\<lambda>i. if i \<in> {0..<s\<^sub>1} \<times> {0..<s\<^sub>2} then (0,0) else undefined)))
    = length xs"
    by (induction xs rule:rev_induct, simp, simp add:split_beta) 
  hence t1: "t1 = length xs" using t fst_conv by auto

  show ?case using snoc
    apply (simp add:  s\<^sub>1_def[symmetric] s\<^sub>2_def[symmetric] t del:fk_update_1.simps fk_update.simps)
    apply (subst bind_map_pmf)
    apply (subst map_bind_pmf)
    apply simp
    by (subst map_bind_pmf, simp add:t1)
qed


lemma power_diff_sum:
  fixes a b :: "'a :: {comm_ring_1,power}"
  assumes "k > 0"
  shows "a^k - b^k = (a-b) * (\<Sum>i = 0..<k. a ^ i * b ^ (k - 1 - i))" (is "?lhs = ?rhs")
proof -
  have insert_lb: "m < n \<Longrightarrow> insert m {Suc m..<n} = {m..<n}" for m n :: nat
    by auto

  have "?rhs = sum (\<lambda>i. a * (a^i * b^(k-1-i))) {0..<k} - sum (\<lambda>i. b * (a^i * b^(k-1-i))) {0..<k}"
    by (simp add: sum_distrib_left[symmetric] algebra_simps)
  also have "... = sum ((\<lambda>i. (a^i * b^(k-i))) \<circ> (\<lambda>i. i+1)) {0..<k} - sum (\<lambda>i. (a^i * (b^(1+(k-1-i))))) {0..<k}"
    by (simp add:algebra_simps)
  also have "... = sum ((\<lambda>i. (a^i * b^(k-i))) \<circ> (\<lambda>i. i+1)) {0..<k} - sum (\<lambda>i. (a^i * b^(k-i))) {0..<k}"
    by (intro arg_cong2[where f="(-)"] sum.cong arg_cong2[where f="(*)"] arg_cong2[where f="(\<lambda>x y. x ^ y)"], auto)
  also have "... = sum (\<lambda>i. (a^i * b^(k-i))) (insert k {1..<k}) - sum (\<lambda>i. (a^i * b^(k-i))) (insert 0 {Suc 0..<k})"
    using assms
    by (subst sum.reindex[symmetric], simp, subst insert_lb, auto)
  also have "... = ?lhs"
    by simp
  finally show ?thesis by presburger
qed

lemma power_diff_est:
  assumes "k > 0"
  assumes "(a :: real) \<ge> b"
  assumes "b \<ge> 0"
  shows "a^k -b^k \<le> (a-b) * k * a^(k-1)"
proof -
  have " \<And>i. i < k \<Longrightarrow> a ^ i * b ^ (k - 1 - i) \<le> a ^ i * a ^ (k-1-i)"
    using assms by (intro mult_left_mono power_mono) auto
  also have "\<And>i. i < k \<Longrightarrow> a ^ i * a ^ (k - 1 - i) = a ^ (k - Suc 0)"
    using assms(1) by (subst power_add[symmetric], simp)
  finally have a: "\<And>i. i < k \<Longrightarrow> a ^ i * b ^ (k - 1 - i) \<le> a ^ (k - Suc 0)"
    by blast
  have "a^k - b^k = (a-b) * (\<Sum>i = 0..<k. a ^ i * b ^ (k - 1 - i))"
    by (rule power_diff_sum[OF assms(1)])
  also have "... \<le> (a-b) * (\<Sum>i = 0..<k.  a^(k-1))"
    using a assms by (intro mult_left_mono sum_mono, auto)
  also have "... = (a-b) * (k * a^(k-Suc 0))"
    by simp
  finally show ?thesis by simp
qed

text \<open>Specialization of the Hoelder inquality for sums.\<close>
lemma Holder_inequality_sum:
  assumes "p > (0::real)" "q > 0" "1/p + 1/q = 1"
  assumes "finite A"
  shows "\<bar>sum (\<lambda>x. f x * g x) A\<bar> \<le> (sum (\<lambda>x. \<bar>f x\<bar> powr p) A) powr (1/p) * (sum (\<lambda>x. \<bar>g x\<bar> powr q) A) powr (1/q)"
proof -
  have "\<bar>LINT x|count_space A. f x * g x\<bar> \<le> 
    (LINT x|count_space A. \<bar>f x\<bar> powr p) powr (1 / p) * 
    (LINT x|count_space A. \<bar>g x\<bar> powr q) powr (1 / q)"
    using assms integrable_count_space
    by (intro Lp.Holder_inequality, auto)
  thus ?thesis
    using assms by (simp add: lebesgue_integral_count_space_finite[symmetric])
qed

lemma real_count_list_pos:
  assumes "x \<in> set as"
  shows "real (count_list as x) > 0"
  using count_list_gr_1 assms by force

lemma fk_estimate:
  assumes "as \<noteq> []"
  shows "real (length as) * real_of_rat (F (2*k-1) as) \<le> real n powr (1 - 1 / real k) * (real_of_rat (F k as))^2"
  (is "?lhs \<le> ?rhs")
proof (cases "k \<ge> 2")
  case True
  define M where "M = Max (count_list as ` set as)" 
  have "M \<in> count_list as ` set as"
    unfolding M_def using assms by (intro Max_in, auto)
  then obtain m where m_in: "m \<in> set as" and m_def: "M = count_list as m"
    by blast

  have a2: "real M > 0" using m_in count_list_gr_1 by (simp add:m_def, force)
  have a1: "2*k-1 = (k-1) + k" by simp
  have a4: "(k-1) = k * ((k-1)/k)" by simp

  have " 0 < real (count_list as m)" 
    using m_in count_list_gr_1 by force
  hence "M powr k = real (count_list as m) ^ k"
    by (simp add: powr_realpow m_def)
  also have "... \<le> (\<Sum>x\<in>set as. real (count_list as x) ^ k)"
    using m_in by (intro member_le_sum, simp_all)
  also have "... \<le> real_of_rat (F k as)"
    by (simp add:F_def of_rat_sum of_rat_power)
  finally have a3: "M powr k \<le> real_of_rat (F k as)" by simp

  have a5: "0 \<le> real_of_rat (F k as)" 
    using F_gr_0[OF assms(1)] by (simp add: order_le_less)

  have "real (k - 1) / real k + 1 = real (k - 1) / real k + real k / real k"
    using assms True by simp
  also have "... =  real (2 * k - 1) / real k"
    using a1 by (subst add_divide_distrib[symmetric], force)
  finally have a7: "real (k - 1) / real k + 1 = real (2 * k - 1) / real k"
    by blast

  have "real_of_rat (F (2*k-1) as) = 
    (\<Sum>x\<in>set as. real (count_list as x) ^ (k - 1) * real (count_list as x) ^ k)" 
    using a1 by (simp add:F_def of_rat_sum sum_distrib_left of_rat_mult power_add of_rat_power)
  also have "... \<le> (\<Sum>x\<in>set as. real M ^ (k - 1) * real (count_list as x) ^ k)"
    by (intro sum_mono mult_right_mono power_mono of_nat_mono) (auto simp:M_def)
  also have "... = M powr (k-1) * of_rat (F k as)" using a2
    by (simp add:sum_distrib_left F_def of_rat_mult of_rat_sum of_rat_power powr_realpow)
  also have "... = (M powr k) powr (real (k - 1) / real k) * of_rat (F k as) powr 1"
    using a5 by (simp add:powr_powr)
  also have "... \<le>  (real_of_rat (F k as)) powr ((k-1)/k) * (real_of_rat (F k as) powr 1)"
    using a3 a5 by (intro mult_right_mono powr_mono2, auto)
  also have "... = (real_of_rat (F k as)) powr ((2*k-1) / k)"
    by (subst powr_add[symmetric], subst a7, simp)
  finally have a: "real_of_rat (F (2*k-1) as) \<le> (real_of_rat (F k as)) powr ((2*k-1) / k)"
    by blast

  have b1: "card (set as) \<le> n"
    using card_mono[OF _ as_range] by simp

  have "length as = abs (sum (\<lambda>x. real (count_list as x)) (set as))"
    by (subst of_nat_sum[symmetric], simp add: sum_count_set)
  also have "... \<le> card (set as) powr ((k-Suc 0)/k) * 
    (sum (\<lambda>x. \<bar>real (count_list as x)\<bar> powr k) (set as)) powr (1/k)"
    using assms True
    by (intro Holder_inequality_sum[where p="k/(k-1)" and q="k" and f="\<lambda>_.1", simplified])
     (auto simp add:algebra_simps add_divide_distrib[symmetric])
  also have "... = (card (set as)) powr ((k-1) / real k) * of_rat (F k as) powr (1/ k)"
    using real_count_list_pos
    by (simp add:F_def of_rat_sum of_rat_power powr_realpow)
  also have "... = (card (set as)) powr (1 - 1 / real k) * of_rat (F k as) powr (1/ k)"
    using k_ge_1
    by (subst of_nat_diff[OF k_ge_1], subst diff_divide_distrib, simp)
  also have "... \<le> n powr (1 - 1 / real k) * of_rat (F k as) powr (1/ k)"
    using k_ge_1 b1
    by (intro mult_right_mono powr_mono2, auto)
  finally have b: "length as \<le> n powr (1 - 1 / real k) * of_rat (F k as) powr (1/real k)"
    by blast

  have c:"1 / real k + real (2 * k - 1) / real k = real 2"
    using True by (subst add_divide_distrib[symmetric], simp_all add:of_nat_diff)

  have "?lhs \<le> n powr (1 - 1/k) * of_rat (F k as) powr (1/k) * (of_rat (F k as)) powr ((2*k-1) / k)"
    using a b F_ge_0 by (intro mult_mono mult_nonneg_nonneg, auto)
  also have "... = ?rhs"
    using c F_gr_0[OF assms] by (simp add:powr_add[symmetric] powr_realpow[symmetric])
  finally show ?thesis
    by blast
next
  case False
  have "n = 0 \<Longrightarrow> False" using as_range assms by auto
  hence "n > 0" by auto
  moreover have "k = 1" using assms k_ge_1 False by linarith
  ultimately show ?thesis
    apply (simp add:power2_eq_square)
    apply (rule mult_right_mono)
    apply (simp add:F_def sum_count_set of_nat_sum[symmetric] del:of_nat_sum)
    using F_gr_0[OF assms(1)] order_le_less by auto
qed

lemma fk_alg_core_exp:
  assumes "as \<noteq> []"
  shows "has_bochner_integral (pmf_of_set S)
        (\<lambda>a. real (length as) * real (Suc (snd a) ^ k - snd a ^ k)) (real_of_rat (F k as))"
proof -
  show ?thesis
    apply (subst has_bochner_integral_iff)
    apply (rule conjI)
     apply (rule integrable_measure_pmf_finite)
     apply (subst set_pmf_of_set, metis non_empty_space assms(1), metis fin_space assms(1))
    apply (subst integral_measure_pmf_real[OF fin_space[OF assms(1)]])
     apply (subst (asm) set_pmf_of_set[OF non_empty_space[OF assms(1)] fin_space[OF assms(1)]], simp)
    apply (subst pmf_of_set[OF non_empty_space[OF assms(1)] fin_space[OF assms(1)]])
    using assms(1) apply (simp add:card_space F_def of_rat_sum of_rat_power)
    apply (subst split_space)
    apply (rule sum.cong, simp)
    apply (subst of_nat_diff) 
    apply (simp add: power_mono)
    apply (subst sum_Suc_diff', simp, simp)
    using assms k_ge_1 by linarith
qed

lemma fk_alg_core_var:
  assumes "as \<noteq> []"
  shows "prob_space.variance (pmf_of_set S)
        (\<lambda>a. real (length as) * real (Suc (snd a) ^ k - snd a ^ k))
         \<le> (of_rat (F k as))\<^sup>2 * real k * real n powr (1 - 1 / real k)"
proof -
  define f :: "nat \<times> nat \<Rightarrow> real" 
    where "f = (\<lambda>x. (real (length as) * real (Suc (snd x) ^ k - snd x ^ k)))"
  define \<Omega> where "\<Omega> = pmf_of_set S"
  
  have integrable: "\<And>k f. integrable (measure_pmf \<Omega>) (\<lambda>\<omega>. (f \<omega>)::real)"
    apply (simp add:\<Omega>_def)
    apply (rule integrable_measure_pmf_finite)
    apply (subst set_pmf_of_set)
    using assms(1) fin_space non_empty_space by auto

  have k_g_0: "k > 0" using k_ge_1 by linarith

  have c:"real (Suc v ^ k) - real (v ^ k) \<le> real k * real (count_list as a) ^ (k - Suc 0)"
    if c_1: "v < count_list as a" for a v
  proof -
    have "real (Suc v ^ k) - real (v ^ k) \<le> (real (v+1) - real v) * real k * (1 + real v) ^ (k - Suc 0)"
      using k_g_0 power_diff_est[where a="Suc v" and b="v"] by simp
    moreover have "(real (v+1) - real v) = 1" by auto
    ultimately have "real (Suc v ^ k) - real (v ^ k) \<le> real k * (1 + real v) ^ (k - Suc 0)"
      by auto
    also have "... \<le> real k * real (count_list as a) ^ (k- Suc 0)"
      using c_1 by (intro mult_left_mono power_mono, auto)
    finally show ?thesis by blast
  qed
      
  have "real (length as) * (\<Sum>a\<in> set as. (\<Sum>v \<in> {0..< count_list as a}. (real (Suc v ^ k - v ^ k))\<^sup>2))
    \<le> real (length as) * (\<Sum>a\<in> set as. (\<Sum>v \<in> {0..< count_list as a}. (real (k * count_list as a ^ (k-1) * (Suc v ^ k - v ^ k)))))"
    apply (rule mult_left_mono)
     apply (rule sum_mono, rule sum_mono)
     apply (simp add:power2_eq_square)
     apply (rule mult_right_mono)
      apply (subst of_nat_diff, simp add:power_mono)
    by (metis c, simp, simp)
  also have "... = real (length as) * (\<Sum>a\<in> set as. real (k * count_list as a ^ (2*k-1)))"
    apply (rule arg_cong2[where f="(*)"], simp)
    apply (rule sum.cong, simp)
    apply (simp add:sum_distrib_left[symmetric])
    apply (subst of_nat_diff, rule power_mono, simp, simp)
    apply (subst sum_Suc_diff', simp, simp add: zero_power[OF k_g_0] sum_distrib_left)
    apply (subst power_add[symmetric]) 
    using assms k_ge_1 by (simp add: mult_2)
  also have "... = real (length as) * real k * real_of_rat (F (2*k-1) as)"
    apply (subst mult.assoc)
    apply (rule arg_cong2[where f="(*)"], simp)
    by (simp add:sum_distrib_left[symmetric] F_def of_rat_sum of_rat_power)
  also have "... \<le> real k * ((real_of_rat (F k as))\<^sup>2 * real n powr (1 - 1 / real k))"
    apply (subst mult.commute)
    apply (subst mult.assoc)
    apply (rule mult_left_mono)
    using fk_estimate[OF assms]    
    by (simp add: mult.commute, simp)
  finally have b: "real (length as) * (\<Sum>a\<in> set as. (\<Sum>v \<in> {0..< count_list as a}. (real (Suc v ^ k - v ^ k))\<^sup>2))
    \<le> real k * ((real_of_rat (F k as))\<^sup>2 * real n powr (1 - 1 / real k))"
    by blast

  have "measure_pmf.expectation \<Omega> (\<lambda>\<omega>. f \<omega>^2) - (measure_pmf.expectation \<Omega> f)^2 \<le> 
    measure_pmf.expectation \<Omega> (\<lambda>\<omega>. f \<omega>^2)" 
    by simp
  also have " measure_pmf.expectation \<Omega> (\<lambda>\<omega>. f \<omega>^2) \<le> (
    real_of_rat (F k as))\<^sup>2 * real k * real n powr (1 - 1 / real k)"
    apply (simp add:\<Omega>_def f_def)
    apply (subst integral_measure_pmf_real[OF fin_space[OF assms(1)]])
     apply (subst (asm) set_pmf_of_set[OF non_empty_space fin_space], metis assms(1), simp)
    apply (subst pmf_of_set[OF non_empty_space fin_space], metis assms(1))
    apply (simp add:card_space[OF assms(1)] power_mult_distrib)
    apply (subst mult.commute, subst (2) power2_eq_square, subst split_space)
    using assms(1) by (simp add:algebra_simps sum_distrib_left[symmetric] b)
  finally have a:"measure_pmf.expectation \<Omega> (\<lambda>\<omega>. f \<omega>^2) - (measure_pmf.expectation \<Omega> f)^2 \<le> 
    (real_of_rat (F k as))\<^sup>2 * real k * real n powr (1 - 1 / real k)"
    by blast

  show ?thesis
    apply (subst measure_pmf.variance_eq)
    apply (subst \<Omega>_def[symmetric], metis integrable)
    apply (subst \<Omega>_def[symmetric], metis integrable)
    apply (simp add: \<Omega>_def[symmetric])
    using a f_def by simp
qed

theorem fk_alg_sketch:
  assumes "as \<noteq> []"
  shows "fold (\<lambda>a state. state \<bind> fk_update a) as (fk_init k \<delta> \<epsilon> n) = map_pmf (\<lambda>x. (s\<^sub>1,s\<^sub>2,k,length as, x)) 
    (prod_pmf ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) (\<lambda>_. pmf_of_set S))" (is "?lhs = ?rhs")
proof -
  let ?f = "map_pmf (\<lambda>x. (s\<^sub>1,s\<^sub>2,k,length as,x))"

  have "?lhs = ?f ((snd (fold (\<lambda>x (c, state). (c + 1, state \<bind> fk_update_1 x c)) as
          (0, return_pmf (\<lambda>i\<in>{0..<s\<^sub>1} \<times> {0..<s\<^sub>2}. (0, 0))))))" 
    using fk_alg_aux_1[OF assms(1)] by simp
  also have "... = ?f (prod_pmf ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2})
    (\<lambda>_. snd (fold (\<lambda>x (c, state). (c + 1, state \<bind> fk_update_2 x c)) as (0, return_pmf (0, 0)))))"
    by (subst lift_eval_to_prod_pmf, simp)
  also have "... = ?f (prod_pmf ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) 
    (\<lambda>_. pmf_of_set {..<length as} \<bind> (\<lambda>k. return_pmf (sketch k))))"
    by (subst fk_update_2_distr[OF assms], simp)
  also have "... = ?rhs"
    by (subst sketch_samples_from_S[OF assms(1)], simp)
  finally show ?thesis by simp
qed

lemma fk_alg_correct':
  defines "M \<equiv> fold (\<lambda>a state. state \<bind> fk_update a) as (fk_init k \<delta> \<epsilon> n) \<bind> fk_result"
  shows "\<P>(\<omega> in measure_pmf M. \<bar>\<omega> - F k as\<bar> \<le> \<delta> * F k as) \<ge> 1 - of_rat \<epsilon>"
proof (cases "as = []")
  case True
  have a: "nat \<lceil>- (18 * ln (real_of_rat \<epsilon>))\<rceil> > 0"  using \<epsilon>_range by simp 
  show ?thesis using True \<epsilon>_range 
    by (simp add:F_def M_def bind_return_pmf median_const[OF a] Let_def)
next
  case False

  define f :: "(nat \<times> nat \<Rightarrow> (nat \<times> nat)) \<Rightarrow> rat"
    where "f = (\<lambda>x. median s\<^sub>2 (\<lambda>i\<^sub>2\<in>{0..<s\<^sub>2}.
       (\<Sum>i\<^sub>1 = 0..<s\<^sub>1. rat_of_nat (length as * (Suc (snd (x (i\<^sub>1, i\<^sub>2))) ^ k - snd (x (i\<^sub>1, i\<^sub>2)) ^ k))) /
       rat_of_nat s\<^sub>1))"

  define f2 :: "(nat \<times> nat \<Rightarrow> (nat \<times> nat)) \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> real)"
    where "f2 = (\<lambda>x i\<^sub>1 i\<^sub>2. real (length as * (Suc (snd (x (i\<^sub>1, i\<^sub>2))) ^ k - snd (x (i\<^sub>1, i\<^sub>2)) ^ k)))"
  define f1 :: "(nat \<times> nat \<Rightarrow> (nat \<times> nat)) \<Rightarrow> (nat \<Rightarrow> real)"
    where "f1 = (\<lambda>x i\<^sub>2. (\<Sum>i\<^sub>1 = 0..<s\<^sub>1. f2 x i\<^sub>1 i\<^sub>2) / real s\<^sub>1)"
  define f' :: "(nat \<times> nat \<Rightarrow> (nat \<times> nat)) \<Rightarrow> real"
    where "f' = (\<lambda>x. median s\<^sub>2 (f1 x))"

  have "set as \<noteq> {}" using assms False by blast
  hence n_nonzero: "n > 0" using as_range by fastforce

  have fk_nonzero: "F k as > 0"
    using F_gr_0[OF False] by simp

  have s1_nonzero: "s\<^sub>1 > 0"
    apply (simp add:s\<^sub>1_def)
    apply (intro divide_pos_pos mult_pos_pos, simp)
    using k_ge_1 apply linarith
    apply (simp add:n_nonzero)
    by (meson \<delta>_range zero_less_of_rat_iff zero_less_power)
  have s2_nonzero: "s\<^sub>2 > 0" using \<epsilon>_range by (simp add:s\<^sub>2_def) 
  have real_of_rat_f: "\<And>x. f' x = real_of_rat (f x)"
    using s2_nonzero apply (simp add:f_def f'_def f1_def f2_def median_rat median_restrict)
    apply (rule arg_cong2[where f="median"], simp)
    by (simp add:of_rat_divide of_rat_sum of_rat_mult)

  define \<Omega> where "\<Omega> = pmf_of_set S"
  have fin_omega: "finite (set_pmf \<Omega>)"
    apply (subst \<Omega>_def, subst set_pmf_of_set)
    using assms fin_space non_empty_space False by auto
  have fin_omega_2: "finite (set_pmf ((prod_pmf ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) (\<lambda>_. \<Omega>))))"
    apply (subst set_prod_pmf, simp)
    apply (rule finite_PiE, simp)
    by (simp add:fin_omega)

  have a:"fold (\<lambda>x state. state \<bind> fk_update x) as (fk_init k \<delta> \<epsilon> n) = map_pmf (\<lambda>x. (s\<^sub>1,s\<^sub>2,k,length as, x)) 
    (prod_pmf ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) (\<lambda>_. pmf_of_set S))"
    apply (subst fk_alg_sketch[OF False])
    by (simp add:s\<^sub>1_def[symmetric] s\<^sub>2_def[symmetric])

  have fk_result_exp: "fk_result = (\<lambda>(x,y,z,u,v). fk_result (x,y,z,u,v))" 
    by (rule ext, fastforce) 

  have b:"M = prod_pmf ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) (\<lambda>_. \<Omega>) \<bind> return_pmf \<circ> f"
    apply (subst M_def)
    apply (subst a)
    apply (subst fk_result_exp, simp)
    apply (simp add:map_pmf_def)
    apply (subst bind_assoc_pmf)
    apply (subst bind_return_pmf)
    by (simp add:f_def comp_def \<Omega>_def)

  have c: "{y. real_of_rat (\<delta> * F k as) \<ge> \<bar>f' y - real_of_rat (F k as)\<bar>} = 
    {y. (\<delta> * F k as) \<ge> \<bar>f y - (F k as)\<bar>}"
    apply (simp add:real_of_rat_f)
    by (metis abs_of_rat of_rat_diff of_rat_less_eq)

  have f2_exp: "\<And>i\<^sub>1 i\<^sub>2. i\<^sub>1 < s\<^sub>1 \<Longrightarrow> i\<^sub>2 < s\<^sub>2 \<Longrightarrow> 
    has_bochner_integral (measure_pmf (prod_pmf ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) (\<lambda>_. \<Omega>))) (\<lambda>x. f2 x i\<^sub>1 i\<^sub>2)
            (real_of_rat (F k as))"
    apply (simp add:f2_def \<Omega>_def of_rat_mult  of_rat_sum of_rat_power)
    apply (rule has_bochner_integral_prod_pmf_sliceI, simp, simp)
    by (rule fk_alg_core_exp[OF False])

  have "3 * real k * real n powr (1 - 1 / real k) = (real_of_rat \<delta>)\<^sup>2 * (3 * real k * real n powr (1 - 1 / real k) / (real_of_rat \<delta>)\<^sup>2)"
    using \<delta>_range by simp
  also have "... \<le>  (real_of_rat \<delta>)\<^sup>2 * (real s\<^sub>1)"
    apply (rule mult_mono, simp)
    apply (simp add:s\<^sub>1_def) 
      apply (meson of_nat_ceiling)
    using assms apply simp
    by simp
  finally have f2_var_2: "3 * real k * real n powr (1 - 1 / real k) \<le> (real_of_rat \<delta>)\<^sup>2 * (real s\<^sub>1)"
    by blast
  have "(real_of_rat (F k as))\<^sup>2 * real k * real n powr (1 - 1 / real k) =
    (real_of_rat (F k as))\<^sup>2 * (real k * real n powr (1 - 1 / real k))"
    by (simp add:ac_simps)
  also have "... \<le> (real_of_rat (F k as * \<delta>))\<^sup>2 * (real s\<^sub>1 / 3)"
    apply (subst of_rat_mult, subst power_mult_distrib) 
    apply (subst mult.assoc[where c="real s\<^sub>1 / 3"])
    apply (rule mult_mono, simp) using f2_var_2 
    by (simp+)
  finally have f2_var_1: "(real_of_rat (F k as))\<^sup>2 * real k * real n powr (1 - 1 / real k) \<le> (real_of_rat (\<delta> * F k as))\<^sup>2 * real s\<^sub>1 / 3"
    by (simp add: mult.commute)
  
  have f2_var: "\<And>i\<^sub>1 i\<^sub>2. i\<^sub>1 < s\<^sub>1 \<Longrightarrow> i\<^sub>2 < s\<^sub>2 \<Longrightarrow>
       prob_space.variance (measure_pmf (prod_pmf ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) (\<lambda>_. \<Omega>))) (\<lambda>\<omega>. f2 \<omega> i\<^sub>1 i\<^sub>2)
           \<le> (real_of_rat (\<delta> * F k as))\<^sup>2 * real s\<^sub>1 / 3" 
    apply (simp only: f2_def)
    apply (subst variance_prod_pmf_slice, simp, simp, rule integrable_measure_pmf_finite[OF fin_omega])
    apply (rule order_trans [where y="(real_of_rat (F k as))\<^sup>2 *
                 real k * real n powr (1 - 1 / real k)"])
    apply (simp add: \<Omega>_def)
    using assms False fk_alg_core_var apply simp
    using f2_var_1 by blast

  have f1_exp_1: "(real_of_rat (F k as)) = (\<Sum>i \<in> {0..<s\<^sub>1}. (real_of_rat (F k as))/real s\<^sub>1)"
    by (simp add:s1_nonzero)

  have f1_exp: "\<And>i. i < s\<^sub>2 \<Longrightarrow> 
      has_bochner_integral (prod_pmf ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) (\<lambda>_. \<Omega>)) (\<lambda>\<omega>. f1 \<omega> i) 
    (real_of_rat (F k as))"
    apply (simp add:f1_def sum_divide_distrib)
    apply (subst f1_exp_1)
    apply (rule has_bochner_integral_sum)
    apply (rule has_bochner_integral_divide_zero)
    by (simp add: f2_exp)

  have f1_var: "\<And>i. i < s\<^sub>2 \<Longrightarrow> 
      prob_space.variance (prod_pmf ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) (\<lambda>_. \<Omega>)) (\<lambda>\<omega>. f1 \<omega> i) 
      \<le> real_of_rat (\<delta> * F k as)^2/3" (is "\<And>i. _ \<Longrightarrow> ?rhs i")
  proof -
    fix i
    assume f1_var_1:"i < s\<^sub>2" 
    have "prob_space.variance (prod_pmf ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) (\<lambda>_. \<Omega>)) (\<lambda>\<omega>. f1 \<omega> i) = 
       (\<Sum>j = 0..<s\<^sub>1. prob_space.variance  (prod_pmf ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) (\<lambda>_. \<Omega>))  (\<lambda>\<omega>. f2 \<omega> j i / real s\<^sub>1))"
      apply (simp add:f1_def sum_divide_distrib)
      apply (subst measure_pmf.var_sum_all_indep, simp, simp)
      apply (rule integrable_measure_pmf_finite[OF fin_omega_2])
      by (rule indep_vars_restrict_intro'[where f="fst"], simp, simp, simp add:restrict_dfl_def f2_def f1_var_1, simp add:s1_nonzero s2_nonzero, simp, simp)
    also have "... = (\<Sum>j = 0..<s\<^sub>1. prob_space.variance  (prod_pmf ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) (\<lambda>_. \<Omega>))  (\<lambda>\<omega>. f2 \<omega> j i) / real s\<^sub>1^2)"
      apply (rule sum.cong, simp)
      apply (rule measure_pmf.variance_divide)
      by (rule integrable_measure_pmf_finite[OF fin_omega_2])
    also have "... \<le> (\<Sum>j = 0..<s\<^sub>1. ((real_of_rat (\<delta> * F k as))\<^sup>2 * real s\<^sub>1 / 3) / (real s\<^sub>1^2))"
      apply (rule sum_mono)
      apply (rule divide_right_mono) 
       apply (rule f2_var[OF _ f1_var_1], simp)
      by simp
    also have "... = real_of_rat (\<delta> * F k as)^2/3"
      apply simp
      apply (subst nonzero_divide_eq_eq, simp add:s1_nonzero)
      by (simp add:power2_eq_square) 
    finally show "?rhs i" by simp
  qed

  have d: " \<And>i. i < s\<^sub>2 \<Longrightarrow> measure_pmf.prob (prod_pmf ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) (\<lambda>_. \<Omega>)) 
  {y. real_of_rat (\<delta> * F k as) < \<bar>f1 y i - real_of_rat (F k as)\<bar>} \<le> 1/3" (is "\<And>i. _ \<Longrightarrow> ?lhs i \<le> _")
  proof -
    fix i
    assume d_1:"i < s\<^sub>2"
    define a where "a = real_of_rat (\<delta> * F k as)"
    have d_2: "0 < a" apply (simp add:a_def)
      using assms \<delta>_range fk_nonzero mult_pos_pos by blast
    have d_3: "integrable (measure_pmf (prod_pmf ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) (\<lambda>_. \<Omega>))) (\<lambda>x. (f1 x i)\<^sup>2)"
      by (rule integrable_measure_pmf_finite[OF fin_omega_2])
    have "?lhs i \<le> measure_pmf.prob (prod_pmf ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) (\<lambda>_. \<Omega>))
      {y. real_of_rat (\<delta> * F k as) \<le> \<bar>f1 y i - real_of_rat (F k as)\<bar>}"
      by (rule prob_space.pmf_mono'[OF prob_space_measure_pmf], simp, simp)
    also have "... \<le> prob_space.variance (prod_pmf ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) (\<lambda>_. \<Omega>)) (\<lambda>\<omega>. f1 \<omega> i)/a^2"
      using f1_exp[OF d_1]
      using prob_space.Chebyshev_inequality[OF prob_space_measure_pmf _ d_3 d_2, simplified]
      by (simp add:a_def[symmetric] has_bochner_integral_iff)
    also have "... \<le> 1/3" using d_2
      using f1_var[OF d_1] 
      by (simp add:algebra_simps, simp add:a_def)
    finally show "?lhs i \<le> 1/3"
      by blast
  qed

  show ?thesis
    apply (simp add: b comp_def map_pmf_def[symmetric])
    apply (subst c[symmetric])
    apply (simp add:f'_def)
    apply (rule prob_space.median_bound_2[where X="\<lambda>i \<omega>. f1 \<omega> i" and M="(prod_pmf ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) (\<lambda>_. \<Omega>))", simplified])
        apply (simp add:prob_space_measure_pmf)
    using \<epsilon>_range apply simp
       using \<epsilon>_range apply simp
       apply (simp add:f1_def f2_def)
       apply (rule indep_vars_restrict_intro'[where f="snd"], simp, simp, simp add:restrict_dfl_def, simp add:s1_nonzero, simp)
     apply (simp add: s\<^sub>2_def) 
       using of_nat_ceiling apply blast
     using d by simp
qed

lemma fk_exact_space_usage':
  defines "M \<equiv> fold (\<lambda>a state. state \<bind> fk_update a) as (fk_init k \<delta> \<epsilon> n)"
  shows "AE \<omega> in M. bit_count (encode_fk_state \<omega>) \<le> fk_space_usage (k, n, length as, \<epsilon>, \<delta>)" (is "AE \<omega> in M. (_  \<le> ?rhs)")
proof (cases "as = []")
  case True
  have a:"M = fk_init k \<delta> \<epsilon> n"
    using True by (simp add:M_def)
  define w where "w = (2::ereal)"

  have h: "\<And>x. x \<in> (\<lambda>x. (0, 0)) ` ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) \<Longrightarrow> bit_count ((N\<^sub>S \<times>\<^sub>S N\<^sub>S) x) \<le> 2"
  proof -
    fix x
    assume h_a: "x \<in> (\<lambda>x. (0 :: nat, 0 :: nat)) ` ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2})"
    have h_1: "fst x \<le> 0" using h_a by force
    have h_2: "snd x \<le> 0" using h_a by force
    
    have "bit_count  ((N\<^sub>S \<times>\<^sub>S N\<^sub>S) x) \<le>  ereal (2 * log 2 (real 0 + 1) + 1) +  ereal (2 * log 2 (real 0 + 1) + 1)"
      apply (subst dependent_bit_count_2)
      apply (rule add_mono)
       apply (rule exp_goloumb_bit_count_est, rule h_1)
      by (rule exp_goloumb_bit_count_est, rule h_2)
    also have "... = 2"
      by simp
    finally show "bit_count  ((N\<^sub>S \<times>\<^sub>S N\<^sub>S) x) \<le> 2" by simp
  qed

  have "bit_count (N\<^sub>S s\<^sub>1) + bit_count (N\<^sub>S s\<^sub>2) + bit_count (N\<^sub>S k) + bit_count (N\<^sub>S 0) + 
    bit_count ((List.product [0..<s\<^sub>1] [0..<s\<^sub>2] \<rightarrow>\<^sub>S N\<^sub>S \<times>\<^sub>S N\<^sub>S) (\<lambda>_\<in>{0..<s\<^sub>1} \<times> {0..<s\<^sub>2}. (0, 0)))
    \<le> ereal (2 * log 2 (real s\<^sub>1 + 1) + 1) + ereal (2 * log 2 (real s\<^sub>2 + 1) + 1) + 
    ereal (2 * log 2 (real k + 1) + 1) + ereal (2 * log 2 (real 0 + 1) + 1) + 
   (ereal (real s\<^sub>1 * real s\<^sub>2) * w)"
    apply (intro add_mono exp_goloumb_bit_count)
    apply (rule fun_bit_count_est[where xs="(List.product [0..<s\<^sub>1] [0..<s\<^sub>2])", simplified], simp)
    apply (subst w_def)
    using h by simp
  also have "... \<le> ereal (fk_space_usage (k, n, length as, \<epsilon>, \<delta>))" 
    apply (simp add:s\<^sub>1_def[symmetric] s\<^sub>2_def[symmetric] w_def True Let_def)
    apply (rule mult_left_mono) 
    by simp+
  finally have "bit_count (N\<^sub>S s\<^sub>1) + (bit_count (N\<^sub>S s\<^sub>2) + (bit_count (N\<^sub>S k) + (bit_count (N\<^sub>S 0) +
    bit_count ((List.product [0..<s\<^sub>1] [0..<s\<^sub>2] \<rightarrow>\<^sub>S N\<^sub>S \<times>\<^sub>S N\<^sub>S) (\<lambda>_\<in>{0..<s\<^sub>1} \<times> {0..<s\<^sub>2}. (0, 0))))))
    \<le> ereal (fk_space_usage (k, n, length as, \<epsilon>, \<delta>))"
    by (simp add:add.assoc del:fk_space_usage.simps)
  thus ?thesis 
    by (simp add: a Let_def s\<^sub>1_def s\<^sub>2_def encode_fk_state_def  AE_measure_pmf_iff dependent_bit_count
        del:fk_space_usage.simps) 
next
  case False

  have a:"M = map_pmf (\<lambda>x.(s\<^sub>1,s\<^sub>2,k,length as, x)) (prod_pmf ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) (\<lambda>_. pmf_of_set S))"
    apply (subst M_def)
    apply (subst fk_alg_sketch[OF False])
    by (simp add:s\<^sub>1_def[symmetric] s\<^sub>2_def[symmetric])

  have "set as \<noteq> {}" using assms False by blast
  hence n_nonzero: "n > 0" using as_range by fastforce
  have length_xs_gr_0: "length as > 0" using False by blast

  have b:"\<And>y. y\<in>{0..<s\<^sub>1} \<times> {0..<s\<^sub>2} \<rightarrow>\<^sub>E S \<Longrightarrow>
       bit_count (encode_fk_state (s\<^sub>1, s\<^sub>2, k, length as, y)) \<le> ?rhs"
  proof -
    fix y
    assume b0:"y \<in> {0..<s\<^sub>1} \<times> {0..<s\<^sub>2} \<rightarrow>\<^sub>E S"
    have "\<And>x. x \<in> y ` ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) \<Longrightarrow> 1 \<le> count_list as (fst x)"
      using b0 by (simp add:PiE_iff case_prod_beta, fastforce)
    hence b1:"\<And>x. x \<in> y ` ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) \<Longrightarrow> fst x \<le> n"
      using as_range 
      by (meson count_list_gr_1 le_eq_less_or_eq lessThan_iff subset_eq)
    have b2: "\<And>x. x \<in> y ` ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) \<Longrightarrow> snd x \<le> length as"
      using count_le_length b0 apply (simp add:PiE_iff case_prod_beta) 
      using dual_order.strict_trans1 by fastforce
    have b3: "y \<in> extensional ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2})" using b0 PiE_iff by blast
    have "bit_count (encode_fk_state (s\<^sub>1, s\<^sub>2, k, length as, y)) \<le> 
      ereal (2 * log 2 (real s\<^sub>1 + 1) + 1) + (
      ereal (2 * log 2 (real s\<^sub>2 + 1) + 1) + ( 
      ereal (2 * log 2 (real k + 1) + 1) + (
      ereal (2 * log 2 (real (length as) + 1) + 1) + (
       (ereal (real s\<^sub>1 * real s\<^sub>2) * ((ereal (2 * log 2 (real n+1) + 1) + 
        ereal (2 * log 2 (real (length as)+1) + 1))))))))"
      unfolding encode_fk_state_def dependent_bit_count
      apply (intro add_mono exp_goloumb_bit_count)
      apply (rule  fun_bit_count_est[where xs="(List.product [0..<s\<^sub>1] [0..<s\<^sub>2])", simplified], simp add:b3)
      apply (subst dependent_bit_count_2)
      apply (rule add_mono)
      using b1 b2 exp_goloumb_bit_count_est by auto
    also have "... \<le> ?rhs"
      using n_nonzero length_xs_gr_0 apply (simp add: s\<^sub>1_def[symmetric] s\<^sub>2_def[symmetric,simplified] Let_def)
      by (simp add:algebra_simps)
    finally show "bit_count (encode_fk_state (s\<^sub>1, s\<^sub>2, k, length as, y)) \<le> ?rhs"
      by blast
  qed
    
  show ?thesis
    apply (simp add: a AE_measure_pmf_iff del:fk_space_usage.simps)
    apply (subst set_prod_pmf, simp, simp add:PiE_def del:fk_space_usage.simps)
    apply (subst set_pmf_of_set [OF non_empty_space[OF False] fin_space[OF False]])
    apply (subst PiE_def[symmetric])
    by (metis b)
qed

end

theorem fk_exact_space_usage:
  assumes "k \<ge> 1"
  assumes "\<epsilon> \<in> {0<..<1}"
  assumes "\<delta> > 0"
  assumes "set as \<subseteq> {..<n}"
  defines "M \<equiv> fold (\<lambda>a state. state \<bind> fk_update a) as (fk_init k \<delta> \<epsilon> n)"
  shows "AE \<omega> in M. bit_count (encode_fk_state \<omega>) \<le> fk_space_usage (k, n, length as, \<epsilon>, \<delta>)" (is "AE \<omega> in M. (_  \<le> ?rhs)")
  unfolding M_def using fk_exact_space_usage'[OF assms(1,2,3,4)] by blast

lemma fk_alg_correct:
  assumes "k \<ge> 1"
  assumes "\<epsilon> \<in> {0<..<1}"
  assumes "\<delta> > 0"
  assumes "set as \<subseteq> {..<n}"
  defines "M \<equiv> fold (\<lambda>a state. state \<bind> fk_update a) as (fk_init k \<delta> \<epsilon> n) \<bind> fk_result"
  shows "\<P>(\<omega> in measure_pmf M. \<bar>\<omega> - F k as\<bar> \<le> \<delta> * F k as) \<ge> 1 - of_rat \<epsilon>"
  unfolding M_def using fk_alg_correct'[OF assms(1,2,3,4)] by blast

lemma fk_asympotic_space_complexity:
  "fk_space_usage \<in> 
  O[at_top \<times>\<^sub>F at_top \<times>\<^sub>F at_top \<times>\<^sub>F at_right (0::rat) \<times>\<^sub>F at_right (0::rat)](\<lambda> (k, n, m, \<epsilon>, \<delta>).
  real k*(real n) powr (1-1/ real k) / (of_rat \<delta>)\<^sup>2 * (ln (1 / of_rat \<epsilon>)) * (ln (real n) + ln (real m)))"
  (is "_ \<in> O[?F](?rhs)")
proof -
  define k_of :: "nat \<times> nat \<times> nat \<times> rat \<times> rat \<Rightarrow> nat" where "k_of = (\<lambda>(k, n, m, \<epsilon>, \<delta>). k)"
  define n_of :: "nat \<times> nat \<times> nat \<times> rat \<times> rat \<Rightarrow> nat" where "n_of = (\<lambda>(k, n, m, \<epsilon>, \<delta>). n)"
  define m_of :: "nat \<times> nat \<times> nat \<times> rat \<times> rat \<Rightarrow> nat" where "m_of = (\<lambda>(k, n, m, \<epsilon>, \<delta>). m)"
  define \<epsilon>_of :: "nat \<times> nat \<times> nat \<times> rat \<times> rat \<Rightarrow> rat" where "\<epsilon>_of = (\<lambda>(k, n, m, \<epsilon>, \<delta>). \<epsilon>)"
  define \<delta>_of :: "nat \<times> nat \<times> nat \<times> rat \<times> rat \<Rightarrow> rat" where "\<delta>_of = (\<lambda>(k, n, m, \<epsilon>, \<delta>). \<delta>)"

  define g1 where "g1 = (\<lambda>x. real (k_of x)*(real (n_of x)) powr (1-1/ real (k_of x)) / 
    (of_rat (\<delta>_of x))\<^sup>2)"

  define g where "g = (\<lambda>x. g1 x * (ln (1 / of_rat (\<epsilon>_of x))) * (ln (real (n_of x)) + ln (real (m_of x))))"

  have k_inf: "\<And>c. eventually (\<lambda>x. c \<le> (real (k_of x))) ?F"
    apply (simp add:k_of_def case_prod_beta')
    apply (subst eventually_prod1', simp add:prod_filter_eq_bot)
    by (meson eventually_at_top_linorder nat_ceiling_le_eq)

  have n_inf: "\<And>c. eventually (\<lambda>x. c \<le> (real (n_of x))) ?F" 
    apply (simp add:n_of_def case_prod_beta')
    apply (subst eventually_prod2', simp add:prod_filter_eq_bot)
    apply (subst eventually_prod1', simp add:prod_filter_eq_bot)
    by (meson eventually_at_top_linorder nat_ceiling_le_eq)

  have m_inf: "\<And>c. eventually (\<lambda>x. c \<le> (real (m_of x))) ?F" 
    apply (simp add:m_of_def case_prod_beta')
    apply (subst eventually_prod2', simp add:prod_filter_eq_bot)+
    apply (subst eventually_prod1', simp add:prod_filter_eq_bot)
    by (meson eventually_at_top_linorder nat_ceiling_le_eq)

  have eps_inf: "\<And>c. eventually (\<lambda>x. c \<le> 1 / (real_of_rat (\<epsilon>_of x))) ?F"
    apply (simp add:\<epsilon>_of_def case_prod_beta')
    apply (subst eventually_prod2', simp)+
    apply (subst eventually_prod1', simp)
    by (rule inv_at_right_0_inf)

  have delta_inf: "\<And>c. eventually (\<lambda>x. c \<le> 1 / (real_of_rat (\<delta>_of x))) ?F"
    apply (simp add:\<delta>_of_def case_prod_beta')
    apply (subst eventually_prod2', simp)+
    by (rule inv_at_right_0_inf)

  have zero_less_eps: "eventually (\<lambda>x. 0 < (real_of_rat (\<epsilon>_of x))) ?F"
    apply (simp add:\<epsilon>_of_def case_prod_beta')
    apply (subst eventually_prod2', simp)+
    apply (subst eventually_prod1', simp)
    by (rule eventually_at_rightI[where b="1"], simp, simp)

  have zero_less_delta: "eventually (\<lambda>x. 0 < (real_of_rat (\<delta>_of x))) ?F"
    apply (simp add:\<delta>_of_def case_prod_beta')
    apply (subst eventually_prod2', simp)+
    by (rule eventually_at_rightI[where b="1"], simp, simp)

  have unit_9: "(\<lambda>_. 1) \<in> O[?F](\<lambda>x. real (n_of x) powr (1 - 1 / real (k_of x)))"
    apply (rule landau_o.big_mono, simp)
    apply (rule eventually_mono[OF eventually_conj[OF n_inf[where c="1"] k_inf[where c="1"]]])
    by (simp add: ge_one_powr_ge_zero)

  have unit_8: "(\<lambda>_. 1) \<in> O[?F](\<lambda>x. real (k_of x))"
    by (rule landau_o.big_mono, simp, rule k_inf)
  have unit_6: "(\<lambda>_. 1) \<in> O[?F](\<lambda>x. real (m_of x))" 
    by (rule landau_o.big_mono, simp, rule m_inf)
  have unit_n: "(\<lambda>_. 1) \<in> O[?F](\<lambda>x. real (n_of x))" 
    by (rule landau_o.big_mono, simp, rule n_inf)

  have unit_2: "(\<lambda>_. 1) \<in> O[?F](\<lambda>x. ln (1 / real_of_rat (\<epsilon>_of x)))"
    apply (rule landau_o.big_mono, simp)
    apply (rule eventually_mono[OF eventually_conj[OF zero_less_eps eps_inf[where c="exp 1"]]])
    by (meson abs_ge_self dual_order.trans exp_gt_zero ln_ge_iff order_trans_rules(22))

  have unit_10: "(\<lambda>_. 1) \<in> O[?F](\<lambda>x. ln (real (n_of x)))"
    apply (rule landau_o.big_mono, simp)
    apply (rule eventually_mono [OF n_inf[where c="exp 1"]]) 
    by (metis abs_ge_self linorder_not_le ln_ge_iff not_exp_le_zero order.trans)

  have unit_3: "(\<lambda>x. 1) \<in> O[?F](\<lambda>x. ln (real (n_of x)) + ln (real (m_of x)))" 
    apply (rule landau_sum_1)
      apply (rule eventually_ln_ge_iff[OF n_inf])
     apply (rule eventually_ln_ge_iff[OF m_inf])
    by (rule unit_10)

  have unit_7: "(\<lambda>_. 1) \<in> O[?F](\<lambda>x. 1 / (real_of_rat (\<delta>_of x))\<^sup>2)"
    apply (rule landau_o.big_mono, simp)
    apply (rule eventually_mono[OF eventually_conj[OF zero_less_delta delta_inf[where c="1"]]])
    by (metis one_le_power power_one_over)

  have unit_4: "(\<lambda>_. 1) \<in> O[?F](g1)"
    apply (simp add:g1_def)
    apply (subst (2) div_commute)
    apply (rule landau_o.big_mult_1[OF unit_7])
    by (rule landau_o.big_mult_1[OF unit_8 unit_9])

  have unit_5: "(\<lambda>_. 1) \<in> O[?F](\<lambda>x. g1 x * ln (1 / real_of_rat (\<epsilon>_of x)))"
    by (rule landau_o.big_mult_1[OF unit_4 unit_2])

  have unit_1: "(\<lambda>_. 1) \<in> O[?F](g)"
    unfolding g_def
    by (rule landau_o.big_mult_1[OF unit_5 unit_3])

  have l6: "(\<lambda>x. real (nat \<lceil>3 * real (k_of x) * real (n_of x) powr (1 - 1 / real (k_of x)) / (real_of_rat (\<delta>_of x))\<^sup>2\<rceil>))
    \<in> O[?F](g1)" 
    apply (rule landau_nat_ceil[OF unit_4])
    apply (simp add:g1_def)
    apply (subst (2) div_commute, subst (4) div_commute)
    apply (rule landau_o.mult, simp)
    by simp

  have l9: "(\<lambda>x. real (nat \<lceil>- (18 * ln (real_of_rat (\<epsilon>_of x)))\<rceil>))
    \<in> O[?F](\<lambda>x. ln (1 / real_of_rat (\<epsilon>_of x)))" 
     apply (rule landau_nat_ceil[OF unit_2])
    apply (subst minus_mult_right)
      apply (subst cmult_in_bigo_iff, rule disjI2)
      apply (subst landau_o.big.in_cong[where g="\<lambda>x. ln( 1 / (real_of_rat (\<epsilon>_of x)))"])
       apply (rule eventually_mono[OF zero_less_eps])
    by (subst ln_div, simp, simp, simp, simp)

  have l1: "(\<lambda>x. real (nat \<lceil>3 * real (k_of x) * real (n_of x) powr (1 - 1 / real (k_of x)) / (real_of_rat (\<delta>_of x))\<^sup>2\<rceil>) *
          real (nat \<lceil>- (18 * ln (real_of_rat (\<epsilon>_of x)))\<rceil>) *
          (2 + 2 * log 2 (real (n_of x) + 1) + 2 * log 2 (real (m_of x) + 1))) \<in> O[?F](g)"
    apply (simp add:g_def)
    apply (rule landau_o.mult)
     apply (rule landau_o.mult, simp add:l6, simp add:l9)
    apply (rule sum_in_bigo)
     apply (rule sum_in_bigo, simp add:unit_3)
     apply (simp add:log_def)
     apply (rule landau_sum_1 [OF eventually_ln_ge_iff[OF n_inf] eventually_ln_ge_iff[OF m_inf]])
     apply (rule landau_ln_2[where a="2"], simp, simp, rule n_inf)
    apply (rule sum_in_bigo, simp, simp add:unit_n)
    apply (simp add:log_def)
     apply (rule landau_sum_2 [OF eventually_ln_ge_iff[OF n_inf] eventually_ln_ge_iff[OF m_inf]])
    apply (rule landau_ln_2[where a="2"], simp, simp, rule m_inf)
    by (rule sum_in_bigo, simp, simp add:unit_6)

  have l2: "(\<lambda>x. ln (real (m_of x) + 1)) \<in> O[?F](g)"
    apply (simp add:g_def)
    apply (rule landau_o.big_mult_1'[OF unit_5])
    apply (rule landau_sum_2 [OF eventually_ln_ge_iff[OF n_inf] eventually_ln_ge_iff[OF m_inf]])
    apply (rule landau_ln_2[where a="2"], simp, simp, rule m_inf)
    by (rule sum_in_bigo, simp, rule unit_6)

  have l7: "(\<lambda>x. ln (real (k_of x) + 1)) \<in> O[?F](g1)"
    apply (simp add:g1_def)
    apply (subst (2) div_commute)
    apply (rule landau_o.big_mult_1'[OF unit_7])
    apply (rule landau_o.big_mult_1)
     apply (rule landau_ln_3, simp)
    by (rule sum_in_bigo, simp, simp add:unit_8, simp add: unit_9)

  have l3: "(\<lambda>x. ln (real (k_of x) + 1)) \<in> O[?F](g)"
    unfolding g_def using unit_2 unit_3 l7
    by (intro landau_o.big_mult_1, auto)

  have l4: " (\<lambda>x. ln (real (nat \<lceil>- (18 * ln (real_of_rat (\<epsilon>_of x)))\<rceil>) + 1)) \<in> O[?F](g)"
    unfolding g_def using l9 unit_2 unit_3
    by (intro landau_o.big_mult_1'[OF unit_4] landau_o.big_mult_1 landau_ln_3 sum_in_bigo, auto)

  have l5: "(\<lambda>x. ln (real (nat \<lceil>3 * real (k_of x) * real (n_of x) powr (1 - 1 / real (k_of x)) / (real_of_rat (\<delta>_of x))\<^sup>2\<rceil>) + 1)) 
    \<in> O[?F](g)"
    apply (rule landau_ln_3, simp)
    apply (rule sum_in_bigo)
     apply (simp add:g_def)
     apply (rule landau_o.big_mult_1)
     apply (rule landau_o.big_mult_1)
       apply (simp add:l6)
    by (rule unit_2, rule unit_3, rule unit_1)

  have "fk_space_usage = (\<lambda>x. fk_space_usage (k_of x, n_of x, m_of x, \<epsilon>_of x, \<delta>_of x))"
    by (simp add:case_prod_beta' k_of_def n_of_def \<epsilon>_of_def \<delta>_of_def m_of_def)
  also have "... \<in> O[?F](g)"
    using l1 l2 l3 l4 l5 unit_1
    by (simp add:Let_def, intro sum_in_bigo, simp_all add:log_def)
  also have "... = O[?F](?rhs)"
    by (simp add:case_prod_beta' g1_def g_def n_of_def \<epsilon>_of_def \<delta>_of_def m_of_def k_of_def)
  finally show ?thesis by simp
qed

end

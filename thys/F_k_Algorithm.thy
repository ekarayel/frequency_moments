theory F_k_Algorithm
  imports Main "HOL-Probability.Probability_Mass_Function" Median "HOL-Probability.Stream_Space" Prod_PMF "Lp.Lp"
  List_Ext Encoding "HOL-Library.Landau_Symbols"
begin

definition if_then_else where "if_then_else p q r = (if p then q else r)"

type_synonym fk_space = "nat \<times> nat \<times> nat \<times> nat \<times> (nat \<times> nat \<Rightarrow> (nat \<times> nat))"

fun fk_init :: "nat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> nat \<Rightarrow> fk_space pmf" where
  "fk_init k \<delta> \<epsilon> n =
    do {
      let s\<^sub>1 = nat \<lceil>8*real k*(real n) powr (1-1/ real k)/ (real_of_rat \<delta>)\<^sup>2\<rceil>;
      let s\<^sub>2 = nat \<lceil>-32/9 * ln (real_of_rat \<epsilon>)\<rceil>;
      return_pmf (s\<^sub>1, s\<^sub>2, k, 0, (\<lambda>_. undefined))
    }"

fun fk_update :: "nat \<Rightarrow> fk_space \<Rightarrow> fk_space pmf" where
  "fk_update x (s\<^sub>1, s\<^sub>2, k, m, r) = 
    do {
      coins \<leftarrow> prod_pmf ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) (\<lambda>_. bernoulli_pmf (1/(real m+1)));
      return_pmf (s\<^sub>1, s\<^sub>2, k, m+1, \<lambda>i \<in> {0..<s\<^sub>1} \<times> {0..<s\<^sub>2}. 
        if coins i then 
          (x,0) 
        else (
          let (a,l) = r i in (a, l + (if a=x then 1 else 0))
        )
      )
    }"

definition encode_state where
  "encode_state = 
    N\<^sub>S \<times>\<^sub>D (\<lambda>s\<^sub>1. 
    N\<^sub>S \<times>\<^sub>D (\<lambda>s\<^sub>2. 
    N\<^sub>S \<times>\<^sub>S  
    N\<^sub>S \<times>\<^sub>S  
    encode_prod_fun s\<^sub>1 s\<^sub>2 (N\<^sub>S \<times>\<^sub>S N\<^sub>S)))"

lemma "is_encoding encode_state"
  apply (simp add:encode_state_def)
  apply (rule dependent_encoding, metis nat_encoding)
  apply (rule dependent_encoding, metis nat_encoding)
  apply (rule prod_encoding, metis nat_encoding)
  apply (rule prod_encoding, metis nat_encoding)
  by (metis encode_prod_fun prod_encoding nat_encoding)

fun fk_result :: "fk_space \<Rightarrow> rat pmf" where
  "fk_result (s\<^sub>1, s\<^sub>2, k, m, r) = 
    return_pmf (median (\<lambda>i\<^sub>2 \<in> {0..<s\<^sub>2}.
      (\<Sum>i\<^sub>1\<in>{0..<s\<^sub>1} . rat_of_nat (let t = snd (r (i\<^sub>1, i\<^sub>2)) + 1 in m * (t^k - (t - 1)^k))) / (rat_of_nat s\<^sub>1)) s\<^sub>2
    )"

definition fk_value where
  "fk_value k xs = (\<Sum> x \<in> set xs. (rat_of_nat (count_list xs x)^k))"


fun fk_update' :: "'a \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat \<Rightarrow> ('a \<times> nat)) \<Rightarrow> (nat \<times> nat \<Rightarrow> ('a \<times> nat)) pmf" where
  "fk_update' x s\<^sub>1 s\<^sub>2 m r = 
    do {
      coins \<leftarrow> prod_pmf ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) (\<lambda>_. bernoulli_pmf (1/(real m+1)));
      return_pmf (\<lambda>i \<in> {0..<s\<^sub>1} \<times> {0..<s\<^sub>2}. 
        if coins i then 
          (x,0) 
        else (
          let (a,l) = r i in (a, l + (if a=x then 1 else 0))
        )
      )
    }"

fun fk_update'' :: "'a \<Rightarrow> nat \<Rightarrow> ('a \<times> nat) \<Rightarrow> (('a \<times> nat)) pmf" where
  "fk_update'' x m (a,l) = 
    do {
      coin \<leftarrow> bernoulli_pmf (1/(real m+1));
      return_pmf ( 
        if coin then 
          (x,0) 
        else (
          (a, l + (if a=x then 1 else 0))
        )
      )
    }"

lemma bernoulli_pmf_1: "bernoulli_pmf 1 = return_pmf True"
    by (rule pmf_eqI, simp add:indicator_def)

lemma split_space:
  "(\<Sum>a\<in>{(u, v). v < count_list xs u}. (f (snd a))) = 
  (\<Sum>u \<in> set xs. (\<Sum>v \<in>{0..<count_list xs u}. (f v)))" (is "?lhs = ?rhs")
proof -
  define A where "A = (\<lambda>u. {u} \<times> {v. v < count_list xs u})"

  have a :"\<And>u v. u < count_list xs v \<Longrightarrow> v \<in> set xs" 
    by (subst count_list_gr_1, force)

  have "?lhs = sum (f \<circ> snd)  (\<Union> (A ` set xs))"
    apply (rule sum.cong, rule order_antisym)
    apply (rule subsetI, simp add:A_def case_prod_beta' mem_Times_iff a)
    apply (rule subsetI, simp add:A_def case_prod_beta' mem_Times_iff a)
    by simp
  also have "... = sum (\<lambda>x. sum (f \<circ> snd) (A x)) (set xs)"
    by (rule sum.UNION_disjoint, simp, simp add:A_def, simp add:A_def, blast) 
  also have "... = ?rhs"
    apply (rule sum.cong, simp)
    apply (subst sum.reindex[symmetric])
     apply (simp add:A_def inj_on_def) 
    apply (simp add:A_def)
    apply (rule sum.cong)
    using lessThan_atLeast0 apply blast
    by simp
  finally show ?thesis by blast
qed

lemma
  assumes "xs \<noteq> []"
  shows fin_space: "finite {(u, v). v < count_list xs u}" and
  non_empty_space: "{(u, v). v < count_list xs u} \<noteq> {}" and
  card_space: "card {(u, v). v < count_list xs u} = length xs"
proof -

  have "{(u, v). v < count_list xs u} \<subseteq> set xs \<times> {k. k < length xs}"
    apply (rule subsetI, simp add:case_prod_beta mem_Times_iff count_list_gr_1)
    by (metis count_le_length order_less_le_trans)

  thus fin_space: "finite  {(u, v). v < count_list xs u}"
    using finite_subset by blast

  have "(xs ! 0, 0) \<in> {(u, v). v < count_list xs u}" 
    apply (simp)
    using assms(1) 
    by (metis count_list_gr_1 gr0I length_greater_0_conv not_one_le_zero nth_mem)
  thus "{(u, v). v < count_list xs u} \<noteq> {}" by blast

  show "card {(u, v). v < count_list xs u} = length xs"
    using fin_space split_space[where f="\<lambda>_. (1::nat)", where xs="xs"]
    by (simp add:sum_count_set[where X="set xs" and xs="xs", simplified])
qed


lemma fk_alg_aux_5:
  assumes "xs \<noteq> []"
  shows "pmf_of_set {k. k < length xs} \<bind> (\<lambda>k. return_pmf (xs ! k, count_list (drop (k+1) xs) (xs ! k)))
  = pmf_of_set {(u,v). v < count_list xs u}"
proof -
  define f where "f = (\<lambda>k. (xs ! k, count_list (drop (k+1) xs) (xs ! k)))"

  have a3: "\<And>x y. y < length xs \<Longrightarrow> x < y \<Longrightarrow> xs ! x = xs ! y \<Longrightarrow>
           count_list (drop (Suc x) xs) (xs ! x) \<noteq> count_list (drop (Suc y) xs) (xs ! y)" 
    (is "\<And>x y. _ \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> ?ths x y")
  proof -
    fix x y
    assume a3_1: "y < length xs"
    assume a3_2: "x < y"
    assume a3_3: "xs ! x = xs ! y"
    have a3_4: "drop (Suc x) xs = take (y-x) (drop (Suc x) xs)@ drop (Suc y) xs"
      apply (subst append_take_drop_id[where xs="drop (Suc x) xs" and n="y - x", symmetric])
      using a3_2 by simp
    have "count_list (drop (Suc x) xs) (xs ! x) = count_list (take (y-x) (drop (Suc x) xs)) (xs ! y) +
        count_list (drop (Suc y) xs) (xs ! y)"
      using a3_3 by (subst a3_4, simp add:count_list_append)
    moreover have "count_list (take (y-x) (drop (Suc x) xs)) (xs ! y) \<ge> 1"
      apply (subst count_list_gr_1[symmetric])  
      apply (simp add:set_conv_nth)
      apply (rule exI[where x="y-x-1"])
      apply (subst nth_take, meson diff_less a3_2  zero_less_diff zero_less_one)
      apply (subst nth_drop) using a3_1 a3_2 apply simp
      apply (rule conjI, rule arg_cong2[where f="(!)"], simp)
      using a3_2 apply simp
      apply (rule conjI)
      using a3_1 a3_2 apply simp
      by (meson diff_less a3_2  zero_less_diff zero_less_one)
    ultimately show "?ths x y" by presburger
  qed

  have a1: "inj_on f {k. k < length xs}"
  proof (rule inj_onI)
    fix x y
    assume "x \<in> {k. k < length xs}"
    moreover assume "y \<in> {k. k < length xs}"
    moreover assume "f x = f y"
    ultimately show "x = y"
      apply (cases "x < y", simp add:f_def, metis a3) 
      apply (cases "y < x", simp add:f_def, metis a3) 
      by simp
  qed
  have a2_1: " \<And>x. x < length xs \<Longrightarrow> count_list (drop (Suc x) xs) (xs ! x) < count_list xs (xs ! x)"
  proof -
    fix x
    assume a:"x < length xs"
    have "1 \<le> count_list (take (Suc x) xs) (xs ! x)"
      apply (subst count_list_gr_1[symmetric])
      using a by (simp add: take_Suc_conv_app_nth)
    hence "count_list (drop (Suc x) xs) (xs ! x) < count_list (take (Suc x) xs) (xs ! x) +count_list (drop (Suc x) xs) (xs ! x)"
      by (simp)
    also have "... = count_list xs (xs ! x)"
      by (simp add:count_list_append[symmetric])
    finally show "count_list (drop (Suc x) xs) (xs ! x) < count_list xs (xs ! x)"
      by blast
  qed
  have a2: "f ` {k. k < length xs} = {(u, v). v < count_list xs u}"
    apply (rule card_seteq) 
      apply (metis fin_space[OF assms(1)])
     apply (rule image_subsetI, simp add:f_def)
    apply (metis a2_1)
    apply (subst card_image[OF a1])
    by (subst card_space[OF assms(1)], simp)

  have "bij_betw f {k. k < length xs} {(u, v). v < count_list xs u}"
    using a1 a2 by (simp add:bij_betw_def)
  thus ?thesis
    using assms apply (subst map_pmf_def[symmetric])
    by (rule map_pmf_of_set_bij_betw, simp add:f_def, blast, simp)
qed

lemma fk_alg_aux_4:
  assumes "xs \<noteq> []"
  shows "fold (\<lambda>x (c,state). (c+1, state \<bind> fk_update'' x c)) xs (0, return_pmf undefined) =
  (length xs, pmf_of_set {k. k < length xs} \<bind> (\<lambda>k. return_pmf (xs ! k, count_list (drop (k+1) xs) (xs ! k))))"
  using assms
proof (induction xs rule:rev_nonempty_induct)
  case (single x)
  have c:"\<And>c. fk_update'' x c = (\<lambda>a. fk_update'' x c (fst a,snd a))" 
    by auto
  have b:"{(u, v). v < (if x = u then count_list [] u + 1 else count_list [] u)} = {(x,0)}"
    apply (rule order_antisym, rule subsetI, simp add:case_prod_beta) 
     apply (metis (full_types) add_cancel_left_left count_list.simps(1) less_nat_zero_code less_one prod.collapse)
    by (rule subsetI, simp)
  have a:"bernoulli_pmf 1 = return_pmf True"
    by (rule pmf_eqI, simp add:indicator_def)
  show ?case using single 
    apply (simp add:bind_return_pmf pmf_of_set_singleton) 
    apply (subst c, subst fk_update''.simps)
    by (simp add:a bind_return_pmf)
next
  case (snoc x xs)
  have c:"\<And>c. fk_update'' x c = (\<lambda>a. fk_update'' x c (fst a,snd a))" 
    by auto
  have a: "\<And>y. pmf_of_set {k. k < length xs} \<bind> (\<lambda>k. return_pmf (xs ! k, count_list (drop (Suc k) xs) (xs ! k)) \<bind>
          (\<lambda>xa. return_pmf (if y then (x, 0) else (fst xa, snd xa + (if fst xa = x then 1 else 0)))))
      = pmf_of_set {k. k < length xs} \<bind> (\<lambda>k. return_pmf (if y then (length xs) else k) \<bind> (\<lambda>k. return_pmf ((xs@[x]) ! k, count_list (drop (Suc k) (xs@[x])) ((xs@[x]) ! k))))"
    apply (simp add:bind_return_pmf)
    apply (rule bind_pmf_cong, simp)
    apply (subst (asm) set_pmf_of_set)
    using snoc apply blast apply simp
    by (simp add:nth_append count_list_append)

  show ?case using snoc 
    apply (simp del:drop_append, subst c, subst fk_update''.simps)
    apply (subst bind_commute_pmf)
    apply (subst bind_assoc_pmf)
    apply (simp add:a del:drop_append)
    apply (subst bind_assoc_pmf[symmetric])
    apply (subst bind_assoc_pmf[symmetric])
    apply (rule arg_cong2[where f="bind_pmf"])
     apply (rule pmf_eqI)
     apply (subst pmf_bind)
     apply (subst pmf_of_set, blast, simp)
     apply (subst pmf_bind)
     apply (simp)
     apply (subst measure_pmf_of_set, blast, simp)
     apply (simp add:indicator_def)
     apply (subst frac_eq_eq, simp, linarith)
     apply (simp add:algebra_simps)
    by simp
qed

lemma fk_alg_aux_2:
  "fold (\<lambda>x (c, state). (c+1, state \<bind> fk_update' x s\<^sub>1 s\<^sub>2 c)) xs (0, return_pmf (\<lambda>_. undefined))
  =  (length xs, prod_pmf ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) (\<lambda>_. (snd (fold (\<lambda>x (c,state). (c+1, state \<bind> fk_update'' x c)) xs (0, return_pmf undefined)))))"
  (is "?lhs = ?rhs")
proof (induction xs rule:rev_induct)
  case Nil
  thus ?case
    apply (simp, rule pmf_eqI)
    apply (simp add:pmf_prod_pmf)
    apply (rule conjI, rule impI)
     apply (simp add:indicator_def, rule conjI, rule impI)
      apply force
     using extensional_arb apply fastforce
    apply (simp add:extensional_def indicator_def)
    by blast
next
  case (snoc x xs)
  obtain t1 t2 where t_def: 
    "(t1,t2) = fold (\<lambda>x (c, state). (Suc c, state \<bind> fk_update'' x c)) xs (0, return_pmf undefined)"
    using surj_pair 
    by (smt (z3))
  have a:"fk_update' x s\<^sub>1 s\<^sub>2 (length xs) = (\<lambda>a. fk_update' x s\<^sub>1 s\<^sub>2 (length xs) a)" 
    by auto
  have c:"\<And>c. fk_update'' x c = (\<lambda>a. fk_update'' x c (fst a,snd a))" 
    by auto
  have "fst (fold (\<lambda>x (c, state). (Suc c, state \<bind> fk_update'' x c)) xs (0, return_pmf undefined)) = length xs"
    by (induction xs rule:rev_induct, simp, simp add:case_prod_beta)
  hence d:"t1 = length xs" 
    by (metis t_def fst_conv)

  show ?case using snoc
    apply (simp del:fk_update''.simps fk_update'.simps)
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
    apply (subst c, subst fk_update''.simps, simp)
    apply (simp add:d)
    apply (subst pair_pmfI)
    apply (rule arg_cong2[where f="bind_pmf"], simp)
    by force
qed

lemma fk_alg_aux_1:
  assumes "k \<ge> 2"
  assumes "\<epsilon> > 0 \<and> \<epsilon> < 1"
  assumes "\<delta> > 0"
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> x < n"
  assumes "xs \<noteq> []"
  defines "sketch \<equiv> fold (\<lambda>x state. state \<bind> fk_update x) xs (fk_init k \<delta> \<epsilon> n)"
  defines "s\<^sub>1 \<equiv> nat \<lceil>8*real k*(real n) powr (1-1/ real k)/ (real_of_rat \<delta>)\<^sup>2\<rceil>"
  defines "s\<^sub>2 \<equiv> nat \<lceil>-(32 * ln (real_of_rat \<epsilon>)/ 9)\<rceil>"
  shows "sketch = 
    map_pmf (\<lambda>x. (s\<^sub>1,s\<^sub>2,k,length xs, x)) 
    (snd (fold (\<lambda>x (c, state). (c+1, state \<bind> fk_update' x s\<^sub>1 s\<^sub>2 c)) xs (0, return_pmf (\<lambda>_. undefined))))"
  using assms(5)
proof (subst sketch_def, induction xs rule:rev_nonempty_induct)
  case (single x)
  then show ?case 
    by (simp add: map_bind_pmf bind_return_pmf s\<^sub>1_def[symmetric] s\<^sub>2_def[symmetric])
next
  case (snoc x xs)
  obtain t1 t2 where t:
    "fold (\<lambda>x (c, state). (Suc c, state \<bind> fk_update' x s\<^sub>1 s\<^sub>2 c)) xs (0, return_pmf (\<lambda>_. undefined)) 
    = (t1,t2)"
    by fastforce

  have "fst (fold (\<lambda>x (c, state). (Suc c, state \<bind> fk_update' x s\<^sub>1 s\<^sub>2 c)) xs (0, return_pmf (\<lambda>_. undefined)))
    = length xs"
    by (induction xs rule:rev_induct, simp, simp add:split_beta) 
  hence t1: "t1 = length xs" using t fst_conv by auto

  show ?case using snoc
    apply (simp add:  s\<^sub>1_def[symmetric] s\<^sub>2_def[symmetric] t del:fk_update'.simps fk_update.simps)
    apply (subst bind_map_pmf)
    apply (subst map_bind_pmf)
    apply simp
    by (subst map_bind_pmf, simp add:t1)
qed


lemma power_diff_sum:
  assumes "k > 0"
  shows "(a :: 'a :: {comm_ring_1,power})^k -b^k = (a-b) * sum (\<lambda>i. a^i * b^(k-1-i)) {0..<k}" (is "?lhs = ?rhs")
proof -
  have "?rhs = sum (\<lambda>i. a * (a^i * b^(k-1-i))) {0..<k} - sum (\<lambda>i. b * (a^i * b^(k-1-i))) {0..<k}"
    by (simp add: sum_distrib_left[symmetric] algebra_simps)
  also have "... = sum ((\<lambda>i. (a^i * b^(k-i))) \<circ> (\<lambda>i. i+1)) {0..<k} - sum (\<lambda>i. (a^i * b^(k-i))) {0..<k}"
    apply (rule arg_cong2[where f="(-)"])
    apply (rule sum.cong, simp, simp add:algebra_simps)
    apply (rule sum.cong, simp)
    apply (subst mult.assoc[symmetric], subst mult.commute, subst mult.assoc)
    by (rule arg_cong2[where f="(*)"], simp, simp add: power_eq_if)
  also have "... = sum (\<lambda>i. (a^i * b^(k-i))) (insert k {1..<k}) - sum (\<lambda>i. (a^i * b^(k-i))) (insert 0 {1..<k})"
    apply (rule arg_cong2[where f="(-)"])
    apply (subst sum.reindex[symmetric], simp)
     apply (rule sum.cong) using assms apply (simp add:atLeastLessThanSuc, simp)
    apply (rule sum.cong) using assms Icc_eq_insert_lb_nat 
     apply (metis One_nat_def Suc_pred atLeastLessThanSuc_atLeastAtMost le_add1 le_add_same_cancel1)
    by simp
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
    apply (rule mult_left_mono, rule power_mono, metis assms(2), metis assms(3))
    using assms by simp
  also have "\<And>i. i < k \<Longrightarrow> a ^ i * a ^ (k - 1 - i) = a ^ (k - Suc 0)"
    apply (subst power_add[symmetric])
    apply (rule arg_cong2[where f="power"], simp)
    using assms(1) by simp
  finally have t: "\<And>i. i < k \<Longrightarrow> a ^ i * b ^ (k - 1 - i) \<le> a ^ (k - Suc 0)"
    by blast
  have "a^k - b^k = (a-b) * sum  (\<lambda>i. a^i * b^(k-1-i)) {0..<k}"
    by (rule power_diff_sum[OF assms(1)])
  also have "... \<le> (a-b) * k * a^(k-Suc 0)"
    apply (subst mult.assoc)
    apply (rule mult_left_mono)
     apply (rule sum_mono[where g="\<lambda>_. a^(k-1)" and K="{0..<k}", simplified])
     apply (metis t)
    using assms(2) by auto
  finally show ?thesis by simp
qed

lemma fk_value_ge_0:
  assumes "xs \<noteq> []"
  shows "fk_value k xs > 0"
proof -
  have "rat_of_nat 1 \<le> rat_of_nat (card (set xs))"
    apply (rule of_nat_mono)
    using assms card_0_eq[where A="set xs"] 
    by (metis List.finite_set One_nat_def Suc_leI neq0_conv set_empty)
  also have "... \<le> fk_value k xs"
    apply (simp add:fk_value_def)
    apply (rule sum_mono[where K="set xs" and f="\<lambda>_.(1::rat)", simplified])
    by (metis  count_list_gr_1  of_nat_1 of_nat_power_le_of_nat_cancel_iff one_le_power)
  finally show  "fk_value k xs > 0" by (simp)
qed

text \<open>Specialization of the Hoelder inquality for sums.\<close>
lemma Holder_inequality_sum:
  assumes "p > (0::real)" "q > 0" "1/p + 1/q = 1"
  assumes "finite A"
  shows "\<bar>sum (\<lambda>x. f x * g x) A\<bar> \<le> (sum (\<lambda>x. \<bar>f x\<bar> powr p) A) powr (1/p) * (sum (\<lambda>x. \<bar>g x\<bar> powr q) A) powr (1/q)"
  using assms apply (simp add: lebesgue_integral_count_space_finite[symmetric])
  apply (rule Lp.Holder_inequality)
  by (simp add:integrable_count_space)+

lemma fk_estimate:
  assumes "xs \<noteq> []"
  assumes "k \<ge> 2"
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> x < n"
  shows "real (length xs) * real_of_rat (fk_value (2*k-1) xs) \<le> real n powr (1 - 1 / real k) * (real_of_rat (fk_value k xs))^2"
  (is "?lhs \<le> ?rhs")
proof -
  define M where "M = Max (count_list xs ` set xs)" 
  then obtain m where m_in: "m \<in> set xs" and m_def: "M = count_list xs m"
    by (metis (mono_tags, lifting) List.finite_set Max_in finite_imageI image_iff image_is_empty set_empty assms(1))

  have a2: "real M > 0" apply (simp add:M_def)
    by (metis (mono_tags, opaque_lifting) List.finite_set assms(1) Max_in bot_nat_0.not_eq_extremum count_list_gr_1 finite_imageI imageE image_is_empty linorder_not_less set_empty zero_less_one)
  have a1: "2*k-1 = (k-1) + k" by simp
  have a4: "(k-1) = k * ((k-1)/k)" by simp

  have a3: "M powr k \<le> real_of_rat (fk_value k xs)"
    apply (simp add:m_def fk_value_def of_rat_sum of_rat_power)
    apply (subst powr_realpow, simp) 
    using m_in  count_list_gr_1 apply force
    by (rule member_le_sum, metis m_in, simp, simp)

  have a5: "0 \<le> real_of_rat (fk_value k xs)" 
    using fk_value_ge_0[OF assms(1)] 
    by (simp add: order_le_less)
  hence a6: "real_of_rat (fk_value k xs) = real_of_rat (fk_value k xs) powr 1" by simp

  have "real (k - 1) / real k + 1 = real (k - 1) / real k + real k / real k"
    using assms by simp
  also have "... =  real (2 * k - 1) / real k"
    apply (subst add_divide_distrib[symmetric])
    apply (rule arg_cong2[where f="(/)"])
    apply (subst of_nat_diff) using assms(2) apply linarith
    apply (subst of_nat_diff) using assms(2) apply linarith
    by simp+
  finally have a7: "real (k - 1) / real k + 1 = real (2 * k - 1) / real k"
    by blast

  have a: "real_of_rat (fk_value (2*k-1) xs) \<le> M powr (k-1) * (real_of_rat (fk_value k xs)) "
    using a1 apply (simp add:fk_value_def of_rat_sum sum_distrib_left of_rat_mult power_add of_rat_power)
    apply (rule sum_mono)
    apply (rule mult_right_mono)
     apply (subst powr_realpow)
      apply (metis a2)
     apply (subst power_mono)
    by (simp add:M_def)+
  also have "... \<le>  (real_of_rat (fk_value k xs)) powr ((k-1)/k) * (real_of_rat (fk_value k xs))"
    apply (rule mult_right_mono)
     apply (subst a4)
     apply (subst powr_powr[symmetric])
    by (subst powr_mono2, simp, simp, metis a3, simp, metis a5)
  also have "... = (real_of_rat (fk_value k xs)) powr ((2*k-1) / k)"
    apply (subst (2) a6)
    apply (subst powr_add[symmetric])
    by (rule arg_cong2[where f="(powr)"], simp, metis a7)
  finally have a: "real_of_rat (fk_value (2*k-1) xs) \<le> (real_of_rat (fk_value k xs)) powr ((2*k-1) / k)"
    by blast

  have b1: "card (set xs) \<le> n"
    apply (rule card_mono[where B="{k. k < n}", simplified])
    by (rule subsetI, simp add: assms (3))

  have "real (length xs) = abs (sum (\<lambda>x. real (count_list xs x)) (set xs))"
    apply (subst of_nat_sum[symmetric])
    by (simp add: sum_count_set)
  also have "... \<le> (real (card (set xs))) powr ((k-Suc 0)/k) * (sum (\<lambda>x. abs (real (count_list xs x)) powr k) (set xs)) powr (1/k)"
    apply (rule Holder_inequality_sum[where p="k/(k-1)" and q="k" and A="set xs" and f="\<lambda>_.1", simplified])
    using assms apply (simp)
    using assms apply (simp)
    apply (subst add_divide_distrib[symmetric])
    using assms by simp
  also have "... \<le> real n powr (1 - 1 / real k) * real_of_rat (fk_value k xs) powr (1/real k)"
    apply (rule mult_mono)
       apply (subst of_nat_diff) using assms apply linarith
       apply (subst diff_divide_distrib) using assms apply simp
       apply (rule powr_mono2, force, simp)
    using b1  of_nat_le_iff apply blast
      apply (rule powr_mono2, force)
       apply (rule sum_mono[where f="\<lambda>_. 0", simplified])
       apply simp
      apply (simp add:fk_value_def of_rat_sum of_rat_power)
    apply (rule sum_mono)
      apply (subst powr_realpow, simp)
    using count_list_gr_1 
    by (metis gr0I not_one_le_zero, simp, simp, simp)

  finally have b: "real (length xs) \<le> real n powr (1 - 1 / real k) * real_of_rat (fk_value k xs) powr (1/real k)"
    by blast

  have c:"1 / real k + real (2 * k - 1) / real k = real 2"
    apply (subst add_divide_distrib[symmetric])
    apply (subst of_nat_diff) using assms(2) apply linarith
    using assms(2) by simp

  have "?lhs \<le> real n powr (1 - 1 / real k) * real_of_rat (fk_value k xs) powr (1/real k) *  (real_of_rat (fk_value k xs)) powr ((2*k-1) / k)"
    apply (rule mult_mono, metis b, metis a, simp, simp add:fk_value_def)
    apply (rule sum_mono[where f="\<lambda>_. (0::rat)", simplified])
    by auto
  also have "... \<le> ?rhs"
    apply (subst mult.assoc, subst powr_add[symmetric], subst mult_left_mono)
    apply (subst c, subst powr_realpow)
    using  fk_value_ge_0[OF assms(1)] by simp+
  finally show ?thesis
    by blast
qed

lemma fk_alg_core_exp:
  assumes "xs \<noteq> []"
  assumes "k \<ge> 2"
  shows "has_bochner_integral (measure_pmf (pmf_of_set {(u, v). v < count_list xs u}))
        (\<lambda>a. real (length xs) * real (Suc (snd a) ^ k - snd a ^ k)) (real_of_rat (fk_value k xs))"
proof -
  show ?thesis
    apply (subst has_bochner_integral_iff)
    apply (rule conjI)
     apply (rule integrable_measure_pmf_finite)
     apply (subst set_pmf_of_set, metis non_empty_space assms(1), metis fin_space assms(1))
    apply (subst integral_measure_pmf_real[OF fin_space[OF assms(1)]])
     apply (subst (asm) set_pmf_of_set[OF non_empty_space[OF assms(1)] fin_space[OF assms(1)]], simp)
    apply (subst pmf_of_set[OF non_empty_space[OF assms(1)] fin_space[OF assms(1)]])
    using assms(1) apply (simp add:card_space fk_value_def of_rat_sum of_rat_power)
    apply (subst split_space)
    apply (rule sum.cong, simp)
    apply (subst of_nat_diff) 
    apply (simp add: power_mono)
    apply (subst sum_Suc_diff', simp, simp)
    using assms by linarith
qed

lemma fk_alg_core_var:
  assumes "xs \<noteq> []"
  assumes "k \<ge> 2"
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> x < n"
  shows "has_variance (measure_pmf (pmf_of_set {(u, v). v < count_list xs u}))
        (\<lambda>a. real (length xs) * real (Suc (snd a) ^ k - snd a ^ k))
        (\<lambda>x. x \<le> (real_of_rat (fk_value k xs))\<^sup>2 * real k * real n powr (1 - 1 / real k))"
proof -
  define f :: "nat \<times> nat \<Rightarrow> real" 
    where "f = (\<lambda>x. (real (length xs) * real (Suc (snd x) ^ k - snd x ^ k)))"
  define \<Omega> where "\<Omega> = pmf_of_set {(u, v). v < count_list xs u}"
  
  have integrable: "\<And>k. integrable (measure_pmf \<Omega>) (\<lambda>\<omega>. f \<omega>^k)"
    apply (simp add:\<Omega>_def, rule integrable_measure_pmf_finite, subst set_pmf_of_set)
    using assms(1) fin_space non_empty_space set_pmf_of_set by auto

  have k_g_0: "k > 0" using assms by linarith

  have c:"\<And>a v. v < count_list xs a \<Longrightarrow> real (Suc v ^ k) - real (v ^ k) \<le> real k * real (count_list xs a) ^ (k - Suc 0)"
  proof -
    fix a v
    assume c_1: "v < count_list xs a"
    have "real (Suc v ^ k) - real (v ^ k) \<le> (real (v+1) - real v) * real k * (1 + real v) ^ (k - Suc 0)"
      using k_g_0 power_diff_est[where a="Suc v" and b="v" and k ="k"]
      by simp
    moreover have "(real (v+1) - real v) = 1" by auto
    ultimately have "real (Suc v ^ k) - real (v ^ k) \<le> real k * (1 + real v) ^ (k - Suc 0)"
      by auto
    also have "... \<le> real k * real (count_list xs a) ^ (k- Suc 0)"
      apply (rule mult_left_mono, rule power_mono)
      using c_1 apply linarith
      by simp+
    finally show "real (Suc v ^ k) - real (v ^ k) \<le> real k * real (count_list xs a) ^ (k- Suc 0)"
      by blast
  qed
      
  have "real (length xs) * (\<Sum>a\<in> set xs. (\<Sum>v \<in> {0..< count_list xs a}. (real (Suc v ^ k - v ^ k))\<^sup>2))
    \<le> real (length xs) * (\<Sum>a\<in> set xs. (\<Sum>v \<in> {0..< count_list xs a}. (real (k * count_list xs a ^ (k-1) * (Suc v ^ k - v ^ k)))))"
    apply (rule mult_left_mono)
     apply (rule sum_mono, rule sum_mono)
     apply (simp add:power2_eq_square)
     apply (rule mult_right_mono)
      apply (subst of_nat_diff, simp add:power_mono)
    by (metis c, simp, simp)
  also have "... = real (length xs) * (\<Sum>a\<in> set xs. real (k * count_list xs a ^ (2*k-1)))"
    apply (rule arg_cong2[where f="(*)"], simp)
    apply (rule sum.cong, simp)
    apply (simp add:sum_distrib_left[symmetric])
    apply (subst of_nat_diff, rule power_mono, simp, simp)
    apply (subst sum_Suc_diff', simp, simp add: zero_power[OF k_g_0] sum_distrib_left)
    apply (subst power_add[symmetric]) 
    using assms by (simp add: mult_2)
  also have "... = real (length xs) * real k * real_of_rat (fk_value (2*k-1) xs)"
    apply (subst mult.assoc)
    apply (rule arg_cong2[where f="(*)"], simp)
    by (simp add:sum_distrib_left[symmetric] fk_value_def of_rat_sum of_rat_power)
  also have "... \<le> real k * ((real_of_rat (fk_value k xs))\<^sup>2 * real n powr (1 - 1 / real k))"
    apply (subst mult.commute)
    apply (subst mult.assoc)
    apply (rule mult_left_mono)
    using fk_estimate[OF assms(1) assms(2) assms(3)] 
    by (simp add: mult.commute, simp)
  finally have b: "real (length xs) * (\<Sum>a\<in> set xs. (\<Sum>v \<in> {0..< count_list xs a}. (real (Suc v ^ k - v ^ k))\<^sup>2))
    \<le> real k * ((real_of_rat (fk_value k xs))\<^sup>2 * real n powr (1 - 1 / real k))"
    by blast

  have "measure_pmf.expectation \<Omega> (\<lambda>\<omega>. f \<omega>^2) - (measure_pmf.expectation \<Omega> f)^2 \<le> 
    measure_pmf.expectation \<Omega> (\<lambda>\<omega>. f \<omega>^2)" 
    by simp
  also have " measure_pmf.expectation \<Omega> (\<lambda>\<omega>. f \<omega>^2) \<le> (
    real_of_rat (fk_value k xs))\<^sup>2 * real k * real n powr (1 - 1 / real k)"
    apply (simp add:\<Omega>_def f_def)
    apply (subst integral_measure_pmf_real[OF fin_space[OF assms(1)]])
     apply (subst (asm) set_pmf_of_set[OF non_empty_space fin_space], metis assms(1), simp)
    apply (subst pmf_of_set[OF non_empty_space fin_space], metis assms(1))
    apply (simp add:card_space[OF assms(1)] power_mult_distrib)
    apply (subst mult.commute, subst (2) power2_eq_square, subst split_space)
    using assms(1) by (simp add:algebra_simps sum_distrib_left[symmetric] b)
  finally have a:"measure_pmf.expectation \<Omega> (\<lambda>\<omega>. f \<omega>^2) - (measure_pmf.expectation \<Omega> f)^2 \<le> 
    (real_of_rat (fk_value k xs))\<^sup>2 * real k * real n powr (1 - 1 / real k)"
    by blast

  show ?thesis
    using prob_space_measure_pmf[where p="\<Omega>"] integrable[where k="1", simplified] integrable
    apply (simp add: f_def[symmetric] \<Omega>_def[symmetric] has_variance_def prob_space.variance_eq)
    using a by simp+
qed

lemma fk_alg_sketch:
  assumes "k \<ge> 2"
  assumes "\<epsilon> > 0 \<and> \<epsilon> < 1"
  assumes "\<delta> > 0"
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> x < n"
  assumes "xs \<noteq> []"
  defines "sketch \<equiv> fold (\<lambda>x state. state \<bind> fk_update x) xs (fk_init k \<delta> \<epsilon> n)"
  defines "s\<^sub>1 \<equiv> nat \<lceil>8*real k*(real n) powr (1-1/ real k)/ (real_of_rat \<delta>)\<^sup>2\<rceil>"
  defines "s\<^sub>2 \<equiv> nat \<lceil>-(32 * ln (real_of_rat \<epsilon>)/ 9)\<rceil>"
  shows "sketch = map_pmf (\<lambda>x. (s\<^sub>1,s\<^sub>2,k,length xs, x)) 
    (prod_pmf ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) (\<lambda>_. pmf_of_set {(u,v). v < count_list xs u}))" 
  apply (simp add:sketch_def)
  using fk_alg_aux_1[OF assms(1) assms(2) assms(3) assms(4) assms(5)]
  apply (simp add:s\<^sub>1_def[symmetric] s\<^sub>2_def[symmetric])
  apply (rule arg_cong2[where f="map_pmf"], simp)
  apply (subst fk_alg_aux_2[simplified], simp)
  apply (subst fk_alg_aux_4[OF assms(5), simplified], simp)
  by (subst fk_alg_aux_5[OF assms(5), simplified], simp)

lemma fk_alg_correct:
  assumes "k \<ge> 2"
  assumes "\<epsilon> > 0 \<and> \<epsilon> < 1"
  assumes "\<delta> > 0"
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> x < n"
  assumes "xs \<noteq> []"
  defines "sketch \<equiv> fold (\<lambda>x state. state \<bind> fk_update x) xs (fk_init k \<delta> \<epsilon> n)"
  shows "\<P>(\<omega> in measure_pmf (sketch \<bind> fk_result). abs (\<omega> - fk_value k xs) \<ge> (\<delta> * fk_value k xs)) \<le> real_of_rat \<epsilon>"
proof -
  define s\<^sub>1 where "s\<^sub>1 = nat \<lceil>8*real k*(real n) powr (1-1/ real k)/ (real_of_rat \<delta>)\<^sup>2\<rceil>"
  define s\<^sub>2 where "s\<^sub>2 = nat \<lceil>-(32 * ln (real_of_rat \<epsilon>)/ 9)\<rceil>"

  define f :: "(nat \<times> nat \<Rightarrow> (nat \<times> nat)) \<Rightarrow> rat"
    where "f = (\<lambda>x. median
             (\<lambda>i\<^sub>2\<in>{0..<s\<^sub>2}.
                 (\<Sum>i\<^sub>1 = 0..<s\<^sub>1. rat_of_nat (length xs * (Suc (snd (x (i\<^sub>1, i\<^sub>2))) ^ k - snd (x (i\<^sub>1, i\<^sub>2)) ^ k))) /
                 rat_of_nat s\<^sub>1)
             s\<^sub>2)"

  define f2 :: "(nat \<times> nat \<Rightarrow> (nat \<times> nat)) \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> real)"
    where "f2 = (\<lambda>x i\<^sub>1 i\<^sub>2. real (length xs * (Suc (snd (x (i\<^sub>1, i\<^sub>2))) ^ k - snd (x (i\<^sub>1, i\<^sub>2)) ^ k)))"
  define f1 :: "(nat \<times> nat \<Rightarrow> (nat \<times> nat)) \<Rightarrow> (nat \<Rightarrow> real)"
    where "f1 = (\<lambda>x i\<^sub>2. (\<Sum>i\<^sub>1 = 0..<s\<^sub>1. f2 x i\<^sub>1 i\<^sub>2) / real s\<^sub>1)"
  define f' :: "(nat \<times> nat \<Rightarrow> (nat \<times> nat)) \<Rightarrow> real"
    where "f' = (\<lambda>x. median (f1 x) s\<^sub>2)"

  have "set xs \<noteq> {}" using assms by blast
  hence n_nonzero: "n > 0" using assms(4) by fastforce

  have fk_nonzero: "fk_value k xs > 0" using fk_value_ge_0 assms by simp

  have s1_nonzero: "s\<^sub>1 > 0"
    apply (simp add:s\<^sub>1_def)
    apply (rule divide_pos_pos)
    apply (rule mult_pos_pos)
    using assms apply linarith
    apply (simp add:n_nonzero)
    by (meson assms zero_less_of_rat_iff zero_less_power)
  have s2_nonzero: "s\<^sub>2 > 0" using assms by (simp add:s\<^sub>2_def) 
  have real_of_rat_f: "\<And>x. f' x = real_of_rat (f x)"
    using s2_nonzero apply (simp add:f_def f'_def f1_def f2_def median_rat median_restrict)
    apply (rule arg_cong2[where f="median"])
    by (simp add:of_rat_divide of_rat_sum of_rat_mult, simp)

  define \<Omega> where "\<Omega> = pmf_of_set {(u, v). v < count_list xs u}"

  have a:"sketch = map_pmf (\<lambda>x. (s\<^sub>1,s\<^sub>2,k,length xs, x)) 
    (prod_pmf ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) (\<lambda>_. pmf_of_set {(u,v). v < count_list xs u}))"
    apply (subst sketch_def)
    apply (subst fk_alg_sketch[OF assms(1) assms(2) assms(3) assms(4) assms(5)], simp)
    by (simp add:s\<^sub>1_def[symmetric] s\<^sub>2_def[symmetric])

  have "sketch \<bind> fk_result = sketch \<bind> (\<lambda>(x,y,z,u,v). fk_result (x,y,z,u,v))"
    by (rule arg_cong2[where f="bind_pmf"], simp, simp del:fk_result.simps)
  also have "... = prod_pmf ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) (\<lambda>_. \<Omega>) \<bind> return_pmf \<circ> f"
    apply (simp add:a map_pmf_def)
    apply (subst bind_assoc_pmf)
    apply (subst bind_return_pmf)
    by (simp add:f_def comp_def \<Omega>_def)
  finally have b: "sketch \<bind> fk_result = prod_pmf ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) (\<lambda>_. \<Omega>) \<bind> return_pmf \<circ> f"
    by blast

  have c: "{y. real_of_rat (\<delta> * fk_value k xs) \<le> \<bar>f' y - real_of_rat (fk_value k xs)\<bar>} = 
    {y. (\<delta> * fk_value k xs) \<le> \<bar>f y - (fk_value k xs)\<bar>}"
    apply (simp add:real_of_rat_f) 
    by (metis abs_of_rat of_rat_diff of_rat_less_eq)

  have f2_exp: "\<And>i\<^sub>1 i\<^sub>2. i\<^sub>1 < s\<^sub>1 \<Longrightarrow> i\<^sub>2 < s\<^sub>2 \<Longrightarrow> 
    has_bochner_integral (measure_pmf (prod_pmf ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) (\<lambda>_. \<Omega>))) (\<lambda>x. f2 x i\<^sub>1 i\<^sub>2)
            (real_of_rat (fk_value k xs))"
    apply (simp add:f2_def \<Omega>_def of_rat_mult  of_rat_sum of_rat_power)
    apply (rule has_bochner_integral_prod_pmf_sliceI, simp, simp)
    by (rule fk_alg_core_exp, metis assms(5), metis assms(1))

  have "8 * real k * real n powr (1 - 1 / real k) = (real_of_rat \<delta>)\<^sup>2 * (8 * real k * real n powr (1 - 1 / real k) / (real_of_rat \<delta>)\<^sup>2)"
    using assms by simp
  also have "... \<le>  (real_of_rat \<delta>)\<^sup>2 * (real s\<^sub>1)"
    apply (rule mult_mono, simp)
    apply (simp add:s\<^sub>1_def) 
      apply (meson of_nat_ceiling)
    using assms apply simp
    by simp
  finally have f2_var_2: "8 * real k * real n powr (1 - 1 / real k) \<le> (real_of_rat \<delta>)\<^sup>2 * (real s\<^sub>1)"
    by blast
  have "(real_of_rat (fk_value k xs))\<^sup>2 * real k * real n powr (1 - 1 / real k) =
    (real_of_rat (fk_value k xs))\<^sup>2 * (real k * real n powr (1 - 1 / real k))"
    by (simp add:ac_simps)
  also have "... \<le> (real_of_rat (fk_value k xs * \<delta>))\<^sup>2 * (real s\<^sub>1 / 8)"
    apply (subst of_rat_mult, subst power_mult_distrib) 
    apply (subst mult.assoc[where c="real s\<^sub>1 / 8"])
    apply (rule mult_mono, simp) using f2_var_2
    by (simp+)
  finally have f2_var_1: "(real_of_rat (fk_value k xs))\<^sup>2 * real k * real n powr (1 - 1 / real k) \<le> (real_of_rat (\<delta> * fk_value k xs))\<^sup>2 * real s\<^sub>1 / 8"
    by (simp add: mult.commute)
  
  have f2_var: "\<And>i\<^sub>1 i\<^sub>2. i\<^sub>1 < s\<^sub>1 \<Longrightarrow> i\<^sub>2 < s\<^sub>2 \<Longrightarrow>
       has_variance (measure_pmf (prod_pmf ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) (\<lambda>_. \<Omega>))) (\<lambda>\<omega>. f2 \<omega> i\<^sub>1 i\<^sub>2)
          (\<lambda>x. x \<le> (real_of_rat (\<delta> * fk_value k xs))\<^sup>2 * real s\<^sub>1 / 8)" 
    apply (subst f2_def, rule has_variance_prod_pmf_sliceI, simp, simp)
    apply (rule has_variance_imp [where r="\<lambda>x. x \<le> (real_of_rat (fk_value k xs))\<^sup>2 *
                 real k * real n powr (1 - 1 / real k)"])
    using f2_var_1 order_trans apply blast
    apply (simp add: \<Omega>_def)
    using assms fk_alg_core_var by blast

  have f1_exp_1: "(real_of_rat (fk_value k xs)) = (\<Sum>i \<in> {0..<s\<^sub>1}. (real_of_rat (fk_value k xs))/real s\<^sub>1)"
    by (simp add:s1_nonzero)

  have f1_exp: "\<And>i. i < s\<^sub>2 \<Longrightarrow> 
      has_bochner_integral (prod_pmf ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) (\<lambda>_. \<Omega>)) (\<lambda>\<omega>. f1 \<omega> i) 
    (real_of_rat (fk_value k xs))"
    apply (simp add:f1_def sum_divide_distrib)
    apply (subst f1_exp_1)
    apply (rule has_bochner_integral_sum)
    apply (rule has_bochner_integral_divide_zero)
    by (simp add: f2_exp)

  have f1_var: "\<And>i. i < s\<^sub>2 \<Longrightarrow> 
      has_variance (prod_pmf ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) (\<lambda>_. \<Omega>)) (\<lambda>\<omega>. f1 \<omega> i) 
    (\<lambda>r. r \<le> real_of_rat (\<delta> * fk_value k xs)^2/8)" (is "\<And>i. _ \<Longrightarrow> ?rhs i")
  proof -
    fix i
    assume f1_var_1:"i < s\<^sub>2" 
    show "?rhs i"
      apply (simp add:f1_def sum_divide_distrib)
      apply (rule prob_space.has_variance_sum [where r="(\<lambda>i r. r \<le> real_of_rat (\<delta> * fk_value k xs)^2/(8*real s\<^sub>1))"])
          apply (metis prob_space_measure_pmf)
         apply (simp)
        apply (rule indep_vars_restrict_intro[where f="\<lambda>j. {j} \<times> {i}"])
            apply (simp add:f2_def)
           apply (simp add:disjoint_family_on_def)
          apply (simp add:s1_nonzero)
         apply (simp add:f1_var_1)
        apply simp
       apply simp
       apply (rule has_variance_divide)
       apply (subst pos_divide_le_eq) using s1_nonzero apply simp
       apply (subst (2) power2_eq_square)
       using f2_var[OF _ f1_var_1] apply (simp)
      using s1_nonzero sum_mono[where K = "{0..<s\<^sub>1}" and g="\<lambda>_.  (real_of_rat (\<delta> * fk_value k xs))\<^sup>2/8/(real s\<^sub>1)"]
      by simp
  qed

  have d: " \<And>i. i < s\<^sub>2 \<Longrightarrow>
    measure_pmf.prob (prod_pmf ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) (\<lambda>_. \<Omega>))
      {y. real_of_rat (\<delta> * fk_value k xs) \<le> \<bar>f1 y i - real_of_rat (fk_value k xs)\<bar>} \<le> 1/8" (is "\<And>i. _ \<Longrightarrow> ?lhs i \<le> _")
  proof -
    fix i
    assume d_1:"i < s\<^sub>2"
    define a where "a = real_of_rat (\<delta> * fk_value k xs)"
    have d_2: "0 < a" apply (simp add:a_def)
      using assms fk_nonzero mult_pos_pos by blast
    have d_3: "integrable (measure_pmf (prod_pmf ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) (\<lambda>_. \<Omega>))) (\<lambda>x. (f1 x i)\<^sup>2)"
      using f1_var[OF d_1] by (simp add:has_variance_def) 
    have "?lhs i \<le> prob_space.variance (prod_pmf ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) (\<lambda>_. \<Omega>)) (\<lambda>\<omega>. f1 \<omega> i)/a^2"
      using f1_exp[OF d_1]
      using prob_space.Chebyshev_inequality[OF prob_space_measure_pmf _ d_3 d_2, simplified]
      by (simp add:a_def[symmetric] has_bochner_integral_iff)
    also have "... \<le> 1/8" using d_2
      using f1_var[OF d_1] 
      by (simp add:algebra_simps has_variance_def, simp add:a_def)
    finally show "?lhs i \<le> 1/8"
      by blast
  qed

  show ?thesis
    apply (simp add: b comp_def map_pmf_def[symmetric])
    apply (subst c[symmetric])
    apply (simp add:f'_def)
    apply (rule prob_space.median_bound[where X="\<lambda>i \<omega>. f1 \<omega> i" and M="(prod_pmf ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) (\<lambda>_. \<Omega>))", simplified])
         apply (simp add:prob_space_measure_pmf)
        using assms(2) apply simp
       using assms(2) apply simp
       apply (simp add:f1_def f2_def)
       apply (rule indep_vars_restrict_intro[where f="\<lambda>i. ({0..<s\<^sub>1}\<times>{i})"])
           apply (simp)
          apply (simp add:disjoint_family_on_def, blast)
         apply (simp add:s2_nonzero)
        apply (rule subsetI, simp, force)
       apply(simp)
      apply (simp)
     apply (simp add: s\<^sub>2_def) 
       using of_nat_ceiling apply blast 
     using d by simp
qed


lemma fk_alg_space:
  assumes "k \<ge> 2"
  assumes "\<epsilon> > 0 \<and> \<epsilon> < 1"
  assumes "\<delta> > 0"
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> x < n"
  assumes "xs \<noteq> []"
  defines "sketch \<equiv> fold (\<lambda>x state. state \<bind> fk_update x) xs (fk_init k \<delta> \<epsilon> n)"
  shows "AE \<omega> in sketch. bit_count (encode_state \<omega>) \<le> 3128"
proof -
  define s\<^sub>1 where "s\<^sub>1 = nat \<lceil>8*real k*(real n) powr (1-1/ real k)/ (real_of_rat \<delta>)\<^sup>2\<rceil>"
  define s\<^sub>2 where "s\<^sub>2 = nat \<lceil>-(32 * ln (real_of_rat \<epsilon>)/ 9)\<rceil>"

  (* log 2 s1 + log 2 s2 + log 2 k + log 2 m + s1*s2*(log 2 m + log 2 n) 

      k can be arbitrarily large
      doesn't matter because k < s1

  *)
  show ?thesis sorry
qed



end
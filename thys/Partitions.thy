section \<open>Partitions\<close>

theory Partitions
  imports Main "HOL-Library.Multiset" "HOL.Real" List_Ext
begin

text \<open>In this section, we define a function that enumerates all the partitions of
@{text "{0..<n}"}. We represent the partitions as lists with @{text "n"} elements. If the element
at index @{text "i"} and @{text "j"} have the same value, then @{text "i"} and @{text "j"} are in
the same partition.\<close>

fun enum_partitions_aux :: "nat \<Rightarrow> (nat \<times> nat list) list"
  where
    "enum_partitions_aux 0 = [(0, [])]" |
    "enum_partitions_aux (Suc n) = 
      [(c+1, c#x). (c,x) \<leftarrow> enum_partitions_aux n]@
      [(c, y#x). (c,x) \<leftarrow> enum_partitions_aux n,  y \<leftarrow> [0..<c]]"

fun enum_partitions where "enum_partitions n = map snd (enum_partitions_aux n)"

definition has_eq_relation :: "nat list \<Rightarrow> 'a list \<Rightarrow> bool"  where
  "has_eq_relation r xs = (length xs = length r \<and> (\<forall>i < length xs. \<forall>j < length xs. (xs ! i = xs ! j) = (r ! i = r ! j)))"

lemma filter_one_elim:
  "length (filter p xs) = 1 \<Longrightarrow> (\<exists>u v w. xs = u@v#w \<and> p v \<and> length (filter p u) = 0 \<and> length (filter p w) = 0)"
  (is "?A xs \<Longrightarrow> ?B xs")
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case
    apply (cases "p a") 
     apply (simp, metis append.left_neutral filter.simps(1))
    by (simp, metis append_Cons filter.simps(2))
qed

lemma has_eq_elim:
  "has_eq_relation (r#rs) (x#xs) = (
    (\<forall>i < length xs. (r = rs ! i) = (x = xs ! i)) \<and>
    has_eq_relation rs xs)"
proof
  assume a:"has_eq_relation (r#rs) (x#xs)"
  have "\<And>i j. i < length xs \<Longrightarrow> j < length xs \<Longrightarrow> (xs ! i = xs ! j) = (rs ! i = rs ! j)"
    (is "\<And>i j. ?l1 i \<Longrightarrow> ?l2 j \<Longrightarrow> ?rhs i j")
  proof -
    fix i j
    assume "i < length xs"
    hence "Suc i < length (x#xs)" by auto
    moreover assume "j < length xs"
    hence "Suc j < length (x#xs)" by auto
    ultimately show "?rhs i j" using a apply (simp only:has_eq_relation_def) 
      by (metis nth_Cons_Suc)
  qed
  hence "has_eq_relation rs xs" using a by (simp add:has_eq_relation_def)
  thus "(\<forall>i<length xs. (r = rs ! i) = (x = xs ! i)) \<and> has_eq_relation rs xs"
    apply simp
    using a apply (simp only:has_eq_relation_def)
    by (metis Suc_less_eq length_Cons nth_Cons_0 nth_Cons_Suc zero_less_Suc)
next
  assume a:"(\<forall>i<length xs. (r = rs ! i) = (x = xs ! i)) \<and> has_eq_relation rs xs"
  have "\<And>i j. i<Suc (length rs) \<Longrightarrow> j<Suc (length rs) \<Longrightarrow> ((x # xs) ! i = (x # xs) ! j) = ((r # rs) ! i = (r # rs) ! j)"
    (is "\<And>i j. ?l1 i \<Longrightarrow> ?l2 j \<Longrightarrow> ?rhs i j")
  proof -
    fix i j
    assume "i < Suc (length rs)"
    moreover assume "j < Suc (length rs)" 
    ultimately show "?rhs i j" using a
      apply (cases i, cases j)
      apply (simp add: has_eq_relation_def)
      apply (cases j)
      apply (simp add: has_eq_relation_def)+
      by (metis less_Suc_eq_0_disj nth_Cons' nth_Cons_Suc)
  qed
  then show "has_eq_relation (r # rs) (x # xs)"
    using a by (simp add:has_eq_relation_def)
qed

lemma enum_partitions_aux_range:
  "x \<in> set (enum_partitions_aux n) \<Longrightarrow> set (snd x) = {k. k < fst x}"
  by (induction n arbitrary:x, simp, simp, force)

lemma enum_partitions_aux_len:
  "x \<in> set (enum_partitions_aux n) \<Longrightarrow> length (snd x) = n"
  by (induction n arbitrary:x, simp, simp, force)

lemma enum_partitions_complete_aux: "k < n \<Longrightarrow> length (filter (\<lambda>x. x = k) [0..<n]) = Suc 0"
  by (induction n, simp, simp)

lemma enum_partitions_complete:
  "length (filter (\<lambda>p. has_eq_relation p x) (enum_partitions (length x))) = 1"
proof (induction "x")
  case Nil
  then show ?case by (simp add:has_eq_relation_def)
next
  case (Cons a y)
  have "length (filter (\<lambda>x. has_eq_relation (snd x) y) (enum_partitions_aux (length y))) = 1"
    using Cons by (simp add:comp_def) 
  then obtain p1 p2 p3 where pi_def: "enum_partitions_aux (length y) = p1@p2#p3" and
   p2_t: "has_eq_relation (snd p2) y" and
   p1_f1: "filter (\<lambda>x. has_eq_relation (snd x) y) p1 = []" and
   p3_f1: "filter (\<lambda>x. has_eq_relation (snd x) y) p3 = []"
    using Cons filter_one_elim by (metis (no_types, lifting) length_0_conv)
  have p2_e: "p2 \<in> set(enum_partitions_aux (length y))" 
    using pi_def by auto
  have p1_f: "\<And>x p. x \<in> set p1 \<Longrightarrow> has_eq_relation (p#(snd x)) (a#y) = False"
    by (metis p1_f1 filter_empty_conv has_eq_elim)
  have p3_f: "\<And>x p. x \<in> set p3 \<Longrightarrow> has_eq_relation (p#(snd x)) (a#y) = False"
    by (metis p3_f1 filter_empty_conv has_eq_elim)
  show ?case
  proof (cases "a \<in> set y")
    case True
    then obtain h where h_def: "h < length y \<and> a = y ! h" by (metis in_set_conv_nth)
    define k where "k = snd p2 ! h"
    have k_bound: "k < fst p2"
      using enum_partitions_aux_len enum_partitions_aux_range p2_e k_def h_def 
      by (metis mem_Collect_eq nth_mem)
    have k_eq: "\<And>i. has_eq_relation (i # snd p2) (a # y) = (i = k)" 
      apply (simp add:has_eq_elim p2_t k_def)
      using h_def has_eq_relation_def p2_t by auto
    show ?thesis 
      apply (simp add: filter_concat length_concat case_prod_beta' comp_def)
      apply (simp add: pi_def p1_f p3_f cong:map_cong)
      by (simp add: k_eq k_bound enum_partitions_complete_aux)
  next
    case False
    hence "has_eq_relation (fst p2 # snd p2) (a # y)"
      apply (simp add:has_eq_elim p2_t)
      using enum_partitions_aux_range p2_e
      by (metis enum_partitions_aux_len mem_Collect_eq nat_neq_iff nth_mem)
    moreover have "\<And>i. i < fst p2 \<Longrightarrow> \<not>(has_eq_relation (i # snd p2) (a # y))" 
      apply (simp add:has_eq_elim p2_t)
      by (metis False enum_partitions_aux_range p2_e has_eq_relation_def in_set_conv_nth mem_Collect_eq p2_t)
    ultimately show ?thesis
      apply (simp add: filter_concat length_concat case_prod_beta' comp_def)
      by (simp add: pi_def p1_f p3_f cong:map_cong)
  qed
qed


fun verify where
  "verify r x 0 _ = True" |
  "verify r x (Suc n) 0 = verify r x n n" |
  "verify r x (Suc n) (Suc m) = (((r ! n = r ! m) = (x ! n = x ! m)) \<and> (verify r x (Suc n) m))"

lemma verify_elim_1:
  "verify r x (Suc n) m = (verify r x n n \<and>  (\<forall>i < m. (r ! n = r ! i) = (x ! n = x ! i)))"
  apply (induction m, simp, simp) 
  using less_Suc_eq by auto

lemma verify_elim:
  "verify r x m m = (\<forall>i < m. \<forall>j < i. (r ! i = r ! j) = (x ! i = x ! j))"
  apply (induction m, simp, simp add:verify_elim_1)
  apply (rule order_antisym, simp, metis less_antisym less_trans)
  apply (simp) 
  using less_Suc_eq by presburger

lemma has_eq_relation_elim:
  "has_eq_relation r xs = (length r = length xs \<and> verify r xs (length xs) (length xs))"
  apply (simp add: has_eq_relation_def verify_elim ) 
  by (metis (mono_tags, lifting) less_trans nat_neq_iff)

lemma sum_filter: "sum_list (map (\<lambda>p. if f p then (r::real) else 0) y) = r*(length (filter f y))"
  by (induction y, simp, simp add:algebra_simps)

lemma sum_partitions: "sum_list (map (\<lambda>p. if has_eq_relation p x then (r::real) else 0) (enum_partitions (length x))) = r"
  by (metis mult.right_neutral of_nat_1 enum_partitions_complete sum_filter)

lemma sum_partitions': 
  assumes "n = length x"
  shows "sum_list (map (\<lambda>p. of_bool (has_eq_relation p x) * (r::real)) (enum_partitions n)) = r"
  apply (simp add:of_bool_def comp_def assms del:enum_partitions.simps)
  apply (subst (2) sum_partitions[where x="x" and r="r", symmetric]) 
  apply (rule arg_cong[where f="sum_list"])
  apply (rule map_cong, simp)
  by simp

lemma eq_rel_obtain_bij:
  assumes "has_eq_relation u v"
  obtains f where "bij_betw f (set u) (set v)" "\<And>y. y \<in> set u \<Longrightarrow> count_list u y = count_list v (f y)"
proof -
  define A where "A = (\<lambda>x. {k. k < length u \<and> u ! k = x})"
  define q where "q = (\<lambda>x. v ! (Min (A x)))"

  have A_ne_iff: "\<And>x. x \<in> set u \<Longrightarrow> A x \<noteq> {}" by (simp add:A_def in_set_conv_nth) 
  have f_A: "\<And>x. finite (A x)" by (simp add:A_def)

  have a:"inj_on q (set u)"
  proof (rule inj_onI)
    fix x y
    assume a_1:"x \<in> set u" "y \<in> set u"
    have "length u > 0" using a_1 by force
    define xi where "xi = Min (A x)"
    have xi_l: "xi < length u"
      using Min_in[OF f_A A_ne_iff[OF a_1(1)]]
      by (simp add:xi_def A_def) 
    have xi_v: "u ! xi = x" 
      using Min_in[OF f_A A_ne_iff[OF a_1(1)]]
      by (simp add:xi_def A_def) 
    define yi where "yi = Min (A y)"
    have yi_l: "yi < length u" 
      using Min_in[OF f_A A_ne_iff[OF a_1(2)]]
      by (simp add:yi_def A_def) 
    have yi_v: "u ! yi = y" 
      using Min_in[OF f_A A_ne_iff[OF a_1(2)]]
      by (simp add:yi_def A_def) 

    assume "q x = q y"
    hence "v ! xi = v ! yi"
      by (simp add:q_def xi_def yi_def)
    hence "u ! xi = u ! yi"
      by (metis (no_types, lifting) has_eq_relation_def assms(1) xi_l yi_l)
    thus "x = y"
      using yi_v xi_v by blast
  qed

  have b:"\<And>y. y \<in> set u \<Longrightarrow> count_list u y = count_list v (q y)"
  proof -
    fix y
    assume b_1:"y \<in> set u"
    define i where "i = Min (A y)"
    have i_bound: "i < length u" 
      using Min_in[OF f_A A_ne_iff[OF b_1]]
      by (simp add:i_def A_def) 
    have y_def: "y = u ! i"
      using Min_in[OF f_A A_ne_iff[OF b_1]]
      by (simp add:i_def A_def) 

    have "count_list u y =  card {k. k < length u \<and> u ! k = u ! i}"
      by (simp add:count_list_card y_def)
    also have "... = card {k. k < length v \<and> v ! k = v ! i}"
      apply (rule arg_cong[where f="card"])
      apply (rule set_eqI, simp)
      by (metis (no_types, lifting) assms(1) has_eq_relation_def i_bound)
    also have "... = card {k. k < length v \<and> v ! k = q y}"
      by (simp add:q_def i_def)
    also have "... = count_list v (q y)"
      by (simp add:count_list_card)
    finally show "count_list u y = count_list v (q y)"
      by simp
  qed

  have c:"q ` set u \<subseteq> set v" 
    apply (rule image_subsetI)
    by (metis b count_list_gr_1)

  have d_1:"length v = length u" using assms has_eq_relation_def by blast
  also have "... = sum (count_list u) (set u)"
    by (simp add:sum_count_set)
  also have "... = sum ((count_list v) \<circ> q) (set u)"
    by (rule sum.cong, simp, simp add:comp_def b)
  also have "... = sum (count_list v) (q ` set u)"
    by (rule sum.reindex[OF a, symmetric])
  finally have d_1:"sum (count_list v) (q ` set u) = length v"
    by simp

  have "sum (count_list v) (q ` set u) + sum (count_list v) (set v - (q ` set u)) = sum (count_list v) (set v)"
    apply (subst sum.union_disjoint[symmetric], simp, simp, simp)
    apply (rule sum.cong)
    using c apply blast
    by simp
  also have "... = length v"
    by (simp add:sum_count_set)
  finally have d_2:"sum (count_list v) (q ` set u) + sum (count_list v) (set v - (q ` set u)) = length v" by simp

  have "sum (count_list v) (set v - (q ` set u)) = 0"
    using d_1 d_2 by linarith

  hence "\<And>x. x \<in> (set v - (q ` set u)) \<Longrightarrow> count_list v x \<le> 0"
    using member_le_sum by simp
  hence "\<And>x. x \<in> (set v - (q ` set u)) \<Longrightarrow> False"
    by (metis count_list_gr_1 Diff_iff le_0_eq not_one_le_zero)
  hence "set v - (q ` set u) = {}"
    by blast

  hence e: "q ` set u = set v"
    using c by blast

  have d:"bij_betw q (set u) (set v)"
    apply (simp add: bij_betw_def)
    using c e a by blast
  have "\<exists>f. bij_betw f (set u) (set v) \<and> (\<forall>y \<in> set u. count_list u y = count_list v (f y))"
    using b d by blast
  with that show ?thesis by blast
qed

end

theory Partitions_2
  imports Main  "HOL-Library.Multiset"
begin

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

fun remdups_indices 
  where 
    "remdups_indices [] = []" |
    "remdups_indices (r#rs) = (if r \<in> set rs then id else (#) 0 ) (map Suc (remdups_indices rs))" 

fun count_list_p where "count_list_p r k = count_list r (r ! k)"

definition remdups_p where "remdups_p r xs = map ((!) xs) (remdups_indices r)"

lemma remdups_indices_range:
  "k \<in> set (remdups_indices r) \<Longrightarrow> k < length r"
proof (induction r arbitrary:k)
  case Nil
  then show ?case by simp
next
  case (Cons a r)
  then show ?case by (cases "a \<in> set r", simp, blast, simp, blast)
qed

lemma
  assumes "has_eq_relation r xs"
  shows set_xs: "set xs = set (remdups_p r xs)" and
    distinct_set_xs: "distinct (remdups_p r xs)"
proof -
  have a:"set (map ((!) r) (remdups_indices r)) = set r"
    apply (induction r, simp, simp) 
    by (metis (no_types, lifting) image_cong image_image insert_absorb nth_Cons_Suc)
  have "set xs \<subseteq> set (remdups_p r xs)"
  proof 
    fix x
    assume "x \<in> set xs"
    then obtain k where k_bound: "k < length xs" and x_def: "x = xs ! k" by (metis in_set_conv_nth)
    hence "r ! k \<in> set r" using k_bound assms by (simp add:has_eq_relation_def)
    then obtain j where j_set: "j \<in> set (remdups_indices r)" and j_k_r: "r ! k = r ! j"
      by (metis (no_types, lifting) a in_set_conv_nth length_map nth_map)
    moreover have "j < length r" using remdups_indices_range j_set by blast
    ultimately have "x = xs ! j" using k_bound j_set a assms by (simp add:has_eq_relation_def x_def)
    thus "x \<in> set (remdups_p r xs)"
      apply (simp add:remdups_p_def)
      using j_set by blast
  qed
  moreover have "set (remdups_p r xs) \<subseteq> set xs"
    apply (simp add:remdups_p_def)
    by (metis remdups_indices_range assms has_eq_relation_def image_subsetI nth_mem)
  ultimately show "set xs = set (remdups_p r xs)"
    by auto
  have "length (remdups_indices r) = card (set r)"
    by (induction r, simp, simp add:insert_absorb)   
  hence "distinct (map ((!) r) (remdups_indices r))"
    by (metis card_distinct length_map a)
  thus "distinct (remdups_p r xs)" using assms
    by (simp add:has_eq_relation_def remdups_indices_range remdups_p_def distinct_conv_nth) 
qed

lemma count_xs_aux:
  "count (mset x) y = count_list x y"
  by (induction x, simp, simp)

lemma count_card: "count_list xs x = card {k. k < length xs \<and> xs ! k = x}"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  have "Suc ` {k. k < length xs \<and> xs ! k = x} = {k. k < Suc (length xs) \<and> (a # xs) ! k = x \<and> k > 0}"
    apply (rule order_antisym, rule image_subsetI, simp, rule subsetI, simp)
    using less_Suc_eq_0_disj by fastforce
  hence a:"card {k. k < length xs \<and> xs ! k = x} = card {k. k < Suc (length xs) \<and> (a # xs) ! k = x \<and> k > 0}"
    by (metis (no_types, lifting) card_image inj_Suc)
  have b:"\<And>A B. finite A \<Longrightarrow> 0 \<notin> A \<Longrightarrow> B = insert 0 A \<Longrightarrow> Suc (card A) = card B"
    by (simp)
  show ?case 
    apply (cases "a=x")
     apply (simp add:a Cons)
     apply (rule b, simp, simp)
    apply (rule order_antisym, rule subsetI, simp, blast, rule subsetI, simp)
     apply (meson nth_Cons_0 zero_less_Suc)
     apply (simp add:a Cons)
    apply (rule arg_cong [where f="card"])
    apply (rule order_antisym, rule subsetI, simp, rule subsetI, simp) 
    by (meson nth_non_equal_first_eq)
qed


lemma count_xs:
  assumes "k \<in> set (remdups_indices r)"
  assumes "has_eq_relation r xs"
  shows "count (mset xs) (xs ! k) = count_list_p r k"
proof -
  have a:"k < length xs" 
    by (metis has_eq_relation_def assms remdups_indices_range )
  have b:"count (mset xs) (xs ! k) = count_list xs (xs ! k)"
    by (simp add: count_xs_aux) 
  have "count_list xs (xs ! k) = count_list_p r k"
    apply (simp add:count_card)
    apply (rule arg_cong [where f="card"])
    apply (rule order_antisym)
     apply (rule subsetI, simp)
    using a assms(2) apply (simp add:has_eq_relation_def, force)
     apply (rule subsetI, simp)
    using a assms(2) by (simp add:has_eq_relation_def)
  thus ?thesis using a b by simp
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

end
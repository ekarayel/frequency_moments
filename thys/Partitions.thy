theory Partitions
  imports Main "HOL-Library.Multiset"
begin

text \<open>This is a disjoint induction scheme for multisets: We can represent each multiset as
a sum like: replicate_mset n x_1 + replicate_mset n x_2 + .. + replicate_mset n x_n where the 
x_i are distinct.\<close>

lemma disj_induct_mset:
  assumes "P {#}"
  assumes "\<And>n M x. P M \<Longrightarrow> \<not>(x \<in># M) \<Longrightarrow> n > 0 \<Longrightarrow> P (M + replicate_mset n x)"
  shows "P M"
proof (induction "size M" arbitrary: M rule:nat_less_induct)
  case 1
  show ?case
  proof (cases "M = {#}")
    case True
    then show ?thesis using assms by simp
  next
    case False
    then obtain x where x_def: "x \<in># M" using multiset_nonemptyE by auto
    define M1 where "M1 = M - replicate_mset (count M x) x"
    then have M_def: "M = M1 + replicate_mset (count M x) x"
      by (metis count_le_replicate_mset_subset_eq dual_order.refl subset_mset.diff_add)
    have "size M1 < size M"
      by (metis M_def x_def count_greater_zero_iff less_add_same_cancel1 size_replicate_mset size_union)
    hence "P M1" using 1 by blast
    then show "P M" 
      apply (subst M_def, rule assms(2), simp)
      by (simp add:M1_def x_def count_eq_zero_iff[symmetric])+
  qed
qed

lemma prod_mset_conv: "prod_mset (image_mset f A) = prod (\<lambda>x. (f x :: 'a :: comm_monoid_mult)^(count A x)) (set_mset A)"
proof (induction A rule: disj_induct_mset)
  case 1
  then show ?case by simp
next
  case (2 n M x)
  moreover have "count M x = 0" using 2 by (simp add: count_eq_zero_iff)
  moreover have "\<And>y. y \<in> set_mset M \<Longrightarrow> y \<noteq> x" using 2 by blast
  ultimately show ?case by (simp add:algebra_simps) 
qed

lemma sum_collapse: 
  assumes "finite A"
  assumes "z \<in> A"
  assumes "\<And>y. y \<in> A \<Longrightarrow> y \<noteq> z \<Longrightarrow> f y = (0::'a ::comm_monoid_add)"
  shows "sum f A = f z"
  using sum.union_disjoint[where A="A-{z}" and B="{z}" and g="f"]
  by (simp add: assms sum.insert_if)

end
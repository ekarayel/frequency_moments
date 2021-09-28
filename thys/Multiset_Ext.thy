section \<open>Multisets\<close> 

theory Multiset_Ext
  imports Main "HOL.Real" "HOL-Library.Multiset"
begin

text \<open>This is a induction scheme over the distinct elements of a multisets: 
We can represent each multiset as a sum like: 
@{text "replicate_mset n\<^sub>1 x\<^sub>1 + replicate_mset n\<^sub>2 x\<^sub>2 + ... + replicate_mset n\<^sub>k x\<^sub>k"} where the 
@{term "x\<^sub>i"} are distinct.\<close>

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

lemma prod_mset_conv: 
  fixes f :: "'a \<Rightarrow> 'b::{comm_monoid_mult}"
  shows "prod_mset (image_mset f A) = prod (\<lambda>x. f x^(count A x)) (set_mset A)"
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
  fixes f :: "'a \<Rightarrow> 'b::{comm_monoid_add}"
  assumes "finite A"
  assumes "z \<in> A"
  assumes "\<And>y. y \<in> A \<Longrightarrow> y \<noteq> z \<Longrightarrow> f y = 0"
  shows "sum f A = f z"
  using sum.union_disjoint[where A="A-{z}" and B="{z}" and g="f"]
  by (simp add: assms sum.insert_if)

text \<open>There is a version @{thm [source] sum_list_map_eq_sum_count} but it doesn't work
if the function maps into the reals.\<close>

lemma sum_list_eval:
  fixes f :: "'a \<Rightarrow> 'b::{ring,semiring_1}"
  shows "sum_list (map f xs) = (\<Sum>x \<in> set xs. of_nat (count_list xs x) * f x)"
proof -
  define M where "M = mset xs"
  have "sum_mset (image_mset f M) = (\<Sum>x \<in> set_mset M. of_nat (count M x) * f x)"
  proof (induction "M" rule:disj_induct_mset)
    case 1
    then show ?case by simp
  next
    case (2 n M x)
    have a:"\<And>y. y \<in> set_mset M \<Longrightarrow> y \<noteq> x" using 2(2) by blast
    show ?case using 2 by (simp add:a  count_eq_zero_iff[symmetric])
  qed
  moreover have "\<And>x. count_list xs x = count (mset xs) x" 
    by (induction xs, simp, simp)
  ultimately show ?thesis
    by (simp add:M_def sum_mset_sum_list[symmetric])
qed


end
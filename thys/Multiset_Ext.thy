section \<open>Multisets\<close>

theory Multiset_Ext
  imports Main "HOL.Real" "HOL-Library.Multiset"
begin

text \<open>This section contains results about multisets in addition to "HOL.Multiset"\<close>

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

lemma prod_list_eval:
  fixes f :: "'a \<Rightarrow> 'b::{ring,semiring_1,comm_monoid_mult}"
  shows "prod_list (map f xs) = (\<Prod>x \<in> set xs. (f x)^(count_list xs x))"
proof -
  define M where "M = mset xs"
  have "prod_mset (image_mset f M) = (\<Prod>x \<in> set_mset M. f x ^ (count M x))"
  proof (induction "M" rule:disj_induct_mset)
    case 1
    then show ?case by simp
  next
    case (2 n M x)
    have a:"\<And>y. y \<in> set_mset M \<Longrightarrow> y \<noteq> x" using 2(2) by blast
    have b:"count M x = 0" using 2 by (subst  count_eq_zero_iff) blast 
    show ?case using 2  by (simp add:a b mult.commute)
  qed
  moreover have "\<And>x. count_list xs x = count (mset xs) x" 
    by (induction xs, simp, simp)
  ultimately show ?thesis
    by (simp add:M_def prod_mset_prod_list[symmetric])
qed

lemma sorted_sorted_list_of_multiset: "sorted (sorted_list_of_multiset M)"
  by (induction M, auto simp:sorted_insort) 

lemma count_mset: "count (mset xs) a = count_list xs a"
  by (induction xs, auto)

lemma swap_filter_image: "filter_mset g (image_mset f A) = image_mset f (filter_mset (g \<circ> f) A)"
  by (induction A, auto)

lemma list_eq_iff:
  assumes "mset xs = mset ys"
  assumes "sorted xs"
  assumes "sorted ys"
  shows "xs = ys" 
  using assms properties_for_sort by blast

lemma sorted_list_of_multiset_image_commute:
  assumes "mono f"
  shows "sorted_list_of_multiset (image_mset f M) = map f (sorted_list_of_multiset M)"
proof -
  have "sorted (sorted_list_of_multiset (image_mset f M))" 
    by (simp add:sorted_sorted_list_of_multiset)
  moreover have " sorted_wrt (\<lambda>x y. f x \<le> f y) (sorted_list_of_multiset M)"
    by (rule sorted_wrt_mono_rel[where P="\<lambda>x y. x \<le> y"]) 
      (auto intro: monoD[OF assms] sorted_sorted_list_of_multiset)
  hence "sorted (map f (sorted_list_of_multiset M))"
    by (subst sorted_wrt_map)
  ultimately show ?thesis
    by (intro list_eq_iff, auto)
qed

end

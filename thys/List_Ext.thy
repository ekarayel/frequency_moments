section \<open>Lists\<close>

theory List_Ext
  imports Main "HOL.List"
begin

text \<open>This section contains results about lists in addition to "HOL.List"\<close>

lemma count_list_gr_1:
  "(x \<in> set xs) = (count_list xs x \<ge> 1)"
  by (induction xs, simp, simp)

lemma count_list_append: "count_list (xs@ys) v = count_list xs v + count_list ys v"
  by (induction xs, simp, simp)

lemma count_list_card: "count_list xs x = card {k. k < length xs \<and> xs ! k = x}"
proof -
  have "count_list xs x = length (filter ((=) x) xs)"
    by (induction xs, simp, simp)
  also have "... = card {k. k < length xs \<and> xs ! k = x}"
    by (subst length_filter_conv_card, metis)
  finally show ?thesis by simp
qed

lemma card_gr_1_iff:
  assumes "finite S"
  assumes "x \<in> S"
  assumes "y \<in> S"
  assumes "x \<noteq> y"
  shows "card S > 1"
  using assms card_le_Suc0_iff_eq leI by auto

lemma count_list_ge_2_iff:
  assumes "y < z"
  assumes "z < length xs"
  assumes "xs ! y = xs ! z"
  shows "count_list xs (xs ! y) > 1"
  apply (subst count_list_card)
  apply (rule card_gr_1_iff[where x="y" and y="z"])
  using assms by simp+

end

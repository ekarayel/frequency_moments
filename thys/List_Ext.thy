section \<open>Lists\<close>

theory List_Ext
  imports Main "HOL.List" "HOL-Library.Sublist"
begin

text \<open>This section contains results about lists in addition to "HOL.List"\<close>

lemma count_list_gr_1:
  "(x \<in> set xs) = (count_list xs x \<ge> 1)"
  by (induction xs, simp, simp)

lemma count_list_append: "count_list (xs@ys) v = count_list xs v + count_list ys v"
  by (induction xs, simp, simp)

lemma count_list_lt_suffix:
  assumes "suffix a b"
  assumes "x \<in> {b ! i| i. i <  length b - length a}"
  shows  "count_list a x < count_list b x"
proof -
  have "length a \<le> length b" using assms(1) 
    by (simp add: suffix_length_le)
  hence "x \<in> set (nths b {i. i < length b - length a})"
    using assms diff_commute by (auto simp add:set_nths) 
  hence a:"x \<in> set (take (length b - length a) b)"
    by (subst (asm) lessThan_def[symmetric], simp)
  have "b = (take (length b - length a) b)@drop (length b - length a) b"
    by simp
  also have "... = (take (length b - length a) b)@a"
    using assms(1) suffix_take by auto 
  finally have b:"b = (take (length b - length a) b)@a" by simp

  have "count_list a x < 1 + count_list a x" by simp
  also have "... \<le> count_list (take (length b - length a) b) x + count_list a x"
    using a count_list_gr_1
    by (intro add_mono, fast, simp)  
  also have "... = count_list b x"
    using b count_list_append by metis
  finally show ?thesis by simp
qed

lemma suffix_drop_drop:
  assumes "x \<ge> y"
  shows "suffix (drop x a) (drop y a)"
proof -
  have "drop y a = take (x - y) (drop y a)@drop (x- y) (drop y a)"
    by (subst append_take_drop_id, simp)
  also have " ... = take (x-y) (drop y a)@drop x a"
    using assms by simp
  finally have "drop y a = take (x-y) (drop y a)@drop x a" by simp
  thus ?thesis 
    by (auto simp add:suffix_def) 
qed

lemma count_list_card: "count_list xs x = card {k. k < length xs \<and> xs ! k = x}"
proof -
  have "count_list xs x = length (filter ((=) x) xs)"
    by (induction xs, simp, simp)
  also have "... = card {k. k < length xs \<and> xs ! k = x}"
    by (subst length_filter_conv_card, metis)
  finally show ?thesis by simp
qed

lemma card_gr_1_iff:
  assumes "finite S"  "x \<in> S"  "y \<in> S"  "x \<noteq> y"
  shows "card S > 1"
  using assms card_le_Suc0_iff_eq leI by auto

lemma count_list_ge_2_iff:
  assumes "y < z"
  assumes "z < length xs"
  assumes "xs ! y = xs ! z"
  shows "count_list xs (xs ! y) > 1"
proof -
  have " 1 < card {k. k < length xs \<and> xs ! k = xs ! y}"
    using assms by (intro card_gr_1_iff[where x="y" and y="z"], auto)

  thus ?thesis
    by (simp add: count_list_card)
qed

end

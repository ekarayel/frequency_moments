section \<open>Ranks, $k$ smallest element and elements\<close>

theory K_Smallest
  imports Main "HOL-Library.Multiset" List_Ext Multiset_Ext Set_Ext
begin

text \<open>This section contains definitions and results for the selection of the $k$ smallest elements, the $k$-th smallest element, rank of an element in an ordered set.\<close>


definition rank_of :: "'a :: linorder \<Rightarrow> 'a set \<Rightarrow> nat" where "rank_of x S = card {y \<in> S. y < x}"  
text \<open>The function @{term "rank_of"} returns the rank of an element within a set.\<close>

lemma rank_mono:
  assumes "finite S"
  shows "x \<le> y \<Longrightarrow> rank_of x S \<le> rank_of y S"
  apply (simp add:rank_of_def)
  apply (rule card_mono)
  using assms apply simp
  by (rule subsetI, simp, force)

lemma rank_mono_commute:
  assumes "finite S"
  assumes "S \<subseteq> T"
  assumes "strict_mono_on f T"
  assumes "x \<in> T"
  shows "rank_of x S = rank_of (f x) (f ` S)"
proof -
  have "rank_of (f x) (f ` S) = card (f ` {y \<in> S. y < x})"
    apply (simp add:rank_of_def)
    apply (rule arg_cong[where f="card"])
    apply (rule order_antisym)
    apply (rule subsetI, simp)
    using assms strict_mono_on_leD apply fastforce
    apply (rule image_subsetI, simp) 
    using assms by (simp add: in_mono strict_mono_on_def)
  also have "... = card {y \<in> S. y < x}"
    apply (rule card_image)
    apply (rule inj_on_subset[where A="T"])
     apply (metis assms(3) strict_mono_on_imp_inj_on)
    using assms by blast
  also have "... = rank_of x S"
    by (simp add:rank_of_def)
  finally show ?thesis
    by simp
qed


definition least where "least k S = {y \<in> S. rank_of y S < k}"
text \<open>The function @{term "least"} returns the k smallest elements of a finite set.\<close>

lemma rank_strict_mono: 
  assumes "finite S"
  shows "strict_mono_on (\<lambda>x. rank_of x S) S"
proof -
  have "\<And>x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> x < y \<Longrightarrow> rank_of x S < rank_of y S"
    apply (simp add:rank_of_def)
    apply (rule psubset_card_mono)
     apply (simp add:assms)
    apply (simp add: psubset_eq)
    apply (rule conjI, rule subsetI, force)
    by blast

  thus ?thesis
    by (simp add:rank_of_def strict_mono_on_def)
qed


lemma rank_of_image:
  assumes "finite S"
  shows "(\<lambda>x. rank_of x S) ` S = {0..<card S}"
  apply (rule card_seteq, simp)
   apply (rule image_subsetI, simp add:rank_of_def)
   apply (rule psubset_card_mono, metis assms, blast)
  apply simp
  apply (subst card_image)
   apply (metis strict_mono_on_imp_inj_on rank_strict_mono assms) 
  by simp

lemma card_least:
  assumes "finite S"
  shows "card (least k S) = min k (card S)"
proof (cases "card S < k")
  case True
  have "\<And>t. rank_of t S \<le> card S" 
    apply (simp add:rank_of_def)
    by (rule card_mono, metis assms, simp)
  hence "\<And>t. rank_of t S < k" 
    by (metis True not_less_iff_gr_or_eq order_less_le_trans)
  hence "least k S = S"
    by (simp add:least_def)
  then show ?thesis using True by simp
next
  case False
  hence a:"card S \<ge> k" using leI by blast
  have "card ((\<lambda>x. rank_of x S) -` {0..<k} \<inter> S) = card {0..<k}"
    apply (rule card_vimage_inj_on)
     apply (metis strict_mono_on_imp_inj_on rank_strict_mono assms) 
    apply (subst rank_of_image, metis assms)
    using a by simp
  hence "card (least k S) = k"
    by (simp add: Collect_conj_eq Int_commute least_def vimage_def)
  then show ?thesis using a by linarith
qed

lemma least_subset: "least k S \<subseteq> S"
  by (simp add:least_def)

lemma preserve_rank:
  assumes "finite S"
  shows "rank_of x (least m S) = min m (rank_of x S)"
proof (cases "rank_of x S \<ge> m")
  case True
  hence "{y \<in> least m S. y < x} = least m S" 
    apply (simp add: least_def)
    apply (rule Collect_cong)
    using rank_mono[OF assms]
    by (metis linorder_not_less order_less_le_trans)
  moreover have "m \<le> card S"
    apply (rule order_trans[where y="rank_of x S"], metis True)
    apply (simp add:rank_of_def)
    by (rule card_mono[OF assms], simp)
  hence "card (least m S) = m"
    apply (subst card_least[OF assms])
    by simp
  ultimately show ?thesis using True by (simp add:rank_of_def)
next
  case False
  have "rank_of x (least m S) = rank_of x S" 
    apply (simp add:rank_of_def)
    apply (rule arg_cong[where f="card"])
    apply (rule Collect_cong)
    apply (simp add: least_def)
    by (metis False rank_mono[OF assms] less_le_not_le min_def min_less_iff_conj nle_le)
  thus ?thesis using False by simp
qed

lemma rank_insert:
  assumes "finite T"
  shows "rank_of y (insert v T) = of_bool (v < y \<and> v \<notin> T) + rank_of y T"
proof -
  have a:"v \<notin> T \<Longrightarrow> v < y \<Longrightarrow> rank_of y (insert v T) = Suc (rank_of y T)"
  proof -
    assume a_1: "v \<notin> T"
    assume a_2: "v < y"
    have "rank_of y (insert v T) = card (insert v {z \<in> T. z < y})"
      apply (simp add: rank_of_def) 
      apply (subst insert_compr)
      by (metis a_2 mem_Collect_eq)
    also have "... = Suc (card {z \<in> T. z < y})"
      apply (subst card_insert_disjoint)
      using assms a_1 by simp+
    also have "... = Suc (rank_of y T)"
      by (simp add:rank_of_def) 
    finally show "rank_of y (insert v T) = Suc (rank_of y T)"
      by blast
  qed
  have b:"v \<notin> T \<Longrightarrow> \<not>(v < y) \<Longrightarrow> rank_of y (insert v T) = rank_of y T"
    by (simp add:rank_of_def, metis)
  have c:"v \<in> T \<Longrightarrow> rank_of y (insert v T) = rank_of y T"
    by (simp add:insert_absorb)

  show ?thesis
    apply (cases "v \<in> T", simp add: c)
    apply (cases "v < y", simp add:a)
    by (simp add:b)
qed

lemma least_mono_commute:
  assumes "finite S"
  assumes "strict_mono_on f S"
  shows "f ` least k S = least k (f ` S)"
proof -
  have a:"inj_on f S" 
    using strict_mono_on_imp_inj_on[OF assms(2)] by simp
  have b: "card (least k (f ` S)) \<le> card (f ` least k S)"
    apply (subst card_least, simp add:assms)
    apply (subst card_image, metis a)
    apply (subst card_image, rule inj_on_subset[OF a], simp add:least_def)
    by (subst card_least, simp add:assms, simp)

  show ?thesis
    apply (rule card_seteq, simp add:least_def assms)
     apply (rule image_subsetI, simp add:least_def)
     apply (subst rank_mono_commute[symmetric, where T="S"], metis assms(1), simp, metis assms(2), simp, simp)
    by (metis b)
qed

lemma least_insert: 
  assumes "finite S"
  shows "least k (insert x (least k S)) = least k (insert x S)" (is "?lhs = ?rhs")
proof -
  have c: "x \<in> least k S \<Longrightarrow> x \<in> S" by (simp add:least_def)
  have b:"min k (card (insert x S)) \<le> card (insert x (least k S))"
    apply (cases "x \<in> least k S")
     using c apply (simp add: insert_absorb)
     apply (subst card_least, simp add:assms least_def, simp)
    apply (subst card_insert_disjoint, simp add:assms least_def, simp)
    apply (cases "x \<in> S")
     apply (simp add:insert_absorb)
     apply (subst card_least, simp add:assms least_def)
     using nat_less_le apply blast
    apply (subst card_insert_disjoint, simp add:assms least_def, simp)
    apply (subst card_least, simp add:assms least_def) 
    by simp
  have a:"card ?rhs \<le> card ?lhs"
    apply (subst card_least, simp add:assms least_def)
    apply (subst card_least, simp add:assms least_def)
    by (meson b min.boundedI min.cobounded1)

  have d:"\<And>y. y \<in> least k (insert x (least k S)) \<Longrightarrow> y \<in> least k (insert x S)" 
    apply (subst least_def, subst (asm) least_def)
    apply (subst rank_insert[OF assms])
    apply (subst (asm) rank_insert, simp add:assms least_def)
    apply (subst (asm) preserve_rank, simp add:assms)
    apply (cases "x \<in> least k S")
    apply (simp, metis insert_subset least_subset min.strict_order_iff min_def mk_disjoint_insert)
    apply (simp) 
     using least_def apply fastforce
    by (metis insert_subset least_subset min_def mk_disjoint_insert nat_neq_iff)
  
  show ?thesis
    apply (rule card_seteq, simp add:least_def assms)
     apply (rule subsetI, metis d)
    using a by simp
qed

definition count_le where "count_le x M = size {#y \<in># M. y \<le> x#}"
definition count_less where "count_less x M = size {#y \<in># M. y < x#}"

definition nth_mset :: "nat \<Rightarrow> ('a :: linorder) multiset \<Rightarrow> 'a" where
  "nth_mset k M = sorted_list_of_multiset M ! k"

lemma nth_mset_bound_left:
  assumes "k < size M"
  assumes "count_less x M \<le> k"
  shows "x \<le> nth_mset k M"
proof (rule ccontr)
  define xs where "xs = sorted_list_of_multiset M"
  have s_xs: "sorted xs" by (simp add:xs_def sorted_sorted_list_of_multiset)
  have l_xs: "k < length xs" apply (simp add:xs_def) 
    by (metis size_mset mset_sorted_list_of_multiset assms(1))  
  have M_xs: "M = mset xs" by (simp add:xs_def)
  hence a:"\<And>i. i \<le> k \<Longrightarrow> xs ! i \<le> xs ! k"
    using s_xs l_xs sorted_iff_nth_mono by blast

  assume "\<not>(x \<le> nth_mset k M)"
  hence "x > nth_mset k M" by simp
  hence b:"x > xs ! k" by (simp add:nth_mset_def xs_def[symmetric])

  have "k < card {0..k}" by simp
  also have "... \<le> card {i. i < length xs \<and> xs ! i < x}"
    apply (rule card_mono, simp)
    apply (rule subsetI, simp)
    using a b l_xs order_le_less_trans by auto
  also have "... = count_less x M"
    apply (simp add:count_less_def M_xs)
    apply (subst mset_filter[symmetric], subst size_mset)
    by (subst length_filter_conv_card, simp)
  also have "... \<le> k"
    using assms by simp
  finally show "False" by simp
qed

lemma nth_mset_bound_left_excl:
  assumes "k < size M"
  assumes "count_le x M \<le> k"
  shows "x < nth_mset k M"
proof (rule ccontr)
  define xs where "xs = sorted_list_of_multiset M"
  have s_xs: "sorted xs" by (simp add:xs_def sorted_sorted_list_of_multiset)
  have l_xs: "k < length xs" apply (simp add:xs_def) 
    by (metis size_mset mset_sorted_list_of_multiset assms(1))  
  have M_xs: "M = mset xs" by (simp add:xs_def)
  hence a:"\<And>i. i \<le> k \<Longrightarrow> xs ! i \<le> xs ! k"
    using s_xs l_xs sorted_iff_nth_mono by blast

  assume "\<not>(x < nth_mset k M)"
  hence "x \<ge> nth_mset k M" by simp
  hence b:"x \<ge> xs ! k" by (simp add:nth_mset_def xs_def[symmetric])

  have "k+1 \<le> card {0..k}" by simp
  also have "... \<le> card {i. i < length xs \<and> xs ! i \<le> xs ! k}"
    apply (rule card_mono, simp)
    apply (rule subsetI, simp)
    using a b l_xs order_le_less_trans by auto
  also have "... \<le> card {i. i < length xs \<and> xs ! i \<le> x}"
    apply (rule card_mono, simp)
    apply (rule subsetI, simp) using b 
    by force
  also have "... = count_le x M"
    apply (simp add:count_le_def M_xs)
    apply (subst mset_filter[symmetric], subst size_mset)
    by (subst length_filter_conv_card, simp)
  also have "... \<le> k"
    using assms by simp
  finally show "False" by simp
qed

lemma nth_mset_bound_right:
  assumes "k < size M"
  assumes "count_le x M > k"
  shows "nth_mset k M \<le> x"
proof (rule ccontr)
  define xs where "xs = sorted_list_of_multiset M"
  have s_xs: "sorted xs" by (simp add:xs_def sorted_sorted_list_of_multiset)
  have l_xs: "k < length xs" apply (simp add:xs_def) 
    by (metis size_mset mset_sorted_list_of_multiset assms(1))  
  have M_xs: "M = mset xs" by (simp add:xs_def)

  assume "\<not>(nth_mset k M \<le> x)"
  hence "x < nth_mset k M" by simp
  hence "x < xs ! k" 
    by (simp add:nth_mset_def xs_def[symmetric])
  hence a:"\<And>i. i < length xs \<and> xs ! i \<le> x \<Longrightarrow> i < k"
    using s_xs l_xs sorted_iff_nth_mono leI by fastforce
  have "count_le x M \<le> card {i. i < length xs \<and> xs ! i \<le> x}"
    apply (simp add:count_le_def M_xs)
    apply (subst mset_filter[symmetric], subst size_mset)
    apply (subst length_filter_conv_card)
    by (rule card_mono, simp, simp)
  also have "... \<le> card {i. i < k}"
    apply (rule card_mono, simp)
    by (rule subsetI, simp add:a)
  also have "... = k" by simp
  finally have "count_le x M \<le> k" by simp
  thus "False" using assms by simp
qed

lemma nth_mset_commute_mono:
  assumes "mono f"
  assumes "k < size M"
  shows "f (nth_mset k M) = nth_mset k (image_mset f M)"
proof -
  have a:"k < length (sorted_list_of_multiset M)"
    by (metis assms(2) mset_sorted_list_of_multiset size_mset)
  show ?thesis
    using a by (simp add:nth_mset_def sorted_list_of_multiset_image_commute[OF assms(1)])
qed 

lemma nth_mset_max: 
  assumes "size A > k"
  assumes "\<And>x. x \<le> nth_mset k A \<Longrightarrow> count A x \<le> 1"
  shows "nth_mset k A = Max (least (k+1) (set_mset A))" and "card (least (k+1) (set_mset A)) = k+1"
proof -
  define xs where "xs = sorted_list_of_multiset A"
  have k_bound: "k < length xs" apply (simp add:xs_def)
    by (metis size_mset mset_sorted_list_of_multiset assms(1))  

  have A_def: "A = mset xs" by (simp add:xs_def)
  have s_xs: "sorted xs" by (simp add:xs_def sorted_sorted_list_of_multiset)
  have a_2: "\<And>x. x \<le> xs ! k \<Longrightarrow> count_list xs x \<le> 1" 
    using assms(2) apply (simp add:xs_def[symmetric] nth_mset_def)
    by (simp add:A_def count_mset) 

  have inj_xs: "inj_on (\<lambda>k. xs ! k) {0..k}"
    apply (rule inj_onI)
    apply simp
    by (metis (full_types) count_list_ge_2_iff k_bound a_2 
        le_neq_implies_less linorder_not_le order_le_less_trans s_xs sorted_iff_nth_mono)

  have rank_conv_2: "\<And>y. y < length xs \<Longrightarrow> rank_of (xs ! y) (set xs) < k+1 \<Longrightarrow> y < k+1"
  proof (rule ccontr)
    fix y
    assume b:"y < length xs"
    assume "\<not>y < k +1"
    hence a:"k + 1 \<le> y" by simp

    have d:"Suc k < length xs" using a b by simp

    have "k+1 = card ((!) xs ` {0..k})" 
      by (subst card_image[OF inj_xs], simp)
    also have "... \<le> rank_of (xs ! (k+1)) (set xs)"
      apply (simp add:rank_of_def)
      apply (rule card_mono, simp)
      apply (rule image_subsetI, simp) 
      apply (rule conjI) using k_bound apply simp
      by (metis count_list_ge_2_iff a_2 not_le le_imp_less_Suc s_xs sorted_iff_nth_mono d order_less_le)
    also have "... \<le> rank_of (xs ! y) (set xs)"
      apply (simp add:rank_of_def)
      apply (rule card_mono, simp)
      apply (rule subsetI, simp)
      by (metis Suc_eq_plus1 a b s_xs order_less_le_trans sorted_iff_nth_mono)
    also assume "... < k+1"
    finally show "False" by force
  qed

  have rank_conv_1: "\<And>y. y < k + 1 \<Longrightarrow> rank_of (xs ! y) (set xs) < k+1"
  proof -
    fix y
    have "rank_of (xs ! y) (set xs) \<le> card ((\<lambda>k. xs ! k) ` {k. k < length xs \<and> xs ! k < xs ! y})"
      apply (simp add:rank_of_def)
      apply (rule card_mono, simp)
      apply (rule subsetI, simp)
      by (metis (no_types, lifting) imageI in_set_conv_nth mem_Collect_eq)
    also have "... \<le> card {k. k < length xs \<and> xs ! k < xs ! y}"
      by (rule card_image_le, simp)
    also have "... \<le> card {k. k < y}"
      apply (rule card_mono, simp)
      apply (rule subsetI, simp)
      apply (rule ccontr, simp add:not_less)
      by (meson leD sorted_iff_nth_mono s_xs)
    also have "... = y" by simp
    also assume "y < k + 1"
    finally show "rank_of (xs ! y) (set xs) < k+1" by simp
  qed

  have rank_conv: "\<And>y. y < length xs \<Longrightarrow> rank_of (xs ! y) (set xs) < k+1 \<longleftrightarrow> y < k+1"
    using rank_conv_1 rank_conv_2 by blast

  have max_1: "\<And>y. y \<in> least (k+1) (set xs) \<Longrightarrow> y \<le> xs ! k" 
  proof -
    fix y
    assume a:"y \<in> least (k+1) (set xs)"
    hence "y \<in> set xs" using least_subset by blast
    then obtain i where i_bound: "i < length xs" and y_def: "y = xs ! i" using in_set_conv_nth by metis
    hence "rank_of (xs ! i) (set xs) < k+1"
      using a y_def i_bound by (simp add: least_def)
    hence "i < k+1"
      using rank_conv i_bound by blast
    hence "i \<le> k" by linarith
    hence "xs ! i \<le> xs ! k"
      using s_xs i_bound k_bound sorted_nth_mono by blast
    thus "y \<le> xs ! k" using y_def by simp
  qed

  have max_2:"xs ! k \<in> least (k+1) (set xs)"
    apply (simp add:least_def)
    using k_bound rank_conv by simp

  have r_1: "Max (least (k+1) (set xs)) = xs ! k"
    apply (rule Max_eqI, rule finite_subset[OF least_subset], simp)
     apply (metis max_1)
    by (metis max_2)

  have "k + 1 = card ((\<lambda>i. xs ! i) ` {0..k})" 
    by (subst card_image[OF inj_xs], simp) 
  also have "... \<le> card (least (k+1) (set xs))"
    apply (rule card_mono, rule finite_subset[OF least_subset], simp)
    apply (rule image_subsetI)
    apply (simp add:least_def)
    using rank_conv k_bound by simp
  finally have "card (least (k+1) (set xs)) \<ge> k+1" by simp
  moreover have "card (least (k+1) (set xs)) \<le> k+1"
    by (subst card_least, simp, simp)
  ultimately have r_2: "card (least (k+1) (set xs)) = k+1" by simp

  show "nth_mset k A = Max (least (k+1) (set_mset A))" 
    apply (simp add:nth_mset_def xs_def[symmetric] r_1[symmetric])
    by (simp add:A_def)

  show "card (least (k+1) (set_mset A)) = k+1" 
    using r_2 by (simp add:A_def)
qed

end

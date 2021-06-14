section \<open>Counting Maps between Finite Sets\<close>

theory CountMaps
  imports Main
begin

lemma count_maps:
  assumes "finite (B :: 'b set)"
  assumes "finite (A :: 'a set)"
  shows "card {f. dom f = A \<and> ran f \<subseteq> B} = card B ^ (card A)"
  using assms(2)
proof (induction A)
  case empty
  have "{f. dom f = {} \<and> ran f \<subseteq> B} = {Map.empty}"
    by (rule order_antisym, rule subsetI, simp, rule subsetI, simp)
  then show ?case using card_1_singleton_iff by fastforce
next
  case (insert x F)
  define M where "M = {f. dom f = insert x F \<and> ran f \<subseteq> B}"
  define N where "N = B \<times> {f. dom f = F \<and> ran f \<subseteq> B}"

  have fin_M: "finite M" 
    by (simp add: finite_set_of_finite_maps insert.hyps(1) M_def assms(1))
  have fin_N: "finite N"
    by (simp add: finite_set_of_finite_maps insert.hyps(1) N_def assms(1))

  define split where "split = (\<lambda>(f :: 'a \<Rightarrow> 'b option). (the (f x), f |` F))"
  have "inj_on split M"
    apply (rule inj_onI, rule ext)
    apply(simp  add:M_def split_def)
    by (metis domIff insert_iff option.collapse restrict_map_def)
  moreover have "split ` M \<subseteq> N"
    apply (rule image_subsetI, simp add:split_def M_def N_def) 
    apply (rule conjI, metis (mono_tags) domIff insertCI option.collapse ranI subsetD)
    apply (rule conjI, fastforce)
    by (meson ranI ran_restrictD subsetD subsetI)
  ultimately have a:"card M \<le> card N" by (metis card_image card_mono fin_N)

  define merge where "merge = (\<lambda>(v,w :: 'a \<Rightarrow> 'b option). (w (x \<mapsto> v)))"
  have "inj_on merge N"
    apply (rule inj_onI)
    apply (simp add:N_def merge_def split:prod.splits) 
    by (metis domIff fun_upd_triv fun_upd_upd insert.hyps(2) map_upd_eqD1)
  moreover have "merge ` N \<subseteq> M"
    apply (rule image_subsetI, simp add:merge_def M_def N_def split:prod.splits)
    using insert.hyps(2) by force
  ultimately have b:"card N \<le> card M" by (metis card_image card_mono fin_M)

  have "card M = card N" by (meson a b order_antisym)
  moreover have "card N = card B * (card B)^(card F)" 
    by (simp add:N_def card_cartesian_product insert)
  ultimately show ?case apply (simp add:M_def) using insert.hyps by simp
qed

lemma
  assumes "finite (B :: 'b set)"
  assumes "y \<in> B"
  shows 
    card_mostly_constant_maps: 
    "card {f. range f \<subseteq> B \<and> (\<forall>x. x \<ge> n \<longrightarrow> f x = y)} = card B ^ n" (is "card ?A = ?B") and
    finite_mostly_constant_maps:
    "finite {f. range f \<subseteq> B \<and> (\<forall>x. x \<ge> n \<longrightarrow> f x = y)}"
proof -
  define C where "C = {f. dom f = {k. k < n} \<and> ran f \<subseteq> B}"
  define forward where "forward = (\<lambda>f k. if k < n then Some ((f k) :: 'b) else None)"
  define backward where "backward = (\<lambda>f k. if k < n then the (f k) else y)"

  have forward_inject:"inj_on forward ?A"
    apply (rule inj_onI, rule ext, simp add:forward_def)
    by (metis not_le option.sel)

  have forward_image:"forward ` ?A \<subseteq> C"
    apply (rule image_subsetI, simp add:forward_def C_def)
    apply (rule conjI, simp add:dom_def)
    apply (simp add:ran_def) by blast
  have finite_C:"finite C"
    by (simp add:C_def finite_set_of_finite_maps assms(1)) 

  have card_ineq_1: "card ?A \<le> card C"
    using card_image card_mono forward_inject forward_image finite_C by (metis (no_types, lifting))

  show "finite ?A"
    using inj_on_finite forward_inject forward_image finite_C by blast
  moreover have "inj_on backward C"
    apply (rule inj_onI, rule ext, simp add:backward_def C_def)
    by (metis domIff mem_Collect_eq option.expand)
  moreover have "backward ` C \<subseteq> ?A"
    apply (rule image_subsetI, simp add:backward_def C_def)
    apply (rule conjI, rule image_subsetI, simp add: domD ranI subset_eq)
    by (rule image_subsetI, simp add:assms)
  ultimately have  card_ineq_2: "card C \<le> card ?A" by (metis (no_types, lifting) card_image card_mono)

  have "card ?A = card C" using card_ineq_1 card_ineq_2 by auto
  moreover have "card C = card B ^ n" using C_def assms(1) by (simp add: count_maps)
  ultimately show "card ?A = ?B" by auto
qed

end

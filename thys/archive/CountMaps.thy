section \<open>Counting Maps between Finite Sets\<close>

theory CountMaps
  imports Main "HOL-Library.FuncSet"
begin

lemma
  assumes "finite (B :: 'b set)"
  assumes "y \<in> B"
  shows 
    card_mostly_constant_maps: 
    "card {f. range f \<subseteq> B \<and> (\<forall>x. x \<ge> n \<longrightarrow> f x = y)} = card B ^ n" (is "card ?A = ?B") and
    finite_mostly_constant_maps:
    "finite {f. range f \<subseteq> B \<and> (\<forall>x. x \<ge> n \<longrightarrow> f x = y)}"
proof -
  define C where "C = {k. k < n} \<rightarrow>\<^sub>E B"
  define forward where "forward = (\<lambda>(f :: nat \<Rightarrow> 'b). restrict f {k. k< n})"
  define backward where "backward = (\<lambda>f k. if k < n then f k else y)"

  have forward_inject:"inj_on forward ?A"
    apply (rule inj_onI, rule ext, simp add:forward_def restrict_def)
    by (metis not_le)

  have forward_image:"forward ` ?A \<subseteq> C"
    apply (rule image_subsetI, simp add:forward_def C_def) by blast
  have finite_C:"finite C"
    by (simp add:C_def finite_PiE assms(1)) 

  have card_ineq_1: "card ?A \<le> card C"
    using card_image card_mono forward_inject forward_image finite_C by (metis (no_types, lifting))

  show "finite ?A"
    using inj_on_finite forward_inject forward_image finite_C by blast
  moreover have "inj_on backward C"
    apply (rule inj_onI, rule ext, simp add:backward_def C_def) 
    by (metis (no_types, lifting) PiE_ext mem_Collect_eq)
  moreover have "backward ` C \<subseteq> ?A"
    apply (rule image_subsetI, simp add:backward_def C_def)
    apply (rule conjI, rule image_subsetI) apply blast
    by (rule image_subsetI, simp add:assms)
  ultimately have  card_ineq_2: "card C \<le> card ?A" by (metis (no_types, lifting) card_image card_mono)

  have "card ?A = card C" using card_ineq_1 card_ineq_2 by auto
  moreover have "card C = card B ^ n" using C_def assms(1) by (simp add: card_PiE)
  ultimately show "card ?A = ?B" by auto
qed

end

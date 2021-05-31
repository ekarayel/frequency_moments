theory Frequency_Moment_2
  imports Main "HOL-Probability.Probability_Measure" "HOL-Library.Multiset"
    "HOL-Probability.Independent_Family" "HOL-Algebra.Congruence"
begin

section \<open>Frequency Moment 2\<close>

subsection \<open>Partitions on Indexes\<close>

text \<open>A partition on an index set I (for example I = {0,..,3}) can be represented using a
mapping g that maps each element to its class number, which we define to be ordered by the index
of its smallest element.

For example the partition {{0,1},{2},{3}} would be represented by the mapping k -> [0,0,1,2] ! k.

In the following we build an enumerator that returns all possible partitions of {0,..,n-1}, 
represented using a list of pairs of inducing mappings and class count.\<close>

fun enum_canonical_mapping
  where 
    "enum_canonical_mapping 0 = [(\<lambda>_. 0, 0)]" |
    "enum_canonical_mapping (Suc n) = [
      (\<lambda>k. if k < n then x k else y, if y < c then c else Suc c). 
      (x,c) \<leftarrow> enum_canonical_mapping n, y \<leftarrow> [0..<Suc c]]" 

subsection \<open>Sketch\<close>

definition f2_sketch_summand
  where
    "f2_sketch_summand f xs x \<omega> = real (count_list xs x) * f x \<omega>"

definition f2_sketch
  where
    "f2_sketch f xs \<omega> = (\<Sum> x \<in> set xs. f2_sketch_summand f xs x \<omega>)"

text \<open>Set of mappings with domain ${0,..,n-1}$ and Range A\<close>

definition fun_set
  where "fun_set n A = {x. dom x = {k. k < n} \<and> ran x \<subseteq> A}"

fun shift where "shift n k = k+(n::nat)"

fun split_fun 
  :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'a option) \<Rightarrow> (nat \<Rightarrow> 'a option) \<times> (nat \<Rightarrow> 'a option)"  where 
  "split_fun m n x = (x|`{k. k < m},(x \<circ> shift m)|`{k. k < n})"

lemma
  split_fun_image:
  "fun_set m A \<times> fun_set n A = split_fun m n ` fun_set (m+n) A" (is ?A) and
  split_fun_inj:
  "inj_on (split_fun m n) (fun_set (m+n) A)" (is ?B)
proof -
  have "fun_set m A \<times> fun_set n A \<subseteq> split_fun m n ` fun_set (m+n) A"
  proof (rule subsetI)
    fix x 
    assume a: "x \<in> fun_set m A \<times> fun_set n A"
    define y where "y = (\<lambda>k. if k < m then (fst x) k else (snd x) (k - m))"
    have b:"dom (fst x) = {k. k < m}" using a by (cases x, simp add:fun_set_def)
    have c:"dom (snd x) = {k. k < n}" using a by (cases x, simp add:fun_set_def)
    have "fst x = fst (split_fun m n y) "
      by (rule ext, metis b domIff fst_conv mem_Collect_eq restrict_in restrict_out split_fun.simps y_def)
    moreover have "snd x = snd (split_fun m n y)"
      apply (rule ext, simp add:y_def restrict_map_def ) using c by blast 
    ultimately have "x = split_fun m n y" by (cases x, simp)
    moreover have "dom y = {k. k < m + n}"
      apply (rule order_antisym, rule subsetI)
      using y_def b c apply (simp add:dom_def set_eq_iff) 
       apply (metis add.commute less_diff_conv2 not_less trans_less_add1) 
      apply (rule subsetI)
      using y_def b c apply (simp add:dom_def set_eq_iff) 
      by (metis add.commute less_diff_conv2 not_less) 
    moreover have "ran y \<subseteq> A" 
      apply (rule subsetI)
      using a apply(cases x, simp add:fun_set_def y_def ran_def) 
      by (metis (mono_tags) fst_conv mem_Collect_eq snd_conv subset_iff)
    ultimately show "x \<in> split_fun m n ` fun_set (m+n) A"
      using fun_set_def by (simp del:split_fun.simps, blast)
  qed
  moreover have "fun_set m A \<times> fun_set n A \<supseteq> split_fun m n ` fun_set (m+n) A"
  proof (rule subsetI)
    fix x
    assume "x \<in> split_fun m n ` fun_set (m+n) A"
    then obtain y where y_mem: "y \<in> fun_set (m+n) A" and y_def: "x = split_fun m n y" by blast
    have "dom (fst x) = {k. k < m}"
      using y_def y_mem by (simp add:fun_set_def set_eq_iff dom_def subset_iff restrict_map_def) 
    moreover have "dom (snd x) = {k. k < n}"
      using y_def y_mem by (simp add:fun_set_def set_eq_iff dom_def subset_iff restrict_map_def) 
    moreover have "ran (fst x) \<subseteq> A"
      apply (rule subsetI)
      using y_def y_mem apply (simp add:fun_set_def set_eq_iff ran_def restrict_map_def subset_iff)
      by (metis option.simps(3)) 
    moreover have "ran (snd x) \<subseteq> A"
      apply (rule subsetI)
      using y_def y_mem apply (simp add:fun_set_def set_eq_iff ran_def restrict_map_def subset_iff)
      by (metis comp_apply option.simps(3))
    ultimately show "x \<in> fun_set m A \<times> fun_set n A" by (cases x, simp add:fun_set_def)
  qed
  ultimately show ?A by auto

  have shift_restrict_eq:
    "\<And>x y. ((x \<circ> shift m) |` {k. k < n} = (y \<circ> shift m) |` {k. k < n}) = 
    (x |` {k. k < (m+n) \<and> k \<ge> m} = y |` {k. k < (m+n) \<and> k \<ge> m})"
    apply (rule order_antisym)
    apply (simp add:restrict_map_def fun_eq_iff)
    apply (metis add.commute nat_add_left_cancel_less nat_le_iff_add)
    by (simp add:restrict_map_def fun_eq_iff)
  show ?B 
    apply (simp add:inj_on_def shift_restrict_eq) apply (rule ballI)+ 
    apply (rule impI, rule ext)
    apply (simp add:restrict_map_def fun_eq_iff fun_set_def set_eq_iff domIff del:not_None_eq) 
    by (metis not_less)
qed

text \<open>Set of injective mappings with domain ${0,..,n-1}$ and Range A\<close>

definition fun_set_inj
  where "fun_set_inj n A = 
    {x. dom x = {k. k < n} \<and> ran x \<subseteq> A \<and> inj_on x {k. k < n}}"


lemma dom_shift: "dom (x \<circ> shift m) = {k. (k :: nat) + m \<in> dom x}"
  by (simp add:dom_def)

lemma ran_shift: "ran x \<subseteq> A \<Longrightarrow> ran (x \<circ> shift m) \<subseteq> A"
  by (rule subsetI,simp add:ran_def,blast)

lemma ran_restrict: "ran x \<subseteq> A \<Longrightarrow> ran (x |` B) \<subseteq> A"
  apply (rule subsetI,simp add:ran_def) 
  by (metis (mono_tags, lifting) mem_Collect_eq option.simps(3) restrict_in restrict_out subsetD)

lemma sum_unroll_1:
  "sum (f :: 'a \<Rightarrow> real) A = sum (\<lambda>x. f (the (x 0))) (fun_set (Suc 0) A)"
proof -
  have a:"sum f ((\<lambda>x. the (x 0))` (fun_set (Suc 0) A)) = sum (f \<circ> (\<lambda>x. the (x 0))) (fun_set (Suc 0) A)"
  apply (rule sum.reindex)
  apply (simp add:fun_set_def inj_on_def) 
    by (metis (mono_tags, lifting) dom_eq_singleton_conv fun_upd_apply option.sel)
  have b:"((\<lambda>x. the (x 0))` (fun_set (Suc 0) A)) \<subseteq> A" 
  proof
    fix x 
    assume "x \<in> ((\<lambda>x. the (x 0))` (fun_set (Suc 0) A))"
    then obtain y where y_elem: "y \<in> (fun_set (Suc 0) A)" and y_def: "x = the (y 0)" by blast
    then show "x \<in> A" using y_def y_elem apply (simp add:fun_set_def) 
      by (metis domIff insertI1 not_None_eq option.sel ranI subset_iff)
  qed
  have c:"((\<lambda>x. the (x 0))` (fun_set (Suc 0) A)) \<supseteq> A" 
  proof
    fix x 
    assume a:"x \<in> A"
    then obtain y where y_def: "y = (\<lambda>k. if k = (0::nat) then Some x else None)" by blast
    hence "y \<in> fun_set (Suc 0) A" by (simp add:fun_set_def dom_def ran_def a)
    then show "x \<in> ((\<lambda>x. the (x 0))` (fun_set (Suc 0) A))" using y_def  image_iff by fastforce
  qed
  show ?thesis using a b c by auto
qed

lemma sum_unroll_2:
  "sum (\<lambda>x. sum (\<lambda>y. f x y :: real) (fun_set n A)) (fun_set (m::nat) (A :: 'a set)) = 
   sum (\<lambda>x. f (x|`{k. k < m}) ((x \<circ> shift m)|`{k. k < n})) (fun_set (n+m) A)"
  apply (simp add:sum.cartesian_product)
  apply (rule sum.reindex_cong[where ?l = "split_fun m n"])
  by (simp add: split_fun_inj split_fun_image add.commute)+

lemma split_fun_set_sum_into_partitions:
  "sum (f :: ((nat \<Rightarrow> 'a option) \<Rightarrow> real)) (fun_set n A) = sum_list (map (\<lambda>(x,c). sum (\<lambda>u. f (\<lambda>i. u (x i))) (fun_set_inj c A)) (enum_canonical_mapping n))"
  sorry

(*
  [0,1,2,3] \<rightarrow> [0,1]
  g

  {0,1} \<rightarrow> A \<Rightarrow> {0,1,2,3} \<rightarrow> A
  (\x k. x (g k))

  f : ({0,1,2,3} \<rightarrow> A) \<rightarrow> R

  f = (\u. f (\<lambda>i. u (g i)))
  
*)


definition f2_tr
  where
    "f2_tr h xs n l \<omega> = prod_list (map (\<lambda>i. f2_sketch_summand h xs (the (n i)) \<omega>) (l :: nat list))"

definition f2_sketch_summand_pow
  where
    "f2_sketch_summand_pow h xs x n \<omega> = ((f2_sketch_summand h xs x \<omega>) ^ n)"

lemma c1: "f2_sketch_summand h xs (the (n k)) \<omega> = f2_tr h xs n [k] \<omega>"
  by (simp add:f2_tr_def)

lemma c2: "f2_tr h xs n a \<omega> * f2_tr h xs n b \<omega> = f2_tr h xs n (a@b) \<omega>"
  by (simp add:f2_tr_def)

fun counts where
  "counts xs = map (\<lambda>x. (x,count_list xs x)) (remdups xs)" 

lemma c4: 
  assumes "x \<in> fun_set_inj n A"
  shows "integral\<^sup>L \<Omega> (f2_tr h xs x a) = prod_list (map (\<lambda>(i,j). (LINT \<omega>|\<Omega>. (f2_sketch_summand_pow h xs (the (x i)) j \<omega>))) (counts a))"
  sorry

fun sm_l where
  "sm_l [] _ = True" |
  "sm_l (a#as) n = (if a < n then sm_l as n else False)"

lemma
  assumes "prob_space \<Omega>"
  assumes "finite A"
  assumes "\<And>I. I \<subseteq> set xs \<Longrightarrow> finite I \<Longrightarrow> card I \<le> 4 \<Longrightarrow> prob_space.indep_vars \<Omega> (\<lambda>_. borel) h I" 
  assumes "\<And>i. i \<in> set xs \<Longrightarrow> \<sigma> \<in> {-1::real, 1} \<Longrightarrow> prob_space.prob \<Omega> (h i -` {\<sigma>}) = 1/2"
  shows var_f2:"(prob_space.expectation \<Omega> (\<lambda>\<omega>. (f2_sketch h xs \<omega>)^4))
       - (prob_space.expectation \<Omega> (\<lambda>\<omega>. (f2_sketch h xs \<omega>)^2))^2 \<le> 2*(sum (\<lambda>i. (count_list xs i)^2) (set xs))^2" (is ?A)
  and exp_f2:"prob_space.expectation \<Omega> (\<lambda>\<omega>. (f2_sketch h xs \<omega>)^2) = sum (\<lambda>i. (count_list xs i)^2) (set xs)" (is ?B)
proof -
  have b:"\<And>x j n m. x \<in> fun_set_inj n (set xs) \<Longrightarrow> j < n \<Longrightarrow> even m \<Longrightarrow>
    integral\<^sup>L \<Omega> (f2_sketch_summand_pow h xs (the (x j)) m) = count_list xs (the (x j)) ^ m"
    sorry

  have c:"\<And>x n j m. x \<in> fun_set_inj  n (set xs) \<Longrightarrow> j < n \<Longrightarrow> odd m \<Longrightarrow>
    integral\<^sup>L \<Omega> (f2_sketch_summand_pow h xs (the (x j)) m) = 0"
    sorry

  have d:"Sigma_Algebra.measure \<Omega> (space \<Omega>) = 1" using assms(1) 
    by (simp add: prob_space.prob_space)

  have e: "\<And>x n a. x \<in> fun_set n (set xs) \<Longrightarrow> sm_l a n \<Longrightarrow> integrable \<Omega> (f2_tr h xs x a)" sorry

  show ?A
    apply (simp add: f2_sketch_def power4_eq_xxxx power2_eq_square  )
    apply (simp add: sum_distrib_left sum_distrib_right sum_unroll_1[where A="set xs"] sum_unroll_2)
    apply (simp add: c1 c2)
    apply (simp add: Bochner_Integration.integral_sum e)
    apply (simp add: f2_tr_def sum_distrib_left sum_distrib_right sum_unroll_2 sum_subtractf[symmetric])
    apply (simp add: split_fun_set_sum_into_partitions)
    apply (simp add: c1 c2)
    apply (simp add: c4 b c d)
    by (simp add: sum_distrib_left sum_nonneg)

  show ?B
    apply (simp add: f2_sketch_def power4_eq_xxxx power2_eq_square  )
    apply (simp add: sum_distrib_left sum_distrib_right sum_unroll_1[where A="set xs"] sum_unroll_2)
    apply (simp add: c1 c2)
    apply (simp add: Bochner_Integration.integral_sum e)
    apply (simp add: f2_tr_def sum_distrib_left sum_distrib_right sum_unroll_2 sum_subtractf[symmetric])
    apply (simp add: split_fun_set_sum_into_partitions)
    apply (simp add: c1 c2)
    by (simp add: c4 b c d)
qed


end
theory SumByPartitions
  imports Main
begin

definition is_same_partition :: "nat => (nat => 'a) => (nat => 'b) \<Rightarrow> bool" where
  "is_same_partition n f g = (\<forall>x y. x < n \<longrightarrow> y < n \<longrightarrow> (f x = f y) = (g x = g y))"

lemma is_same_partition_simp_1: "is_same_partition 0 f g" using is_same_partition_def by auto

fun is_same_partition_test_loop :: "nat => nat \<Rightarrow> (nat => 'a) => (nat => 'b) \<Rightarrow> bool" where
  "is_same_partition_test_loop k 0 f g = True" |
  "is_same_partition_test_loop k (Suc n) f g = ((f k = f n) = (g k = g n) \<and> is_same_partition_test_loop k n f g)"

lemma is_same_partition_test_aux: "(\<forall>y. y < m \<longrightarrow> (f n = f y) = (g n = g y)) = is_same_partition_test_loop n m f g"
  apply (induction m, simp, simp) using less_Suc_eq by auto

lemma is_same_partition_simp_2: 
  "is_same_partition (Suc n) f g = (is_same_partition n f g \<and> is_same_partition_test_loop n n f g)"
  apply (simp add:is_same_partition_def is_same_partition_test_aux[symmetric])
  apply (rule order_antisym)
  using less_Suc_eq apply force
  using less_Suc_eq by fastforce

fun enum_canonical_mapping
  where 
    "enum_canonical_mapping 0 = [(\<lambda>_. 0, 0)]" |
    "enum_canonical_mapping (Suc n) = [
      (\<lambda>k. if k < n then x k else (if k = n then y else c), c). 
      (x,c) \<leftarrow> enum_canonical_mapping n, y \<leftarrow> [0..<c]]@
      [(\<lambda>k. if k < n then x k else (if k = n then c else Suc c), Suc c). 
      (x,c) \<leftarrow> enum_canonical_mapping n]"

lemma is_canonical:
  "p \<in> set (enum_canonical_mapping n) \<Longrightarrow> (fst p) ` {k. k < n} = {k. k < (snd p)} \<and> (fst p) ` {k. k \<ge> n} = {snd p}" 
proof (induction n arbitrary: p)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then consider
    (i) "\<exists>x\<in>set (enum_canonical_mapping n). \<exists>y\<in>{0..<snd x}. p = (\<lambda>k. if k < n then fst x k else if k = n then y else snd x, snd x)" |
    (ii) "\<exists>x\<in>set (enum_canonical_mapping n). p = (\<lambda>k. if k < n then fst x k else if k = n then snd x else Suc (snd x), Suc (snd x))" 
    by (simp add:case_prod_unfold image_iff, blast) 
  then show ?case
  proof cases
    case i
    then obtain x y where 
      a:"x\<in>set (enum_canonical_mapping n)"
      and b:"y\<in>{0..<snd x}"
      and c:"p = (\<lambda>k. if k < n then fst x k else if k = n then y else snd x, snd x)"
      by blast
    have "(fst x) ` {k. k < n} = {k. k < snd x}" using Suc a by blast
    hence f2:"(fst p) ` {k. k < n} = {k. k < snd p}" by (simp add:c)
    have f1:"(fst p) n \<in> {k. k < snd p}" using c b by simp
    have "(fst p) ` {k. k < Suc n} = {k. k < snd p}"
      apply (rule order_antisym, rule image_subsetI) using f1 f2 apply (simp add:less_Suc_eq, blast)
      by (metis (mono_tags, lifting) Collect_mono_iff f2 image_mono less_Suc_eq)
    moreover have "(fst p) ` {k. k \<ge> Suc n} = {snd p}"
      using c apply simp by blast
    ultimately show ?thesis by blast
  next
    case ii
    then obtain x  where 
      a:"x\<in>set (enum_canonical_mapping n)"
      and c:"p = (\<lambda>k. if k < n then fst x k else if k = n then snd x else Suc (snd x), Suc (snd x))"
      by blast
    have "(fst x) ` {k. k < n} = {k. k < snd x}" using Suc a by blast
    hence f2:"(fst p) ` {k. k < n} = {k. k < snd x}" by (simp add:c)
    have f1:"(fst p) n = snd x" using c by simp
    have "(fst p) ` {k. k < Suc n} = {k. k < Suc (snd x)}"
      using f1 f2 apply (simp add:image_def set_eq_iff less_Suc_eq) by metis
    moreover have "(fst p) ` {k. k \<ge> Suc n} = {Suc (snd x)}"
      using c apply simp by blast
    moreover have "snd p = Suc (snd x)" using c by auto
    ultimately show ?thesis by auto
  qed
qed

lemma canonincal_mapping_split:
  assumes "n = 4"
  shows "length (filter (\<lambda>g. is_same_partition n f (fst g)) (enum_canonical_mapping n)) = 1"
  apply (case_tac [!] "f 0 = f 1")
  apply (case_tac [!] "f 2 = f 3")
  apply (case_tac [!] "f 0 = f 3")
  apply (case_tac [!] "f 1 = f 2")
  by (simp add:assms numeral_eq_Suc is_same_partition_simp_1 is_same_partition_simp_2)+

lemma sum_split_list:
  assumes "\<And>x. x \<in> A \<Longrightarrow> length (filter (\<lambda>i. x \<in> B i) I) = 1"
  assumes "\<And>i. i \<in> set I \<Longrightarrow> B i \<subseteq> A"
  assumes "\<And>i. i \<in> set I \<Longrightarrow> finite (B i)"
  shows "sum (f :: 'a \<Rightarrow> ('b :: comm_monoid_add)) A = sum_list (map (\<lambda>i. sum f (B i)) I)"
proof -
  define I' where "I' = filter (\<lambda>i. B i \<noteq> {}) I"
  have assm1': "\<And>x. x \<in> A \<Longrightarrow> length (filter (\<lambda>i. x \<in> B i) I') = 1"
    by (simp add:I'_def, metis (mono_tags, lifting) assms(1) One_nat_def empty_iff filter_cong)  
  have assm2': "\<Union> (set (map B I')) = A"
    apply (rule order_antisym, rule subsetI)
    using I'_def assms(2) apply simp apply blast
    apply (rule subsetI) using assm1' 
    by (metis (no_types, lifting) One_nat_def UN_iff filter_set image_set lessI member_filter nth_mem)
  have assm3': "\<And>i. i \<in> set I' \<Longrightarrow> B i \<noteq> {} \<and> finite (B i)" using I'_def assms(3) by auto
  have d:"\<And>i j. i < length I' \<Longrightarrow> j < length I' \<Longrightarrow> i \<noteq> j \<Longrightarrow> B (I' ! i) \<inter> B (I' ! j) = {}"
  proof (rule equals0I)
    fix i
    fix j
    assume d1:"i < length I'"
    assume d2:"j < length I'"
    assume d3:"i \<noteq> j"
    fix x
    assume d4:"x \<in> B (I' ! i) \<inter> B (I' ! j)"
    hence "{i, j} \<subseteq> {i. i < length I' \<and> x \<in> B(I' ! i)}"
      using d1 d2 by simp
    moreover have "card {i, j} = 2" using d3 by simp
    moreover have "finite {i. i < length I' \<and> x \<in> B (I' ! i)}" by simp
    ultimately have "2 \<le> card {i. i < length I' \<and> x \<in> B(I' ! i)}"
      using card_mono by metis
    hence "2 \<le> length (filter (\<lambda>i. x \<in> B i) I')" using length_filter_conv_card 
      by (metis (mono_tags, lifting) Collect_cong)
    moreover have "x \<in> A" using d4 assm2' d1 by fastforce
    ultimately show "False" using assm1' by simp
  qed
  hence "\<And>i j. i < length I' \<Longrightarrow> j < length I' \<Longrightarrow> i \<noteq> j \<Longrightarrow> B (I' ! i) \<noteq> B (I' ! j)"
    by (metis assm3' inf.idem nth_mem)
  hence b:"distinct (map B I')" using distinct_conv_nth by force
  hence c:"distinct I'" using distinct_map by blast
  have "sum (sum f) (set (map B I')) = sum_list (map (sum f) (map B I'))" using b
    by (rule sum_list_distinct_conv_sum_set[symmetric])
  hence a:"sum (\<lambda>x. sum f (B x)) (set I') = sum_list (map (\<lambda>i. sum f (B i)) I')" 
    by (simp add: c sum_list_distinct_conv_sum_set)
  hence a:"sum f A =  sum_list (map (\<lambda>i. sum f (B i)) I')" 
    apply (simp add:assm2'[symmetric] a[symmetric])
    apply (rule sum.UNION_disjoint, simp)
    using assm3' apply simp
    by (metis in_set_conv_nth d)
  then show ?thesis
    apply (simp add:I'_def)
    by (metis (mono_tags, lifting) sum.empty sum_list_map_filter)
qed

definition maps :: "nat \<Rightarrow> 'a set \<Rightarrow> (nat \<Rightarrow> 'a option) set" where 
  "maps n A = {x. dom x = {k. k < n} \<and> ran x \<subseteq> A}"

fun shift where "shift n k = k+(n::nat)"

fun split_map 
  :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'a option) \<Rightarrow> (nat \<Rightarrow> 'a option) \<times> (nat \<Rightarrow> 'a option)"  where 
  "split_map m n x = (x|`{k. k < m},(x \<circ> shift m)|`{k. k < n})"

lemma
  split_map_image:
  "maps m A \<times> maps n A = split_map m n ` maps (m+n) A" (is ?A) and
  split_map_inj:
  "inj_on (split_map m n) (maps (m+n) A)" (is ?B)
proof -
  have "maps m A \<times> maps n A \<subseteq> split_map m n ` maps (m+n) A"
  proof (rule subsetI)
    fix x 
    assume a: "x \<in> maps m A \<times> maps n A"
    define y where "y = (\<lambda>k. if k < m then (fst x) k else (snd x) (k - m))"
    have b:"dom (fst x) = {k. k < m}" using a by (cases x, simp add:maps_def)
    have c:"dom (snd x) = {k. k < n}" using a by (cases x, simp add:maps_def)
    have "fst x = fst (split_map m n y)"
      by (rule ext, metis b domIff fst_conv mem_Collect_eq restrict_in restrict_out split_map.simps y_def)
    moreover have "snd x = snd (split_map m n y)"
      apply (rule ext, simp add:y_def restrict_map_def ) using c by blast 
    ultimately have "x = split_map m n y" by (cases x, simp)
    moreover have "dom y = {k. k < m + n}"
      apply (rule order_antisym, rule subsetI)
      using y_def b c apply (simp add:dom_def set_eq_iff) 
       apply (metis add.commute less_diff_conv2 not_less trans_less_add1) 
      apply (rule subsetI)
      using y_def b c apply (simp add:dom_def set_eq_iff) 
      by (metis add.commute less_diff_conv2 not_less) 
    moreover have "ran y \<subseteq> A" 
      apply (rule subsetI)
      using a apply(cases x, simp add:maps_def y_def ran_def) 
      by (metis (mono_tags) fst_conv mem_Collect_eq snd_conv subset_iff)
    ultimately show "x \<in> split_map m n ` maps (m+n) A"
      using maps_def by (simp del:split_map.simps, blast)
  qed
  moreover have "maps m A \<times> maps n A \<supseteq> split_map m n ` maps (m+n) A"
  proof (rule subsetI)
    fix x
    assume "x \<in> split_map m n ` maps (m+n) A"
    then obtain y where y_mem: "y \<in> maps (m+n) A" and y_def: "x = split_map m n y" by blast
    have "dom (fst x) = {k. k < m}"
      using y_def y_mem by (simp add:maps_def set_eq_iff dom_def subset_iff restrict_map_def) 
    moreover have "dom (snd x) = {k. k < n}"
      using y_def y_mem by (simp add:maps_def set_eq_iff dom_def subset_iff restrict_map_def) 
    moreover have "ran (fst x) \<subseteq> A"
      apply (rule subsetI)
      using y_def y_mem apply (simp add:maps_def set_eq_iff ran_def restrict_map_def subset_iff)
      by (metis option.simps(3)) 
    moreover have "ran (snd x) \<subseteq> A"
      apply (rule subsetI)
      using y_def y_mem apply (simp add:maps_def set_eq_iff ran_def restrict_map_def subset_iff)
      by (metis comp_apply option.simps(3))
    ultimately show "x \<in> maps m A \<times> maps n A" by (cases x, simp add:maps_def)
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
    apply (simp add:restrict_map_def fun_eq_iff maps_def set_eq_iff domIff del:not_None_eq) 
    by (metis not_less)
qed

definition maps_inj :: "nat \<Rightarrow> 'a set \<Rightarrow> (nat \<Rightarrow> 'a option) set" where 
  "maps_inj n A = {x. dom x = {k. k < n} \<and> ran x \<subseteq> A \<and> inj_on x {k. k < n}}"

definition maps_like :: "nat \<Rightarrow> 'a set \<Rightarrow> (nat \<Rightarrow> 'b) \<Rightarrow> (nat \<Rightarrow> 'a option) set" where 
  "maps_like n A f = {x. dom x = {k. k < n} \<and> ran x \<subseteq> A \<and> is_same_partition n x f}"

lemma finite_maps_like:
  assumes "finite A"
  shows "finite (maps_like n A f)"
proof -
  have "finite (maps n A)"
    apply (simp add:maps_def) using assms finite_set_of_finite_maps by blast
  moreover have "maps_like n A f \<subseteq> maps n A"
    by (auto simp add:maps_def maps_like_def)
  ultimately show ?thesis using finite_subset by blast
qed

lemma split_sum_maps_aux:
  assumes "n = 4"
  assumes "finite A"
  shows "sum f (maps n A) 
    = sum_list (map (\<lambda>(p,c). sum f (maps_like n A p)) (enum_canonical_mapping n))"
  apply (simp add:case_prod_unfold)
  apply (rule sum_split_list)
  using assms canonincal_mapping_split apply (simp add:maps_def maps_like_def) apply auto[1]
   apply (simp add:maps_def maps_like_def) apply force
  using assms by (simp add:finite_maps_like)

lemma eq_dom_circ: "range x \<supseteq> dom f \<Longrightarrow> range x \<supseteq> dom g \<Longrightarrow> f \<circ> x = g \<circ> x \<Longrightarrow> f = g"
  apply (rule ext)
  apply (simp add:dom_def subset_iff)
  by (metis comp_eq_dest image_iff option.exhaust)

lemma dom_circ_simp: "dom (y \<circ> x) = {k. x k \<in> dom y}"
  by (simp add:dom_def)

lemma ran_circ_inv: "ran y \<subseteq> A \<Longrightarrow> ran (y \<circ> x) \<subseteq> A"
  by (simp add:ran_def subset_iff, blast)

lemma card_1_rule:
  assumes "X \<noteq> {}"
  assumes "\<And>x y. x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> x = y"
  shows "card X = 1"
proof -
  obtain x where "x \<in> X" using assms by (meson all_not_in_conv)
  then have "X = {x}"
    using assms by blast
  thus ?thesis by auto
qed

lemma ran_rule: "(\<And>x. x \<in> dom f \<Longrightarrow> the (f x) \<in> A) \<Longrightarrow> ran f \<subseteq> A"
  by (simp add:ran_def dom_def, force)

lemma make_inj:
  assumes "g ` {k. k < (n::nat)} = {k. k < c}"
  assumes "g ` {k. k \<ge> n} = {c::nat}"
  shows "sum f (maps_like n A g) = sum (\<lambda>u. f (\<lambda>i. u (g i))) (maps_inj c A)"
proof -
  have e2: "\<And>k. k\<ge> n \<Longrightarrow> g k = c" using assms(2) by blast
  have c:"inj_on (\<lambda>h. h \<circ> g) (maps_inj c A)"
    using assms(1) apply (simp add:inj_on_def maps_inj_def) 
    by (metis eq_dom_circ image_subset_iff rangeI)
  have "maps_like n A g \<supseteq> (\<lambda>h. h \<circ> g) ` maps_inj c A"
  proof (rule image_subsetI)
    fix y
    assume f:"y \<in> maps_inj c A"
    have "dom (y \<circ> g) = {k. k < n}" using assms(1) e2 f apply (simp add:maps_inj_def dom_circ_simp)
       by (metis imageI less_irrefl_nat mem_Collect_eq not_less)
    moreover have "ran (y \<circ> g) \<subseteq> A" using f by (simp add:maps_inj_def ran_circ_inv) 
    moreover have "is_same_partition n (y \<circ> g) g" using f assms(1)
      apply (simp add:is_same_partition_def maps_inj_def) 
      using inj_onD by fastforce
    ultimately have "y \<circ> g \<in> maps_like n A g" 
      by (simp add:maps_like_def)
    thus "(\<lambda>h. h \<circ> g) y \<in> maps_like n A g" by simp
  qed
  moreover have "maps_like n A g \<subseteq> (\<lambda>h. h \<circ> g) ` maps_inj c A"
  proof 
    fix y
    assume h:"y \<in> maps_like n A g"
    have g:"\<And>k. k < c \<Longrightarrow> card (y ` (g -` {k})) = 1"
      apply (rule card_1_rule)
      apply (metis empty_iff image_iff insertI1 mem_Collect_eq vimage_eq assms(1))
      using h apply (simp add:maps_like_def is_same_partition_def)
      by (metis (no_types, lifting) e2 imageE nat_neq_iff not_less vimage_singleton_eq)
    have "\<exists>h. \<forall>k. (k < c \<longrightarrow> (y ` (g -` {k})) = {h k}) \<and> (k \<ge> c \<longrightarrow> h k = None)"
      by (rule choice, metis card_1_singletonE g not_less)
    then obtain h
      where h_def:"\<And>k. k < c \<Longrightarrow> y ` (g -` {k}) = {h k}" and h_dom: "\<And>k. k \<ge> c \<Longrightarrow> h k = None"
      by blast
    have "\<And>k. k < n \<Longrightarrow> y k = h (g k)" using assms(1) h_def by blast
    moreover have "\<And>k. k \<ge> n \<Longrightarrow> y k = h (g k)" using e2 h_dom h apply (simp add:dom_def)
      by (metis (mono_tags, lifting) domIff maps_like_def h mem_Collect_eq not_less)
    ultimately have h1:"\<And>k. y k  = h (g k)" by (meson not_less)
    hence f4: "y = h \<circ> g" by auto
    have "\<And>a b. a < c \<Longrightarrow> b < c \<Longrightarrow> h a = h b \<Longrightarrow> a = b"
    proof -
      fix a b
      assume "a < c"
      hence "\<exists>a' < n. a = g a'" using assms(1) by auto
      then obtain a' where a'_def: "a = g a'" and a'_ran: "a' < n" by blast
      assume "b < c"
      hence "\<exists>b' < n. b = g b'" using assms(1) by auto
      then obtain b' where b'_def: "b = g b'" and b'_ran: "b' < n" by blast
      assume "h a = h b"
      then have "y a' = y b'" using a'_def b'_def h1 by auto
      hence "g a' = g b'"
        using h a'_ran b'_ran by (simp add:maps_like_def is_same_partition_def)
      thus "a = b" using a'_def b'_def by auto
    qed
    hence f1:"inj_on h {k. k < c}" by (simp add:inj_on_def)

    have "dom h \<subseteq> {k. k < c}"
      by (metis (mono_tags, lifting) h_dom dom_def mem_Collect_eq not_less subsetI)

    moreover have "{k. k < c} \<subseteq> dom h" using h1 h 
      by (metis (mono_tags, lifting) domIff assms(1) maps_like_def image_subset_iff mem_Collect_eq)
    ultimately have h2: "dom h = {k. k < c}" by auto

    have f3:"ran h \<subseteq> A"
      apply (rule ran_rule) using h apply (simp add:maps_like_def dom_def ran_def subset_iff) 
      by (metis (mono_tags, lifting) domI assms(1) h1 h2 imageE option.sel)
    hence "h \<in> maps_inj c A" using f3 f1 h2 by (simp add:maps_inj_def)
    thus "y \<in> (\<lambda>h. h \<circ> g) ` maps_inj c A" using f4 by blast
  qed
  ultimately have d:"maps_like n A g = (\<lambda>h. h \<circ> g) ` maps_inj c A" by auto
  show "sum f (maps_like n A g) = sum (\<lambda>u. f (\<lambda>i. u (g i))) (maps_inj c A)"
    apply (rule sum.reindex_cong[where ?l = "(\<lambda>h. h \<circ> g)"])
      apply (simp add:c d)+
    by (meson comp_apply)
qed

lemma split_sum_maps:
  assumes "n = 4"
  assumes "finite A"
  shows "sum f (maps n A) 
    = sum_list (map (\<lambda>(p,c). sum (\<lambda>u. f (\<lambda>i. u (p i))) (maps_inj c A)) (enum_canonical_mapping n))"
  apply (simp add:split_sum_maps_aux assms case_prod_unfold)
  apply (rule arg_cong[where f="sum_list"])
    apply (rule list.map_cong0)
    apply (rule make_inj)
    using is_canonical by auto

lemma dom_shift: "dom (x \<circ> shift m) = {k. (k :: nat) + m \<in> dom x}"
  by (simp add:dom_def)

lemma ran_shift: "ran x \<subseteq> A \<Longrightarrow> ran (x \<circ> shift m) \<subseteq> A"
  by (rule subsetI,simp add:ran_def,blast)

lemma ran_restrict: "ran x \<subseteq> A \<Longrightarrow> ran (x |` B) \<subseteq> A"
  apply (rule subsetI,simp add:ran_def) 
  by (metis (mono_tags, lifting) mem_Collect_eq option.simps(3) restrict_in restrict_out subsetD)


lemma sum_unroll_1:
  "sum (f :: 'a \<Rightarrow> 'b :: comm_monoid_add) A = sum (\<lambda>x. f (the (x 0))) (maps (Suc 0) A)"
proof -
  have a:"sum f ((\<lambda>x. the (x 0))` (maps (Suc 0) A)) = sum (f \<circ> (\<lambda>x. the (x 0))) (maps (Suc 0) A)"
  apply (rule sum.reindex)
  apply (simp add:maps_def inj_on_def) 
    by (metis (mono_tags, lifting) dom_eq_singleton_conv fun_upd_apply option.sel)
  have b:"((\<lambda>x. the (x 0))` (maps (Suc 0) A)) \<subseteq> A" 
  proof
    fix x 
    assume "x \<in> ((\<lambda>x. the (x 0))` (maps (Suc 0) A))"
    then obtain y where y_elem: "y \<in> (maps (Suc 0) A)" and y_def: "x = the (y 0)" by blast
    then show "x \<in> A" using y_def y_elem apply (simp add:maps_def) 
      by (metis domIff insertI1 not_None_eq option.sel ranI subset_iff)
  qed
  have c:"((\<lambda>x. the (x 0))` (maps (Suc 0) A)) \<supseteq> A" 
  proof
    fix x 
    assume a:"x \<in> A"
    then obtain y where y_def: "y = (\<lambda>k. if k = (0::nat) then Some x else None)" by blast
    hence "y \<in> maps (Suc 0) A" by (simp add:maps_def dom_def ran_def a)
    then show "x \<in> ((\<lambda>x. the (x 0))` (maps (Suc 0) A))" using y_def  image_iff by fastforce
  qed
  show ?thesis using a b c by auto
qed

fun split_fun 
  :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'a option) \<Rightarrow> (nat \<Rightarrow> 'a option) \<times> (nat \<Rightarrow> 'a option)"  where 
  "split_fun m n x = (x|`{k. k < m},(x \<circ> shift m)|`{k. k < n})"

lemma
  split_fun_image:
  "maps m A \<times> maps n A = split_fun m n ` maps (m+n) A" (is ?A) and
  split_fun_inj:
  "inj_on (split_fun m n) (maps (m+n) A)" (is ?B)
proof -
  have "maps m A \<times> maps n A \<subseteq> split_fun m n ` maps (m+n) A"
  proof (rule subsetI)
    fix x 
    assume a: "x \<in> maps m A \<times> maps n A"
    define y where "y = (\<lambda>k. if k < m then (fst x) k else (snd x) (k - m))"
    have b:"dom (fst x) = {k. k < m}" using a by (cases x, simp add:maps_def)
    have c:"dom (snd x) = {k. k < n}" using a by (cases x, simp add:maps_def)
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
      using a apply(cases x, simp add:maps_def y_def ran_def) 
      by (metis (mono_tags) fst_conv mem_Collect_eq snd_conv subset_iff)
    ultimately show "x \<in> split_fun m n ` maps (m+n) A"
      using maps_def by (simp del:split_fun.simps, blast)
  qed
  moreover have "maps m A \<times> maps n A \<supseteq> split_fun m n ` maps (m+n) A"
  proof (rule subsetI)
    fix x
    assume "x \<in> split_fun m n ` maps (m+n) A"
    then obtain y where y_mem: "y \<in> maps (m+n) A" and y_def: "x = split_fun m n y" by blast
    have "dom (fst x) = {k. k < m}"
      using y_def y_mem by (simp add:maps_def set_eq_iff dom_def subset_iff restrict_map_def) 
    moreover have "dom (snd x) = {k. k < n}"
      using y_def y_mem by (simp add:maps_def set_eq_iff dom_def subset_iff restrict_map_def) 
    moreover have "ran (fst x) \<subseteq> A"
      apply (rule subsetI)
      using y_def y_mem apply (simp add:maps_def set_eq_iff ran_def restrict_map_def subset_iff)
      by (metis option.simps(3)) 
    moreover have "ran (snd x) \<subseteq> A"
      apply (rule subsetI)
      using y_def y_mem apply (simp add:maps_def set_eq_iff ran_def restrict_map_def subset_iff)
      by (metis comp_apply option.simps(3))
    ultimately show "x \<in> maps m A \<times> maps n A" by (cases x, simp add:maps_def)
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
    apply (simp add:restrict_map_def fun_eq_iff maps_def set_eq_iff domIff del:not_None_eq) 
    by (metis not_less)
qed

lemma sum_unroll_2:
  "sum (\<lambda>x. sum (\<lambda>y. f x y :: 'a :: comm_monoid_add) (maps n A)) (maps (m::nat) (A :: 'a set)) = 
   sum (\<lambda>x. f (x|`{k. k < m}) ((x \<circ> shift m)|`{k. k < n})) (maps (n+m) A)"
  apply (simp add:sum.cartesian_product)
  apply (rule sum.reindex_cong[where ?l = "split_fun m n"])
  by (simp add: split_fun_inj split_fun_image add.commute)+

end
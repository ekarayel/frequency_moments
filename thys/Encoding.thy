theory Encoding
  imports Main "HOL-Library.Sublist" "HOL-Library.Monad_Syntax" "HOL-Library.List_Lexorder"
    "HOL-Library.Option_ord" "HOL-Library.Extended_Nat" "Multiset_Ext"
  "HOL-Library.Extended_Nonnegative_Real" "HOL-Library.FuncSet"
begin

fun is_prefix where 
  "is_prefix (Some x) (Some y) = prefix x y" |
  "is_prefix _ _ = False"

type_synonym 'a encoding = "('a \<Rightarrow> bool list option)"

definition is_encoding :: "'a encoding \<Rightarrow> bool"
  where "is_encoding f = (\<forall>x y. is_prefix (f x) (f y) \<longrightarrow> x = y)"

lemma encoding_imp_inj:
  assumes "is_encoding f"
  shows "inj_on f (dom f)"
  apply (rule inj_onI)
  using assms by (simp add:is_encoding_def, force)

definition decode where 
  "decode f t = (
    if (\<exists>!z. is_prefix (f z) (Some t)) then 
      (let z = (THE z. is_prefix (f z) (Some t)) in (z, drop (length (the (f z))) t))
    else 
      (undefined, t)
    )"

lemma decode_elim:
  assumes "is_encoding f"
  assumes "f x = Some r"
  shows "decode f (r@r1) = (x,r1)"
proof -
  have a:"\<And>y. is_prefix (f y) (Some (r@r1)) \<Longrightarrow> y = x"
  proof -
    fix y
    assume "is_prefix (f y) (Some (r@r1))"
    then obtain u where u_1: "f y = Some u" "prefix u (r@r1)"
      by (metis is_prefix.elims(1) option.sel)
    hence "prefix u r \<or> prefix r u" 
      using prefix_def prefix_same_cases by blast
    hence "is_prefix (f y) (f x) \<or> is_prefix (f x) (f y)"
      using u_1 assms(2) by simp
    thus "y = x"
      using assms(1) apply (simp add:is_encoding_def) by blast
  qed
  have b:"is_prefix (f x) (Some (r@r1))" 
    using assms(2) by simp
  have c:"\<exists>!z. is_prefix (f z) (Some (r@r1))" 
    using a b by auto
  have d:"(THE z. is_prefix (f z) (Some (r@r1))) = x" 
    using a b by blast
  show "decode f (r@r1) = (x,r1)"
    using c d assms(2) by  (simp add: decode_def)
qed


lemma decode_elim_2:
  assumes "is_encoding f"
  assumes "x \<in> dom f"
  shows "decode f (the (f x)@r1) = (x,r1)"
  using assms decode_elim by fastforce

lemma snd_decode_suffix:
  "suffix (snd (decode f t)) t"
proof (cases "\<exists>!z. is_prefix (f z) (Some t)")
  case True
  then obtain z where  "is_prefix (f z) (Some t)" by blast
  hence "(THE z. is_prefix (f z) (Some t)) = z" using True by blast
  thus ?thesis using True by (simp add: decode_def suffix_drop)
next
  case False
  then show ?thesis by (simp add:decode_def)
qed

lemma snd_decode_len:
  assumes "decode f t = (u,v)"
  shows "length v \<le> length t"
  using snd_decode_suffix assms suffix_length_le 
  by (metis snd_conv)

lemma encoding_by_witness:
  assumes "\<And>x y. x \<in> dom f \<Longrightarrow> g (the (f x)@y) = (x,y)"
  shows "is_encoding f"
proof -
  have "\<And>x y. is_prefix (f x) (f y) \<Longrightarrow> x = y"
  proof -
    fix x y
    assume a:"is_prefix (f x) (f y)"
    then obtain d where d_def:"the (f x)@d = the (f y)"
      apply (case_tac [!] "f x", case_tac [!] "f y", simp, simp, simp, simp)
      by (metis prefixE)
    have "x \<in> dom f" using a apply (simp add:dom_def del:not_None_eq)
      by (metis is_prefix.simps(2) a)
    hence "g (the (f y)) = (x,d)" using assms by (simp add:d_def[symmetric])
    moreover have "y \<in> dom f" using a apply (simp add:dom_def del:not_None_eq)
      by (metis is_prefix.simps(3) a)
    hence "g (the (f y)) = (y,[])" using assms[where y="[]"] by simp
    ultimately show "x = y" by simp
  qed
  thus ?thesis by (simp add:is_encoding_def)
qed

fun bit_count where
  "bit_count None = \<infinity>" |
  "bit_count (Some x) = ereal (length x)"

fun encoding_length where 
  "encoding_length None = \<infinity>" |
  "encoding_length (Some x) = enat (length x)"

fun encode where
  "encode f x = f x"

fun assert :: "bool \<Rightarrow> unit option" where 
  "assert True = Some ()" |
  "assert False = None"

fun append_encoding :: "bool list option \<Rightarrow> bool list option \<Rightarrow> bool list option" (infixr "@\<^sub>S" 65)
  where
    "append_encoding (Some x) (Some y) = Some (x@y)" |
    "append_encoding _ _ = None"

lemma bit_count_append: "bit_count (x1@\<^sub>Sx2) = bit_count x1 + bit_count x2"
  by (cases x1, simp, cases x2, simp, simp)

lemma encoding_length_sum: "encoding_length (x1@\<^sub>Sx2) = encoding_length x1 + encoding_length x2"
  by (cases x1, simp, cases x2, simp, simp)

section \<open>Lists\<close>

fun list\<^sub>S where
  "list\<^sub>S f [] = Some [False]" |
  "list\<^sub>S f (x#xs) = Some [True]@\<^sub>Sf x@\<^sub>Slist\<^sub>S f xs"

function decode_list :: "('a \<Rightarrow> bool list option) \<Rightarrow> bool list 
  \<Rightarrow> 'a list \<times> bool list" 
  where 
    "decode_list e (True#x0) = (
      let (r1,x1) = decode e x0 in (
        let (r2,x2) = decode_list e x1 in (r1#r2,x2)))" |
    "decode_list e (False#x0) = ([], x0)" |
    "decode_list e [] = undefined"
  by pat_completeness auto
termination
  apply (relation "measure (\<lambda>(_,x). length x)")
  by (simp+, metis le_imp_less_Suc snd_decode_len)

lemma list_encoding_dom:
  assumes "set l \<subseteq> dom f"
  shows "l \<in> dom (list\<^sub>S f)"
  using assms apply (induction l, simp add:dom_def, simp) by fastforce

lemma list_encoding_length:
  "encoding_length (list\<^sub>S f xs) = sum_list (map (\<lambda>x. encoding_length (f x) + 1) xs) + 1"
  by (induction xs, simp add:one_enat_def, simp add:encoding_length_sum one_enat_def)

lemma list_bit_count:
  "bit_count (list\<^sub>S f xs) = sum_list (map (\<lambda>x. bit_count (f x) + 1) xs) + 1"
  apply (induction xs, simp, simp add:bit_count_append) 
  by (metis add.commute add.left_commute one_ereal_def)

lemma list_encoding_length_est:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> encoding_length (f x) \<le> a"
  shows "encoding_length (list\<^sub>S f xs) \<le> enat (length xs) * (a+1) + 1"
  using assms sum_list_mono[where g="\<lambda>_. a+1" and f="\<lambda>x. encoding_length (f x)+1" and xs="xs"]
  by (simp add:sum_list_triv of_nat_eq_enat list_encoding_length)

lemma list_bit_count_est:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> bit_count (f x) \<le> a"
  shows "bit_count (list\<^sub>S f xs) \<le> ereal (length xs) * (a+1) + 1"
proof -
  have a:"sum_list (map (\<lambda>_. (a+1)) xs) = length xs * (a+1)"
    apply (induction xs, simp)
    by (simp, subst plus_ereal.simps(1)[symmetric], subst ereal_left_distrib, simp+)

  have b: "\<And>x. x \<in> set xs \<Longrightarrow> bit_count (f x) +1 \<le> a+1"
    using assms add_right_mono by blast

  show ?thesis  
    using assms a  b sum_list_mono[where g="\<lambda>_. a+1" and f="\<lambda>x. bit_count (f x)+1" and xs="xs"]
    by (simp add:list_bit_count ereal_add_le_add_iff2)
qed

lemma list_bit_count_estI:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> bit_count (f x) \<le> a"
  assumes "ereal (real (length xs)) * (a+1) + 1 \<le> h"
  shows "bit_count (list\<^sub>S f xs) \<le> h"
  using list_bit_count_est[OF assms(1)] assms(2) order_trans by fastforce 

lemma list_encoding_lengthI:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> encoding_length (f x) \<le> a"
  assumes "enat (length xs) * (a+1) + 1 \<le> h"
  shows "encoding_length (list\<^sub>S f xs) \<le> h"
  using list_encoding_length_est[OF assms(1)] assms(2) order_trans by fastforce 

lemma list_encoding_aux:
  assumes "is_encoding f"
  shows "x \<in> dom (list\<^sub>S f) \<Longrightarrow> decode_list f (the (list\<^sub>S f x) @ y) = (x, y)"
proof  (induction x)
  case Nil
  then show ?case by simp
next
  case (Cons a x)
  then show ?case
    apply (cases "f a", simp add:dom_def)
    apply (cases "list\<^sub>S f x", simp add:dom_def)
    using assms by (simp add: dom_def decode_elim)
qed

lemma list_encoding:
  assumes "is_encoding f"
  shows "is_encoding (list\<^sub>S f)"
  by (metis encoding_by_witness[where g="decode_list f"] list_encoding_aux assms)

section \<open>Natural numbers\<close>

fun nat_encoding_aux :: "nat \<Rightarrow> bool list" 
  where
    "nat_encoding_aux 0 = [False]" |
    "nat_encoding_aux (Suc n) = True#(odd n)#nat_encoding_aux (n div 2)"

fun N\<^sub>S where "N\<^sub>S n = Some (nat_encoding_aux n)"

fun decode_nat :: "bool list \<Rightarrow> nat \<times> bool list" 
  where
    "decode_nat (False#y) = (0,y)" |
    "decode_nat (True#x#xs) = 
      (let (n, rs) = decode_nat xs in (n * 2 + 1 + (if x then 1 else 0), rs))" |
    "decode_nat _ = undefined"

lemma nat_encoding_aux:
  "decode_nat (nat_encoding_aux x @ y) = (x, y)"
  by (induction x rule:nat_encoding_aux.induct, simp, simp add:mult.commute)

lemma nat_encoding:
  shows "is_encoding N\<^sub>S"
  by (rule encoding_by_witness[where g="decode_nat"], simp add:nat_encoding_aux)

fun log2_floor :: "nat \<Rightarrow> nat" where
  "log2_floor n = (if n > 1 then (Suc (log2_floor (n div 2))) else 0)"

declare log2_floor.simps [simp del]

lemma real_log2_floor:
  assumes "x > 0"
  shows "real (log2_floor x) = \<lfloor>log 2 (real x)\<rfloor>"
proof -
  have "x > 0 \<Longrightarrow> 2^(log2_floor x) \<le> x"
  proof (induction x rule: log2_floor.induct)
    case (1 n)
    then show ?case
      apply (cases "1 < n")
      apply (subst log2_floor.simps)
       apply (simp)
      by (simp add:log2_floor.simps)
  qed
  hence "x > 0 \<Longrightarrow> 2 powr (real (log2_floor x)) \<le> real x"
    by (simp add:powr_realpow)
  hence "x > 0 \<Longrightarrow> real (log2_floor x) \<le> log 2 (real x)"
    using le_log_iff by auto
  hence a:"x > 0 \<Longrightarrow> real (log2_floor x) \<le> \<lfloor>log 2 (real x)\<rfloor>"
    by (metis le_floor_iff of_int_le_iff of_int_of_nat_eq)

  have "x > 0 \<Longrightarrow> x < 2^(1+log2_floor x)"
  proof (induction x rule: log2_floor.induct)
    case (1 n)
    then show ?case
      apply (cases "1 < n")
      apply (subst log2_floor.simps)
       apply (simp)
      by (simp add:log2_floor.simps)
  qed
  hence "x > 0 \<Longrightarrow> real x < 2 powr (1+real (log2_floor x))"
    using powr_realpow 
    by (metis (no_types, opaque_lifting) assms of_nat_1 of_nat_add of_nat_less_iff of_nat_power one_add_one zero_less_numeral)
  hence "x > 0 \<Longrightarrow> log 2 (real x) < (1+real (log2_floor x))"
    by (simp add:less_powr_iff)
  hence b:"x > 0 \<Longrightarrow> \<lfloor>log 2 (real x)\<rfloor> \<le> real (log2_floor x)"
    by (metis add.commute floor_le_iff floor_of_nat le_floor_iff of_int_of_nat_eq)

  show ?thesis using a b assms by linarith
qed

lemma log2_floor_mono:
  assumes "n \<le> m"
  shows "log2_floor n \<le> log2_floor m"
proof -
  have "real (log2_floor n) \<le> real (log2_floor m)"
    apply (cases "n > 0")
    using assms apply (simp add:real_log2_floor floor_mono)
    by (simp, subst log2_floor.simps, simp)
  thus ?thesis
    using of_nat_le_iff by blast
qed

lemma log2_floor_mult:
  "log2_floor (n*m) \<le> log2_floor n + log2_floor m + 1"
proof -
  have "n = 0 \<Longrightarrow> ?thesis" by simp
  moreover have "m = 0 \<Longrightarrow> ?thesis" by simp
  moreover have "n > 0 \<Longrightarrow> m > 0 \<Longrightarrow> real (log2_floor (n*m)) \<le> real (log2_floor n) + real (log2_floor m) + 1"
    by (simp add: log_mult real_log2_floor floor_add)
  hence "n > 0 \<Longrightarrow> m > 0 \<Longrightarrow> ?thesis"
    by force
  ultimately show ?thesis by blast
qed

lemma nat_bit_count:
  "bit_count (N\<^sub>S n) \<le> 2 * log 2 (n+1) + 1"
proof (induction n rule:nat_encoding_aux.induct)
  case 1
  then show ?case by simp
next
  case (2 n)
  have "log 2 2 + log 2 (1 + real (n div 2)) \<le> log 2 (2 + real n)"
    apply (subst log_mult[symmetric], simp, simp, simp)
    by (subst log_le_cancel_iff, simp+)
  hence "1 + 2 * log 2 (1 + real (n div 2)) + 1 \<le> 2 * log 2 (2 + real n)"
    by simp
  thus ?case using 2 by simp 
qed

lemma nat_bit_count_est:
  assumes "n \<le> m"
  shows "bit_count (N\<^sub>S n) \<le> 2 * log 2 (m+1) + 1"
proof -
  have "2 * log 2 (n+1) + 1 \<le> 2 * log 2 (m+1) + 1" 
    using assms by simp
  thus ?thesis using nat_bit_count assms le_ereal_le by blast
qed

lemma nat_encoding_length:
  "encoding_length (N\<^sub>S n) = 2*enat (log2_floor (n + 1))+1"
  apply (induction n rule:nat_encoding_aux.induct)
  apply (simp add:log2_floor.simps) 
  using one_enat_def zero_enat_def apply force
  apply (subst log2_floor.simps)
  apply (simp add:eSuc_enat[symmetric])
  by (metis distrib_left_numeral iadd_Suc_right mult_2 plus_1_eSuc(2))

lemma nat_encoding_length_est:
  assumes "n \<le> m"
  shows "encoding_length (N\<^sub>S n) \<le> 2*enat (log2_floor (m + 1))+1"
  apply (simp add:nat_encoding_length del:N\<^sub>S.simps)
  using log2_floor_mono of_nat_mono of_nat_eq_enat 
  by (simp add: assms mult_left_mono)

section \<open>Integers\<close>

fun I\<^sub>S :: "int \<Rightarrow> bool list option"
  where 
    "I\<^sub>S n = (if n \<ge> 0 then Some [True]@\<^sub>SN\<^sub>S (nat n) else Some [False]@\<^sub>S (N\<^sub>S (nat (-n-1))))" 

fun decode_int :: "bool list \<Rightarrow> (int \<times> bool list)"
  where 
    "decode_int (True#xs) = (\<lambda>(x::nat,y). (int x, y)) (decode_nat xs)" | 
    "decode_int (False#xs) = (\<lambda>(x::nat,y). (-(int x)-1, y)) (decode_nat xs)" |
    "decode_int [] = undefined"

lemma int_encoding: "is_encoding I\<^sub>S"
  apply (rule encoding_by_witness[where g="decode_int"])
  by (simp add:nat_encoding_aux)

lemma int_encoding_length:
  "encoding_length (I\<^sub>S n) \<le> 2*enat (log2_floor (nat (abs n) + 1))+2"
proof -
  have a:"\<And>x. x+1+1 = x+(2::enat)" by simp
  have b:"\<And>x y. x \<le> y \<Longrightarrow> 2 * x \<le> 2 * (y::enat)"
    by (simp add:add_mono mult_2)
  have "\<And>x y. 0 < x \<Longrightarrow> x \<le> y \<Longrightarrow> real (log2_floor x) \<le> real (log2_floor y)"
    apply (subst real_log2_floor, simp)
    apply (subst real_log2_floor, linarith) 
    by (simp add:floor_mono)

  hence "\<And>x y. 0 < x \<Longrightarrow> x \<le> y \<Longrightarrow> log2_floor x \<le> log2_floor y"
    by simp
  moreover have "\<And>y. 0 \<le> y \<Longrightarrow> log2_floor 0 \<le> log2_floor y"
    by (simp add: log2_floor.simps)
  ultimately have d:"\<And>x y.  x \<le> y \<Longrightarrow> log2_floor x \<le> log2_floor y"
    by (metis bot_nat_0.not_eq_extremum)
  show ?thesis
  apply (cases "n \<ge> 0")
  using nat_encoding_length[where n="nat n"]
   apply (simp add:eSuc_enat[symmetric] eSuc_plus_1)
  using nat_encoding_length[where n="nat (-n-1)"]
  apply (simp add:eSuc_enat[symmetric] eSuc_plus_1 a)
  using b d by fastforce
qed

lemma int_bit_count:
  "bit_count (I\<^sub>S x) \<le> 2 * log 2 (abs x+1) + 2"
proof -
  have a:"\<not>(0 \<le> x) \<Longrightarrow> 1 + 2 * log 2 (- real_of_int x) \<le> 1 + 2 * log 2 (1 - real_of_int x)"
    by simp
  show ?thesis
    apply (cases "x \<ge> 0")
     using nat_bit_count[where n="nat x"] apply (simp add: bit_count_append add.commute)
     using nat_bit_count[where n="nat (-x-1)"] apply (simp add: bit_count_append add.commute)
     using a order_trans by blast
qed

lemma int_bit_count_est:
  assumes "abs n \<le> m"
  shows "bit_count (I\<^sub>S n) \<le> 2 * log 2 (m+1) + 2"
proof -
  have "2 * log 2 (abs n+1) + 2 \<le> 2 * log 2 (m+1) + 2" using assms by simp
  thus ?thesis using assms le_ereal_le int_bit_count by blast
qed

lemma int_encoding_length_est:
  assumes "nat (abs n) \<le> m"
  shows "encoding_length (I\<^sub>S n) \<le> 2*enat (log2_floor (m + 1))+2"
proof -
  have "encoding_length (I\<^sub>S n) \<le> 2*enat (log2_floor (nat (abs n) + 1))+2"
    by (metis int_encoding_length)
  also have "... \<le> 2*enat (log2_floor (m + 1))+2"
    by (metis assms add_mono add_right_mono enat_ord_simps(1) log2_floor_mono mult_2)
  finally show ?thesis by blast
qed

section \<open>Cartesian Product\<close>

fun encode_prod :: "'a encoding \<Rightarrow> 'b encoding \<Rightarrow> ('a \<times> 'b) encoding" (infixr "\<times>\<^sub>S" 65)
  where 
    "encode_prod e1 e2 x = e1 (fst x)@\<^sub>S e2 (snd x)"

fun decode_prod :: "'a encoding \<Rightarrow> 'b encoding \<Rightarrow> bool list \<Rightarrow> ('a \<times> 'b) \<times> bool list"
  where
    "decode_prod e1 e2 x0 = (
      let (r1,x1) = decode e1 x0 in (
        let (r2,x2) = decode e2 x1 in ((r1,r2),x2)))"

lemma prod_encoding_dom:
  "x \<in> dom (e1 \<times>\<^sub>S e2) = (fst x \<in> dom e1 \<and> snd x \<in> dom e2)"
  apply (case_tac [!] "e1 (fst x)")
   apply (case_tac [!] "e2 (snd x)")
  by (simp add:dom_def del:not_None_eq)+

lemma prod_encoding:
  assumes "is_encoding e1"
  assumes "is_encoding e2"
  shows "is_encoding (encode_prod e1 e2)"
proof  (rule encoding_by_witness[where g="decode_prod e1 e2"])
  fix x y
  assume a:"x \<in> dom (e1 \<times>\<^sub>S e2)"

  have b:"e1 (fst x) = Some (the (e1 (fst x)))"
    by (metis a prod_encoding_dom domIff option.exhaust_sel)
  have c:"e2 (snd x) = Some (the (e2 (snd x)))" 
    by (metis a prod_encoding_dom domIff option.exhaust_sel)

  show "decode_prod e1 e2 (the ((e1 \<times>\<^sub>S e2) x) @ y) = (x, y)"
    apply (simp, subst b, subst c)
    apply simp
    using assms b c by (simp add:decode_elim)
qed

lemma prod_encoding_length:
  "encoding_length ((e1 \<times>\<^sub>S e2) x) = encoding_length (e1 (fst x)) + encoding_length (e2 (snd x))"
  by (simp add:encoding_length_sum)

lemma prod_bit_count:
  "bit_count ((e1 \<times>\<^sub>S e2) x) = bit_count (e1 (fst x)) + bit_count (e2 (snd x))"
  by (simp add:bit_count_append)


section \<open>Dependent Product>\<close>

fun encode_dependent_sum :: "'a encoding \<Rightarrow> ('a \<Rightarrow> 'b encoding) \<Rightarrow> ('a \<times> 'b) encoding" (infixr "\<times>\<^sub>D" 65)
  where 
    "encode_dependent_sum e1 e2 x = e1 (fst x)@\<^sub>S e2 (fst x) (snd x)"

lemma dependent_encoding:
  assumes "is_encoding e1"
  assumes "\<And>x. is_encoding (e2 x)"
  shows "is_encoding (encode_dependent_sum e1 e2)"
proof -
  define d where "d = (\<lambda>x0. 
    let (r1, x1) = decode e1 x0 in 
    let (r2, x2) = decode (e2 r1) x1 in ((r1,r2), x2))"

  have a: "\<And>x. x \<in> dom (e1 \<times>\<^sub>D e2) \<Longrightarrow> fst x \<in> dom e1"
    apply (simp add:dom_def del:not_None_eq) 
    using append_encoding.simps by metis
  have b: "\<And>x. x \<in> dom (e1 \<times>\<^sub>D e2) \<Longrightarrow> snd x \<in> dom (e2 (fst x))"
    apply (simp add:dom_def del:not_None_eq) 
    using append_encoding.simps by metis
  have c: "\<And>x. x \<in> dom (e1 \<times>\<^sub>D e2) \<Longrightarrow> e1 (fst x) = Some (the (e1 (fst x)))"
    using a by (simp add: domIff)
  have d: "\<And>x. x \<in> dom (e1 \<times>\<^sub>D e2) \<Longrightarrow> e2 (fst x) (snd x) = Some (the (e2 (fst x) (snd x)))"
    using b by (simp add: domIff)
  show ?thesis
    apply (rule encoding_by_witness[where g="d"])
    apply (simp add:d_def, subst c, simp, subst d, simp)
    using assms a b by (simp add:d_def decode_elim_2)
qed

lemma dependent_encoding_length:
  "encoding_length ((e1 \<times>\<^sub>D e2) x) = encoding_length (e1 (fst x)) + encoding_length (e2 (fst x) (snd x))"
  by (simp add:encoding_length_sum)

lemma dependent_bit_count:
  "bit_count ((e1 \<times>\<^sub>D e2) x) = bit_count (e1 (fst x)) + bit_count (e2 (fst x) (snd x))"
  by (simp add:bit_count_append)


section \<open>Set\<close>

fun set\<^sub>S :: "'a encoding \<Rightarrow> 'a set encoding" 
  where
    "set\<^sub>S e x = (
      if finite x \<and> (x \<subseteq> dom e) then
        (list\<^sub>S e) (linorder.sorted_key_list_of_set (\<le>) e x)
      else
        None
    )"

fun decode_set :: "'a encoding \<Rightarrow> bool list \<Rightarrow> (('a set) \<times> bool list)" 
  where
    "decode_set e xs = (\<lambda>(x,y). (set x,y)) (decode (list\<^sub>S e) xs)"

lemma set_encoding:
  assumes "is_encoding e"
  shows "is_encoding (set\<^sub>S e)"
proof  (rule encoding_by_witness[where g="decode_set e"])
  fix x y
  interpret folding_insort_key "((\<le>) :: bool list option \<Rightarrow> bool list option \<Rightarrow> bool)" 
      "(<)" "dom e" "e"
    by (standard, metis encoding_imp_inj[OF assms])
  assume "x \<in> dom (set\<^sub>S e)"
  hence a:"finite x \<and> x \<subseteq> dom e"
    apply (simp add:dom_def del:not_None_eq) by presburger
  have b:"set (linorder.sorted_key_list_of_set (\<le>) e x) = x"
    using a set_sorted_key_list_of_set by auto
  have "(linorder.sorted_key_list_of_set (\<le>) e x) \<in> dom (list\<^sub>S e)"
    apply (rule list_encoding_dom, rule subsetI)
    apply (simp add:b)
    using a by blast
  thus "decode_set e (the (set\<^sub>S e x) @ y) = (x, y)"
    using decode_elim_2[OF list_encoding[OF assms]] by (simp add:a b del:not_None_eq)
qed
                        
lemma set_encoding_dom:
  assumes "is_encoding e"
  assumes "finite x"
  assumes "x \<subseteq> dom e"
  shows "x \<in> dom (set\<^sub>S e)"
proof -
  interpret folding_insort_key "((\<le>) :: bool list option \<Rightarrow> bool list option \<Rightarrow> bool)" 
      "(<)" "dom e" "e"
    by (standard, metis encoding_imp_inj[OF assms(1)])
  have "linorder.sorted_key_list_of_set (\<le>) e x \<in> dom (list\<^sub>S e)"
    apply (rule list_encoding_dom)
    using assms by simp
  thus ?thesis
    using assms by (simp add:dom_def)
qed

lemma sum_enat_inf: 
  fixes f :: "'a \<Rightarrow> enat"
  assumes "finite I"
  assumes "i \<in> I"
  assumes "f i = \<infinity>"
  shows "sum f I = \<infinity>"
  using assms apply (induction I, simp, simp) 
  using plus_eq_infty_iff_enat by presburger  

lemma set_encoding_length:
  assumes "is_encoding e"
  assumes "finite x"
  shows "encoding_length (set\<^sub>S e x) = sum (\<lambda>y. encoding_length (e y) + 1) x + 1"
proof -
  interpret folding_insort_key "((\<le>) :: bool list option \<Rightarrow> bool list option \<Rightarrow> bool)" 
      "(<)" "dom e" "e"
    by (standard, metis encoding_imp_inj[OF assms(1)])

  have "x \<subseteq> dom e \<Longrightarrow> ?thesis"
    using assms(2) sorted_key_list_of_set distinct_if_distinct_map 
    by (simp add:list_encoding_length sum_list_distinct_conv_sum_set del:not_None_eq)
  moreover have "\<not>(x \<subseteq> dom e) \<Longrightarrow> ?thesis"
  proof -
    assume a:"\<not>(x \<subseteq> dom e)"
    then obtain u where b:"u \<in> x"  and c:"e u = None" by auto 
    show ?thesis
    using a apply simp
    by (subst sum_enat_inf[where i="u"], metis assms(2), metis b, simp add:c, simp)
  qed
  ultimately show ?thesis by blast
qed

section \<open>Composition\<close>

lemma encoding_compose:
  assumes "is_encoding f"
  assumes "inj_on g A"
  shows "is_encoding (\<lambda>x. if x \<in> A then f (g x) else None)"
  using assms by (simp add: inj_onD is_encoding_def)


section \<open>Maps\<close>

fun graph where "graph f = {(x, f x)|x . f x \<noteq> undefined }"
fun singleton where "singleton S = (if card S = 1 then (THE x. x \<in> S) else undefined)"
fun ungraph where "ungraph S = (\<lambda>x. singleton {y. (x,y) \<in> S})"

lemma ungraph_graph: "ungraph (graph f) = f"
proof (rule ext)
  fix x
  show "ungraph (graph f) x = f x"
    apply (simp)
    by (cases "f x = undefined", simp, simp)
qed

fun encode_fun :: "'a encoding \<Rightarrow> 'b encoding \<Rightarrow> ('a \<Rightarrow> 'b) encoding" (infixr "\<rightarrow>\<^sub>S" 65)
  where
    "encode_fun e1 e2 f = (set\<^sub>S (e1 \<times>\<^sub>S e2)) (graph f)"

fun decode_fun :: "'a encoding \<Rightarrow> 'b encoding \<Rightarrow>  bool list \<Rightarrow> ('a \<Rightarrow> 'b) \<times> bool list"
  where
    "decode_fun e1 e2 xs = (\<lambda>(x,y). (ungraph x, y)) (decode (set\<^sub>S (e1 \<times>\<^sub>S e2)) xs)"

lemma fun_encoding:
  assumes "is_encoding e1"
  assumes "is_encoding e2"
  shows "is_encoding (e1 \<rightarrow>\<^sub>S e2)"
  apply (rule encoding_by_witness[where g="decode_fun e1 e2"])
  using set_encoding[OF prod_encoding[OF assms]]
  by (simp add:dom_def ungraph_graph decode_elim_2 del:set\<^sub>S.simps not_None_eq graph.simps ungraph.simps)

lemma fun_encoding_dom:
  assumes "is_encoding e1"
  assumes "is_encoding e2"
  assumes "finite {x. f x \<noteq> undefined}"
  assumes "None \<notin> e1 ` {x. f x \<noteq> undefined}"
  assumes "None \<notin> e2 ` (f ` UNIV - {undefined})"
  shows "f \<in> dom (e1 \<rightarrow>\<^sub>S e2)"
proof -
  have "graph f \<in> dom (set\<^sub>S (e1 \<times>\<^sub>S e2))"
    apply (rule set_encoding_dom)
      using prod_encoding assms apply blast
     apply (simp add:image_Collect[symmetric])
    apply (metis finite_imageI assms(3))
      apply (rule subsetI, subst prod_encoding_dom)
      apply (rule conjI)
     using assms  image_iff apply fastforce
    apply (simp del:not_None_eq) 
    by (metis Diff_iff assms(5) domIff empty_iff imageI insert_iff rangeI snd_conv)
  thus ?thesis by (simp add:dom_def)
qed
    
lemma fun_encoding_length:
  assumes "is_encoding e1"
  assumes "is_encoding e2"
  assumes "finite {x. f x \<noteq> undefined}"
  shows "encoding_length ((e1 \<rightarrow>\<^sub>S e2) f) = 
    (\<Sum>x \<in> {x. f x  \<noteq> undefined}. encoding_length (e1 x) +  encoding_length (e2 (f x)) + 1) + 1"
  apply (simp del:set\<^sub>S.simps)
  apply (subst set_encoding_length, metis prod_encoding[OF assms(1) assms(2)])
  using assms(3) apply simp
  apply (simp add: prod_encoding_length setcompr_eq_image del:set\<^sub>S.simps encode_prod.simps)
  apply (subst sum.reindex)
   apply (simp add: inj_on_convol_ident)
  by simp

lemma fun_encoding_length_est:
  assumes "is_encoding e1"
  assumes "is_encoding e2"
  assumes "finite A"
  assumes "\<And>i. i \<in> A \<Longrightarrow> encoding_length (e1 i) \<le> (a::enat)"
  assumes "\<And>i. i \<in> B \<Longrightarrow> encoding_length (e2 i) \<le> (b::enat)"
  assumes "f \<in> A \<rightarrow>\<^sub>E B"
  shows "encoding_length ((e1 \<rightarrow>\<^sub>S e2) f) \<le> enat (card A) * (a + b + 1) + 1"

proof -
  have a1: "\<And>x. x \<in> {x. f x \<noteq> undefined} \<Longrightarrow> x \<in> A"
    using assms(6) PiE_iff extensional_def by blast
  have a2: "\<And>x. x \<in> {x. f x \<noteq> undefined} \<Longrightarrow> f x \<in> B" 
    using assms(6) PiE_iff extensional_def by blast
  have "card {x. f x \<noteq> undefined} \<le> card A"
    by (rule card_mono, metis assms(3), rule subsetI, metis a1)
  hence a3: "enat (card {x. f x \<noteq> undefined}) \<le> enat (card A)" 
    using enat_ord_simps(1) by blast
  have "(\<Sum>x \<in> {x. f x \<noteq> undefined}. encoding_length (e1 x) + encoding_length (e2 (f x)) + 1) + 1 \<le> (\<Sum>x \<in> {x. f x \<noteq> undefined}. a + b + 1) + 1"
    apply (rule add_mono)
     apply (rule sum_mono)
    apply (rule add_mono)
      apply (rule add_mono)
    apply (metis a1 assms(4))  
      apply (metis a2 assms(5)) 
    by simp+
  also  have "... \<le>  enat (card A) * (a + b + 1) + 1" apply simp using a3 
    by (simp add: mult_right_mono of_nat_eq_enat)

  finally have a:"(\<Sum>x \<in> {x. f x \<noteq> undefined}. encoding_length (e1 x) + encoding_length (e2 (f x)) + 1) + 1 \<le> enat (card A) * (a + b + 1) + 1"
    by blast
  show ?thesis 
  apply (subst fun_encoding_length)
     apply (metis assms(1))
    apply (metis assms(2))
   apply (rule finite_subset[OF _ assms(3)], metis subsetI a1)
  by (metis a)

qed

lemma log_est: "log 2 (real n + 1) \<le> n"
proof -
  have "n + 1 \<le> 2 ^ ( n)"
    by (induction n, simp, simp)
  hence "real n + 1 \<le> 2 powr (real n)"
    apply (simp add: powr_realpow)
    by (metis add.commute numeral_power_eq_of_nat_cancel_iff of_nat_Suc of_nat_mono)
  thus ?thesis 
    by (simp add: log_le_iff)
qed
end

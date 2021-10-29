section \<open>Primes\<close>

text \<open>In this section we introduce a function that retrieves the next larger odd prime.\<close>

theory Primes_Ext
imports Main "HOL-Computational_Algebra.Primes" "Bertrands_Postulate.Bertrand" 
begin

lemma inf_primes: "wf ((\<lambda>n. (Suc n, n)) ` {n. \<not> (prime n)})" (is "wf ?S") 
proof (rule wfI_min)
  fix x :: nat
  fix Q :: "nat set"
  assume a:"x \<in> Q"

  have "\<exists>z \<in> Q. prime z \<or> Suc z \<notin> Q" 
  proof (cases "\<exists>z \<in> Q. Suc z \<notin> Q")
    case True
    then show ?thesis by auto
  next
    case False
    hence b:"\<And>z. z \<in> Q \<Longrightarrow> Suc z \<in> Q" by blast
    have c:"\<And>k. k + x \<in> Q"
    proof -
      fix k
      show "k+x \<in> Q"
        by (induction "k", simp add:a, simp add:b)
    qed
    show ?thesis 
      apply (cases "\<exists>z \<in> Q. prime z")
       apply blast
        by (metis add.commute less_natE bigger_prime c)
  qed
  thus "\<exists>z \<in> Q. \<forall>y. (y,z) \<in> ?S \<longrightarrow> y \<notin> Q" by blast
qed

function find_prime_above :: "nat \<Rightarrow> nat" where
  "find_prime_above n = (if prime n then n else find_prime_above (Suc n))"
  by auto
termination
  apply (relation "(\<lambda>n. (Suc n, n)) ` {n. \<not> (prime n)}")
  using inf_primes apply blast
  by simp

declare find_prime_above.simps [simp del]

lemma find_prime_above_is_prime:
  "prime (find_prime_above n)"
  apply (induction n rule:find_prime_above.induct)
  by (simp add: find_prime_above.simps)+

lemma find_prime_above_min:
  "find_prime_above n \<ge> 2"
  by (metis find_prime_above_is_prime prime_ge_2_nat)

lemma find_prime_above_lower_bound:
  "find_prime_above n \<ge> n"
  apply (induction n rule:find_prime_above.induct)
  by (metis find_prime_above.simps linorder_le_cases not_less_eq_eq)

lemma find_prime_above_upper_boundI:
  assumes "prime m"
  shows "n \<le> m \<Longrightarrow> find_prime_above n \<le> m"
proof (induction n rule:find_prime_above.induct)
  case (1 n)
  have a:"\<not>prime n \<Longrightarrow> Suc n \<le> m"
    by (metis assms "1.prems" not_less_eq_eq le_antisym)
  show ?case using 1 
    apply (cases "prime n")
     apply (subst find_prime_above.simps)
    using assms(1) apply simp
    by (metis a find_prime_above.simps)
qed

lemma find_prime_above_upper_bound:
  "find_prime_above n \<le> 2*n+2"
proof (cases "n \<le> 1")
  case True
  have "find_prime_above n \<le> 2"
    apply (rule find_prime_above_upper_boundI, simp) using True by simp 
  then show ?thesis using trans_le_add2 by blast
next
  case False
  hence a:"n > 1" by auto
  then obtain p where p_bound: "p \<in> {n<..<2*n}" and p_prime: "prime p" 
    using bertrand by metis
  have "find_prime_above n \<le> p"
    apply (rule find_prime_above_upper_boundI)
     apply (metis p_prime)
    using p_bound by simp
  thus ?thesis using p_bound 
    by (metis greaterThanLessThan_iff nat_le_iff_add nat_less_le trans_le_add1)
qed

end
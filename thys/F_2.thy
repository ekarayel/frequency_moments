theory F_2
  imports Field scratch
begin

text \<open>Alon et. al. observe in \cite[2.2]{alon1996} that only 4-wise independent hash functions with
uniform distribution in @{term "{-1,1}"} are necessary. We obtain such random variables using
the previously constructed Carter Wegman hash family over the finite field @{term "2^d"} where
@{term "d"} is chosen such that @{term "2^d"} is larger or equal to the size of the universe.
We can map the resulting values of such hash function to @{term "-1"} and @{term "1"}
using one of the bits of the result discarding any of the other bits of the hash function.

Alon et. al. refer to \cite[Proposition 6.5]{alon1985} for an explicit construction of a 5-wise
independent two-valued hash family of size @{term "(2^(d+1))^2"} using parity check matrices of
BCH codes of length @{term "2^d"}. Note: The matrix cannot itself be stored in memory, but its
coefficients can be computed on the fly. We decided to avoid using that construction, since we don't
need two-valued hash families for any of the other algorithms. The drawback of our  implementation
with the Carter-Wegman hash family is that we requiring twice as many coin tosses, i.e., our hash
family has size @{term "2^(4*d)"}. (Note: We obtain the same theorem, since the difference is a
constant factor in the space complexity.).

A drawback of both of these solutions is that they require multiplications in the finite field with
order @{term "2^d"}. These require $O(d)$ machine instructions using a naive implementation,
although there are methods such as optimal normal bases, generator based representations, 
carry-less multiply operations, decomposition (for example $F_{64}$ can be represented as a field
extension of $F_16$).

Hence, we also given an alternate version using the Carter-Wegman hash familiy over
finite fields with prime order @{term "p"}, where @{term "p"} must be larger than the universe size.
On common modern machine architectures these hash functions can be evaluated a lot faster than the
above variant, since multiplications can be implemented a lot faster in prime order fields (as
opposed to prime power fields). We however end up with hash functions that are slightly biased
upwards or downwards, e.g., their value is @{term "1"} with probability @{term "(p+1)/(2*p)"}
or @{term "(p-1)/(2*p)"}. The bias can be removed if we randomly decide for each hash
function whether we flip the sign or not, i.e., we have an additional coin toss in addition to the
choice of the hash function. Note: We cannot change the decision about flipping the sign
during the course of the algorithm, i.e., we have to consistently flip or not using an initial
coin toss. Even with the bias eliminated, we end up with new non-zero terms in the variance
calculation, though we can still show the same confidence and error probabilities.

As far as we know this alternate version has not been published yet, and we think it is worthwhile
to include here, as it may improve speed on modern machines and maybe relevant for some high
performance use-cases.\<close>

definition f2_sketch
  where
    "f2_sketch f xs \<omega> = (\<Sum> x \<in> set xs. (count_list xs x) * f x \<omega>)"

definition f2 :: "nat list \<Rightarrow> nat"
  where
    "f2 xs = (\<Sum> x \<in> set xs. (count_list xs x)^2)"

definition sign_hash
  where
    "sign_hash f2 xs = (\<Sum> x \<in> set xs. (count_list xs x)^2)"


lemma
  assumes "field F"
  assumes "f {n. n < (2^d :: nat)} \<subseteq> carrier F"
  assumes "inj_on f {n. n < (2^d :: nat)}"
  shows "prob_space.expectation (poly_family F 4) (\<lambda>\<omega>. (f2_sketch () xs \<omega>)^2) 


definition to_sign
  where "to_sign x = (if x mod 2 = 0 then 1 else (-1))"

definition sign_hash
  where "sign_hash p x \<omega> = to_sign (zfact_embed_inv p (ring.eval (ZFact p) \<omega> (zfact_embed p x)))"




lemma "{n. n < (3 :: nat)} \<noteq> {}" by force




lemma 
  assumes "prime p"
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> x < p"
  shows "prob_space.expectation (poly_family (ZFact p) 4) (\<lambda>\<omega>. (f2_sketch p xs \<omega>)^2) = f2 xs"
  sorry

lemma 
  assumes "prime p"
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> x < p"
  shows "prob_space.prob (poly_family (ZFact p) 4) {\<omega>. abs ((f2_sketch p xs \<omega>)^2 - f2 xs) > (f2 xs)} < 1/2"
  sorry


datatype f2_estimator_setup = F2_Estimator_Setup "nat" "nat list list list"

datatype f2_sketch = F2_Sketch "int list list"


(* make this random *)
fun start :: "nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> f2_estimator_setup"
  where
    "start universe_size \<epsilon> \<delta> = F2_Estimator_Setup 3 []"


fun sketch :: "nat \<Rightarrow> f2_estimator_setup \<Rightarrow> f2_sketch"
  where
    "sketch x y = F2_Sketch []"

fun merge_sketch :: "f2_sketch \<Rightarrow> f2_sketch \<Rightarrow> f2_sketch"
  where
    "merge_sketch _ _ = F2_Sketch []"

fun estimate :: "f2_estimator_setup \<Rightarrow> f2_sketch \<Rightarrow> real"
  where
    "estimate _ _ = 0"


(*
  [x]   \<longrightarrow> sketch       \<longrightarrow>  F2_Sketch
  @     \<longrightarrow> merge_sketch \<rightarrow> 
  
  is_sketch_for c x1 l1
  is_sketch_for c x2 l2
    \<Longrightarrow>
  is_sketch_for c (merge_sketch x1 x2) (l1 @ l2)

  a < univ_size c \<Longrightarrow> is_sketch_for c (sketch c [a]) [a]
  
  is_sketch_for c [] (null c)

  P(is_sketch_for (setup n e d) x y = 1) \<Longrightarrow> P( |estimate x - f2 y| < d f2)) > (1-e)

  c is a random variable, x1 is a random variable (same probability space)
  
  
  








*)




(*
  F_1 requires coin tosses during the run of the algorithm.
  
  Misra/Gries has a merge operation.
  Does not use coin tosses.






*)



end

theory Sample (* Code just for typesetting sample content *)
imports Main  "HOL-Probability.Probability_Mass_Function"
begin

definition example1 where
  "example1 = 
    do {
      a \<leftarrow> pmf_of_set {0,1::nat};
      return_pmf (a+1)
    }
  "

lemma "example1 = pmf_of_set {1,2}"
  apply (simp add:example1_def)
  apply (subst map_pmf_def[symmetric])
  apply (subst map_pmf_of_set_inj, simp, simp, simp)
  by (simp add: numeral_2_eq_2)

definition example2 where
  "example2 = 
    do {
      a \<leftarrow> pmf_of_set {0,1::nat};
      b \<leftarrow> pmf_of_set {2,3::nat};
      return_pmf (a,b)
    }
  "

definition example3 where
  "example3 = 
    do {
      a \<leftarrow> pmf_of_set {1,2::nat};
      b \<leftarrow> pmf_of_set {0..<a};
      return_pmf (a,b)
    }
  "

definition init :: "rat \<Rightarrow> rat \<Rightarrow> nat \<Rightarrow> nat pmf" where "init = undefined"
definition update :: "nat \<Rightarrow> nat \<Rightarrow> nat pmf" where "update = undefined"
definition result :: "nat \<Rightarrow> rat pmf" where "result = undefined"

definition dist1 where
  "dist1 \<delta> \<epsilon> n a\<^sub>0 a\<^sub>1 = 
    do {
      s\<^sub>0 \<leftarrow> init \<delta> \<epsilon> n;
      s\<^sub>1 \<leftarrow> update s\<^sub>0 a\<^sub>0;
      s\<^sub>2 \<leftarrow> update s\<^sub>1 a\<^sub>1;

      s\<^sub>m \<leftarrow> update s\<^sub>2 a\<^sub>1;
      result s\<^sub>m
    }"

definition dist2 where
  "dist2 \<delta> \<epsilon> n as = fold (\<lambda>a s. s \<bind> update a) as (init \<delta> \<epsilon> n) \<bind> result"


end

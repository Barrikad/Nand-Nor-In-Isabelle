theory BoolRelations imports Main
begin
primrec member where
  \<open>member _ [] = False\<close> |
  \<open>member m (n # A) = (m = n \<or> member m A)\<close>

lemma member_iff [iff]: \<open>member m A \<longleftrightarrow> m \<in> set A\<close>
  by (induct A) simp_all

primrec common where
  \<open>common _ [] = False\<close> |
  \<open>common A (m # B) = (member m A \<or> common A B)\<close>

lemma common_iff [iff]: \<open>common A B \<longleftrightarrow> set A \<inter> set B \<noteq> {}\<close>
  by (induct B) simp_all

datatype 'a form = Pro 'a 
                 | Neg \<open>'a form\<close>
                 | Con \<open>'a form\<close> \<open>'a form\<close> 
                 | Dis \<open>'a form\<close> \<open>'a form\<close> 
                 | Imp \<open>'a form\<close> \<open>'a form\<close> 
                 | Iff \<open>'a form\<close> \<open>'a form\<close> 
                 | Non \<open>'a form\<close> \<open>'a form\<close>
                 | Nis \<open>'a form\<close> \<open>'a form\<close> 

datatype 'a non_form = ProNon 'a | Non' \<open>'a non_form\<close> \<open>'a non_form\<close> (infix \<open>\<up>\<close> 0)

datatype 'a nis_form = ProNis 'a | Nis' \<open>'a nis_form\<close> \<open>'a nis_form\<close> (infix \<open>\<down>\<close> 0)

fun semantics where
  \<open>semantics i (Pro a)   = i a\<close> | 
  \<open>semantics i (Neg p)   = (\<not>(semantics i p))\<close> |
  \<open>semantics i (Con p q) = ((semantics i p) \<and> (semantics i q))\<close> |
  \<open>semantics i (Dis p q) = ((semantics i p) \<or> (semantics i q))\<close> |
  \<open>semantics i (Imp p q) = ((semantics i p) \<longrightarrow> (semantics i q))\<close> |
  \<open>semantics i (Iff p q) = ((semantics i p) \<longleftrightarrow> (semantics i q))\<close> |
  \<open>semantics i (Non p q) = (\<not>((semantics i p) \<and> (semantics i q)))\<close> |
  \<open>semantics i (Nis p q) = (\<not>((semantics i p) \<or> (semantics i q)))\<close>

primrec non_semantics where
  \<open>non_semantics i (ProNon n) = i n\<close> |
  \<open>non_semantics i (p \<up> q) = (\<not>(non_semantics i p \<and> non_semantics i q))\<close>

primrec nis_semantics where
  \<open>nis_semantics i (ProNis n) = i n\<close> |
  \<open>nis_semantics i (p \<down> q) = (\<not>(nis_semantics i p \<or> nis_semantics i q))\<close>

fun f_size :: \<open>bool \<Rightarrow> 'a form \<Rightarrow> nat\<close> where
  \<open>f_size m (Pro a)   = (1)\<close> | 
  \<open>f_size m (Nis p q) = ((if m then 1 else 5) + (f_size m p) + (f_size m q))\<close> |
  \<open>f_size m (Non p q) = ((if m then 5 else 1) + (f_size m p) + (f_size m q))\<close> |
  \<open>f_size m (Neg p)   = (1 + (f_size m p))\<close> |
  \<open>f_size m (Con p q) = (5 + (f_size m p) + (f_size m q))\<close> |
  \<open>f_size m (Dis p q) = (5 + (f_size m p) + (f_size m q))\<close> |
  \<open>f_size m (Imp p q) = (5 + (f_size m p) + (f_size m q))\<close> |
  \<open>f_size m (Iff p q) = (20 + 2*((f_size m p) + (f_size m q)))\<close>

function non_expand where
  \<open>non_expand (Pro a)   = ProNon a\<close> |
  \<open>non_expand (Non p q) = (non_expand p \<up> non_expand q)\<close> |
  \<open>non_expand (Neg p)   = (let pex = non_expand p in (pex \<up> pex))\<close> |
  \<open>non_expand (Con p q) = non_expand (Neg (Non p q))\<close> |
  \<open>non_expand (Dis p q) = (non_expand (Neg p) \<up> non_expand (Neg q))\<close> |
  \<open>non_expand (Imp p q) = (non_expand p \<up> non_expand (Neg q))\<close> |
  \<open>non_expand (Nis p q) = non_expand (Neg (Non (Neg p) (Neg q)))\<close> |
  \<open>non_expand (Iff p q) = non_expand (Con (Imp p q) (Imp q p))\<close>
  by pat_completeness auto
termination by (relation \<open>measure (\<lambda>(p). f_size False p)\<close>) auto

function nis_expand where
  \<open>nis_expand (Pro a)   = ProNis a\<close> |
  \<open>nis_expand (Nis p q) = (nis_expand p \<down> nis_expand q)\<close> |
  \<open>nis_expand (Neg p)   = (let pex = nis_expand p in (pex \<down> pex))\<close> |
  \<open>nis_expand (Con p q) = (nis_expand (Neg p) \<down> nis_expand (Neg q))\<close> |
  \<open>nis_expand (Dis p q) = nis_expand (Neg (Nis p q))\<close> |
  \<open>nis_expand (Imp p q) = nis_expand (Neg (Nis (Neg p) q))\<close> |
  \<open>nis_expand (Non p q) = nis_expand (Neg (Nis (Neg p) (Neg q)))\<close> |
  \<open>nis_expand (Iff p q) = nis_expand (Con (Imp p q) (Imp q p))\<close>
  by pat_completeness auto
termination by (relation \<open>measure (\<lambda>(p). (f_size True p))\<close>) auto

lemma non_equal: \<open>(semantics i p) \<longleftrightarrow> (non_semantics i (non_expand p))\<close>
  by (induct p) (auto simp add: Let_def)

lemma nis_equal: \<open>(semantics i p) \<longleftrightarrow> (nis_semantics i (nis_expand p))\<close>
  by (induct p) (auto simp add: Let_def)

datatype atoms = A' | B' | C'
abbreviation example where  \<open>example \<equiv> 
  Imp (Con (Imp (Pro A') (Pro C')) 
      (Con (Imp (Neg (Pro A')) (Pro B')) 
           (Imp (Neg (Pro C')) (Neg (Pro B')))))
      (Pro C')\<close>


value \<open>nis_expand example\<close>

end
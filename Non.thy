theory Non imports Main BoolRelations begin

abbreviation \<open>sc X Y i \<equiv> (\<forall>p \<in> set X. non_semantics i p) \<longrightarrow> (\<exists>q \<in> set Y. non_semantics i q)\<close>

function mp where
  \<open>mp A B (ProNon n # C) [] = mp (n # A) B C []\<close> |
  \<open>mp A B C (ProNon n # D) = mp A (n # B) C D\<close> |
  \<open>mp A B ((p \<up> q) # C) [] = (mp A B C [p] \<and> mp A B C [q])\<close> |
  \<open>mp A B C ((p \<up> q) # D) = mp A B (p # q # C) D\<close> |
  \<open>mp A B [] [] = common A B\<close>
  by pat_completeness auto
termination by (relation \<open>measure (\<lambda>(_,_,C,D). \<Sum>p \<leftarrow> C @ D. size p)\<close>) auto

theorem main: \<open>(\<forall>i. sc (map ProNon A @ C) (map ProNon B @ D) i) \<longleftrightarrow> mp A B C D\<close>
  by (induct rule: mp.induct) auto

definition \<open>prover p \<equiv> mp [] [] [] [p]\<close>

corollary \<open>(\<forall>i. non_semantics i p) \<longleftrightarrow> prover p\<close>
  unfolding prover_def by (simp flip: main)

definition \<open>main \<equiv> prover (ProNon () \<up> (ProNon () \<up> ProNon ()))\<close>

proposition main by code_simp

export_code main in Haskell


end
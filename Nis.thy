theory Nis imports Main BoolRelations begin

abbreviation \<open>sc X Y i \<equiv> (\<forall>p \<in> set X. nis_semantics i p) \<longrightarrow> (\<exists>q \<in> set Y. nis_semantics i q)\<close>

function mp where
  \<open>mp A B (ProNis n # C) [] = mp (n # A) B C []\<close> |
  \<open>mp A B C (ProNis n # D) = mp A (n # B) C D\<close> |
  \<open>mp A B ((p \<down> q) # C) [] = mp A B C [p, q]\<close> |
  \<open>mp A B C ((p \<down> q) # D) = (mp A B (p # C) D \<and> mp A B (q # C) D)\<close> |
  \<open>mp A B [] [] = common A B\<close>
  by pat_completeness auto
termination by (relation \<open>measure (\<lambda>(_,_,C,D). \<Sum>p \<leftarrow> C @ D. size p)\<close>) auto

theorem main: \<open>(\<forall>i. sc (map ProNis A @ C) (map ProNis B @ D) i) \<longleftrightarrow> mp A B C D\<close>
proof (induct rule: mp.induct)
  case 4
  then show ?case
    by simp meson
qed auto

definition \<open>prover p \<equiv> mp [] [] [] [p]\<close>

corollary \<open>prover p \<longleftrightarrow> (\<forall>i. nis_semantics i p)\<close>
  unfolding prover_def by (simp flip: main)

definition \<open>main \<equiv> 
  prover ((ProNis () \<down> (ProNis () \<down> ProNis ())) \<down> (ProNis () \<down> (ProNis () \<down> ProNis ())))\<close>

proposition main by code_simp

export_code main in Haskell

end
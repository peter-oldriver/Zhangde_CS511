theory CommAnd
  imports Main
begin
 
text\<open> Apply style, the proof here corresponds to the proof for lem_j_3 \<close>
lemma lem_i_1 : "(p \<and> q) \<longrightarrow> (p \<and> q)"
  apply (rule impI)
  apply assumption
  done

text\<open> Isar style, the proof illustrates the use of intermediate facts,
   with keywords 'from ... have ...' \<close>
lemma lem_j_1 : "(p \<and> q) \<longrightarrow> (p \<and> q)"
proof
  assume a : "p \<and> q"
  from a have b : "p" by (rule conjE)   (* INTERMEDIATE fact *)
  from a have c : "q" by (rule conjE)   (* INTERMEDIATE fact *)
  from b c show "p \<and> q" by (rule conjI)
qed

text\<open> Isar style, lem_j_1 again, the proof illustrates the use of nested proofs \<close>
lemma lem_j_2 : "(p \<and> q) \<longrightarrow> (p \<and> q)"
proof
  assume a : "p \<and> q"
  show "p \<and> q" 
  proof (rule conjE [OF a])  (* a nested proof, i.e. a subproof *)
    (* do not omit '(rule conjE [OF a])' Isabelle is not smart enough to guess it *)
    assume b : "p"
    assume c : "q"
    from b c show "p \<and> q" by (rule conjI)
  qed
qed

text\<open> Isar style, lem_j_1 again, with the simplest possible proof \<close>
lemma lem_j_3 : "(p \<and> q) \<longrightarrow> (p \<and> q)"
proof
  assume a : "p \<and> q"
  show "p \<and> q" by (rule a)
qed

text\<open> Apply style \<close>
lemma lem_k_1 : "(p \<and> q) \<longrightarrow> (q \<and> p)"
  apply (rule impI)
  apply (rule conjI)
  apply (erule conjE)
   apply assumption
  apply (erule conjE)
  apply assumption
  done

text\<open> Isar style, the proof illustrates the use of intermediate facts,
   once more with keywords 'from ... have ...' \<close>
lemma lem_l_1 : "(p \<and> q) \<longrightarrow> (q \<and> p)"
proof
  assume a : "p \<and> q"
  from a have b : "p" by (rule conjE)     (* INTERMEDIATE fact *)
  from a have c : "q" by (rule conjE)     (* INTERMEDIATE fact *)
  from c b show "q \<and> p" by (rule conjI)   (* we must write 'from c b' not 'from b c' *)
qed

text\<open> Isar style, lem_l_1 again, with more abbreviations \<close>
lemma lem_l_2 : "(p \<and> q) \<longrightarrow> (q \<and> p)"
proof
  assume a : "p \<and> q"
  from a have b : "p" ..
  from a have c : "q" ..
  from c b show "(q \<and> p)" ..
qed

text\<open> Isar style, lem_l_1 again, with nested proofs \<close>
lemma lem_l_3 : "(p \<and> q) \<longrightarrow> (q \<and> p)"
proof
  assume a : "p \<and> q"
  from a show "q \<and> p"
  proof
    assume b : "p"
    assume c : "q"
    from c b show "q \<and> p" by (rule conjI)
  qed
qed

end


section \<open>Weakest Precondition is Sound w.r.t. the Denotational Semantics\<close>

theory WpSoundness
  imports  Denotational MonoDenotational Wp
begin

subsection \<open>Theorems about update\<close>

theorem UpdateWithLookupUnchanged:
  assumes "e \<in> defined l"
  shows "update l e {E (lookup l e)} = {E e}"
  using assms
proof (induct l arbitrary: e )
  case empty then show ?case
    by simp
next
  case (Lcons pos location) then show ?case
    apply (case_tac e)
    by (case_tac pos, fastforce+)+
qed

theorem UpdateErrGivesErr: 
  assumes "e \<in> defined l"
  shows "update l e {Err} = {Err}"
  using assms
proof (induct l arbitrary: e)
  case empty then show ?case
    by simp
next
  case (Lcons pos location) then show ?case
    apply (case_tac e)
    by (case_tac pos, fastforce+)+  
qed

lemma update_inter_err_div: 
  assumes "e \<in> defined l"
  shows "update l e es \<inter> {Err, Div} = es \<inter> {Err, Div}" 
  using assms proof (induction l arbitrary: e es)
  case empty
  then show ?case by simp
next
  case (Lcons pos l)
  then show ?case by (case_tac pos, fastforce+)+
qed

lemma defined_append : "x \<in> defined (loc \<triangleright> pos) \<Longrightarrow> x \<in> defined loc"
proof (induct loc arbitrary: x)
  case empty
  then show ?case by simp
next
  case (Lcons x1 loc)
  then show ?case apply (case_tac x1)
    by fastforce+
qed

lemma lookup_id_append_undefined: "x \<in> defined loc \<Longrightarrow>
       lookup loc x = exp.Leaf xa \<Longrightarrow>
       x \<notin> defined (loc\<triangleright>p)"
proof (induct loc arbitrary: x)
  case empty
  then show ?case by (case_tac p; simp)
next
  case (Lcons pos loc)
  then show ?case
    by (case_tac pos, fastforce+)+
qed

lemma append_undefined_lookup_id: "x \<in> defined loc \<Longrightarrow>
         x \<notin> defined (loc\<triangleright>p) \<Longrightarrow> \<exists>n. lookup loc x = Leaf n"
proof (induct loc arbitrary: x)
  case empty
  then show ?case 
    apply simp
    apply (case_tac p)
     apply (case_tac x; simp)
    apply (case_tac x; simp)
    done
next
  case (Lcons pos loc)
  then show ?case by (case_tac pos, fastforce+)+
qed

subsection \<open>The @{text "lookup_exec_update"} function\<close>
definition lookup_exec_update :: "strategy \<Rightarrow> location \<Rightarrow> exp \<Rightarrow> env \<Rightarrow> exp_err_div set"
  where "lookup_exec_update s loc e senv = (update loc e (PdToSet (exec s senv (lookup loc e))))"

text
 \<open> The following simp rules mean that (for defined locations), you shouldn't usually need to use 
   @{text "lookup_exec_update_def"}. Instead, these rules give an alternative definitionn. For 
   @{text "lookup_exec_update"} that doesn't refer to other functions like update, lookup etc. at 
   all \<close>
lemma lookup_exec_update_simp1[simp] : 
  "lookup_exec_update s \<epsilon> e senv = PdToSet (exec s senv e)" 
  by (simp add: lookup_exec_update_def)
lemma lookup_exec_update_simp2[simp] : 
  assumes "e1 \<in> defined loc"
  shows "lookup_exec_update s (Left\<triangleleft>loc) (Node l e1 e2) senv 
       = {E (Node l x e2) | x. E x \<in> lookup_exec_update s loc e1 senv} \<union> (lookup_exec_update s loc e1 senv \<inter> {Err, Div})" 
  using assms by (force simp add: lookup_exec_update_def update_inter_err_div)
lemma lookup_exec_update_simp3[simp] : 
  assumes "e2 \<in> defined loc"
  shows "lookup_exec_update s (Right\<triangleleft>loc) (Node l e1 e2) senv 
       = {E (Node l e1 x) | x. E x \<in> lookup_exec_update s loc e2 senv} \<union> (lookup_exec_update s loc e2 senv \<inter> {Err, Div})" 
  using assms by (force simp add: lookup_exec_update_def update_inter_err_div)

text
 \<open> If @{text "l"} is defined in an expression, updating that expression with 
   @{text "lookup_exec_update"} will maintain the definedness of @{text "l"}. \<close>
theorem lookup_exec_update_defined:
  assumes "e \<in> defined l"
  shows "\<forall> x. E x \<in> lookup_exec_update s l e senv \<longrightarrow> x \<in> defined l"
  using assms proof (induction l arbitrary: e)
  case empty
  then show ?case 
    by auto
next
  case (Lcons pos l)
  then show ?case 
    apply clarsimp
    apply (case_tac e) by (case_tac pos, fastforce+)+
qed

lemma lookup_exec_update_nonempty:
  assumes "x \<in> defined loc"
  shows   "\<exists>r. r \<in> lookup_exec_update s loc x senv" 
  using assms proof (induct loc arbitrary: x)
  case empty
  then show ?case using Rep_powerdomain[simplified] by auto
next
  case (Lcons pos loc)
  then show ?case
    apply (case_tac pos)
     apply simp
     apply (elim disjE conjE exE)
     apply clarsimp
     apply (rename_tac l e1 e2)
     apply (drule_tac x = e1 in meta_spec, drule meta_mp, simp)
     apply clarsimp
     apply (rename_tac r)
     apply (case_tac r)
       apply blast
      apply auto[1]
     apply blast
    apply simp
    apply (elim disjE conjE exE)
    apply (rename_tac l e1 e2)
    apply clarsimp
    apply (drule_tac x = e2 in meta_spec, drule meta_mp, simp)
    apply clarsimp
    apply (rename_tac r)
    apply (case_tac r)
      apply blast
     apply auto[1]
    by blast
qed

subsection \<open>Order independence lemmas\<close>
text \<open> A collection of lemmas about defined and @{text "lookup_exec_update"} that are useful for 
   reordering  executions, in e.g. the soundness proofs of all \<close>
lemma defined_left_right : "x \<in> defined (loc \<triangleright> Left) \<Longrightarrow> x \<in> defined (loc \<triangleright> Right)"
proof (induct loc arbitrary: x)
  case empty
  then show ?case by simp
next
  case (Lcons pos loc)
  then show ?case by (case_tac pos; auto)
qed

lemma defined_right_left : "x \<in> defined (loc \<triangleright> Right) \<Longrightarrow> x \<in> defined (loc \<triangleright> Left)"
proof (induct loc arbitrary: x)
  case empty
  then show ?case by simp
next
  case (Lcons pos loc)
  then show ?case by (case_tac pos; auto)
qed

lemma defined_right_after_left: 
  assumes "E x2 \<in> lookup_exec_update s (loc\<triangleright>Left) x1 senv"
  shows   "x1 \<in> defined (loc \<triangleright> Right) \<Longrightarrow> x2 \<in> defined (loc\<triangleright>Right)"
  using assms 
  apply -
  apply (drule defined_right_left)
  apply (frule lookup_exec_update_defined[rule_format], simp)
  by (rule defined_left_right, simp)

lemma defined_left_after_right:
  assumes "E x2 \<in> lookup_exec_update s (loc\<triangleright>Right) x1 senv"
  shows   "x1 \<in> defined (loc \<triangleright> Left) \<Longrightarrow> x2 \<in> defined (loc\<triangleright>Left)"
  using assms 
  apply - 
  apply (drule defined_left_right)
  apply (frule lookup_exec_update_defined[rule_format], simp)
  by (rule defined_right_left, simp)

lemma lookup_exec_update_left_right_swap : 
  assumes "x1 \<in> defined (loc \<triangleright> Left)"
    and     "x1 \<in> defined (loc \<triangleright> Right)"
  shows   "(\<exists>i. E i \<in> lookup_exec_update s1 (loc \<triangleright> Left) x1 senv \<and> E x2 \<in> lookup_exec_update s2 (loc \<triangleright> Right) i senv)
       \<longleftrightarrow> (\<exists>i. E i \<in> lookup_exec_update s2 (loc \<triangleright> Right) x1 senv \<and> E x2 \<in> lookup_exec_update s1 (loc \<triangleright> Left) i senv)"
  using assms proof (induct loc arbitrary: x1 x2)
  case empty
  then show ?case by (case_tac x1; fastforce)
next
  case (Lcons pos loc)
  then show ?case
    apply simp
    apply (case_tac pos)
     apply simp
     apply (elim exE conjE disjE)
     apply clarsimp
     apply (rename_tac l e1 e2)
     apply (rule iffI)
      apply clarsimp
      apply (frule defined_right_after_left, simp)
      apply clarsimp
      apply (rename_tac x xa)
      apply (drule_tac x = e1 in meta_spec)
      apply (drule_tac x = xa in meta_spec)
      apply (drule meta_mp, simp)
      apply (drule meta_mp, simp)
      apply (drule iffD1)
       apply auto[1]
      apply clarsimp
      apply (rename_tac i)
      apply (rule_tac x = "Node l i e2" in exI)
      apply (rule)
       apply clarsimp
      apply (frule defined_left_after_right, simp, simp)
     apply clarsimp
     apply (frule defined_left_after_right, simp)
     apply clarsimp
     apply (rename_tac x xa)
     apply (drule_tac x = e1 in meta_spec)
     apply (drule_tac x = xa in meta_spec)
     apply (drule meta_mp, simp)
     apply (drule meta_mp, simp)
     apply (drule iffD2)
      apply auto[1]
     apply clarsimp
     apply (rename_tac i)
     apply (rule_tac x = "Node l i e2" in exI)
     apply (rule)
      apply clarsimp
     apply (frule defined_right_after_left, simp, simp)
    apply simp
    apply (elim exE conjE disjE)
    apply clarsimp
    apply (rename_tac l e1 e2)
    apply (rule iffI)
     apply clarsimp
     apply (frule defined_right_after_left, simp)
     apply clarsimp
     apply (rename_tac x xa)
     apply (drule_tac x = e2 in meta_spec)
     apply (drule_tac x = xa in meta_spec)
     apply (drule meta_mp, simp)
     apply (drule meta_mp, simp)
     apply (drule iffD1)
      apply auto[1]
     apply clarsimp
     apply (rename_tac i)
     apply (rule_tac x = "Node l e1 i" in exI)
     apply (rule)
      apply clarsimp
     apply (frule defined_left_after_right, simp, simp)
    apply clarsimp
    apply (frule defined_left_after_right, simp)
    apply clarsimp
    apply (rename_tac x xa)
    apply (drule_tac x = e2 in meta_spec)
    apply (drule_tac x = xa in meta_spec)
    apply (drule meta_mp, simp)
    apply (drule meta_mp, simp)
    apply (drule iffD2)
     apply auto[1]
    apply clarsimp
    apply (rename_tac i)
    apply (rule_tac x = "Node l e1 i" in exI)
    apply (rule)
     apply clarsimp
    apply (frule defined_right_after_left, simp, simp)
    done
qed

lemma err_right_after_left: 
  assumes "E x2 \<in> lookup_exec_update s (loc\<triangleright>Left) x1 senv"
    and     "x1 \<in> defined (loc \<triangleright> Left)" 
  shows   "Err \<in> lookup_exec_update s (loc\<triangleright>Right) x1 senv \<longleftrightarrow> Err \<in> lookup_exec_update s (loc\<triangleright>Right) x2 senv"
  using assms proof (induct loc arbitrary: x1 x2)
  case empty
  then show ?case by (case_tac x1; clarsimp)
next
  case (Lcons pos loc)
  then show ?case 
    apply simp
    apply (frule lookup_exec_update_defined[rule_format], simp)
    apply (case_tac pos)
     apply clarsimp
    using defined_left_right apply auto[1]
    using defined_left_right by auto[1]
qed

lemma err_left_after_right: 
  assumes "E x2 \<in> lookup_exec_update s (loc\<triangleright>Right) x1 senv" 
    and     "x1 \<in> defined (loc \<triangleright> Right)" 
  shows   "Err \<in> lookup_exec_update s (loc\<triangleright>Left) x1 senv \<longleftrightarrow> Err \<in> lookup_exec_update s (loc\<triangleright>Left) x2 senv"
  using assms proof (induct loc arbitrary: x1 x2)
  case empty
  then show ?case by (case_tac x1; clarsimp)
next
  case (Lcons pos loc)
  then show ?case 
    apply simp
    apply (frule lookup_exec_update_defined[rule_format], simp)
    apply (case_tac pos)
     apply clarsimp
    using defined_right_left apply auto[1]
    using defined_right_left by auto[1]
qed

lemma div_right_after_left: 
  assumes "E x2 \<in> lookup_exec_update s (loc\<triangleright>Left) x1 senv"
    and     "x1 \<in> defined (loc \<triangleright> Left)"
  shows   "Div \<in> lookup_exec_update s (loc\<triangleright>Right) x1 senv \<longleftrightarrow> Div \<in> lookup_exec_update s (loc\<triangleright>Right) x2 senv"
  using assms proof (induct loc arbitrary: x1 x2)
  case empty
  then show ?case by (case_tac x1; clarsimp)
next
  case (Lcons pos loc)
  then show ?case 
    apply simp
    apply (frule lookup_exec_update_defined[rule_format], simp)
    apply (case_tac pos)
     apply clarsimp
    using defined_left_right apply auto[1]
    using defined_left_right by auto[1]
qed

lemma div_left_after_right: 
  assumes "E x2 \<in> lookup_exec_update s (loc\<triangleright>Right) x1 senv" 
    and     "x1 \<in> defined (loc \<triangleright> Right)" 
  shows   "Div \<in> lookup_exec_update s (loc\<triangleright>Left) x1 senv \<longleftrightarrow> Div \<in> lookup_exec_update s (loc\<triangleright>Left) x2 senv"
  using assms proof (induct loc arbitrary: x1 x2)
  case empty
  then show ?case by (case_tac x1; clarsimp)
next
  case (Lcons pos loc)
  then show ?case 
    apply simp
    apply (frule lookup_exec_update_defined[rule_format], simp)
    apply (case_tac pos)
     apply clarsimp
    using defined_right_left apply auto[1]
    using defined_right_left by auto[1]
qed

subsection \<open>@{text "wp_sound_set"} and @{text "wp_err_sound_set"}\<close> 

text 
 \<open> These definitions are an aid to help us to formulate our inductive hypotheses.
   They are the semantic meaning of wp. \<close>
definition wp_sound_set :: "strategy \<Rightarrow> location \<Rightarrow> exp set \<Rightarrow> env \<Rightarrow> exp set"
  where "wp_sound_set s loc P senv = 
          {e | e. e \<in> defined loc \<and> lookup_exec_update s loc e senv \<subseteq> E ` P}"

definition wp_err_sound_set :: "strategy \<Rightarrow> location \<Rightarrow> exp set \<Rightarrow> env \<Rightarrow> exp set"
  where "wp_err_sound_set s loc P senv = 
          {e | e. e \<in> defined loc \<and>  lookup_exec_update s loc e senv \<subseteq> E ` P \<union> {Err}}"

subsection \<open>Sequential Composition Lemmas\<close>
  (* Helper to avoid having to do lots of SetToPd (PdToSet ..) reasoning *)
lemma PdToSet_seq : "PdToSet ((s1 ;;s s2) e)
                   =  (\<Union>{PdToSet (s2 x) | x. E x \<in> PdToSet (s1 e)}
                            \<union> {x | x. x \<in> PdToSet (s1 e) \<inter> {Div, Err}})"
  apply (simp add: seq_s_def)
  apply (subst Abs_powerdomain_inverse; simp)
  apply clarsimp
  apply (case_tac "\<exists>x. x \<in> PdToSet (s1 e)")
   apply clarsimp
   apply (case_tac x, simp)
     apply auto[1]
    apply simp
    apply (rule, rule, rule, rule, simp, simp)
    apply (rule Rep_powerdomain[simplified])
   apply auto[1]
  apply clarsimp
  using Rep_powerdomain by blast

(* lookup_exec_update of sequential composition is sequential composition of lookup_exec_update *)
lemma lookup_exec_update_seq: 
  assumes "e \<in> defined loc"
  shows "lookup_exec_update (s1;; s2) loc e senv
       = (\<Union> {lookup_exec_update s2 loc x senv | x. E x \<in> lookup_exec_update s1 loc e senv} 
           \<union> {x | x. x \<in> lookup_exec_update s1 loc e senv \<inter> {Div, Err}})"
  using assms proof (induction loc arbitrary: e)
  case empty
  then show ?case unfolding lookup_exec_update_def
    by (simp add: PdToSet_seq)
next
  case (Lcons pos loc)
  then show ?case using lookup_exec_update_defined
    apply simp
    apply (case_tac pos; simp)
     apply (elim exE disjE conjE)
     apply fastforce (* more like slowforce *)
    by fastforce
qed

(* wp_sound_set rule for sequential_composition  (mirrors the wp rule) *)
lemma seq_wp_sound_set: "wp_sound_set (s1 ;; s2) loc P senv = wp_sound_set s1 loc (wp_sound_set s2 loc P senv) senv"
  apply (simp add: wp_sound_set_def)
  apply (rule subset_antisym)
   apply clarsimp
   apply (rename_tac xa)
   apply (frule_tac ?s1.0 = s1 and ?s2.0 = s2 in lookup_exec_update_seq, simp)
   apply (case_tac xa)
     apply blast
    apply clarsimp
    apply (rule imageI)
    apply clarsimp
    apply (rule conjI)
     apply (frule_tac s = s1 in lookup_exec_update_defined)
     apply auto[1]
    apply blast
   apply blast
  apply clarsimp
  apply (frule_tac ?s1.0 = s1 and ?s2.0 = s2 in lookup_exec_update_seq, simp)
  by blast

(* wp_err_sound_set rule for sequential_composition  (mirrors the wp_err rule) *)
lemma seq_wp_err_sound_set: "wp_err_sound_set (s1 ;; s2) loc P senv = wp_err_sound_set s1 loc (wp_err_sound_set s2 loc P senv) senv"
  apply (simp add: wp_err_sound_set_def)
  apply (rule subset_antisym)
   apply clarsimp
   apply (rename_tac xa)
   apply (frule_tac ?s1.0 = s1 and ?s2.0 = s2 and senv = senv in lookup_exec_update_seq, simp)
   apply (case_tac xa)
     apply blast
    apply clarsimp
    apply (erule notE)
    apply (rule imageI)
    apply clarsimp
    apply (rule conjI)
     apply (frule_tac s = s1 in lookup_exec_update_defined)
     apply auto[1]
    apply blast
   apply blast
  apply clarsimp
  apply (frule_tac ?s1.0 = s1 and ?s2.0 = s2 and senv=senv in lookup_exec_update_seq, simp)
  by blast

subsection \<open>Left Choice Lemmas\<close>
(* Helper for PdToSet of left choice *)
lemma PdToSet_lc : "PdToSet ((s <+s t) e) = (PdToSet (s e) - {Err})  \<union> {x | x. x \<in> PdToSet (t e) \<and> Err \<in> PdToSet (s e)}"
  unfolding lchoice_s_def
  apply (subst Abs_powerdomain_inverse[simplified])
   apply clarsimp
   apply (rule)
  using Rep_powerdomain[simplified] apply blast
   apply (simp add: \<open>\<And>x. PdToSet x \<noteq> {}\<close> subset_singleton_iff)
  by blast

(* lookup_exec_update of left choice is the left choice of lookup_exec_update *)
lemma lookup_exec_update_lc: 
  assumes "e \<in> defined loc" 
  shows "lookup_exec_update (s1 <+ s2) loc e senv = (lookup_exec_update s1 loc e senv - {Err}) 
                                                    \<union> {x | x. x \<in> lookup_exec_update s2 loc e senv \<and> Err \<in> lookup_exec_update s1 loc e senv}"
  using assms proof (induction loc arbitrary: e)
  case empty
  then show ?case by (simp add: PdToSet_lc)
next
  case (Lcons pos loc)
  then show ?case 
    apply clarsimp
    apply (case_tac pos)
    by auto
qed

(* wp_sound_set rule for left choice (simplified wp rule) *)
lemma lc_wp_sound_set: "wp_sound_set (s1 <+ s2) loc P senv = wp_sound_set s1 loc P senv \<union> (wp_err_sound_set s1 loc P senv \<inter> wp_sound_set s2 loc P senv)"
  apply (simp add: wp_sound_set_def wp_err_sound_set_def)
  apply (rule subset_antisym)
   apply clarsimp
   apply (frule_tac ?s1.0 = s1 and ?s2.0 = s2 and senv = senv in lookup_exec_update_lc, simp)
   apply blast
  apply clarsimp
  apply (rule conjI)
   apply (clarsimp)
   apply (frule_tac ?s1.0 = s1 and ?s2.0 = s2 and senv = senv in lookup_exec_update_lc, simp)
   apply blast
  apply clarsimp
  apply (frule_tac ?s1.0 = s1 and ?s2.0 = s2 and senv = senv in lookup_exec_update_lc, simp)
  by blast

(* wp_err_sound_set rule for left choice (simplified wp_err rule) *)
lemma lc_wp_err_sound_set: "wp_err_sound_set (s1 <+ s2) loc P senv = wp_sound_set s1 loc P senv \<union> (wp_err_sound_set s1 loc P senv \<inter> wp_err_sound_set s2 loc P senv)"
  apply (simp add: wp_sound_set_def wp_err_sound_set_def)
  apply (rule subset_antisym)
   apply clarsimp
   apply (frule_tac ?s1.0 = s1 and ?s2.0 = s2 and senv = senv in lookup_exec_update_lc, simp)
   apply blast
  apply clarsimp
  apply (rule conjI)
   apply (clarsimp)
   apply (frule_tac ?s1.0 = s1 and ?s2.0 = s2 and senv = senv in lookup_exec_update_lc, simp)
   apply blast
  apply clarsimp
  apply (frule_tac ?s1.0 = s1 and ?s2.0 = s2 and senv = senv in lookup_exec_update_lc, simp)
  by blast

subsection \<open>Choice Lemmas\<close>
  (* Helper for PdToSet of choice *)
lemma PdToSet_choice : "PdToSet ((s1 ><s s2) e) = {E x | x. E x \<in> PdToSet (s1 e)}
                                  \<union> {d. d = Div \<and> Div \<in> PdToSet (s1 e)}
                                  \<union> {E y | y. E y \<in> PdToSet (s2 e)}
                                  \<union> {d. d = Div \<and> Div \<in> PdToSet (s2 e)}
                                  \<union> {err. err = Err \<and> Err \<in> PdToSet (s1 e) \<inter> PdToSet (s2 e)}"
  unfolding choice_s_def
  apply (subst Abs_powerdomain_inverse[simplified])
   apply clarsimp
   apply (metis (mono_tags, lifting) Rep_powerdomain ex_in_conv exp_err_div.exhaust mem_Collect_eq)
  by blast

(* lookup_exec_update of choice is the choice of lookup_exec_update, this is the simplified choice semantics *)
lemma lookup_exec_update_choice: 
  assumes "e \<in> defined loc" 
  shows "lookup_exec_update (s1 >< s2) loc e senv = {E x | x. E x \<in> lookup_exec_update s1 loc e senv}
                                  \<union> {d. d = Div \<and> Div \<in> lookup_exec_update s1 loc e senv}
                                  \<union> {E y | y. E y \<in> lookup_exec_update s2 loc e senv}
                                  \<union> {d. d = Div \<and> Div \<in> lookup_exec_update s2 loc e senv}
                                  \<union> {err. err = Err \<and> Err \<in> lookup_exec_update s1 loc e senv \<inter> lookup_exec_update s2 loc e senv}"
  using assms proof (induction loc arbitrary: e)
  case empty
  then show ?case by (simp add: PdToSet_choice)
next
  case (Lcons pos loc)
  then show ?case (* Rather slow*)
    apply clarsimp
    apply (case_tac pos)
     apply simp
     apply (elim exE disjE conjE)
     apply auto[1]
    by auto[1]
qed

(* wp_sound_set rule for choice (simplified wp rule) *)
lemma choice_wp_sound_set: "wp_sound_set (s1 >< s2) loc P senv = (wp_sound_set s1 loc P senv \<inter> wp_err_sound_set s2 loc P senv) \<union> (wp_err_sound_set s1 loc P senv \<inter> wp_sound_set s2 loc P senv)"
  apply (simp add: wp_sound_set_def wp_err_sound_set_def)
  apply (rule subset_antisym)
   apply clarsimp
   apply (rule conjI)
    apply clarsimp
    apply (frule_tac ?s1.0 = s1 and ?s2.0 = s2 and senv = senv in lookup_exec_update_choice, simp)
    apply clarsimp
    apply (erule impE)
     apply clarsimp
     apply (rename_tac xb)
     apply (case_tac "Err \<in> lookup_exec_update s1 loc x senv")
      apply (case_tac xb)
        apply blast
       apply blast
      apply blast
     apply (case_tac "Div \<in> lookup_exec_update s1 loc x senv")
      apply blast
     apply clarsimp
     apply (case_tac xb)
       apply blast
      apply blast
     apply blast
    apply clarsimp
    apply (rename_tac xa xb)
    apply (case_tac "Err \<in> lookup_exec_update s2 loc x senv")
     apply (case_tac xb)
       apply clarsimp
       apply (case_tac xa)
         apply auto[1]
        apply blast
       apply blast
      apply auto[1]
     apply simp
    apply clarsimp
    apply (case_tac "Div \<in> lookup_exec_update s2 loc x senv")
     apply auto[1]
    apply (case_tac xb)
      apply blast
     apply auto[1]
    apply blast
   apply clarsimp
  apply (rename_tac xa)
   apply (frule_tac ?s1.0 = s1 and ?s2.0 = s2 and senv = senv in lookup_exec_update_choice, simp)
   apply clarsimp
   apply (erule impE)
    apply clarsimp
    apply (rename_tac xb)
    apply (case_tac "Err \<in> lookup_exec_update s1 loc x senv")
     apply (case_tac xb)
       apply blast
      apply blast
     apply simp
    apply (case_tac "Div \<in> lookup_exec_update s1 loc x senv")
     apply blast
    apply (case_tac xb)
      apply blast
     apply blast
    apply blast
   apply clarsimp
   apply (rename_tac xb)
   apply (case_tac "Err \<in> lookup_exec_update s2 loc x senv")
    apply (case_tac xb)
      apply clarsimp
      apply (case_tac xa)
        apply blast
       apply fast
      apply simp
     apply auto[1]
    apply simp
   apply (case_tac "Div \<in> lookup_exec_update s2 loc x senv")
    apply auto[1]
   apply (case_tac xb)
     apply blast
    apply auto[1]
   apply blast
  apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (frule_tac ?s1.0 = s1 and ?s2.0 = s2 and senv = senv in lookup_exec_update_choice, simp)
   apply blast
  apply clarsimp
  apply (frule_tac ?s1.0 = s1 and ?s2.0 = s2 and senv = senv in lookup_exec_update_choice, simp)
  by blast

(* wp_err_sound_set rule for choice (simplified wp rule) *)
lemma choice_wp_err_sound_set: "wp_err_sound_set (s1 >< s2) loc P senv = wp_err_sound_set s1 loc P senv \<inter> wp_err_sound_set s2 loc P senv"
  apply (simp add: wp_sound_set_def wp_err_sound_set_def)
  apply (rule subset_antisym)
   apply clarsimp
   apply (rule conjI)
    apply clarsimp
    apply (rename_tac xa)
    apply (frule_tac ?s1.0 = s1 and ?s2.0 = s2 and senv = senv in lookup_exec_update_choice, simp)
    apply clarsimp
    apply (case_tac "Err \<in> lookup_exec_update s1 loc x senv")
     apply (case_tac xa)
       apply blast
      apply blast
     apply blast
    apply (case_tac xa)
      apply blast
     apply blast
    apply blast
   apply clarsimp
   apply (rename_tac xa)
   apply (frule_tac ?s1.0 = s1 and ?s2.0 = s2 and senv = senv in lookup_exec_update_choice, simp)
   apply clarsimp
   apply (case_tac "Err \<in> lookup_exec_update s2 loc x senv")
    apply (case_tac xa)
      apply blast
     apply fast
    apply simp
   apply (case_tac xa)
     apply blast
    apply fast
   apply simp
  apply clarsimp
  apply (frule_tac ?s1.0 = s1 and ?s2.0 = s2 and senv = senv in lookup_exec_update_choice, simp)
  by blast

subsection \<open>One Lemmas\<close>
lemma PdToSet_one: 
  "PdToSet ((one_s s) e) = {E (Node l x e2) | l x e1 e2. e = Node l e1 e2 \<and> E x \<in> PdToSet (s e1)}
                   \<union> {d | l e1 e2 d. e = Node l e1 e2 \<and> d = Div \<and> Div \<in> PdToSet (s e1)}
                   \<union> {E (Node l e1 x) | l x e1 e2. e = Node l e1 e2 \<and> E x \<in> PdToSet (s e2)}
                   \<union> {d | l e1 e2 d. e = Node l e1 e2 \<and> d = Div \<and> Div \<in> PdToSet (s e2)}
                   \<union> {err | e1 e2 l err. err = Err \<and> (e = Leaf l \<or> (e = Node l e1 e2 \<and> Err \<in> PdToSet (s e1) \<inter> PdToSet (s e2)))}"
  unfolding one_s_def
  apply (subst Abs_powerdomain_inverse; simp)
  apply (case_tac e)
   apply simp
  apply simp
  apply (subgoal_tac "\<exists>r1. r1 \<in> PdToSet (s x22)")
   apply (erule exE)
   apply (case_tac r1)
     apply (subgoal_tac "\<exists>r2. r2 \<in> PdToSet (s x23)")
      apply (erule exE)
      apply (case_tac r2)
        apply blast
       apply blast
      apply blast
  using Rep_powerdomain apply fastforce
    apply blast
   apply blast
  using Rep_powerdomain by fastforce

lemma lookup_exec_update_one:
  assumes "e \<in> defined loc" 
  shows  "lookup_exec_update (one s) loc e senv 
                                  = {E x | x. e \<in> defined (loc \<triangleright> Left) \<and> E x \<in> lookup_exec_update s (loc \<triangleright> Left) e senv}
                                  \<union> {d. d = Div \<and> e \<in> defined (loc \<triangleright> Left) \<and> Div \<in> lookup_exec_update s (loc \<triangleright> Left) e senv}
                                  \<union> {E y | y. e \<in> defined (loc \<triangleright> Right) \<and>  E y \<in> lookup_exec_update s (loc \<triangleright> Right) e senv}
                                  \<union> {d. d = Div \<and> e \<in> defined (loc \<triangleright> Right) \<and> Div \<in> lookup_exec_update s (loc \<triangleright> Right) e senv}
                                  \<union> {err. err = Err \<and> (e \<in> defined (loc \<triangleright> Left) 
                                                  \<longrightarrow>  e \<in> defined (loc \<triangleright> Right) 
                                                  \<longrightarrow> Err \<in> lookup_exec_update s (loc \<triangleright> Left) e senv \<inter> lookup_exec_update s (loc \<triangleright> Right) e senv)}"
  using assms proof (induct loc arbitrary: e)
  case empty
  then show ?case 
    apply (simp add: PdToSet_one)
    apply (case_tac e)
     apply auto[1]
    by auto
next
  case (Lcons pos loc)
  then show ?case 
    apply (case_tac e)
     apply clarsimp
     apply (case_tac pos)
      apply auto[1]
     apply auto[1]
    apply clarsimp
    apply (case_tac pos)
     apply clarsimp
     apply auto[1]
    apply clarsimp
    by auto[1]
qed

(* wp_sound_set rule for one (simplified wp rule) *)
lemma one_wp_sound_set: "wp_sound_set (one s) loc P senv 
                      = (wp_err_sound_set s (loc \<triangleright> Left) P senv \<inter> wp_sound_set s (loc \<triangleright> Right) P senv)
                      \<union> (wp_sound_set s (loc \<triangleright> Left) P senv \<inter> wp_err_sound_set s (loc \<triangleright> Right) P senv)"
  apply (simp add: wp_sound_set_def wp_err_sound_set_def)
  apply (rule subset_antisym)
   apply (rule subsetI)
   apply clarsimp
   apply (rename_tac x)
   apply (simp add: lookup_exec_update_one)
   apply (intro conjI)
      apply auto[1]
     apply clarsimp
     apply (rename_tac xa)
     apply (case_tac xa)
       apply blast
      apply blast
     apply auto[1]
    apply auto[1]
   apply (case_tac "x \<notin> defined (loc\<triangleright>Right)")
    apply auto[1]
   apply (case_tac "x \<notin> defined (loc\<triangleright>Left)")
    apply auto[1]
   apply simp
   apply (case_tac "Err \<in> lookup_exec_update s (loc\<triangleright>Left) x senv")
    apply (case_tac "Err \<in> lookup_exec_update s (loc\<triangleright>Right) x senv")
     apply auto[1]
    apply clarsimp
    apply (rename_tac xa)
    apply (case_tac xa)
      apply blast
     apply blast
    apply simp
   apply (case_tac "Err \<in> lookup_exec_update s (loc\<triangleright>Right) x senv")
    apply (drule mp)
     apply (rule subsetI)
     apply (rename_tac xa)
     apply (case_tac xa)
       apply simp
      apply auto[1]
     apply blast
    apply (rotate_tac 6, erule notE)
    apply (clarsimp)
    apply (rename_tac xa)
    apply (case_tac xa)
      apply blast
     apply blast
    apply simp
   apply (clarsimp)
   apply (rename_tac xa)
   apply (case_tac xa)
     apply blast
    apply blast
   apply simp
  apply clarsimp
  apply (rule)
   apply (clarsimp)
   apply (frule defined_append)
   apply (simp add: lookup_exec_update_one)
   apply blast
  apply (clarsimp)
  apply (frule defined_append)
  apply (simp add: lookup_exec_update_one)
  by blast

(* wp_err_sound_set rule for one (simplified wp rule) *)
lemma one_wp_err_sound_set: "wp_err_sound_set (one s) loc P senv
                                = {e | e x. e \<in> defined loc \<and> lookup loc e = Leaf x}
                                \<union> wp_err_sound_set s (loc \<triangleright> Left) P senv \<inter> wp_err_sound_set s (loc \<triangleright> Right) P senv"
  apply (simp add: wp_sound_set_def wp_err_sound_set_def)
  apply (rule subset_antisym)
   apply (rule subsetI)
   apply (clarsimp)
   apply (rename_tac x)
   apply (simp add: lookup_exec_update_one)
   apply (elim conjE)
   apply (case_tac "x \<in> defined (loc \<triangleright> Right) \<and> x \<in> defined (loc \<triangleright> Left)")
    apply clarsimp
    apply (drule mp)
     apply clarsimp
     apply (rename_tac xa)
     apply (case_tac xa)
       apply simp
      apply blast
     apply blast
    apply (erule notE)
    apply clarsimp
    apply (rename_tac xa)
    apply (case_tac xa)
      apply simp
     apply blast
    apply blast
   apply clarsimp
   apply (case_tac "x \<in> defined (loc\<triangleright>pos.Right)")
    apply simp
    apply (rule append_undefined_lookup_id, simp, simp)
   apply (rule append_undefined_lookup_id, simp, simp)
  apply clarsimp
  apply (rule conjI)
   apply (rule subsetI)
   apply (clarsimp simp add: lookup_exec_update_one)
   apply (frule_tac p = Left in lookup_id_append_undefined, simp)
   apply (frule_tac p = Right in lookup_id_append_undefined, simp)
   apply simp
  apply clarsimp
  apply (frule defined_append)
  apply (clarsimp simp add: lookup_exec_update_one)
  by blast

subsection \<open>All Lemmas\<close>
lemma PdToSet_all:
  "PdToSet ((all_s s) e) = {E (Node l x1 x2) | l x1 x2 e1 e2. e = Node l e1 e2 \<and> E x1 \<in> PdToSet (s e1) \<and> E x2 \<in> PdToSet (s e2)}
                   \<union> {E (Leaf l) | l. e = Leaf l }
                   \<union> {d | l e1 e2 d. (e = Node l e1 e2 \<and> d = Div \<and> Div \<in> PdToSet (s e1) \<union> PdToSet (s e2)) }
                   \<union> {err | e1 e2 l err. err = Err \<and> (e = Node l e1 e2 \<and> Err \<in> PdToSet (s e1) \<union> PdToSet (s e2))}"
  apply (simp add: all_s_def)
  apply (subst Abs_powerdomain_inverse)
   apply clarsimp
   apply (case_tac e)
    apply (rotate_tac 2)  
    apply blast
   apply clarsimp
  using Rep_powerdomain[simplified] 
   apply (metis equals0I exp_err_div.exhaust)
  using Rep_powerdomain[simplified] 
  by (metis equals0I exp_err_div.exhaust)

lemma lookup_exec_update_all:
  assumes "e \<in> defined loc" 
  shows  "lookup_exec_update (all s) loc e senv 
                                    = {E y | x y. e \<in> defined (loc \<triangleright> Left) \<and> x \<in> defined (loc \<triangleright> Right) \<and> E x \<in> lookup_exec_update s (loc \<triangleright> Left) e senv
                                            \<and> E y \<in> lookup_exec_update s (loc \<triangleright> Right) x senv}
                                      \<union> {E e | l. lookup loc e = Leaf l}
                                      \<union> {d. d = Div \<and> e \<in> defined (loc \<triangleright> Left) \<and> Div \<in> lookup_exec_update s (loc \<triangleright> Left) e senv}
                                      \<union> {d. d = Div \<and> e \<in> defined (loc \<triangleright> Right) \<and> Div \<in> lookup_exec_update s (loc \<triangleright> Right) e senv}
                                      \<union> {err. err = Err \<and> e \<in> defined (loc \<triangleright> Left) \<and> Err \<in> lookup_exec_update s (loc \<triangleright> Left) e senv}
                                      \<union> {err. err = Err \<and> e \<in> defined (loc \<triangleright> Right) \<and> Err \<in> lookup_exec_update s (loc \<triangleright> Right) e senv}"
  using assms proof (induct loc arbitrary: e)
  case empty
  then show ?case 
    apply (simp add: PdToSet_all)
    apply (rule subset_antisym)
     apply (rule subsetI)
     apply simp
      (* getting try to solve this requires us to break it down first *)
     apply (elim disjE conjE exE)
          apply clarsimp
          apply fastforce
         apply clarsimp
        apply force
       apply simp
      apply simp
     apply simp
    apply simp
    apply (case_tac e)
     apply simp
    apply simp
    by fastforce
next
  case (Lcons pos loc)
  then show ?case
    apply (case_tac pos)
     apply (case_tac e)
      apply simp
     apply clarsimp
     apply (rule set_eqI)
     apply clarsimp
     apply (rule iffI)
      apply (elim disjE conjE exE)
                   apply clarsimp
                   apply fastforce
                  apply clarsimp
                 apply blast
                apply blast
               apply blast
              apply blast
             apply auto[1]
            apply auto[1]
           apply simp
          apply simp
         apply simp
        apply simp
       apply blast
      apply simp
     apply (elim disjE conjE exE)
        apply simp
          apply auto[1]
         apply simp
        apply simp
       apply auto[1]
      apply simp
     apply auto[1]
    apply (rule set_eqI)
    apply clarsimp
    apply (rule iffI)
     apply (elim disjE conjE exE)
                  apply clarsimp
                  apply fastforce
                 apply force
                apply auto[1]
               apply blast
              apply blast
             apply blast
            apply blast
           apply simp
          apply auto[1]
         apply blast
        apply simp
       apply simp
      apply simp
     apply simp
    apply (elim disjE conjE exE)
         apply auto[1]
        apply simp
       apply simp
      apply simp
     apply simp
    by auto[1]
qed

(* wp_sound_set rule for all (simplified wp rule) *)
lemma all_wp_sound_set: "wp_sound_set (all s) loc P senv = (P \<inter> {e | e x. e \<in> defined loc \<and> lookup loc e = Leaf x})
                          \<union> wp_sound_set s (loc \<triangleright> Left) (wp_sound_set s (loc \<triangleright> Right) P senv) senv
                          \<union> wp_sound_set s (loc \<triangleright> Right) (wp_sound_set s (loc \<triangleright> Left) P senv) senv"
  apply (simp add: wp_sound_set_def)
  apply (rule subset_antisym)
   apply (rule subsetI)
  apply (rename_tac x)
   apply clarsimp
   apply (simp add: lookup_exec_update_all)
   apply clarsimp
   apply (rule conjI)
  using append_undefined_lookup_id apply (smt (verit, ccfv_threshold) Collect_mono_iff Setcompr_eq_image exp_err_div.inject)
   apply clarsimp
  apply (rename_tac xa)
   apply (case_tac xa)
     apply clarsimp
  using append_undefined_lookup_id apply (smt (verit, ccfv_threshold) Collect_mem_eq Collect_mono_iff exp_err_div.distinct(1) exp_err_div.inject image_iff)
    apply clarsimp
    apply (rule imageI)
    apply (case_tac "x \<notin> defined (loc\<triangleright>Right)")
     apply simp
     apply (rule conjI)
  using append_undefined_lookup_id apply force
  using append_undefined_lookup_id apply force
    apply simp
    apply (rule conjI)
     apply (meson defined_right_after_left)
    apply (case_tac "x \<notin> defined (loc\<triangleright>Left)")
     apply (meson defined_right_left)
    apply clarsimp
    apply (smt (verit, del_insts) defined_right_after_left div_right_after_left err_right_after_left exp_err_div.exhaust mem_Collect_eq subsetD)
  using append_undefined_lookup_id apply (smt (verit, del_insts) exp_err_div.inject exp_err_div.simps(7) imageE mem_Collect_eq subsetD)
  apply (rule subsetI)
  apply clarsimp
  apply (rename_tac x)
  apply (rule conjI)
  using defined_append apply blast
  apply (elim conjE disjE)
    apply (simp add: lookup_exec_update_all)
  using lookup_id_append_undefined apply blast
   apply clarsimp
   apply (rename_tac xa)
   apply (frule defined_append)
   apply (simp add: lookup_exec_update_all)
   apply (case_tac xa)
     apply clarsimp
     apply (frule_tac s = s and x = x and senv = senv in lookup_exec_update_nonempty)
     apply clarsimp
  using err_right_after_left apply blast
    apply clarsimp
    apply (frule_tac s = s and x = x and senv = senv in lookup_exec_update_nonempty)
    apply clarsimp
  using lookup_id_append_undefined apply auto[1]
   apply clarsimp
   apply (frule_tac s = s and x = x and senv = senv in lookup_exec_update_nonempty)
   apply clarsimp
  using div_right_after_left apply blast
  apply clarsimp
  apply (frule defined_append)
  apply (simp add: lookup_exec_update_all)
  apply (rename_tac xa)
  apply (case_tac xa)
    apply clarsimp
    apply (frule_tac s = s and x = x and senv = senv in lookup_exec_update_nonempty)
    apply clarsimp
  using err_left_after_right apply blast
   apply clarsimp
   apply (frule_tac s = s and x = x and senv = senv in lookup_exec_update_nonempty)
   apply clarsimp
  using lookup_exec_update_left_right_swap lookup_id_append_undefined apply fastforce
  apply clarsimp
  apply (frule_tac s = s and x = x and senv = senv in lookup_exec_update_nonempty)
  apply clarsimp
  using div_left_after_right by blast

(* wp_err_sound_set rule for all (simplified wp rule) *)
lemma all_wp_err_sound_set: "wp_err_sound_set (all s) loc P senv 
                      = (P \<inter> {e | e x. e \<in> defined loc \<and> lookup loc e = Leaf x})
                        \<union> (wp_err_sound_set s (loc \<triangleright> Left) (wp_err_sound_set s (loc \<triangleright> Right) P senv) senv
                        \<inter> wp_err_sound_set s (loc \<triangleright> Right) (wp_err_sound_set s (loc \<triangleright> Left) P senv) senv)"
  apply (simp add: wp_err_sound_set_def)
  apply (rule subset_antisym)
   apply (rule subsetI)
   apply (rename_tac x)
   apply simp
   apply (case_tac "x \<notin> defined (loc\<triangleright>pos.Left)")
    apply clarsimp
    apply (rule conjI)
     apply (simp add: lookup_exec_update_all)
  using append_undefined_lookup_id apply auto[1]
    apply (rule append_undefined_lookup_id, simp, simp)
   apply simp
   apply (rule disjI2)
   apply (erule conjE)
   apply (simp add: lookup_exec_update_all)
   apply (clarsimp)
   apply (intro conjI)
     apply (rule subsetI)
     apply (rename_tac xa)
     apply (frule defined_left_right)
     apply (case_tac xa)
       apply simp
      apply simp
      apply (rule imageI)
      apply clarsimp
      apply (rename_tac x1)
      apply (frule lookup_exec_update_defined[rule_format], simp)
      apply (rule conjI)
       apply (rule defined_left_right, simp)
      apply (rule subsetI)
      apply (rename_tac xb)
      apply (case_tac xb)
        apply simp
       apply (drule_tac c = xb in subsetD)
        apply simp
        apply (rule_tac x = x1 in exI)
        apply (rule conjI)
         apply (rule defined_left_right, simp)
        apply blast
       apply simp
      apply simp
      apply (frule div_right_after_left, simp)
      apply simp
     apply simp
     apply blast
    apply (rule defined_left_right,simp)
   apply (rule subsetI)
   apply (rename_tac xa)
   apply (case_tac xa)
     apply simp
    apply (rename_tac x1)
    apply simp
    apply (rule imageI)
    apply simp
    apply (rule)
     apply (rule defined_right_left, rule lookup_exec_update_defined[rule_format], rule defined_left_right, simp, simp)
    apply (rule subsetI)
    apply (rename_tac xb)
    apply (case_tac xb)
      apply simp
     apply (rename_tac x2)
     apply simp
     apply (frule lookup_exec_update_left_right_swap[THEN iffD2], rule defined_left_right, simp)
      apply (rule_tac x = "x1" in exI, rule conjI)
       apply simp
      apply simp
     apply (elim exE conjE)
     apply (drule_tac c = "E x2" in subsetD)
      apply simp
      apply (rename_tac x3)
      apply (rule_tac x = x3 in exI)
      apply (intro conjI)
        apply (rule defined_right_after_left, simp, rule defined_left_right, simp)
       apply simp
      apply simp
     apply simp
    apply clarsimp
    apply (frule div_left_after_right, rule defined_left_right, simp)
    apply simp
   apply clarsimp
   apply (frule defined_left_right)
   apply auto[1]
  apply clarsimp
  apply (intro conjI)
   apply (rule subsetI)
   apply clarsimp
   apply (rename_tac x xa xb)
   apply (case_tac xa, simp)
    apply (simp add: lookup_exec_update_all)
    apply clarsimp
    apply (frule_tac p = Left in lookup_id_append_undefined, simp, simp)
   apply (simp add: lookup_exec_update_all)
   apply clarsimp
   apply (frule_tac p = Right in lookup_id_append_undefined, simp, simp)
   apply (frule_tac p = Left in lookup_id_append_undefined, simp, simp)
  apply (rule subsetI)
  apply clarsimp
  apply (frule defined_append, simp)
  apply (simp add: lookup_exec_update_all)
  apply (intro conjI)
     apply (rule subsetI)
     apply clarsimp
       apply blast
  using lookup_id_append_undefined apply blast
     apply blast
    apply blast
   apply blast
  by blast

subsection \<open>Some Lemmas\<close>
lemma PdToSet_some: 
  "PdToSet ((some_s s) e) = {E (Node l x1 x2) | l x1 x2 e1 e2. e = Node l e1 e2 \<and> E x1 \<in> PdToSet (s e1) \<and> E x2 \<in> PdToSet (s e2)}
                    \<union> {E (Node l x e2) | l x e1 e2. e = Node l e1 e2 \<and> E x \<in> PdToSet (s e1) \<and> Err \<in> PdToSet (s e2)} 
                    \<union> {E (Node l e1 x) | l x e1 e2. e = Node l e1 e2 \<and> E x \<in> PdToSet (s e2) \<and> Err \<in> PdToSet (s e1)}
                    \<union> {d | l e1 e2 d. (e = Node l e1 e2 \<and> d = Div \<and> Div \<in> PdToSet (s e1) \<union> PdToSet (s e2))}
                    \<union> {err | e1 e2 l err. err = Err \<and> (e = Leaf l \<or> (e = Node l e1 e2 \<and> Err \<in> PdToSet (s e1) \<inter> PdToSet (s e2)))}"
  apply (simp add: some_s_def)
  apply (subst Abs_powerdomain_inverse)
   apply simp
   apply (case_tac e)
    apply blast
   apply simp
  using Rep_powerdomain[simplified] apply (metis equals0I exp_err_div.exhaust)
  by simp

lemma lookup_exec_update_some:
  assumes "e \<in> defined loc" 
  shows  "lookup_exec_update (some s) loc e senv 
                                  = {E x | x. e \<in> defined (loc \<triangleright> Left) \<inter> defined (loc \<triangleright> Right) 
                                            \<and> E x \<in> lookup_exec_update s (loc \<triangleright> Left) e senv \<and> Err \<in> lookup_exec_update s (loc \<triangleright> Right) e senv}
                                  \<union> {d. d = Div \<and> e \<in> defined (loc \<triangleright> Left) \<and> Div \<in> lookup_exec_update s (loc \<triangleright> Left) e senv}
                                  \<union> {E y | y. e \<in> defined (loc \<triangleright> Left) \<inter> defined (loc \<triangleright> Right) 
                                            \<and> E y \<in> lookup_exec_update s (loc \<triangleright> Right) e senv \<and> Err \<in> lookup_exec_update s (loc \<triangleright> Left) e senv}
                                  \<union> {d. d = Div \<and> e \<in> defined (loc \<triangleright> Right) \<and> Div \<in> lookup_exec_update s (loc \<triangleright> Right) e senv}
                                  \<union> {E z | x z. e \<in> defined (loc \<triangleright> Left) \<inter> defined (loc \<triangleright> Right) \<and> E x \<in> lookup_exec_update s (loc \<triangleright> Left) e senv
                                            \<and> E z \<in> lookup_exec_update s (loc \<triangleright> Right) x senv}
                                  \<union> {err. err = Err \<and> (e \<in> defined (loc \<triangleright> Left) 
                                                  \<longrightarrow>  e \<in> defined (loc \<triangleright> Right) 
                                                  \<longrightarrow> Err \<in> lookup_exec_update s (loc \<triangleright> Left) e senv \<inter> lookup_exec_update s (loc \<triangleright> Right) e senv)}"
  using assms proof (induct loc arbitrary: e)
  case empty
  then show ?case
    apply (simp add: PdToSet_some)
    apply (rule subset_antisym)
     apply (rule subsetI)
     apply simp
     apply (elim disjE conjE exE)
           apply auto[1]
          apply auto[1]
         apply auto[1]
        apply auto[1]
       apply simp
      apply auto[1]
     apply simp
    apply simp
    apply (case_tac e)
     apply auto[1]
    by fastforce
next
  case (Lcons pos loc)
  then show ?case
    apply (case_tac pos)
     apply (case_tac e)
      apply simp
     apply clarsimp
     apply (rename_tac x1 x2 x3)
     apply (rule set_eqI)
     apply clarsimp
     apply (rule iffI)
      apply (elim disjE conjE exE)
                    apply auto[1]
                   apply simp
                  apply simp
                  apply (rule disjI2)
                  apply (rule disjI2)
                  apply (rename_tac xb)
                  apply (rule_tac x="Node x1 xb x3" in exI)
                  apply (rule conjI)
                   apply blast
    using defined_right_after_left apply simp
                 apply simp
                apply blast
               apply blast
              apply blast
             apply blast
            apply simp
           apply blast
          apply simp
         apply blast
        apply auto[1]
       apply blast
      apply blast
     apply (elim disjE conjE exE)
          apply auto[1]
         apply auto[1]
        apply auto[1]
       apply simp
      apply clarsimp
    using defined_right_after_left apply auto[1]
     apply blast
    apply clarsimp
    apply (rule set_eqI)
    apply clarsimp
    apply (rule iffI)
     apply (elim disjE conjE exE)
                   apply simp
                  apply simp
    using defined_right_after_left apply auto[1]
                apply blast
               apply blast
              apply blast
             apply blast
            apply blast
           apply auto[1]
          apply blast
         apply simp
        apply blast
       apply simp
      apply blast
     apply blast
    apply (elim disjE conjE exE)
         apply auto[1]
        apply simp
       apply auto[1]
      apply simp
    using defined_right_after_left apply auto[1]
    by blast
qed

(* wp_sound_set rule for some (simplified wp rule) *)
lemma some_wp_sound_set: "wp_sound_set (some s) loc P senv 
                      = wp_sound_set s (loc \<triangleright> Left) (wp_sound_set s (loc \<triangleright> Right) P senv) senv
                           \<union> wp_sound_set s (loc \<triangleright> Right) (wp_sound_set s (loc \<triangleright> Left) P senv) senv 
                           \<union> (wp_sound_set s (loc \<triangleright> Left) P senv \<inter> wp_sound_set s (loc \<triangleright> Left) (wp_err_sound_set s (loc \<triangleright> Right) P senv) senv)
                           \<union> (wp_sound_set s (loc \<triangleright> Right) P senv \<inter> wp_sound_set s (loc \<triangleright> Right) (wp_err_sound_set s (loc \<triangleright> Left) P senv) senv)"
  apply (simp add: wp_sound_set_def wp_err_sound_set_def)
  apply (rule subset_antisym)
   apply (rule subsetI)
   apply (rename_tac x)
   apply (simp add: lookup_exec_update_some)
   apply simp
   apply (case_tac "x \<in> defined (loc\<triangleright>pos.Right)")
    apply (frule defined_right_left)
    apply simp
    apply (erule conjE)
    apply (simp add: lookup_exec_update_some)
    apply (elim conjE)
    apply (case_tac "Err \<in> lookup_exec_update s (loc\<triangleright>pos.Left) x senv")
     apply (case_tac "Err \<in> lookup_exec_update s (loc\<triangleright>pos.Right) x senv")
      apply simp
      apply blast
     apply simp
     apply (rule disjI2)
     apply (rule disjI2)
     apply (rule disjI2)
     apply (rule conjI)
      apply (rule subsetI)
      apply (rename_tac xa)
      apply (case_tac xa)
        apply blast
       apply auto[1]
      apply blast
     apply (rule subsetI)
     apply (rename_tac xa)
     apply (case_tac xa)
       apply blast
      apply clarsimp
      apply (rule imageI)
      apply simp
      apply (rule conjI)
       apply (rule defined_left_after_right)
        apply simp
       apply simp
      apply (rule subsetI)
      apply (rename_tac xa)
      apply (case_tac xa)
        apply blast
  using lookup_exec_update_left_right_swap apply fast
  using div_left_after_right apply simp
     apply auto[1]
    apply (case_tac "Err \<in> lookup_exec_update s (loc\<triangleright>pos.Right) x senv")
     apply (rule disjI2)
     apply (rule disjI2)
     apply (rule disjI1)
     apply (rule conjI)
      apply simp
      apply (rule subsetI)
      apply (rename_tac xa)
      apply(case_tac xa)
        apply blast
       apply blast
      apply blast
     apply simp
     apply (rule subsetI)
     apply (rename_tac xa)
     apply(case_tac xa)
       apply blast
      apply simp
      apply (rule imageI)
      apply clarsimp
      apply (rule conjI)
       apply (rule defined_right_after_left)
        apply simp
       apply blast
      apply (rule subsetI)
      apply (rename_tac xa)
      apply(case_tac xa)
        apply blast
       apply fast
  using div_right_after_left apply simp
     apply blast
    apply (rule disjI1)
    apply simp
    apply (rule subsetI)
    apply (rename_tac xa)
    apply(case_tac xa)
      apply blast
     apply clarsimp
     apply (rule imageI)
     apply simp
     apply (rule conjI)
      apply (rule defined_right_after_left)
       apply simp
      apply simp
     apply (rule subsetI)
     apply (rename_tac xa)
     apply(case_tac xa)
  using err_right_after_left apply simp
      apply blast
  using div_right_after_left apply simp
    apply blast
   apply simp
   apply (erule conjE)
   apply (simp add: lookup_exec_update_some)
   apply blast
  apply (rule subsetI)
  apply (rename_tac x)
  apply (simp add: lookup_exec_update_some)
  apply (subgoal_tac "x \<in> defined loc")
   apply simp
   apply (elim disjE)
      apply (simp add: lookup_exec_update_some)
      apply (intro conjI)
           apply clarsimp
           apply (rename_tac xa)
           apply (drule_tac c="E xa" in subsetD)
            apply blast
  using err_right_after_left  apply blast
          apply blast
         apply blast
        apply clarsimp
        apply (rotate_tac 1)
        apply (frule_tac s=s and senv=senv in lookup_exec_update_nonempty)
        apply(erule exE)
        apply (rename_tac xb)
        apply (case_tac xb)
          apply auto[1]
  using div_right_after_left apply blast
        apply blast
       apply clarsimp
       apply blast
      apply clarsimp
  using defined_left_right apply blast
     apply (simp add: lookup_exec_update_some)
     apply (intro conjI)
          apply clarsimp
  using err_right_after_left apply blast
         apply clarsimp
         apply (rotate_tac 1)
         apply (frule_tac s=s and senv=senv in lookup_exec_update_nonempty)
         apply(erule exE)
         apply (rename_tac xb)
         apply (case_tac xb)
           apply blast
  using div_left_after_right apply blast
         apply blast
        apply clarsimp
  using err_left_after_right apply auto[1]
       apply blast
      apply clarsimp
  using lookup_exec_update_left_right_swap apply blast
     apply clarsimp
  using defined_right_left apply blast
    apply (simp add: lookup_exec_update_some)
    apply (intro conjI)
         apply blast
        apply blast
       apply blast
      apply clarsimp
      apply (rotate_tac 4)
      apply (frule_tac s=s and senv=senv in lookup_exec_update_nonempty)
      apply (erule exE)
      apply (rename_tac xb)
      apply (case_tac xb)
        apply blast
  using div_right_after_left apply blast
      apply blast
     apply blast
    apply clarsimp
  using defined_left_right apply blast
   apply (simp add: lookup_exec_update_some)
   apply (intro conjI)
        apply blast
       apply clarsimp
       apply (rotate_tac 4)
       apply (frule_tac s=s and senv=senv in lookup_exec_update_nonempty)
       apply (erule exE)
       apply (rename_tac xb)
       apply (case_tac xb)
         apply blast
  using div_left_after_right apply blast
       apply blast
      apply blast
     apply blast
    apply clarsimp
  using lookup_exec_update_left_right_swap apply blast
   apply clarsimp
  using defined_right_left apply blast
  using defined_append by blast

(* wp_err_sound_set rule for some (simplified wp rule) *)
lemma some_wp_err_sound_set: "wp_err_sound_set (some s) loc P senv 
                      = {e | e x. e \<in> defined loc \<and> lookup loc e = Leaf x}
                        \<union> (wp_err_sound_set s (loc \<triangleright> Left) (wp_err_sound_set s (loc \<triangleright> Right) P senv) senv
                           \<inter> wp_err_sound_set s (loc \<triangleright> Right) (wp_err_sound_set s (loc \<triangleright> Left) P senv) senv
                           \<inter> (wp_err_sound_set s (loc \<triangleright> Left) P senv \<union> wp_err_sound_set s (loc \<triangleright> Left) (wp_sound_set s (loc \<triangleright> Right) P senv) senv)
                           \<inter> (wp_err_sound_set s (loc \<triangleright> Right) P senv \<union> wp_err_sound_set s (loc \<triangleright> Right) (wp_sound_set s (loc \<triangleright> Left) P senv) senv))"
  apply (simp add: wp_sound_set_def wp_err_sound_set_def)
  apply (rule subset_antisym)
   apply (rule subsetI)
   apply (rename_tac x)
   apply simp
   apply (erule conjE)
   apply (simp add: lookup_exec_update_some)
   apply simp
   apply (elim conjE exE)
   apply (case_tac "x \<in> defined (loc\<triangleright>pos.Left)")
    apply (frule defined_left_right)
    apply simp
    apply (rule disjI2)
    apply (case_tac "Err \<in> lookup_exec_update s (loc\<triangleright>pos.Left) x senv")
     apply (case_tac "Err \<in> lookup_exec_update s (loc\<triangleright>pos.Right) x senv")
      apply simp
      apply (intro conjI)
         apply (rule subsetI)
         apply (rename_tac xa)
         apply (case_tac xa)
           apply blast
          apply clarsimp
          apply (rule imageI)
          apply simp
          apply (rule conjI)
  using defined_right_after_left apply simp
          apply (rule subsetI)
          apply (rename_tac xa)
          apply (case_tac xa)
            apply blast
           apply fast
  using div_right_after_left apply simp
         apply blast
        apply (rule subsetI)
        apply (rename_tac xa)
        apply (case_tac xa)
          apply blast
         apply clarsimp
         apply (rule imageI)
         apply simp
         apply (rule conjI)
  using defined_left_after_right apply simp
         apply (rule subsetI)
         apply (rename_tac xa)
         apply (case_tac xa)
           apply blast
  using lookup_exec_update_left_right_swap apply fast
  using div_left_after_right apply simp
        apply auto[1]
       apply (rule disjI1)
       apply (rule subsetI)
       apply (rename_tac xa)
       apply (case_tac xa)
         apply blast
        apply blast
       apply blast
      apply (rule disjI1)
      apply (rule subsetI)
      apply (rename_tac xa)
      apply (case_tac xa)
        apply blast
       apply blast
      apply blast
     apply simp
     apply (intro conjI)
        apply (rule subsetI)
        apply (rename_tac xa)
        apply (case_tac xa)
          apply blast
         apply clarsimp
         apply (rule imageI)
         apply simp
         apply (rule conjI)
  using defined_right_after_left apply auto[1]
         apply (rule subsetI)
         apply (rename_tac xa)
         apply (case_tac xa)
           apply blast
          apply fast
  using div_right_after_left apply simp
        apply blast
       apply (rule subsetI)
       apply (rename_tac xa)
       apply (case_tac xa)
         apply blast
        apply clarsimp
        apply (rule imageI)
        apply simp
        apply (rule conjI)
  using defined_left_after_right apply simp
        apply (rule subsetI)
        apply (rename_tac xa)
        apply (case_tac xa)
          apply blast
  using lookup_exec_update_left_right_swap apply fast
  using div_left_after_right apply simp
       apply auto[1]
      apply (rule disjI2)
      apply (rule subsetI)
      apply (rename_tac xa)
      apply (case_tac xa)
        apply blast
       apply clarsimp
       apply (rule imageI)
       apply simp
       apply (rule conjI)
  using defined_right_after_left apply auto[1]
       apply (rule subsetI)
       apply (rename_tac xa)
       apply (case_tac xa)
  using err_right_after_left apply simp
        apply fast
  using div_right_after_left apply auto[1]
      apply blast
     apply (rule disjI1)
     apply (rule subsetI)
     apply (rename_tac xa)
     apply (case_tac xa)
       apply blast
      apply auto[1]
     apply blast
    apply (case_tac "Err \<in> lookup_exec_update s (loc\<triangleright>pos.Right) x senv")
     apply simp
     apply (intro conjI)
        apply (rule subsetI)
        apply (rename_tac xa)
        apply (case_tac xa)
          apply blast
         apply clarsimp
         apply (rule imageI)
         apply simp
         apply (rule conjI)
  using defined_right_after_left apply simp
         apply (rule subsetI)
         apply (rename_tac xa)
         apply (case_tac xa)
           apply blast
          apply fast
  using div_right_after_left apply auto[1]
        apply blast
       apply (rule subsetI)
       apply (rename_tac xa)
       apply (case_tac xa)
         apply blast
        apply clarsimp
        apply (rule imageI)
        apply simp
        apply (rule conjI)
  using defined_left_after_right apply auto[1]
        apply (rule subsetI)
        apply (rename_tac xa)
        apply (case_tac xa)
          apply blast
  using lookup_exec_update_left_right_swap apply fast
  using div_left_after_right apply simp
       apply auto[1]
      apply (rule disjI1)
      apply (rule subsetI)
      apply (rename_tac xa)
      apply (case_tac xa)
        apply blast
       apply blast
      apply blast
     apply (rule disjI2)
     apply (rule subsetI)
     apply (rename_tac xa)
     apply (case_tac xa)
       apply blast
      apply clarsimp
      apply (rule imageI)
      apply simp
      apply (rule conjI)
  using defined_left_after_right apply auto[1]
      apply (rule subsetI)
      apply (rename_tac xa)
      apply (case_tac xa)
  using err_left_after_right apply simp
  using lookup_exec_update_left_right_swap apply fast
  using div_left_after_right apply simp
     apply auto[1]
    apply simp
    apply (intro conjI)
       apply (rule subsetI)
       apply (rename_tac xa)
       apply (case_tac xa)
         apply blast
        apply clarsimp
        apply (rule imageI)
        apply simp
        apply (rule conjI)
  using defined_right_after_left apply auto[1]
        apply (rule subsetI)
        apply (rename_tac xa)
        apply (case_tac xa)
          apply blast
         apply fast
  using div_right_after_left apply simp
       apply blast
      apply (rule subsetI)
      apply (rename_tac xa)
      apply (case_tac xa)
        apply blast
       apply clarsimp
       apply (rule imageI)
       apply simp
       apply (rule conjI)
  using defined_left_after_right apply auto[1]
       apply (rule subsetI)
       apply (rename_tac xa)
       apply (case_tac xa)
         apply blast
  using lookup_exec_update_left_right_swap apply fast
  using div_left_after_right apply simp
      apply blast
     apply (rule disjI2)
     apply (rule subsetI)
     apply (rename_tac xa)
     apply (case_tac xa)
       apply blast
      apply clarsimp
      apply (rule imageI)
      apply simp
      apply (rule conjI)
  using defined_right_after_left apply simp
      apply (rule subsetI)
      apply (rename_tac xa)
      apply (case_tac xa)
  using err_right_after_left apply simp
       apply fast
  using div_right_after_left apply auto[1]
     apply blast
    apply (rule disjI2)
    apply (rule subsetI)
    apply (rename_tac xa)
    apply (case_tac xa)
      apply blast
     apply clarsimp
     apply (rule imageI)
     apply simp
     apply (rule conjI)
  using defined_left_after_right apply simp
     apply (rule subsetI)
     apply (rename_tac xa)
     apply (case_tac xa)
  using err_left_after_right apply simp
  using lookup_exec_update_left_right_swap apply fast
  using div_left_after_right apply auto[1]
    apply blast
   apply simp
   apply (rule append_undefined_lookup_id)
    apply simp
   apply simp
  apply (rule subsetI)
  apply (rename_tac x)
  apply simp
  apply (subgoal_tac "x \<in> defined loc")
   apply simp
   apply (simp add: lookup_exec_update_some)
   apply (erule disjE)
    apply clarsimp
    apply (frule_tac p=Left in lookup_id_append_undefined)
     apply simp
    apply (frule_tac p=Right in lookup_id_append_undefined)
     apply simp
    apply simp
   apply (elim conjE disjE)
      apply simp
      apply auto[1]
     apply simp
     apply (intro conjI)
          apply blast
         apply blast
        apply (rule subsetI)
        apply clarsimp
  using err_left_after_right apply fast
       apply blast
      apply blast
     apply blast
    apply simp
    apply (intro conjI)
         apply (rule subsetI)
         apply clarsimp
  using err_right_after_left apply auto[1]
        apply blast
       apply blast
      apply blast
     apply blast
    apply blast
   apply simp
   apply (intro conjI)
        apply (rule subsetI)
        apply clarsimp
  using err_right_after_left apply auto[1]
       apply blast
      apply (rule subsetI)
      apply clarsimp
  using err_left_after_right apply auto[1]
     apply blast
    apply blast
   apply blast
  using defined_append by blast

subsection \<open>Mu lemmas\<close>

lemma update_big_union_equals_big_union_update:
  assumes "x \<in> defined loc"
  shows
    "update loc x (\<Union>xa\<in>A. PdToSet (snd xa (lookup loc x))) = (\<Union>xa\<in>A. update loc x (PdToSet (snd xa (lookup loc x))))"
  using assms proof (induct loc arbitrary: x)
  case empty
  then show ?case 
    by simp
next
  case (Lcons pos loc)
  then show ?case
    apply (case_tac pos)
     apply (case_tac x)
      apply auto[1]
     apply auto[1]
    by fastforce
qed

lemma wp_mu_admissible : "ccpo.admissible Sup (\<le>)
        (\<lambda>x. Rep_pt (fst (fst x) loc) P = {e \<in> defined loc. update loc e (PdToSet (snd x (lookup loc e))) \<subseteq> E ` P})"
  apply (rule ccpo.admissibleI)
  apply (simp add : prod_Sup Sup_pt)
  apply (subst Abs_pt_inverse)
   apply simp
   apply (intro mono_intros)
  apply (rule set_eqI)
  apply simp
  apply (rename_tac A x)
  apply (case_tac "\<forall> elem \<in> (\<lambda> xa. xa (lookup loc x)) ` (snd ` A). Div \<in> PdToSet elem")
   apply (frule div_Sup_ub[rotated 2])
     apply clarsimp
    apply simp
    apply (frule chain_snd_exist)
    apply (metis (mono_tags, lifting) chain_imageI le_fun_def)
   apply simp
   apply (subst Abs_powerdomain_inverse)
    apply simp
    apply blast
   apply (rule iffI)
    apply clarsimp
    apply (rotate_tac 3)
    apply (rename_tac a b c)
    apply (drule_tac x = "((a, b), c)" in bspec)
     apply simp
    apply simp
  using update_inter_err_div apply blast
   apply clarsimp
   apply (simp add: update_big_union_equals_big_union_update)
   apply blast
  apply clarsimp
  apply (rename_tac a b c)
  apply (frule_tac A="(\<lambda> xa. xa (lookup loc x)) ` (snd ` A)" in no_div_Sup_ub[rotated 2])
    apply clarsimp
    apply (frule chain_snd_exist)
    apply (metis (mono_tags, lifting) chain_imageI le_fun_def)
   apply clarsimp
   apply (rule imageI)
  using image_iff apply fastforce
  apply clarsimp
  apply (rule iffI)
   apply clarsimp
   apply (rename_tac a1 b1 c1)
   apply (subgoal_tac "c (lookup loc x) = c1 (lookup loc x)")
    apply simp
    apply blast
   apply (rule antisym)
    apply (rule_tac A="(\<lambda> xa. xa (lookup loc x)) ` (snd ` A)" in no_div_collapses)
       apply clarsimp
       apply (frule chain_snd_exist)
       apply (metis (mono_tags, lifting) chain_imageI le_fun_def)
      apply (rule imageI)
      apply simp
  using image_eqI apply (metis (no_types, opaque_lifting) snd_conv)
     apply (rule imageI)
     apply simp
  using image_eqI apply (metis (no_types, opaque_lifting) snd_conv)
    apply clarsimp
  using update_inter_err_div apply blast
   apply (rule_tac A="(\<lambda> xa. xa (lookup loc x)) ` (snd ` A)" in no_div_collapses)
      apply clarsimp
      apply (frule chain_snd_exist)
      apply (metis (mono_tags, lifting) chain_imageI le_fun_def)
     apply (rule imageI)
     apply simp
  using image_eqI apply (metis (no_types, opaque_lifting) snd_conv)
    apply (rule imageI)
    apply simp
  using image_eqI apply (metis (no_types, opaque_lifting) snd_conv)
   apply clarsimp
  apply clarsimp
  apply (frule chain_snd_exist)
  by fastforce

lemma wp_err_mu_admissible : "ccpo.admissible Sup (\<le>)
        (\<lambda>x. Rep_pt (snd (fst x) loc) P = {e \<in> defined loc. update loc e (PdToSet (snd x (lookup loc e))) \<subseteq> E ` P \<union> {Err}})"
  apply (rule ccpo.admissibleI)
  apply (simp add : prod_Sup Sup_pt)
  apply (subst Abs_pt_inverse)
   apply simp
   apply (intro mono_intros)
  apply (rule set_eqI)
  apply simp
  apply (rename_tac A x)
  apply (case_tac "\<forall> elem \<in> (\<lambda> xa. xa (lookup loc x)) ` (snd ` A). Div \<in> PdToSet elem")
   apply (frule div_Sup_ub[rotated 2])
     apply clarsimp
    apply simp
    apply (frule chain_snd_exist)
    apply (metis (mono_tags, lifting) chain_imageI le_fun_def)
   apply simp
   apply (subst Abs_powerdomain_inverse)
    apply simp
    apply blast
   apply (rule iffI)
    apply clarsimp
    apply (rotate_tac 3)
    apply (rename_tac a b c)
    apply (drule_tac x = "((a, b), c)" in bspec)
     apply simp
    apply simp
  using update_inter_err_div apply blast
   apply clarsimp
   apply (simp add: update_big_union_equals_big_union_update)
   apply blast
  apply clarsimp
  apply (frule_tac A="(\<lambda> xa. xa (lookup loc x)) ` (snd ` A)" in no_div_Sup_ub[rotated 2])
    apply clarsimp
    apply (frule chain_snd_exist)
    apply (metis (mono_tags, lifting) chain_imageI le_fun_def)
   apply clarsimp
   apply (rule imageI)
  using image_iff apply fastforce
  apply clarsimp
  apply (rename_tac a b c)
  apply (rule iffI)
   apply clarsimp
   apply (rename_tac a1 b1 c1)
   apply (subgoal_tac "c (lookup loc x) = c1 (lookup loc x)")
    apply simp
    apply blast
   apply (rule antisym)
    apply (rule_tac A="(\<lambda> xa. xa (lookup loc x)) ` (snd ` A)" in no_div_collapses)
       apply clarsimp
       apply (frule chain_snd_exist)
       apply (metis (mono_tags, lifting) chain_imageI le_fun_def)
      apply (rule imageI)
      apply simp
  using image_eqI apply (metis (no_types, opaque_lifting) snd_conv)
     apply (rule imageI)
     apply simp
  using image_eqI apply (metis (no_types, opaque_lifting) snd_conv)
    apply clarsimp
  using update_inter_err_div apply blast
   apply (rule_tac A="(\<lambda> xa. xa (lookup loc x)) ` (snd ` A)" in no_div_collapses)
      apply clarsimp
      apply (frule chain_snd_exist)
      apply (metis (mono_tags, lifting) chain_imageI le_fun_def)
     apply (rule imageI)
     apply simp
  using image_eqI apply (metis (no_types, opaque_lifting) snd_conv)
    apply (rule imageI)
    apply simp
  using image_eqI apply (metis (no_types, opaque_lifting) snd_conv)
   apply clarsimp
  apply clarsimp
  apply (frule chain_snd_exist)
  by fastforce


subsection \<open>Soundness theorem\<close>

theorem wp_wp_err_soundness: 
  assumes "\<forall> X l P. (Rep_pt (env (X, Tot) l) P) 
                    = {e | e. e \<in> (defined l) \<and> (update l e (PdToSet ((senv X) (lookup l e)))) \<subseteq> E ` P}
            \<and> (Rep_pt (env (X, Par) l) P) 
                = {e | e. e \<in> (defined l) \<and> (update l e (PdToSet ((senv X) (lookup l e)))) \<subseteq> E ` P \<union> {Err}}"
  shows "(wp s loc P env) 
          = {e | e. e \<in> (defined loc) \<and> (update loc e (PdToSet (exec s senv (lookup loc e)))) \<subseteq> E ` P}"
    "(wp_err s loc P env)
          = {e | e. e \<in> (defined loc) \<and> (update loc e (PdToSet (exec s senv (lookup loc e)))) \<subseteq> E ` P \<union> {Err}}"
  using assms
proof (induct s arbitrary: P loc env senv)
  case SKIP case 1 then show ?case
    using UpdateWithLookupUnchanged
    by auto
next
  case SKIP case 2 then show ?case
    using UpdateWithLookupUnchanged
    by auto
next
  case ABORT case 1 then show ?case
    using UpdateErrGivesErr
    by auto
next
  case ABORT case 2 then show ?case
    using UpdateErrGivesErr
    by auto
next
  case Atomic case 1 then show ?case
    by simp
next 
  case Atomic case 2 then show ?case
    by simp
next
  case (Seq s1 s2) note hyps=this {
    case 1 then show ?case
      apply (clarsimp)
      apply (subst hyps(1)[where senv=senv])
       apply simp
      apply (subst hyps(3)[where senv=senv])
       apply simp
      apply (subst seq_wp_sound_set[simplified wp_sound_set_def lookup_exec_update_def, simplified, 
            where loc=loc and ?s1.0=s1 and senv=senv and ?s2.0=s2 and P=P])
      by simp
  next 
    case 2 then show ?case
      apply (clarsimp)
      apply (subst hyps(2)[where senv=senv])
       apply simp
      apply (subst hyps(4)[where senv=senv])
       apply simp
      apply (subst seq_wp_err_sound_set[simplified wp_err_sound_set_def lookup_exec_update_def, simplified, 
            where loc=loc and ?s1.0=s1 and senv=senv and ?s2.0=s2 and P=P])
      by simp
  }
next
  case (Left_Choice s1 s2) note hyps=this {
    case 1 then show ?case 
      apply clarsimp
      apply (subst hyps(1)[where senv=senv], simp)
      apply (subst hyps(2)[where senv=senv], simp)
      apply (subst hyps(3)[where senv=senv], simp)
      apply (subst lc_wp_sound_set[simplified wp_sound_set_def wp_err_sound_set_def lookup_exec_update_def, simplified, 
            where loc=loc and ?s1.0=s1 and senv=senv and ?s2.0=s2 and P=P])
      by simp
  next
    case 2 then show ?case 
      apply clarsimp
      apply (subst hyps(1)[where senv=senv], simp)
      apply (subst hyps(2)[where senv=senv], simp)
      apply (subst hyps(4)[where senv=senv], simp)
      apply (subst lc_wp_err_sound_set[simplified wp_sound_set_def wp_err_sound_set_def lookup_exec_update_def, simplified, 
            where loc=loc and ?s1.0=s1 and senv=senv and ?s2.0=s2 and P=P])
      by simp
  }
next
  case (Choice s1 s2) note hyps=this {
    case 1 then show ?case
      apply clarsimp
      apply (subst hyps(1)[where senv=senv], simp)
      apply (subst hyps(2)[where senv=senv], simp)
      apply (subst hyps(3)[where senv=senv], simp)
      apply (subst hyps(4)[where senv=senv], simp)
      apply (subst choice_wp_sound_set[simplified wp_sound_set_def wp_err_sound_set_def lookup_exec_update_def, simplified, 
            where loc=loc and ?s1.0=s1 and senv=senv and ?s2.0=s2 and P=P])
      by auto
    case 2 then show ?case
      apply clarsimp
      apply (subst hyps(2)[where senv=senv], simp)
      apply (subst hyps(4)[where senv=senv], simp)
      apply (subst choice_wp_err_sound_set[simplified wp_sound_set_def wp_err_sound_set_def lookup_exec_update_def, simplified,
            where loc=loc and ?s1.0=s1 and senv=senv and ?s2.0=s2 and P=P])
      by auto
  }
next 
  case (One s) note hyps=this {
    case 1 then show ?case
      apply clarsimp
      apply (subst hyps(1)[where senv=senv], simp)
      apply (subst hyps(2)[where senv=senv], simp)
      apply (subst hyps(1)[where senv=senv], simp)
      apply (subst hyps(2)[where senv=senv], simp)
      apply (subst one_wp_sound_set[simplified wp_sound_set_def wp_err_sound_set_def lookup_exec_update_def, simplified,
            where loc=loc and ?s=s and senv=senv  and P=P])
      by auto
  next
    case 2 then show ?case
      apply clarsimp
      apply (subst hyps(2)[where senv=senv], simp)
      apply (subst hyps(2)[where senv=senv], simp)
      apply (subst one_wp_err_sound_set[simplified wp_sound_set_def wp_err_sound_set_def lookup_exec_update_def, simplified,
            where loc=loc and ?s=s and senv=senv  and P=P])
      by auto
  }
next
  case (All s) note hyps=this {
    case 1 then show ?case
      apply clarsimp
      apply (subst hyps(1)[where senv=senv], simp)
      apply (subst hyps(1)[where senv=senv], simp)
      apply (subst hyps(1)[where senv=senv], simp)
      apply (subst hyps(1)[where senv=senv], simp)
      apply (subst all_wp_sound_set[simplified wp_sound_set_def wp_err_sound_set_def lookup_exec_update_def, simplified,
            where loc=loc and ?s=s and senv=senv  and P=P])
      by auto
  next
    case 2 then show ?case
      apply clarsimp
      apply (subst hyps(2)[where senv=senv], simp)
      apply (subst hyps(2)[where senv=senv], simp)
      apply (subst hyps(2)[where senv=senv], simp)
      apply (subst hyps(2)[where senv=senv], simp)
      apply (subst all_wp_err_sound_set[simplified wp_sound_set_def wp_err_sound_set_def lookup_exec_update_def, simplified,
            where loc=loc and ?s=s and senv=senv  and P=P])
      by auto
  }

next
  case (CSome s) note hyps=this {
    case 1 then show ?case
      apply clarsimp
      apply (subst hyps(2)[where senv=senv], simp)
      apply (subst hyps(1)[where senv=senv], simp)
      apply (subst hyps(1)[where senv=senv], simp)
      apply (subst hyps(2)[where senv=senv], simp)
      apply (subst hyps(1)[where senv=senv], simp)
      apply (subst hyps(1)[where senv=senv], simp)
      apply (subst hyps(1)[where senv=senv], simp)
      apply (subst hyps(1)[where senv=senv], simp)
      apply (subst hyps(1)[where senv=senv], simp)
      apply (subst hyps(1)[where senv=senv], simp)
      apply (subst some_wp_sound_set[simplified wp_sound_set_def wp_err_sound_set_def lookup_exec_update_def, simplified,
            where loc=loc and ?s=s and senv=senv  and P=P])
      by simp
  next
    case 2 then show ?case
      apply clarsimp
      apply (subst hyps(2)[where senv=senv], simp)
      apply (subst hyps(2)[where senv=senv], simp)
      apply (subst hyps(2)[where senv=senv], simp)
      apply (subst hyps(2)[where senv=senv], simp)
      apply (subst hyps(2)[where senv=senv], simp)
      apply (subst hyps(2)[where senv=senv], simp)
      apply (subst hyps(2)[where senv=senv], simp)
      apply (subst hyps(2)[where senv=senv], simp)
      apply (subst hyps(1)[where senv=senv], simp)
      apply (subst hyps(1)[where senv=senv], simp)
      apply (subst some_wp_err_sound_set[simplified wp_sound_set_def wp_err_sound_set_def lookup_exec_update_def, simplified,
            where loc=loc and ?s=s and senv=senv  and P=P])
      by simp
  }

next
  case FixVar case 1 then show ?case
    by simp
next
  case FixVar case 2 then show ?case
    by simp
next 
  case (Mu v s) note hyps=this {
    case 1 then show ?case
      apply (subgoal_tac 
          "\<forall> P loc. 
                (wp (mu v. s) loc P env = {e |e. e \<in> defined loc \<and> update loc e (PdToSet (exec (mu v. s) senv (lookup loc e))) \<subseteq> E ` P})
                \<and> (wp_err (mu v. s) loc P env = {e |e. e \<in> defined loc \<and> update loc e (PdToSet (exec (mu v. s) senv (lookup loc e))) \<subseteq> E ` P \<union> {Err}})")
       apply simp
      apply simp
      apply (rule parallel_fixp_induct[where f="\<lambda> x. (\<lambda>loc. Abs_pt (\<lambda>P. wp s loc P (env((v, Tot) := fst x, (v, Par) := snd x))),
                  \<lambda>loc. Abs_pt (\<lambda>P. wp_err s loc P (env((v, Tot) := fst x, (v, Par) := snd x))))"and g="\<lambda> x. exec s (senv(v := x))"])
          apply (rule admissible_all)
          apply (rule admissible_all)
          apply (rule admissible_conj)
           apply (rule wp_mu_admissible)
          apply (rule wp_err_mu_admissible[simplified])
         apply (simp add: prod_Sup Sup_pt pd_Sup)
         apply (subst Abs_pt_inverse)
          apply simp
          apply (intro mono_intros)
         apply (subst Abs_pt_inverse)
          apply simp
          apply (intro mono_intros)
         apply clarsimp
      using update_inter_err_div apply blast
        apply (intro mono_intros)
       apply (rule monoI)
       apply (rule exec_mono)
       apply simp
      apply clarsimp
      apply (subst Abs_pt_inverse)
       apply simp
       apply (intro mono_intros)
      apply (subst Abs_pt_inverse)
       apply simp
       apply (intro mono_intros)
      apply (rule conjI)
      using hyps(1) apply simp
      using hyps(2) by simp
  next
    case 2 then show ?case
      apply (subgoal_tac 
          "\<forall> P loc. 
                (wp (mu v. s) loc P env = {e |e. e \<in> defined loc \<and> update loc e (PdToSet (exec (mu v. s) senv (lookup loc e))) \<subseteq> E ` P})
                \<and> (wp_err (mu v. s) loc P env = {e |e. e \<in> defined loc \<and> update loc e (PdToSet (exec (mu v. s) senv (lookup loc e))) \<subseteq> E ` P \<union> {Err}})")
       apply simp
      apply simp
      apply (rule parallel_fixp_induct[where f="\<lambda> x. (\<lambda>loc. Abs_pt (\<lambda>P. wp s loc P (env((v, Tot) := fst x, (v, Par) := snd x))),
                  \<lambda>loc. Abs_pt (\<lambda>P. wp_err s loc P (env((v, Tot) := fst x, (v, Par) := snd x))))"and g="\<lambda> x. exec s (senv(v := x))"])
          apply (rule admissible_all)
          apply (rule admissible_all)
          apply (rule admissible_conj)
           apply (rule wp_mu_admissible)
          apply (rule wp_err_mu_admissible[simplified])
         apply (simp add: prod_Sup Sup_pt pd_Sup)
         apply (subst Abs_pt_inverse)
          apply simp
          apply (intro mono_intros)
         apply (subst Abs_pt_inverse)
          apply simp
          apply (intro mono_intros)
         apply clarsimp
      using update_inter_err_div apply blast
        apply (intro mono_intros)
       apply (rule monoI)
       apply (rule exec_mono)
       apply simp
      apply clarsimp
      apply (subst Abs_pt_inverse)
       apply simp
       apply (intro mono_intros)
      apply (subst Abs_pt_inverse)
       apply simp
       apply (intro mono_intros)
      apply (rule conjI)
      using hyps(1) apply simp
      using hyps(2) by simp
  }
qed

end
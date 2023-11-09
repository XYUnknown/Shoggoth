section \<open>The Denotational Semantics and Big-Step Operational Semantics are Equivalent\<close>

theory SemanticsEquivalence
  imports Denotational Operational WpSoundness
begin

fun fv :: "strategy \<Rightarrow> var set" 
  where
    "fv SKIP = {}" 
  | "fv ABORT = {}"
  | "fv \<lparr>v\<rparr> = {v}"
  | "fv \<llangle>atomic\<rrangle> = {}"
  | "fv (Seq s1 s2) = fv s1 \<union> fv s2"
  | "fv (Left_Choice s1 s2) = fv s1 \<union> fv s2"
  | "fv (Choice s1 s2) = fv s1 \<union> fv s2"
  | "fv (One s) = fv s"
  | "fv (CSome s) = fv s"
  | "fv (All s) = fv s"
  | "fv (Mu v s) = fv s - {v}"

lemma env_irrelevant:
  assumes "\<forall> X \<in> fv s. \<xi>1 X = \<xi>2 X"
  shows "exec s \<xi>1 = exec s \<xi>2"
  using assms
proof (induct s arbitrary: \<xi>1 \<xi>2)
  case SKIP
  then show ?case
    by simp
next
  case ABORT
  then show ?case
    by simp
next
  case (FixVar x)
  then show ?case
    by simp
next
  case (Atomic x)
  then show ?case
    by simp
next
  case (Seq s1 s2)
  then show ?case
    apply simp
    by (metis UnI1 UnI2)
next
  case (Left_Choice s1 s2)
  then show ?case
    apply simp
    by (metis UnI1 UnI2)
next
  case (Choice s1 s2)
  then show ?case
    apply simp
    by (metis UnI1 UnI2)
next
  case (One s)
  then show ?case
    by fastforce
next
  case (CSome s)
  then show ?case
    by fastforce
next
  case (All s)
  then show ?case
    by fastforce
next
  case (Mu x1 s)
  then show ?case
    apply simp
    apply (subgoal_tac "\<forall> x. exec s (\<xi>1(x1 := x)) =  exec s (\<xi>2(x1 := x))")
     apply presburger
    by auto
qed

subsection \<open>Computational soundness one\<close>
lemma substitution: 
  assumes "fv s' = {}"
  shows "exec (s \<lbrace> X \<mapsto> s'\<rbrace>) \<xi> = exec s (\<xi>(X := (exec s' \<xi>)))"
  using assms
proof (induct s arbitrary: \<xi>)
  case SKIP
  then show ?case
    by simp
next
  case ABORT
  then show ?case
    by simp
next
  case (FixVar x)
  then show ?case
    by simp
next
  case (Atomic x)
  then show ?case
    by simp
next
  case (Seq s1 s2)
  then show ?case
    by simp
next
  case (Left_Choice s1 s2)
  then show ?case
    by auto
next
  case (Choice s1 s2)
  then show ?case
    by simp
next
  case (One s)
  then show ?case
    by simp
next
  case (CSome s)
  then show ?case
    by simp
next
  case (All s)
  then show ?case 
    by auto
next
  case (Mu x1 s)
  then show ?case
    apply simp
    apply (intro impI conjI)
     apply (subgoal_tac "\<forall> x. ((\<lambda>a. if a = X then exec s' \<xi> else \<xi> a)(X := x)) = (\<xi>(X := x))")
      apply simp
     apply auto[1]
    apply (subgoal_tac "\<forall> x. (\<lambda>a. if a = X then exec s' (\<xi>(x1 := x)) else (\<xi>(x1 := x)) a) = ((\<lambda>a. if a = X then exec s' \<xi> else \<xi> a)(x1 := x))")
     apply simp
    apply clarsimp
    apply (rule ext)
    apply clarsimp
    apply (rule env_irrelevant)
    by simp
qed

lemma subst_var_empty: "fv Y = {} \<Longrightarrow> fv (s\<lbrace>X\<mapsto>Y\<rbrace>) = fv s - {X}"
proof (induct s arbitrary: X Y)
  case SKIP
  then show ?case
    by simp
next
  case ABORT
  then show ?case
    by simp
next
  case (FixVar x)
  then show ?case
    by simp
next
  case (Atomic x)
  then show ?case
    by auto
next
  case (Seq s1 s2)
  then show ?case try
    by auto
next
  case (Left_Choice s1 s2)
  then show ?case
    by auto
next
  case (Choice s1 s2)
  then show ?case
    by auto
next
  case (One s)
  then show ?case 
    by auto
next
  case (CSome s)
  then show ?case
    by auto
next
  case (All s)
  then show ?case 
    by auto
next
  case (Mu x1 s)
  then show ?case
    apply simp
    by blast
qed

text \<open>Computational soundness one for non-diverging executions\<close>
theorem soundness:
  assumes "(s , e) \<Down> e'"
    and "fv s = {}"
  shows "e' \<in> PdToSet (exec s \<xi> e)"
  using assms
proof (induct "(s, e)" "e'" arbitrary: s \<xi> e rule: big_step.induct)
  case (Skip e)
  then show ?case 
    by simp
next
  case (Abort e)
  then show ?case
    by simp
next
  case (Atomic atomic e)
  then show ?case  
    by (simp split: option.split)
next
  case (Seq s1 e1 e2 s2 e3)
  then show ?case
    apply (simp add: PdToSet_seq)
    by auto
next
  case (SeqEr1 s1 e1 s2)
  then show ?case 
    by (simp add: PdToSet_seq)
next
  case (SeqEr2 s1 e1 e2 s2)
  then show ?case 
    apply (simp add: PdToSet_seq)
    by auto
next
  case (LeftL s1 e e1 s2)
  then show ?case 
    by (simp add: PdToSet_lc)
next
  case (LeftR s1 e s2 e1)
  then show ?case 
    by (simp add: PdToSet_lc)
next
  case (LeftEr s1 e s2)
  then show ?case  
    by (simp add: PdToSet_lc)
next
  case (ChoiceL s1 e e1 s2)
  then show ?case 
    by (simp add: PdToSet_choice)
next
  case (ChoiceR s2 e e1 s1)
  then show ?case 
    by (simp add: PdToSet_choice)
next
  case (ChoiceEr s1 e s2)
  then show ?case 
    by (simp add: PdToSet_choice)
next
  case (OneLeaf s label)
  then show ?case 
    by (simp add: PdToSet_one)
next
  case (OneNodeL s l l' r)
  then show ?case
    by (simp add: PdToSet_one)
next
  case (OneNodeR s r r' l)
  then show ?case
    by (simp add: PdToSet_one)
next
  case (OneNodeEr s l r)
  then show ?case 
    by (simp add: PdToSet_one)
next
  case (SomeLeaf s label)
  then show ?case
    by (simp add: PdToSet_some)
next
  case (SomeNodeL s l l' r)
  then show ?case 
    by (simp add: PdToSet_some)
next
  case (SomeNodeR s r r' l)
  then show ?case
    by (simp add: PdToSet_some)
next
  case (SomeNode s l l' r r')
  then show ?case 
    by (simp add: PdToSet_some)
next
  case (SomeNodeEr s l r)
  then show ?case
    by (simp add: PdToSet_some)
next
  case (AllLeaf s label)
  then show ?case
    by (simp add: PdToSet_all)
next
  case (AllNode s l l' r r')
  then show ?case
    by (simp add: PdToSet_all)
next
  case (AllNodeErL s l r)
  then show ?case
    by (simp add: PdToSet_all)
next
  case (AllNodeErR s r l)
  then show ?case
    by (simp add: PdToSet_all)
next
  case (FixedPoint s X e e')
  then show ?case
    apply (simp add: substitution)
    apply (subst fixp_unfold)
     apply (rule monoI)
     apply (rule exec_mono)
     apply simp
    apply (drule_tac x=\<xi> in meta_spec)
    apply (drule meta_mp)
     apply (subst subst_var_empty)
      apply simp
    by blast
next
  case (FixedPointEr s X e)
  then show ?case
    apply (simp add: substitution)
    apply (subst fixp_unfold)
     apply (rule monoI)
     apply (rule exec_mono)
     apply simp
    apply (drule_tac x=\<xi> in meta_spec)
    apply (drule meta_mp)
     apply (subst subst_var_empty)
      apply simp
    by blast
qed

subsection \<open>Computational adequacy one\<close>
definition approximate :: "strategy \<Rightarrow> D \<Rightarrow> bool"
  where
    "approximate s d \<longleftrightarrow> (fv s = {}) \<and> (\<forall> e e'. (e' \<in> PdToSet (d e)) \<and> (e' \<noteq> Div) \<longrightarrow> (s, e) \<Down> e')"

type_synonym \<Theta> = "var \<Rightarrow> strategy"

fun map_strategy :: "\<Theta> \<Rightarrow> strategy \<Rightarrow> strategy"
  where
    "map_strategy f SKIP = SKIP"
  | "map_strategy f ABORT = ABORT"
  | "map_strategy f \<lparr>X\<rparr> = f X"
  | "map_strategy f \<llangle>atomic\<rrangle> = \<llangle>atomic\<rrangle>"
  | "map_strategy f (s1 ;; s2) = (map_strategy f s1) ;; (map_strategy f s2)"
  | "map_strategy f (s1 <+ s2) = (map_strategy f s1) <+ (map_strategy f s2)"
  | "map_strategy f (s1 >< s2) = (map_strategy f s1) >< (map_strategy f s2)"
  | "map_strategy f (one s) = one (map_strategy f s)"
  | "map_strategy f (some s) = some (map_strategy f s)"
  | "map_strategy f (all s) = all (map_strategy f s)"
  | "map_strategy f (mu X. s) = mu X. (map_strategy (f(X := \<lparr>X\<rparr>)) s)"

lemma approximate_seq: 
  assumes "approximate s1 d1"
    and "approximate s2 d2"
  shows "approximate (s1 ;; s2) (d1 ;;s d2)"
  using assms
  unfolding approximate_def
  apply clarsimp
  apply (rename_tac e e')
  apply (simp add: PdToSet_seq)
  apply (elim disjE conjE exE)
   apply (rename_tac x xa)
   apply (case_tac e')
     apply simp
     apply (rule_tac ?e2.0=xa in big_step.SeqEr2)
      apply blast
     apply blast
    apply simp
    apply (rule_tac ?e2.0=xa in big_step.Seq)
     apply blast
    apply blast
   apply blast
  apply simp
  apply (rule big_step.SeqEr1)
  by blast

lemma approximate_lc: 
  assumes "approximate s1 d1"
    and "approximate s2 d2"
  shows "approximate (s1 <+ s2) (d1 <+s d2)"
  using assms
  unfolding approximate_def
  apply clarsimp
  apply (rename_tac e e')
  apply (simp add: PdToSet_lc)
  apply (elim disjE conjE exE)
   apply (case_tac e')
     apply simp
    apply simp
    apply (rule big_step.LeftL)
    apply blast
   apply blast
  apply (case_tac e')
    apply simp
    apply (rule big_step.LeftEr)
     apply blast
    apply blast
   apply simp
   apply (rule big_step.LeftR)
    apply blast
   apply blast
  by blast

lemma approximate_choice: 
  assumes "approximate s1 d1"
    and "approximate s2 d2"
  shows "approximate (s1 >< s2) (d1 ><s d2)"
  using assms
  unfolding approximate_def
  apply clarsimp
  apply (rename_tac e e')
  apply (simp add: PdToSet_choice)
  apply (elim disjE conjE exE)
    apply (case_tac e')
      apply blast
     apply simp
     apply (rule big_step.ChoiceL)
     apply blast
    apply blast
   apply (case_tac e')
     apply blast
    apply simp
    apply (rule big_step.ChoiceR)
    apply blast
   apply blast
  apply simp
  apply (rule big_step.ChoiceEr)
   apply blast
  by blast

lemma approximate_one: 
  assumes "approximate s d"
  shows "approximate (one s) (one_s d)"
  using assms
  unfolding approximate_def
  apply clarsimp
  apply (simp add: PdToSet_one)
  apply (elim disjE conjE exE)
  using big_step.OneNodeL apply blast
  using big_step.OneNodeR apply blast
  using big_step.OneLeaf apply blast
  using big_step.OneNodeEr by metis

lemma approximate_some: 
  assumes "approximate s d"
  shows "approximate (some s) (some_s d)"
  using assms
  unfolding approximate_def
  apply clarsimp
  apply (simp add: PdToSet_some)
  apply (elim disjE conjE exE)
  using big_step.SomeNode apply blast
  using big_step.SomeNodeL apply blast
  using big_step.SomeNodeR apply blast
  using big_step.SomeLeaf apply blast
  using big_step.SomeNodeEr by metis

lemma approximate_all: 
  assumes "approximate s d"
  shows "approximate (all s) (all_s d)"
  using assms
  unfolding approximate_def
  apply clarsimp
  apply (simp add: PdToSet_all)
  apply (elim disjE conjE exE)
  using big_step.AllNode apply blast
  using big_step.AllLeaf apply blast
  using big_step.AllNodeErL apply blast
  using big_step.AllNodeErR by blast

lemma map_strategy_closed:
  assumes "\<forall>y\<in>fv s. fv (\<theta> y) \<subseteq> vs"
  shows " fv (map_strategy \<theta> s) \<subseteq> vs"
  using assms
proof (induct s arbitrary: \<theta> vs)
  case SKIP
  then show ?case by simp
next
  case ABORT
  then show ?case by simp
next
  case (FixVar x)
  then show ?case by simp
next
  case (Atomic x)
  then show ?case by simp
next
  case (Seq s1 s2)
  then show ?case by simp
next
  case (Left_Choice s1 s2)
  then show ?case by auto
next
  case (Choice s1 s2)
  then show ?case by auto
next
  case (One s)
  then show ?case by simp
next
  case (CSome s)
  then show ?case by auto
next
  case (All s)
  then show ?case by simp
next
  case (Mu x1 s)
  then show ?case
    apply simp
    apply (drule_tac x="\<theta>(x1 := \<lparr>x1\<rparr>)" in meta_spec)
    apply (drule_tac x="vs \<union> {x1}" in meta_spec)
    apply (drule meta_mp)
     apply auto[1]
    by blast
qed

lemma subst_does_nothing: "x \<notin> fv s \<Longrightarrow>  s \<lbrace>x\<mapsto>s'\<rbrace> = s"
  apply (induct s)
  by auto

(*
(map_strategy (\<lambda>a. if a = x1 then \<lparr>x1\<rparr> else \<theta> a) s\<lbrace>x1\<mapsto>(mux1.map_strategy (\<lambda>a. if a = x1 then \<lparr>x1\<rparr> else \<theta> a) s)\<rbrace>,  e)
*)
lemma map_strategy_subst:
  assumes "\<forall> y \<in> fv(s) - {x}. x \<notin> fv (\<theta> y)"
  shows "map_strategy (\<theta>(x := \<lparr>x\<rparr>)) s\<lbrace>x \<mapsto> s'\<rbrace> = map_strategy (\<theta>(x := s')) s"
  using assms
proof (induct s arbitrary: \<theta>)
  case SKIP
  then show ?case  by simp
next
  case ABORT
  then show ?case by simp
next
  case (FixVar x)
  then show ?case
    apply clarsimp
    apply (rule subst_does_nothing)
    by simp
next
  case (Atomic x)
  then show ?case
    by simp
next
  case (Seq s1 s2)
  then show ?case
    by simp
next
  case (Left_Choice s1 s2)
  then show ?case
    by simp
next
  case (Choice s1 s2)
  then show ?case
    by simp
next
  case (One s)
  then show ?case
    by simp
next
  case (CSome s)
  then show ?case
    by simp
next
  case (All s)
  then show ?case
    by simp
next
  case (Mu x1 s)
  then show ?case
    apply clarsimp
    apply (rule conjI)
     apply clarsimp
     apply (subgoal_tac "((\<lambda>a. if a = x then \<lparr>x\<rparr> else \<theta> a)(x := \<lparr>x\<rparr>)) = ((\<lambda>a. if a = x then s' else \<theta> a)(x := \<lparr>x\<rparr>))")
      apply simp
     apply (rule ext)
     apply simp
    apply clarsimp
    apply (drule_tac x="\<theta>(x1 := \<lparr>x1\<rparr>)" in meta_spec)
    apply (drule meta_mp)
     apply simp
    apply (subgoal_tac "(\<lambda>a. if a = x then \<lparr>x\<rparr> else (\<theta>(x1 := \<lparr>x1\<rparr>)) a) = ((\<lambda>a. if a = x then \<lparr>x\<rparr> else \<theta> a)(x1 := \<lparr>x1\<rparr>))")
     apply (subgoal_tac "(\<lambda>a. if a = x then s' else (\<theta>(x1 := \<lparr>x1\<rparr>)) a) = ((\<lambda>a. if a = x then s' else \<theta> a)(x1 := \<lparr>x1\<rparr>))")
      apply simp
     apply (rule ext)
     apply simp
    apply (rule ext)
    by simp
qed

lemma approximation_lemma : 
  assumes "\<forall> y \<in> (fv s). approximate (\<theta> y) (\<xi> y)"
    and "sc = map_strategy \<theta> s"
  shows "approximate sc (exec s \<xi>)"
  using assms
proof (induct s arbitrary: \<theta> sc \<xi>)
  case SKIP
  then show ?case
    unfolding approximate_def
    using big_step.Skip by auto
next
  case ABORT
  then show ?case
    unfolding approximate_def
    using big_step.Abort by auto
next
  case (FixVar X)
  then show ?case
    by simp
next
  case (Atomic atomic)
  then show ?case
    unfolding approximate_def
    apply (simp split: option.split)
    apply clarsimp
    apply (rename_tac e)
    apply (rule conjI)
     apply clarsimp
    using big_step.Atomic[where atomic=atomic]
     apply -
     apply (drule_tac x=e in meta_spec)
     apply simp
    apply clarsimp
    apply (drule_tac x=e in meta_spec)
    by simp
next
  case (Seq s1 s2)
  then show ?case
    apply simp
    apply (rule approximate_seq)
     apply blast
    by blast
next
  case (Left_Choice s1 s2)
  then show ?case
    apply simp
    apply (rule approximate_lc)
     apply simp
    by blast
next
  case (Choice s1 s2)
  then show ?case
    apply simp
    apply (rule approximate_choice)
     apply simp
    by simp
next
  case (One s)
  then show ?case
    apply simp
    apply (rule approximate_one)
    by blast
next
  case (CSome s)
  then show ?case
    apply simp
    apply (rule approximate_some)
    by blast
next
  case (All s)
  then show ?case 
    apply simp
    apply (rule approximate_all)
    by blast
next
  case (Mu x1 s)
  then show ?case
    apply simp
    apply (rule_tac f="\<lambda> x. exec s (\<xi>(x1 := x))" in fixp_induct)
       apply (rule ccpo.admissibleI)
       apply (simp add: approximate_def)
       apply (rule conjI)
    using map_strategy_closed apply auto[1]
       apply clarsimp
       apply (subgoal_tac "Complete_Partial_Order.chain (\<le>) ((\<lambda> b. b e) ` A)")
        apply (case_tac "\<exists> a \<in> A. Div \<notin> PdToSet (a e)")
         apply clarsimp
         apply(frule_tac A="(\<lambda> b. b e) ` A" in no_div_Sup_ub[rotated 2])
           apply simp
          apply simp
         apply simp
        apply clarsimp
        apply (frule div_Sup_ub[rotated])
          apply simp
         apply blast
        apply simp
    using Rep_powerdomain apply auto[1]
       apply (metis (no_types, lifting) chain_imageI le_funE)
      apply (rule monoI)
      apply (rule exec_mono)
      apply auto[1]
     apply (simp add: Sup_empty approximate_def)
    using map_strategy_closed apply simp
    apply clarsimp
    apply (drule_tac x="\<theta>(x1 := map_strategy \<theta> (mu x1. s))" in meta_spec)
    apply (drule_tac x="\<xi>(x1 := x)" in meta_spec)
    apply (drule_tac x = "map_strategy (\<theta>(x1 := map_strategy \<theta> (mu x1. s))) s" in meta_spec)
    apply (drule meta_mp)
     apply clarsimp
     apply (simp add: fun_upd_def)
    apply (drule meta_mp)
     apply (simp add: fun_upd_def)
    apply (simp add: approximate_def)
    apply clarsimp
    apply (rename_tac e e')
    apply (case_tac e' ; simp)
     apply (rule big_step.FixedPointEr)
     apply (subst map_strategy_subst[simplified fun_upd_def])
      apply simp
     apply (rotate_tac 5)
     apply (drule_tac x="e" in spec)
     apply (rotate_tac 7)
     apply (drule_tac x="Err" in spec)
     apply (drule mp)
      apply (simp add: fun_upd_def)
     apply (subgoal_tac "(\<lambda>a. if a = x1 then mu x1. map_strategy (\<theta>(x1 := \<lparr>x1\<rparr>)) s else \<theta> a) = (\<lambda>x. if x = x1 then mu x1. map_strategy (\<lambda>a. if a = x1 then \<lparr>x1\<rparr> else \<theta> a) s else \<theta> x)")
      apply simp
     apply (rule ext)
     apply (simp add: fun_upd_def)
    apply (rule big_step.FixedPoint)
    apply (subst map_strategy_subst[simplified fun_upd_def])
     apply simp
    apply (rotate_tac 5)
    apply (drule_tac x="e" in spec)
    apply (rotate_tac 7)
    apply (rename_tac y)
    apply (drule_tac x="E y" in spec)
    apply (drule mp)
     apply (simp add: fun_upd_def)
    apply (subgoal_tac "(\<lambda>a. if a = x1 then mu x1. map_strategy (\<theta>(x1 := \<lparr>x1\<rparr>)) s else \<theta> a) = (\<lambda>x. if x = x1 then mu x1. map_strategy (\<lambda>a. if a = x1 then \<lparr>x1\<rparr> else \<theta> a) s else \<theta> x)")
     apply simp
    apply (rule ext)
    by (simp add: fun_upd_def)
qed

lemma map_closed_strategy_unchanged:
  assumes "\<forall> y \<in> fv s. \<theta> y = \<lparr> y \<rparr>"
  shows "map_strategy \<theta> s = s"
  using assms
proof (induct s arbitrary: \<theta>)
qed auto

text \<open> The computational adequacy theorem one for non-diverging executions \<close>
theorem computational_adequacy:
  assumes "fv (s) = {}"
    and "e' \<in> PdToSet (exec s \<xi> e)"
    and "e' \<noteq> Div"
  shows "(s, e) \<Down> e'"
  using assms
  using approximation_lemma[where s=s and \<theta>="\<lambda> x. \<lparr> x \<rparr>" and \<xi>=\<xi> and sc = "map_strategy (\<lambda> x. \<lparr> x \<rparr>) s"]
  apply -
  apply (drule meta_mp)
   apply simp
  apply (drule meta_mp)
   apply simp
  apply (simp add : map_closed_strategy_unchanged)
  by (simp add : approximate_def)

subsection \<open>Computational soundness two\<close>
definition rel :: "strategy \<Rightarrow> D \<Rightarrow> bool" where
  rel_def: "rel s d \<longleftrightarrow> (fv s = {}) \<and> (\<forall>e. (((s,e) \<Up>) \<longrightarrow> Div \<in> PdToSet (d e)) \<and> (d e \<le> exec s (\<lambda>x. undefined) e) )" 

fun semantics_subst :: "(var \<Rightarrow> strategy) \<Rightarrow> env \<Rightarrow> env" where
  "semantics_subst \<theta> \<xi> y = exec (\<theta> y) \<xi>" 

theorem exec_mono_fv:
  assumes "\<forall>x \<in> fv s. env1 x \<le> env2 x"  
  shows "exec s env1 \<le> exec s env2"
  apply (subgoal_tac "exec s env1 = exec s (\<lambda>x. if x \<in> fv s then env1 x else (\<lambda>e. SetToPd {Div}))")
   apply simp
   apply (subgoal_tac "exec s env2 = exec s (\<lambda>x. if x \<in> fv s then env2 x else (\<lambda>e. SetToPd {Div}))")
    apply simp
    apply (rule exec_mono)
    apply (clarsimp simp: assms)
   apply (rule env_irrelevant)
   apply simp
  apply (rule env_irrelevant)
  by simp

lemma simul_substitution: 
  assumes "\<forall>y \<in> fv s1. fv (\<theta> y) = {} \<or> fv (\<theta> y) = {y}"
  shows "exec (map_strategy \<theta> s1) \<xi> = exec s1 (semantics_subst \<theta> \<xi>)"
  using assms apply (induct s1 arbitrary: \<theta> \<xi>; simp)
  apply (rename_tac x1 s1' \<theta>' \<xi>)
  apply (subgoal_tac "\<And> x. exec (map_strategy (\<theta>'(x1 := \<lparr>x1\<rparr>)) s1') (\<xi>(x1 := x)) 
                     =  exec s1' ((semantics_subst \<theta>' \<xi>)(x1 := x))")
   apply simp
  apply (drule_tac x = "(\<theta>'(x1 := \<lparr>x1\<rparr>))" in meta_spec)
  apply (drule_tac x = "(\<xi>(x1 := x))" in meta_spec)
  apply (drule meta_mp)
   apply clarsimp
  apply simp
  apply (rule env_irrelevant)
  apply clarsimp
  apply (rule env_irrelevant)
  by auto

lemma map_strategy_irrelevant:
  assumes "\<forall>y \<in> fv t. \<theta>1 y = \<theta>2 y" 
  shows "map_strategy \<theta>1 t = map_strategy \<theta>2 t" 
  using assms by (induct t arbitrary: \<theta>1 \<theta>2; simp)

lemma double_substitution: 
  assumes "\<forall>y \<in> fv t. fv (\<theta>1 y) \<subseteq> {y}"
    and     "\<forall>y \<in> fv (map_strategy \<theta>1 t). fv (\<theta>2 y) \<subseteq> {y}"
  shows "map_strategy \<theta>2 (map_strategy \<theta>1 t) = map_strategy (\<lambda>y. map_strategy \<theta>2 (\<theta>1 y)) t"
  using assms proof (induct t arbitrary: \<theta>1 \<theta>2)
  case (Mu x1 t)
  then show ?case 
    apply (simp add: fun_upd_def)
    apply (rule map_strategy_irrelevant)
    apply clarsimp
    apply (rule map_strategy_irrelevant)
    apply clarsimp
    by blast
qed auto

lemma map_strategy_decomp:
  assumes "fv u = {}"
    and     "\<forall>y \<in> fv t - {x1}. fv (\<theta> y) = {}"
  shows "map_strategy (\<theta>(x1 := u)) t 
       = map_strategy (\<theta>(x1 := u)) (map_strategy (\<theta>(x1 := \<lparr> x1 \<rparr>)) t)"
  using assms
  apply (subst double_substitution)
    apply auto[1]
   apply clarsimp
   apply (rename_tac y x)
   apply (subgoal_tac "fv (map_strategy (\<theta>(x1 := \<lparr> x1 \<rparr>)) t) \<subseteq> fv t")
    apply (drule_tac x = y in bspec)
     apply simp
     apply blast
    apply clarsimp
   apply (rule map_strategy_closed)
   apply clarsimp
  apply (rule map_strategy_irrelevant)
  apply clarsimp
  apply (rule sym)
  apply (rule map_closed_strategy_unchanged)
  by simp

lemma div_soundness_lemma: 
  assumes "\<forall> y \<in> fv s. rel (\<theta> y) (\<xi> y)"
  shows "rel (map_strategy \<theta> s) (exec s \<xi>)"
  using assms 
proof (induct s arbitrary: \<theta> \<xi>)
  case SKIP
  then show ?case by (auto simp: rel_def elim: big_step_div.cases) 
next
  case ABORT
  then show ?case by (auto simp: rel_def  elim: big_step_div.cases)
next
  case (FixVar x)
  then show ?case by (auto simp: rel_def  elim: big_step_div.cases)
next
  case (Atomic x)
  then show ?case by (auto simp: rel_def elim: big_step_div.cases)
next
  case (Seq s1 s2)
  then show ?case 
    apply simp
    apply (simp add: rel_def)
    apply (intro conjI)
      apply fast
     apply blast
    apply clarsimp
    apply (intro conjI)
     apply clarsimp
     apply (erule big_step_div.cases; simp)
      apply (drule_tac x = \<theta> in meta_spec)
      apply (drule_tac x = \<xi> in meta_spec)
      apply (drule meta_mp)
       apply simp
      apply clarsimp
      apply (simp add: PdToSet_seq)
     apply (frule_tac \<xi>=" (\<lambda>x. undefined)" in soundness)
      apply fast
     apply (drule sym)
     apply (simp add: simul_substitution)
     apply (rename_tac e s1' e1)
     apply (subgoal_tac "Div \<in> PdToSet (exec s1 \<xi> e) \<or> E e1 \<in> PdToSet (exec s1 \<xi> e)")
      apply (erule disjE)
       apply (simp add: PdToSet_seq)
      apply (rotate_tac)
      apply (drule_tac  x = \<theta> in meta_spec)
      apply (drule_tac x = "\<xi>" in meta_spec)
      apply (drule meta_mp)
       apply blast
      apply clarsimp
      apply (drule_tac x = e1 in spec)
      apply clarsimp
      apply (simp add: PdToSet_seq)
      apply (rule disjI1)
      apply blast
     apply (simp add: porcupine_eglimilner)
     apply fastforce
    apply (subgoal_tac "(exec s1 \<xi>;;s exec s2 \<xi>)
         \<le> (exec (map_strategy \<theta> s1) (\<lambda>x. undefined);;s exec (map_strategy \<theta> s2) (\<lambda>x. undefined))")
     apply (simp add: le_fun_def)
    apply (rule seq_s_mono)
     apply (simp add: le_fun_def)
    by (simp add: le_fun_def)
next
  case (Left_Choice s1 s2)
  then show ?case 
    apply simp
    apply (simp add: rel_def)
    apply (intro conjI)
      apply fast
     apply fast
    apply (clarsimp)
    apply (rule conjI)
     apply clarsimp
     apply (erule big_step_div.cases; simp)
      apply (drule_tac x = \<theta> in meta_spec)
      apply (drule_tac x = \<xi> in meta_spec)
      apply (drule meta_mp)
       apply auto[1]
      apply (clarsimp)
      apply (rename_tac e)
      apply (drule_tac x = e in spec)
      apply simp
      apply (simp add: PdToSet_lc)
     apply (simp add: PdToSet_lc)
     apply (drule_tac x = \<theta> in meta_spec)
     apply (drule_tac x = \<xi> in meta_spec)
     apply (drule meta_mp)
      apply blast
     apply (erule conjE, simp)
     apply (rename_tac e s1')
     apply (drule_tac x = e in spec)
     apply (erule conjE)
     apply (case_tac "Div \<in> PdToSet (exec s1 \<xi> e)")
      apply simp
     apply (rule disjI2)
     apply (rule conjI)
      apply (drule_tac x = \<theta> in meta_spec)
      apply (drule_tac x = \<xi> in meta_spec)
      apply (drule meta_mp)
       apply simp
      apply clarsimp
     apply (frule_tac \<xi>=" (\<lambda>x. undefined)" in soundness)
      apply fast
     apply (simp add: porcupine_eglimilner)
    apply (subgoal_tac "(exec s1 \<xi><+sexec s2 \<xi>)
         \<le> (exec (map_strategy \<theta> s1) (\<lambda>x. undefined)<+sexec (map_strategy \<theta> s2) (\<lambda>x. undefined))")
     apply (simp add: le_fun_def)
    apply (rule lchoice_s_mono)
     apply (drule_tac x = \<theta> in meta_spec)
     apply (drule_tac x = \<xi> in meta_spec)
     apply (drule meta_mp)
      apply simp
     apply clarsimp
     apply (simp add: le_fun_def)
    apply (drule_tac x = \<theta> in meta_spec)
    apply (drule_tac x = \<xi> in meta_spec)
    apply (drule meta_mp)
     apply simp
    apply clarsimp
    by (simp add: le_fun_def)
next
  case (Choice s1 s2)
  then show ?case 
    apply simp
    apply (simp add: rel_def)
    apply (intro conjI)
      apply fast
     apply fast
    apply (clarsimp)
    apply (rule conjI)
     apply clarsimp
     apply (erule big_step_div.cases; simp)
      apply (simp add: PdToSet_choice)
      apply blast
     apply (simp add: PdToSet_choice)
     apply blast
    apply (subgoal_tac "(exec s1 \<xi>><sexec s2 \<xi>)
         \<le> (exec (map_strategy \<theta> s1) (\<lambda>x. undefined)><sexec (map_strategy \<theta> s2) (\<lambda>x. undefined))")
     apply (simp add: le_fun_def)
    apply (rule choice_s_mono)
    using le_fun_def apply fast
    using le_fun_def by fast
next
  case (One s)
  then show ?case 
    apply simp
    apply (simp add: rel_def)
    apply (intro conjI)
     apply fast
    apply (clarsimp)
    apply (rule conjI)
     apply clarsimp
     apply (erule big_step_div.cases; simp)
      apply (simp add: PdToSet_one)
     apply (simp add: PdToSet_one)
    apply (subgoal_tac "one_s (exec s \<xi>) \<le> one_s (exec (map_strategy \<theta> s) (\<lambda>x. undefined))")
     apply (simp add: le_fun_def)
    apply (rule one_s_mono)
    using le_fun_def by fast
next
  case (CSome s)
  then show ?case
    apply simp
    apply (simp add: rel_def)
    apply (intro conjI)
     apply fast
    apply (clarsimp)
    apply (rule conjI)
     apply clarsimp
     apply (erule big_step_div.cases; simp)
      apply (simp add: PdToSet_some)
     apply (simp add: PdToSet_some)
    apply (subgoal_tac "some_s (exec s \<xi>) \<le> some_s (exec (map_strategy \<theta> s) (\<lambda>x. undefined))")
     apply (simp add: le_fun_def)
    apply (rule some_s_mono)
    using le_fun_def by fast
next
  case (All s)
  then show ?case
    apply simp
    apply (simp add: rel_def)
    apply (intro conjI)
     apply fast
    apply (clarsimp)
    apply (rule conjI)
     apply clarsimp
     apply (erule big_step_div.cases; simp)
      apply (simp add: PdToSet_all)
     apply (simp add: PdToSet_all)
    apply (subgoal_tac "all_s (exec s \<xi>) \<le> all_s (exec (map_strategy \<theta> s) (\<lambda>x. undefined))")
     apply (simp add: le_fun_def)
    apply (rule all_s_mono)
    using le_fun_def by fast
next
  case (Mu x1 t)
  then show ?case
    apply simp 
    apply (rule_tac f ="\<lambda> x. exec t (\<xi>(x1 := x))" in fixp_induct)
       apply (rule ccpo.admissibleI)
       apply (simp add: rel_def)
       apply (rule conjI)
        apply (rule map_strategy_closed)
        apply simp
       apply (rule allI)
       apply (rule conjI)
        apply (rule impI)
        apply (subgoal_tac "Complete_Partial_Order.chain (\<le>) ((\<lambda>x. x e) ` A)")
         apply (rotate_tac 5)
         apply (frule div_Sup_ub[rotated])
           apply clarsimp
          apply simp
         apply simp
         apply (subst Abs_powerdomain_inverse)
          apply auto[1]
          apply fast
         apply auto[1]
        apply (simp add: chain_def)
        apply (simp add: le_fun_def)
        apply metis
       apply (rule ccpo_Sup_least)
        apply (simp add: chain_def)
        apply (simp add: le_fun_def)
        apply metis
       apply auto[1]
      apply (rule monoI)
      apply (rule exec_mono)
      apply auto[1]
     apply (simp add: rel_def Sup_empty)
     apply (simp add: bottom_element)
     apply (rule map_strategy_closed)
     apply simp
    apply (rename_tac x)
    apply (drule_tac x = "\<theta>(x1 := map_strategy \<theta> (mu x1. t))" in meta_spec)
    apply (drule_tac x = "\<xi>(x1 := x)" in meta_spec)
    apply (drule meta_mp)
     apply (simp add: rel_def)
     apply clarsimp
     apply (rule conjI)
      apply (rule map_strategy_closed)
      apply simp
     apply (simp add: fun_upd_def)
    apply (simp add: rel_def)
    apply clarsimp
    apply (rename_tac e)
    apply (rule conjI)
     apply clarsimp
     apply (drule_tac x = e in spec)
     apply simp
     apply clarsimp
     apply (drule_tac x = e in spec)
     apply (erule conjE)
     apply (drule mp)
      apply (erule big_step_div.cases; simp)
      apply (rotate_tac 6)
      apply (drule sym)
      apply clarsimp
      apply (subgoal_tac "(map_strategy (\<lambda>a. if a = x1 then \<lparr>x1\<rparr> else \<theta> a) t)\<lbrace>x1\<mapsto>(mu x1. map_strategy (\<lambda>a. if a = x1 then \<lparr>x1\<rparr> else \<theta> a) t)\<rbrace>
                      = map_strategy (\<lambda>a. if a = x1 then (mu x1. map_strategy (\<lambda>a. if a = x1 then \<lparr>x1\<rparr> else \<theta> a) t) else \<theta> a) t") 
       apply simp
       apply (subst fun_upd_def)
       apply simp
      apply (simp add: map_strategy_subst[simplified fun_upd_def])
     apply (simp add: fun_upd_def)
    apply (rule_tac y = "exec t (semantics_subst (\<theta>(x1 := map_strategy \<theta> (mu x1. t)))  (\<lambda>x. undefined)) e" in order_trans)
     apply (rule_tac f = "exec t (\<xi>(x1 := x))" and g = "exec t (semantics_subst (\<theta>(x1 := map_strategy \<theta> (mu x1. t))) (\<lambda>x. undefined))" in le_funD)
     apply (subgoal_tac "exec t (\<xi>(x1 := x)) = exec t (\<lambda>y. if y \<in> fv t then (\<xi>(x1 := x)) y else (\<lambda>x. SetToPd {Div}))")
      apply simp
      apply (rule exec_mono)
      apply clarsimp
      apply (rule conjI)
       apply clarsimp
       apply (rule conjI)
        apply clarsimp
        apply (subst le_fun_def)
        apply (rule allI)
        apply (rename_tac xa)
        apply (drule_tac x = xa in spec)
        apply (simp add: fun_upd_def)
       apply clarsimp
       apply (simp add: le_fun_def bottom_element)
      apply (clarsimp)
      apply (rule conjI)
       apply clarsimp
       apply (rename_tac xa)
       apply (erule_tac x = xa in ballE)
        apply (erule conjE)
        apply (simp add: le_fun_def)
       apply blast
      apply clarsimp
      apply (simp add: le_fun_def bottom_element)
     apply (rule env_irrelevant)
     apply simp
    apply (subst simul_substitution[THEN sym])
     apply (rule ballI)
     apply simp
     apply (rule impI)
     apply (rule disjI1)
     apply (rule map_strategy_closed)
     apply auto[1]
    apply (subst fixp_unfold)
     apply (rule monoI)
     apply (rule exec_mono)
     apply simp
    apply (rotate_tac 4)
    apply (drule_tac x = e in spec)
    apply (clarsimp)
    apply (subgoal_tac " exec (map_strategy (\<theta>(x1 := map_strategy \<theta> (mu x1. t))) t) (\<lambda>x. undefined) e
                       = exec (map_strategy (\<theta>(x1 := map_strategy \<theta> (mu x1. t))) (map_strategy (\<theta>(x1 := \<lparr> x1 \<rparr>)) t)) (\<lambda>x. undefined) e")
     apply simp
     apply (subst simul_substitution)
      apply simp
      apply (subgoal_tac "fv (map_strategy (\<theta>(x1 := \<lparr>x1\<rparr>)) t) \<subseteq> {x1}")
       apply blast
    using map_strategy_closed apply auto[1]
     apply (simp add: fun_upd_def)
     apply (rule exec_mono_fv[simplified le_fun_def, rule_format])
     apply clarsimp
     apply (rule conjI)
      apply (simp add: fun_upd_def)
     apply (subgoal_tac " fv (map_strategy (\<lambda>x. if x = x1 then \<lparr>x1\<rparr> else \<theta> x) t) \<subseteq> {x1}")
      apply blast
     apply (rule map_strategy_closed)
     apply auto[1]
    apply (subst map_strategy_decomp)
      apply (simp add: map_strategy_closed)
     apply blast
    apply simp
    done
qed


lemma map_strategy_fixvar[simp]: "map_strategy (\<lambda>x. \<lparr> x \<rparr>) s = s" 
  by (induct s; simp)

text \<open>Computational soundness two for diverging executions\<close>
theorem div_soundness:
  assumes "fv s = {}"
  shows "(s, e) \<Up> \<Longrightarrow> Div \<in> PdToSet (exec s \<xi> e)"
  using div_soundness_lemma[where s = s and \<theta> = "\<lambda>x. \<lparr> x \<rparr>" and \<xi> = \<xi> ]
  apply -
  using assms apply simp
  apply (simp add: rel_def)
  done

section \<open>Computational adequacy two\<close>
lemma fixp_unfoldE[rule_format, rotated]:
  assumes "mono f" 
  shows   "P (\<mu> X. f X) \<longrightarrow> (P (f (\<mu> X. f X)) \<longrightarrow> R) \<longrightarrow> R" 
  apply (subst fixp_unfold)
  using assms apply simp
  by simp 

text \<open>Computational adequacy two for diverging executions\<close>
theorem div_adequacy:
  assumes "fv s = {}" 
    and "Div \<in> PdToSet (exec s (\<lambda>x. undefined) e)" 
  shows "(s,e) \<Up>"
  apply -
  apply (rule_tac X = "\<lambda>(s, e). fv s = {} \<and> Div \<in> PdToSet (exec s (\<lambda>x. undefined) e)" in big_step_div.coinduct)
   apply (simp split: prod.split)
  using assms apply simp
  apply (simp split: prod.split)
  apply (rename_tac x)
  apply (case_tac x)
  apply simp
  apply (rename_tac a b)
  apply (erule conjE)
  apply (case_tac a)
            apply simp
           apply simp
          apply simp
         apply simp
         apply (rename_tac x1)
         apply (case_tac "x1 b"; simp)
        apply (rename_tac x2 x3)
        apply simp
        apply (simp add: PdToSet_seq)
        apply (elim exE conjE disjE)
         apply (rule disjI2)
         apply (rule disjI2)
         apply simp
         apply (frule computational_adequacy, simp, simp)
         apply (rename_tac xa xb)
         apply (rule_tac x = xb in exI)
         apply simp
        apply simp
       apply (simp add: PdToSet_lc)
       apply (elim exE conjE disjE)
        apply simp
       apply (rule disjI2)
       apply (frule computational_adequacy, simp, simp)
       apply (rule disjI2)
       apply simp
      apply (simp add: PdToSet_choice)
      apply (elim exE conjE disjE)
       apply simp
      apply simp
     apply (simp add: PdToSet_one)
     apply blast
    apply (simp add: PdToSet_some)
    apply blast
   apply (simp add: PdToSet_all)
   apply blast
  apply simp
  apply (rename_tac x1 x2)
  apply (erule_tac f = "\<lambda>x. exec x2 ((\<lambda>x. undefined)(x1 := x))" and P = "\<lambda>m. Div \<in> PdToSet (m b)" in fixp_unfoldE)
   apply (rule disjI1)
   apply (subst substitution)
    apply simp
   apply simp
  using subst_var_empty apply simp
  apply (rule monoI)
  apply (rule exec_mono)
  by simp

subsection \<open>The semantic equivalence theorem\<close>
theorem sem_equivalence: 
  assumes "fv s = {}" 
  shows "PdToSet (exec s (\<lambda>x. undefined) e) = { r |r. (s,e) \<Down> r } \<union> { r |r. r = Div \<and> ((s,e) \<Up>) }"
  using assms 
  apply -
  apply (rule set_eqI)
  apply (rename_tac x)
  apply (rule iffI)
   apply simp
   apply (case_tac "x = Div")
    apply simp
  using div_adequacy apply auto[1]
  using computational_adequacy apply auto[1]
  apply clarsimp
  apply (erule disjE)
  using soundness apply simp
  apply clarsimp
  using div_soundness by simp
end
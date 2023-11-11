section \<open>Case Study: Lambda Calculus\<close>
theory LambdaCalc
imports WpSoundness SemanticsEquivalence
begin

(* The normalisation example in paper section 5.3 *)
abbreviation "Abs \<equiv> Node ABS (Leaf EMPTY)"
abbreviation "App l r \<equiv> Node APP l r"
abbreviation "Idd n \<equiv> Leaf (Var n)" (* Isabelle does not like Id to be used here *)

(* upshift @{text "t \<upharpoonleft> k"} moves all indices @{text "\<ge> k"} up by one, for when we go under a binder *)
fun deBruijn_upshift :: "exp \<Rightarrow> nat \<Rightarrow> exp" (infix "\<upharpoonleft>" 50) where
  "Idd n \<upharpoonleft> k = (if n \<ge> k then Idd (Suc n) else Idd n)" 
| "Abs t      \<upharpoonleft> k = Abs (t \<upharpoonleft> Suc k)"   
| "Node l t u \<upharpoonleft> k = Node l (t \<upharpoonleft> k) (u \<upharpoonleft> k)"
(* Ignore invalid leaf expressions *)
| "Leaf b       \<upharpoonleft> k = Leaf b" 

(* substitution @{term "t [\<downharpoonright> k := e ]"} replaces variable at index @{text "k"} with @{text "e"}, 
   and moves all indices greater than @{text "k"} down by one, as the index @{text "k"} is now gone. *)
fun deBruijn_subst :: "exp \<Rightarrow> exp \<Rightarrow> nat \<Rightarrow> exp" ("_[ _ \<setminus> _ ]" [50,0,0] 50 ) where 
  "Idd n [ e \<setminus> k ] = (if n = k then e else 
                             if n > k then Idd (n - 1) 
                             else Idd n)"
| "Abs t      [ e \<setminus> k ] = Abs (t [ e \<upharpoonleft> 0 \<setminus> Suc k ])"
| "Node l t u [ e \<setminus> k ] = Node l (t [ e \<setminus> k ]) (u [ e \<setminus> k ])"
(* Ignore invalid leaf expressions *)
| "Leaf b     [ e \<setminus> k ] = Leaf b"

(* downshift @{text "t \<downharpoonright> k"} is a partial operation that requires that the term @{text "t"} does not 
   mention the variable at index @{text "k"}. It moves all indices @{text "> k"} down by one. *)
fun deBruijn_downshift :: "exp \<Rightarrow> nat \<Rightarrow> exp option" (infix "\<downharpoonright>" 50) where
  "Idd n \<downharpoonright> k = (if n = k then None 
                              else Some (Idd (if n > k then n - 1 else n)))"
| "Abs t      \<downharpoonright> k = map_option Abs (t \<downharpoonright> Suc k)"
| "Node l t u \<downharpoonright> k = (case t \<downharpoonright> k of None \<Rightarrow> None | Some t' \<Rightarrow> map_option (Node l t') (u \<downharpoonright> k))"
(* Ignore invalid leaf expressions *)
| "Leaf  b       \<downharpoonright> k = Some (Leaf b)"

(* A quick proof to ensure that substituting an unmentioned variable is the same as downshifting
   to remove the unmentioned variable *)
lemma sanity_check : "x \<downharpoonright> k = Some y \<Longrightarrow> x [ e \<setminus> k ] = y" 
proof (induct x k arbitrary: y e rule: deBruijn_downshift.induct)
qed (auto split: option.split_asm)

(* An expression is a well-formed lambda term if it only uses the Abs and App labels in the right way,
   and it only mentions variable indices that are in scope. The context number 'n' indicates how many 
   variables are in scope.*) 
inductive wf_lambda :: "nat \<Rightarrow> exp \<Rightarrow> bool" ("_ \<turnstile> _ wf" [50,0] 50) where 
  "\<lbrakk> k < n                \<rbrakk> \<Longrightarrow> n \<turnstile> Idd k wf" 
| "\<lbrakk> Suc n \<turnstile> t wf        \<rbrakk> \<Longrightarrow> n \<turnstile> Abs t wf"
| "\<lbrakk> n \<turnstile> t wf; n \<turnstile> u wf \<rbrakk> \<Longrightarrow> n \<turnstile> App t u wf" 


(* You can bump up the number of available variables without affecting wellformedness *)
lemma wf_bump:
  assumes "n \<turnstile> t wf" 
  and     "n \<le> n'"
  shows   "n' \<turnstile> t wf" 
  using assms 
  proof (induct arbitrary: n' rule: wf_lambda.induct)
  qed (auto intro: wf_lambda.intros) 

(* Our upshift operation preserves wellformedness *)
lemma wf_upshift: 
  assumes "n \<turnstile> t wf" 
  shows   "Suc n \<turnstile> t \<upharpoonleft> k wf" 
  using assms 
  proof (induct arbitrary: k rule: wf_lambda.induct)
  qed (auto intro: wf_lambda.intros)

(* Our substitution operation preserves wellformedness *)
lemma wf_subst: 
  assumes "Suc n \<turnstile> t wf"
  and     "n \<turnstile> e wf" 
  and     "k < Suc n" 
  shows   "n \<turnstile> t [ e \<setminus> k ] wf" 
  using assms 
  proof (induct "Suc n" t arbitrary: n k e rule: wf_lambda.induct)
  qed (auto intro: wf_lambda.intros simp: wf_upshift)

(* Our downshift operation preserves wellformedness *)
lemma wf_downshift: 
  assumes "Suc n \<turnstile> t wf"
  and     "k < Suc n"
  and     "t \<downharpoonright> k = Some t'"
  shows   "n \<turnstile> t' wf" 
  using assms 
  proof (induct "Suc n" t arbitrary: n k t' rule: wf_lambda.induct)
  qed (auto split: if_split_asm option.split_asm intro!: wf_lambda.intros)


(* These functions could be used as atomic strategies *)
fun beta :: "exp \<Rightarrow> exp option"  where
  "beta (App (Abs f) e) = Some (f [ e \<setminus> 0 ])" 
| "beta _ = None"

fun eta :: "exp \<Rightarrow> exp option" where 
  "eta (Abs (App f (Idd 0))) = (f \<downharpoonright> 0)"
| "eta _ = None"


(* Some helpers to simplify reasoning about repeat and topdown, avoiding
   the need to think about environments for those combinators. *)
lemma wp_env_irrelevant: 
  assumes "\<forall>y \<in> fv s. \<forall>t. env1 (y , t) = env2 (y , t)" 
  shows "wp     s loc P env1 = wp     s loc P env2"
  and   "wp_err s loc P env1 = wp_err s loc P env2"
using assms proof (induct s arbitrary: loc P env1 env2)
  case (Seq s1 s2)
  {
    case 1
    then show ?case using Seq[where ?env1.0 = env1 and ?env2.0 = env2] by simp
  next
    case 2
    then show ?case using Seq[where ?env1.0 = env1 and ?env2.0 = env2] by simp
  }
next
  case (Left_Choice s1 s2)
  {
    case 1
    then show ?case using Left_Choice[where ?env1.0 = env1 and ?env2.0 = env2] by simp
  next
    case 2
    then show ?case using Left_Choice[where ?env1.0 = env1 and ?env2.0 = env2] by simp
  }
next
  case (Choice s1 s2)
  {
    case 1
    then show ?case using Choice[where ?env1.0 = env1 and ?env2.0 = env2] by simp
  next
    case 2
    then show ?case using Choice[where ?env1.0 = env1 and ?env2.0 = env2] by simp
  }
next
  case (One s)
  {
    case 1
    then show ?case using One[where ?env1.0 = env1 and ?env2.0 = env2] by simp
  next
    case 2
    then show ?case using One[where ?env1.0 = env1 and ?env2.0 = env2] by simp
  }
next
  case (CSome s)
  {
    case 1
    then show ?case using CSome[where ?env1.0 = env1 and ?env2.0 = env2] by simp
  next
    case 2
    then show ?case using CSome[where ?env1.0 = env1 and ?env2.0 = env2] by simp
  }
next
  case (All s)
  {
    case 1
    then show ?case using All[where ?env1.0 = env1 and ?env2.0 = env2] by simp
  next
    case 2
    then show ?case using All[where ?env1.0 = env1 and ?env2.0 = env2] by simp
  }
next
  case (Mu x1 s)
  {
    case 1
    then show ?case 
      apply simp
      apply (subgoal_tac "\<And>x loc P. wp s loc P (env1((x1, Tot) := fst x, (x1, Par) := snd x))
                                   = wp s loc P (env2((x1, Tot) := fst x, (x1, Par) := snd x))")
      apply (subgoal_tac "\<And>x loc P. wp_err s loc P (env1((x1, Tot) := fst x, (x1, Par) := snd x))
                                   = wp_err s loc P (env2((x1, Tot) := fst x, (x1, Par) := snd x))")
        apply simp
       apply (rule Mu(2))
       apply clarsimp
       apply (rename_tac t)
       apply (case_tac t; simp)
      apply (rule Mu(1))
      apply clarsimp
      apply (rename_tac t)
      by (case_tac t; simp)
  next
    case 2
    then show ?case
      apply simp
      apply (subgoal_tac "\<And>x loc P. wp s loc P (env1((x1, Tot) := fst x, (x1, Par) := snd x))
                                   = wp s loc P (env2((x1, Tot) := fst x, (x1, Par) := snd x))")
      apply (subgoal_tac "\<And>x loc P. wp_err s loc P (env1((x1, Tot) := fst x, (x1, Par) := snd x))
                                   = wp_err s loc P (env2((x1, Tot) := fst x, (x1, Par) := snd x))")
        apply simp
       apply (rule Mu(2))
       apply clarsimp
       apply (rename_tac t)
       apply (case_tac t; simp)
      apply (rule Mu(1))
      apply clarsimp
      apply (rename_tac t)
      by (case_tac t; simp)
  }
qed auto

(* This lemma gives a simpler presentation of the wp/wp_err of repeat. It's just what you 
   get if you expand the definition of repeat and remove all the Rep_pt/Abs_pt stuff *)
lemma wp_wp_err_repeat:
  assumes "0 \<notin> fv s"
  shows "wp (repeat s) loc P env = (\<mu> X. wp s loc X env \<union> wp_err s loc X env \<inter> (P \<inter> defined loc))
       \<and> wp_err (repeat s) loc P env =  (\<mu> X. wp s loc X env \<union> wp_err s loc X env \<inter> (P \<inter> defined loc))"
  apply simp
  apply (rule parallel_fixp_induct)
      apply (rule admissible_conj)
       apply (rule ccpo.admissibleI)
       apply (simp  add: prod_Sup Sup_pt)
       apply (subst Abs_pt_inverse)
        apply simp
        apply (intro mono_intros)
       apply auto[1]
      apply (rule ccpo.admissibleI)
      apply (simp  add: prod_Sup Sup_pt)
      apply (subst Abs_pt_inverse)
       apply simp
       apply (intro mono_intros)
      apply auto[1]
     apply (simp add: prod_Sup Sup_pt)
     apply (subst Abs_pt_inverse)
      apply simp
      apply (intro mono_intros)
     apply simp
    apply (intro mono_intros)
   apply (intro mono_intros)
  apply simp
  apply (rename_tac x)
  apply (subst Abs_pt_inverse)
   apply simp
   apply (intro mono_intros)
  apply (subgoal_tac " wp s loc (Rep_pt (fst x loc) P) (env((0, Tot) := fst x, (0, Par) := snd x))
                    =  wp s loc (Rep_pt (fst x loc) P) env")
  apply (subgoal_tac " wp_err s loc (Rep_pt (snd x loc) P) (env((0, Tot) := fst x, (0, Par) := snd x))
                    =  wp_err s loc (Rep_pt (fst x loc) P) env")
    apply simp
   apply simp
   apply (rule wp_env_irrelevant)
  using assms apply auto[1]
  apply (rule wp_env_irrelevant)
  using assms by auto

lemma wp_repeat:
  assumes "0 \<notin> fv s" 
  shows "wp (repeat s) loc P env = (\<mu> X. wp s loc X env \<union> wp_err s loc X env \<inter> (P \<inter> defined loc))"
  using wp_wp_err_repeat assms by blast

lemma wp_err_repeat:
  assumes "0 \<notin> fv s" 
  shows "wp_err (repeat s) loc P env = (\<mu> X. wp s loc X env \<union> wp_err s loc X env \<inter> (P \<inter> defined loc))"
  using wp_wp_err_repeat assms by blast


(* This lemma gives a simpler presentation of the wp/wp_err of topDown. It's just what you 
   get if you expand the definition of topDown and remove all the Rep_pt/Abs_pt stuff *)
lemma wp_wp_err_topDown:
  assumes "0 \<notin> fv s" 
  shows "\<forall> loc. wp (topDown s) loc P env 
      = fst (\<mu> x. (\<lambda>loc. wp s loc P env \<union>
                             wp_err s loc P env \<inter>
                             (snd x (loc\<triangleright>pos.Left) \<inter> fst x (loc\<triangleright>pos.Right)
                            \<union> fst x (loc\<triangleright>pos.Left) \<inter> snd x (loc\<triangleright>pos.Right)),
                 \<lambda>loc.  wp s loc P env \<union>
                             wp_err s loc P env \<inter>
                             ({uu \<in> defined loc. \<exists>x. lookup loc uu = exp.Leaf x} \<union>
                               snd x (loc\<triangleright>pos.Left) \<inter> snd x (loc\<triangleright>pos.Right))))
        loc
 \<and>  wp_err (topDown s) loc P env 
      = snd (\<mu> x. (\<lambda>loc. wp s loc P env \<union>
                           wp_err s loc P env \<inter>
                             (snd x (loc\<triangleright>pos.Left) \<inter> fst x (loc\<triangleright>pos.Right)
                            \<union> fst x (loc\<triangleright>pos.Left) \<inter> snd x (loc\<triangleright>pos.Right)),
                   \<lambda>loc. wp s loc P env \<union>
                           wp_err s loc P env \<inter>
                             ({uu \<in> defined loc. \<exists>x. lookup loc uu = exp.Leaf x}
                            \<union> snd x (loc\<triangleright>pos.Left) \<inter> snd x (loc\<triangleright>pos.Right))))
        loc
    " 
  apply (simp add: TopDown_def)
  apply (rule parallel_fixp_induct)
  apply (rule admissible_all)
  apply (rule admissible_conj)
       apply (rule ccpo.admissibleI)
       apply (simp add: prod_Sup Sup_pt)
       apply (subst Abs_pt_inverse)
        apply (simp, intro mono_intros)
       apply simp
      apply (rule ccpo.admissibleI)
      apply (simp add: prod_Sup Sup_pt)
      apply (subst Abs_pt_inverse)
       apply (simp, intro mono_intros)
      apply simp
     apply (simp add: prod_Sup Sup_pt)
     apply (subst Abs_pt_inverse)
      apply (simp, intro mono_intros)
     apply simp
    apply (intro mono_intros)
   apply (intro mono_intros)
  apply (rename_tac x y)
  apply (subgoal_tac "\<And> loc P. wp s loc P (env((0, Tot) := fst x, (0, Par) := snd x)) = wp s loc P env")
  apply (subgoal_tac "\<And> loc P. wp_err s loc P (env((0, Tot) := fst x, (0, Par) := snd x)) = wp_err s loc P env")
  apply (simp add: fun_upd_def)
  apply (subst Abs_pt_inverse)
   apply (simp, intro mono_intros)
  apply (subst Abs_pt_inverse)
   apply (simp, intro mono_intros)
    apply clarsimp
   apply (rule wp_env_irrelevant)
  using assms apply auto[1]
   apply (rule wp_env_irrelevant)
  using assms by auto[1]

lemma wp_topDown:
  assumes "0 \<notin> fv s" 
  shows "wp (topDown s) loc P env 
      = fst (\<mu> x. (\<lambda>loc. wp s loc P env \<union>
                             wp_err s loc P env \<inter>
                             (snd x (loc\<triangleright>pos.Left) \<inter> fst x (loc\<triangleright>pos.Right)
                            \<union> fst x (loc\<triangleright>pos.Left) \<inter> snd x (loc\<triangleright>pos.Right)),
                 \<lambda>loc.  wp s loc P env \<union>
                             wp_err s loc P env \<inter>
                             ({uu \<in> defined loc. \<exists>x. lookup loc uu = exp.Leaf x} \<union>
                               snd x (loc\<triangleright>pos.Left) \<inter> snd x (loc\<triangleright>pos.Right))))
        loc"
  using assms wp_wp_err_topDown by simp

lemma wp_err_topDown:
  assumes "0 \<notin> fv s" 
  shows "wp_err (topDown s) loc P env 
      = snd (\<mu> x. (\<lambda>loc. wp s loc P env \<union>
                             wp_err s loc P env \<inter>
                             (snd x (loc\<triangleright>pos.Left) \<inter> fst x (loc\<triangleright>pos.Right)
                            \<union> fst x (loc\<triangleright>pos.Left) \<inter> snd x (loc\<triangleright>pos.Right)),
                 \<lambda>loc.  wp s loc P env \<union>
                             wp_err s loc P env \<inter>
                             ({uu \<in> defined loc. \<exists>x. lookup loc uu = exp.Leaf x} \<union>
                               snd x (loc\<triangleright>pos.Left) \<inter> snd x (loc\<triangleright>pos.Right))))
        loc"
  using assms wp_wp_err_topDown by simp

(* Omega is the term (\<lambda>x. (x x)) (\<lambda>x. (x x)), which \<beta>-reduces to itself *)
definition Omega :: exp where
"Omega = App (Abs (App (Idd 0) (Idd 0))) (Abs (App (Idd 0) (Idd 0)))"

lemma beta_omega[simp]: "beta Omega = Some Omega"
  by (simp add: Omega_def)
lemma eta_omega[simp]: "eta Omega = None"
  by (simp add: Omega_def)

(* Normalise is just repeat composed with topDown *)
definition normalise :: "strategy \<Rightarrow> strategy" where
"normalise s = repeat (topDown s)"

(* Section 5.3 Omega is not in the wp of normalise(beta/eta) (for any postcondition), because it diverges.
   This is shown by Scott induction. *)
theorem omega_bad : "Omega \<notin> wp (normalise (\<llangle> beta \<rrangle> <+ \<llangle> eta \<rrangle>)) \<epsilon> P env"
  unfolding normalise_def
  apply (subst wp_repeat)
   apply (simp add: TopDown_def)
  apply (rule fixp_induct)
     apply (rule ccpo.admissibleI, simp)
    apply (intro mono_intros)
   apply simp
  apply (subst wp_topDown, simp)
  apply (subst wp_err_topDown, simp)
  apply (subst fixp_unfold, intro mono_intros)
  apply clarsimp
  apply (intro conjI)
     apply blast
    apply blast
   apply blast
  apply (subst fixp_unfold, intro mono_intros)
  by auto 

definition betaEtaNormalForm :: "exp \<Rightarrow> bool" where
"betaEtaNormalForm e = (\<forall> l. e \<in> defined l \<longrightarrow> beta (lookup l e) = None \<and> eta (lookup l e) = None)"

(* The next 4 lemmas are just handling individual reduction steps for our long normalisation 
   example below. All of them are trivial and could be proved automatically by a tactic that just 
   intelligently decides how much to unfold a fixp operator, but for now we just do it by hand. *)
lemma top_topDown : 
  assumes "0 \<notin> fv s"
  shows "x \<in> wp s \<epsilon> P env \<Longrightarrow> x \<in> wp (topDown s) \<epsilon> P env"
  apply (subst wp_topDown)
   apply (simp add: assms)
  apply (subst fixp_unfold, intro mono_intros)
  by simp

lemma descendRRRL: 
  assumes "eta (Abs (App (Idd n) (App e (Idd m)))) = None" 
  and     "beta (App e (Idd m)) = None"
  and     "Abs (Abs (App (Idd n) (App e (Idd m)))) \<in> wp (\<llangle> beta \<rrangle> <+ \<llangle> eta \<rrangle>) (Right \<triangleleft> (Right \<triangleleft> (Right \<triangleleft> (Left \<triangleleft> \<epsilon>)))) P env"
shows     "Abs (Abs (App (Idd n) (App e (Idd m)))) \<in> wp (topDown (\<llangle> beta \<rrangle> <+ \<llangle> eta \<rrangle>)) \<epsilon> P env"
  using assms 
  apply (subst wp_topDown, simp)
  apply (subst fixp_unfold, intro mono_intros, simp)
  apply (rule disjI2, rule disjI1, rule conjI)
   apply (subst fixp_unfold, intro mono_intros, simp)
  apply (subst fixp_unfold, intro mono_intros, simp)
  apply (rule disjI2, rule disjI1, rule conjI)
   apply (subst fixp_unfold, intro mono_intros, simp)
  apply (subst fixp_unfold, intro mono_intros, simp)
  apply (rule disjI2, rule disjI1, rule conjI)
   apply (subst fixp_unfold, intro mono_intros, simp)
  apply (subst fixp_unfold, intro mono_intros, simp)
  apply (rule disjI2, rule disjI2, rule conjI)
   apply (subst fixp_unfold, intro mono_intros, simp)
  apply (subst fixp_unfold, intro mono_intros, simp)
  done


lemma descendRRR: 
  assumes "eta (Abs (App (Idd n) e)) = None" 
  and     "Abs (Abs (App (Idd n) e)) \<in> wp (\<llangle> beta \<rrangle> <+ \<llangle> eta \<rrangle>) (Right \<triangleleft> (Right \<triangleleft> (Right \<triangleleft>  \<epsilon>))) P env"
  shows   "Abs (Abs (App (Idd n) e)) \<in> wp (topDown (\<llangle> beta \<rrangle> <+ \<llangle> eta \<rrangle>)) \<epsilon> P env"
  using assms 
  apply (subst wp_topDown, simp)
  apply (subst fixp_unfold, intro mono_intros, simp)
  apply (rule disjI2, rule disjI1, rule conjI)
   apply (subst fixp_unfold, intro mono_intros, simp)
  apply (subst fixp_unfold, intro mono_intros, simp)
  apply (rule disjI2, rule disjI1, rule conjI)
   apply (subst fixp_unfold, intro mono_intros, simp)
  apply (subst fixp_unfold, intro mono_intros, simp)
  apply (rule disjI2, rule disjI1, rule conjI)
   apply (subst fixp_unfold, intro mono_intros, simp)
  apply (subst fixp_unfold, intro mono_intros, simp)
  done

lemma term_normalised: "Abs (Abs (App (Idd (Suc 0)) (App (Idd (Suc 0)) (Idd 0))))
    \<in> wp_err (topDown (\<llangle>beta\<rrangle><+ \<llangle>eta\<rrangle>)) \<epsilon> P env" 
  apply (subst wp_err_topDown)
   apply simp
  apply (subst fixp_unfold, intro mono_intros, simp)
  apply (rule disjI2, intro conjI)
   apply (subst fixp_unfold, intro mono_intros, simp)
  apply (subst fixp_unfold, intro mono_intros, simp)
  apply (rule disjI2, intro conjI)
   apply (subst fixp_unfold, intro mono_intros, simp)
  apply (subst fixp_unfold, intro mono_intros, simp)
  apply (rule disjI2, intro conjI)
   apply (subst fixp_unfold, intro mono_intros, simp)
  apply (subst fixp_unfold, intro mono_intros, simp)
  apply (rule disjI2, intro conjI)
   apply (subst fixp_unfold, intro mono_intros, simp)
  apply (subst fixp_unfold, intro mono_intros, simp)
  done

(* Section 5.3  A longer example of beta-eta normalisation *)
(* (\<lambda>n \<lambda>f \<lambda>x. f (n f x)) (\<lambda>f \<lambda>x. f x) is left by normalise(beta/eta) in beta-eta normal form *)
theorem long_exp_good : "App (Abs (Abs (Abs (App (Idd 1) (App (App (Idd 2) (Idd 1)) (Idd 0))))))
                (Abs (Abs (App (Idd 1) (Idd 0)))) 
     \<in> wp (normalise (\<llangle> beta \<rrangle> <+ \<llangle> eta \<rrangle>)) \<epsilon> {e | e. betaEtaNormalForm e } env"
  unfolding betaEtaNormalForm_def normalise_def
  apply (subst wp_repeat)
   apply (simp add: TopDown_def)
  apply (subst fixp_unfold, intro mono_intros)
  apply (rule UnI1)
  apply (rule top_topDown)
   apply simp
  apply simp
  apply (rule disjI1)
  apply (rule imageI)
  apply (subst fixp_unfold, intro mono_intros)
  apply (rule UnI1)
  apply (rule descendRRRL, simp)
   apply simp
  apply simp
  apply (rule disjI1)
  apply (rule imageI)
  apply (subst fixp_unfold, intro mono_intros)
  apply (rule UnI1)
  apply (rule descendRRR, simp)
   apply simp
  apply simp
  apply (rule disjI1)
  apply (rule imageI)
  apply (subst fixp_unfold, intro mono_intros)
  apply simp
  apply (rule disjI2)
  apply (rule conjI)
   apply (rule term_normalised)
  apply (clarsimp)
  apply (rename_tac l)
  apply (case_tac l; simp)
  apply (rename_tac x21 x22)
  apply (case_tac x21; case_tac x22; simp)
   apply (rename_tac x21a x22a)
   apply (case_tac x21a;simp)
  apply (rename_tac x21a x22a)
  apply (case_tac x21a; simp; case_tac x22a; simp)
   apply (rename_tac x21b x22b)
   apply (case_tac x21b;simp)
  apply (rename_tac x21b x22b)
  apply (case_tac x21b; simp; case_tac x22b; simp)
   apply (rename_tac x21c x22c)
   apply (case_tac x21c; simp)
  apply (rename_tac x21c x22c)
  apply (case_tac x21c; simp; case_tac x22c; simp)
   apply (rename_tac x21d x22d)
   apply (case_tac x21d;simp)
  apply (rename_tac x21d x22d)
  apply (case_tac x21d;simp)
  done
end


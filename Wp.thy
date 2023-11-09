section \<open>The location-based weakest precondition calculus\<close>

theory Wp
  imports CCPO Denotational MonoDenotational
begin

datatype tag = Tot | Par
datatype pos = Left | Right
datatype location = empty ("\<epsilon>") | Lcons pos location ("_\<triangleleft>_"  [60, 61] 60)

fun append :: "location \<Rightarrow> pos \<Rightarrow> location" ("_\<triangleright>_"  [60, 61] 60)
  where
    "append \<epsilon> p = p \<triangleleft> \<epsilon>"
  | "append (i \<triangleleft> loc) p = i \<triangleleft> (append loc p) "


text 
 \<open> A predicate transformer is internally just a function from a set of expressions to a set of 
   expressions, with a side condition that it is monotonic \<close>
typedef pt = "{pt::exp set \<Rightarrow> exp set. mono pt}"
  by (simp add: mono_def, rule_tac x = "\<lambda>x. x" in exI, simp)

text
 \<open> For predicate transformers a and b, a \<le> b not only requires that they are equal pointwise, but 
   also that a and b are both monotonic \<close> 
instantiation pt :: ccpo begin
definition less_eq_pt : 
  "(a :: pt) \<le> b \<longleftrightarrow> mono (Rep_pt a) \<and>  mono (Rep_pt b) \<and> (\<forall>x. Rep_pt a x \<subseteq> Rep_pt b x)"
definition less_pt [simp] : 
  "(a :: pt) < b \<longleftrightarrow> a \<le> b \<and> \<not> (b \<le> a)" 
definition Sup_pt : 
  "Sup (A :: pt set) \<equiv> Abs_pt (\<lambda>x. \<Union>t\<in>A. Rep_pt t x)"

lemma bigU_mono [simp]:
  assumes "\<forall> x \<in> A. mono x" 
  shows "mono (\<lambda>x. \<Union>t \<in> A. t x)"
  using assms
  unfolding mono_def
  by fast

instance 
  apply (intro_classes)
       apply (simp)
      using Rep_pt less_eq_pt apply force
     using less_eq_pt apply fastforce
    apply (metis Rep_pt_inject le_fun_def less_eq_pt order_class.order_eq_iff)
   apply (smt (verit, del_insts) Abs_pt_inverse Rep_pt SUP_mono' Sup_pt UN_iff less_eq_pt mem_Collect_eq monoD monoI subsetI)
    apply (simp add: Sup_pt less_eq_pt)
     apply (subst Abs_pt_inverse, simp)
    apply (metis (mono_tags, lifting) Rep_pt SUP_mono' mem_Collect_eq monoI monotoneD)
    by (smt (verit, ccfv_threshold) Abs_pt_inverse Rep_pt UN_iff mem_Collect_eq monoD monoI subsetD subsetI)

(* if smt shoudl be avoided, use the following. * )
      apply (simp add: Sup_pt less_eq_pt)
     apply (subst Abs_pt_inverse, simp)
       apply (metis (no_types, lifting) Rep_pt SUP_mono' mem_Collect_eq monoD monoI)
       apply (intro conjI)   
        apply (rule Rep_pt[simplified])
     apply (metis (mono_tags, lifting) Rep_pt SUP_mono' mem_Collect_eq monoI monotoneD)
     apply (metis (no_types, lifting) Abs_pt_inverse Rep_pt SUP_mono' UN_I mem_Collect_eq monoD monoI subsetI) 
     apply (simp add: less_eq_pt Sup_pt)
       apply (subst Abs_pt_inverse, simp)
      apply (metis (no_types, lifting) Rep_pt SUP_mono' mem_Collect_eq monoD monoI)
     apply(intro conjI)
     apply (metis (no_types, lifting) Rep_pt SUP_mono' mem_Collect_eq monoD monoI)
     using Rep_pt apply blast
     apply clarsimp
     apply (rule, simp_all)
     apply (subst Abs_pt_inverse, simp)
     apply (metis (no_types, lifting) CollectD Rep_pt SUP_mono' monoD monoI)
     by blast
*)
end

text
 \<open> In the environment, we use the pt type to add the side condition we need that 
   every function in the environment is monotone \<close>
type_synonym lenv = "var \<times> tag \<Rightarrow> location \<Rightarrow> pt "

subsection \<open>Helper functions\<close>
fun update :: "location \<Rightarrow> exp \<Rightarrow> exp_err_div set \<Rightarrow> exp_err_div set" 
  where
    "update \<epsilon> e xs = xs"
  | "update (i\<triangleleft>loc) (Leaf l) xs = undefined"
  | "update (Left\<triangleleft>loc) (Node l e1 e2) xs = {E (Node l x e2) | x. E x \<in> (update loc e1 xs)} \<union> (xs \<inter> {Div, Err})"
  | "update (Right\<triangleleft>loc) (Node l e1 e2) xs = {E (Node l e1 x) | x. E x \<in> (update loc e2 xs)} \<union> (xs \<inter> {Div, Err})"

fun lookup :: "location \<Rightarrow> exp \<Rightarrow> exp"
  where
    "lookup \<epsilon> e = e"
  | "lookup (i\<triangleleft>loc) (Leaf l) = undefined"
  | "lookup (Left\<triangleleft>loc) (Node l e1 e2) = lookup loc e1"
  | "lookup (Right\<triangleleft>loc) (Node l e1 e2) = lookup loc e2"

fun defined :: "location \<Rightarrow> exp set"
  where
    "defined \<epsilon> = UNIV"
  | "defined (Left\<triangleleft>loc) = {Node l e1 e2 | l e1 e2. e1 \<in> defined loc}"
  | "defined (Right\<triangleleft>loc) = {Node l e1 e2 | l e1 e2. e2 \<in> defined loc}"

subsection \<open>Weakest must succeed and weakest may fail preconditions\<close>
fun wp_err :: "strategy \<Rightarrow> location \<Rightarrow> exp set \<Rightarrow> lenv \<Rightarrow> exp set" and wp :: "strategy \<Rightarrow> location \<Rightarrow> exp set \<Rightarrow> lenv \<Rightarrow> exp set"
  where
    "wp_err SKIP loc P env = P \<inter> (defined loc)"
  | "wp SKIP loc P env = P \<inter> (defined loc)"
  | "wp_err ABORT loc P env = defined loc"
  | "wp ABORT loc P env = {}"
  | "wp_err \<llangle>atomic\<rrangle> loc P env = {e | e. e \<in> (defined loc) 
                        \<and> (update loc e (PdToSet (exec \<llangle>atomic\<rrangle> (\<lambda> X. undefined) (lookup loc e)))) \<subseteq> E ` P \<union> {Err}}"
  | "wp \<llangle>atomic\<rrangle> loc P env = {e | e. e \<in> (defined loc) 
                        \<and> (update loc e (PdToSet (exec \<llangle>atomic\<rrangle> (\<lambda> X. undefined) (lookup loc e)))) \<subseteq> E ` P}"
  | "wp_err (s1 ;; s2) loc P env = wp_err s1 loc (wp_err s2 loc P env) env"
  | "wp (s1 ;; s2) loc P env = wp s1 loc (wp s2 loc P env) env"
  | "wp_err (s1 <+ s2) loc P env = wp s1 loc P env \<union> (wp_err s1 loc P env \<inter> wp_err s2 loc P env)"
  | "wp (s1 <+ s2) loc P env = wp s1 loc P env \<union> (wp_err s1 loc P env \<inter> wp s2 loc P env)"
  | "wp_err (s1 >< s2) loc P env =  wp_err s1 loc P env \<inter> wp_err s2 loc P env"
  | "wp (s1 >< s2) loc P env = (wp s1 loc P env \<inter> wp_err s2 loc P env) \<union> (wp_err s1 loc P env \<inter> wp s2 loc P env)"
  | "wp_err (one s) loc P env = {e | e x. e \<in> defined loc \<and> lookup loc e = Leaf x } \<union> (wp_err s (loc \<triangleright> Left) P env \<inter> wp_err s (loc \<triangleright> Right) P env)"
  | "wp (one s) loc P env = (wp_err s (loc \<triangleright> Left) P env \<inter> wp s (loc \<triangleright> Right) P env) \<union> (wp s (loc \<triangleright> Left) P env \<inter> wp_err s (loc \<triangleright> Right) P env)"
(* wp and wp_err for the leaf case are like SKIP *)
  | "wp_err (all s) loc P env = (P \<inter> {e | e x. e \<in> defined loc \<and> lookup loc e = Leaf x}) \<union> (wp_err s (loc \<triangleright> Left) (wp_err s (loc \<triangleright> Right) P env) env \<inter> wp_err s (loc \<triangleright> Right) (wp_err s (loc \<triangleright> Left) P env) env)"
  | "wp (all s) loc P env = (P \<inter> {e | e x. e \<in> defined loc \<and> lookup loc e = Leaf x})
                            \<union> wp s (loc \<triangleright> Left) (wp s (loc \<triangleright> Right) P env) env \<union> wp s (loc \<triangleright> Right) (wp s (loc \<triangleright> Left) P env) env"
  | "wp_err (some s) loc P env = {e | e x. e \<in> defined loc \<and> lookup loc e = Leaf x } \<union> 
                              (wp_err s (loc \<triangleright> Left) (wp_err s (loc \<triangleright> Right) P env) env
                              \<inter> wp_err s (loc \<triangleright> Right) (wp_err s (loc \<triangleright> Left) P env) env
                              \<inter> (wp_err s (loc \<triangleright> Left) P env \<union> wp_err s (loc \<triangleright> Left) (wp s (loc \<triangleright> Right) P env) env)
                              \<inter> (wp_err  s (loc \<triangleright> Right) P env \<union> wp_err s (loc \<triangleright> Right) (wp s (loc \<triangleright> Left) P env) env))"
  | "wp (some s) loc P env = wp s (loc \<triangleright> Left) (wp s (loc \<triangleright> Right) P env) env
                           \<union> wp s (loc \<triangleright> Right) (wp s (loc \<triangleright> Left) P env) env
                           \<union> (wp s (loc \<triangleright> Left) P env \<inter> wp s (loc \<triangleright> Left) (wp_err s (loc \<triangleright> Right) P env) env)
                           \<union> (wp s (loc \<triangleright> Right) P env \<inter> wp s (loc \<triangleright> Right) (wp_err s (loc \<triangleright> Left) P env) env)
                        "
    (* Fixed points and variables are computed with the pt type, not functions from sets to sets, because we need to carry around 
   monotonicity side conditions. *)
  | "wp \<lparr>X\<rparr> loc P env = Rep_pt (env (X, Tot) loc) P"
  | "wp_err \<lparr>X\<rparr> loc P env = Rep_pt (env (X, Par) loc) P"
  | "wp (mu X. s) loc P env = Rep_pt (fst 
          (\<mu> Delta. ( (\<lambda>loc. Abs_pt (\<lambda> P. wp s loc P (env((X, Tot) := fst Delta, (X, Par) := snd Delta)))),
                      (\<lambda>loc. Abs_pt (\<lambda>P. wp_err s loc P (env((X, Tot) := fst Delta, (X, Par) := snd Delta))))
                    )) loc) P" 
  | "wp_err (mu X. s) loc P env = Rep_pt (snd 
          (\<mu> Delta. ( (\<lambda>loc. Abs_pt (\<lambda> P. wp s loc P (env((X, Tot) := fst Delta, (X, Par) := snd Delta)))),
                      (\<lambda>loc. Abs_pt (\<lambda>P. wp_err s loc P (env((X, Tot) := fst Delta, (X, Par) := snd Delta))))
                    )) loc) P" 


subsection \<open> Monotonicity proofs for wp and wp_err \<close>

definition ap :: "('a \<Rightarrow> 'b) \<times> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> ('b \<times>'b)"
  where "ap \<equiv> \<lambda>fg a. (fst fg a, snd fg a)" 

theorem ap_mono: 
  assumes "\<forall>x y. x \<le> y \<longrightarrow> f x \<le> f' y" 
    and "\<forall>x y. (x::'a::ccpo) \<le> y \<longrightarrow> (g x::'b::ccpo) \<le> g' y" 
    and "x \<le> y"
  shows "ap (f, g) x \<le> ap (f', g') y"
  using assms 
  by (auto simp add: ap_def prod_less_eq)

lemma Sup_mono_two:
  "\<forall>x\<in>A. \<forall>P. (fst (fst x) P :: 'a :: ccpo) \<le> fst (snd x) P \<and> (snd (fst x) P :: 'b :: ccpo) \<le> snd (snd x) P \<Longrightarrow>
       Complete_Partial_Order.chain (\<le>) (fst ` A) \<Longrightarrow>
       Complete_Partial_Order.chain (\<le>) (snd ` A) \<Longrightarrow> 
       fst (fst (Sup A)) P \<le> fst (snd (Sup A)) P \<and> snd (fst (Sup A)) P \<le> snd (snd (Sup A))P"
  apply (simp add: prod_Sup)
  apply (frule chain_fst_exist)
  apply (drule chain_snd_exist)
  apply (frule chain_fst_exist)
  apply (drule chain_snd_exist)
  apply (rule)
   apply (subst Sup_below)
    apply (rule chain_imageI, simp, simp add: le_fun_def)
   apply clarsimp
  apply (metis (mono_tags, lifting) below_Sup chain_imageI fst_conv image_eqI le_funE)
  apply (subst Sup_below)
   apply (rule chain_imageI, simp, simp add: le_fun_def)
  apply clarsimp
  by (metis (mono_tags, lifting) below_Sup chain_imageI fst_conv image_eqI le_funE snd_conv)

lemma Sup_fst: "Sup (fst ` A) = fst (Sup A)" 
  by (simp add: prod_Sup)
lemma Sup_snd: "Sup (snd ` A) = snd (Sup A)" 
  apply (subst prod_Sup)
  apply simp
  done

theorem mu_wp_mono[rule_format]:
  assumes f_mono: "\<And> (env1 :: lenv) env2 loc. \<forall> loc p. env1 p loc \<le> env2 p loc \<Longrightarrow> f loc env1 \<le> f loc env2"
    and g_mono: "\<And> (env1 :: lenv) env2 loc. \<forall> loc p. env1 p loc \<le> env2 p loc \<Longrightarrow> g loc env1 \<le> g loc env2"
    and env_ordered: "\<forall>p loc. env1 p loc \<le> env2 p loc"
  shows "\<forall>loc. ap (\<mu> x. (\<lambda>loc. f loc (env1((x1, Tot) := fst x, (x1, Par) := snd x)),
                   \<lambda>loc. g loc (env1((x1, Tot) := fst x, (x1, Par) := snd x)))) loc
             \<le> ap (\<mu> x. (\<lambda>loc. f loc (env2((x1, Tot) := fst x, (x1, Par) := snd x)),
                   \<lambda>loc. g loc (env2((x1, Tot) := fst x, (x1, Par) := snd x)))) loc"
  apply (rule parallel_fixp_induct)
      apply (rule ccpo.admissibleI)
      apply (simp add: prod_Sup ap_def prod_less_eq)
      apply (rule allI)
      apply (rename_tac loc)
      apply (frule_tac P = loc in Sup_mono_two)
        apply (rule chain_fst_exist, simp)
       apply (rule chain_snd_exist, simp)
      apply (rule)
       apply (metis Sup_apply Sup_fst Sup_snd)
      apply (metis Sup_apply Sup_fst Sup_snd)
     apply (simp add: prod_Sup ap_def)
    apply (rule monoI)
    apply (simp add: prod_less_eq, rule)
     apply (clarsimp simp add: le_fun_def)
     apply (rule f_mono)
     apply (clarsimp intro!: le_funI)
    apply (clarsimp intro!: le_funI)
    apply (rule g_mono)
    apply clarsimp
    apply (simp add: le_fun_def less_eq_pt)
   apply (rule monoI)
   apply (simp add: prod_less_eq, rule)
    apply (clarsimp simp add: le_fun_def)
    apply (rule f_mono)
    apply (clarsimp intro!: le_funI)
   apply (clarsimp intro!: le_funI)
   apply (rule g_mono)
   apply (clarsimp intro!: le_funI)
   apply (simp add: le_fun_def less_eq_pt)
  apply (simp add: ap_def prod_less_eq)
  apply (rule)
  apply (rule conjI)
   apply (rule f_mono)
   apply (simp add: less_eq_pt)
   apply (intro conjI impI allI)
     apply (rule Rep_pt[simplified])
    apply (rule Rep_pt[simplified])
   apply (rule env_ordered[simplified less_eq_pt, rule_format, THEN conjunct2, THEN conjunct2, rule_format])
  apply (rule g_mono)
  apply clarsimp
  apply (rule env_ordered[rule_format])
  done

lemma ap_fstI:
  assumes "ap f P \<le> ap g Q" 
  shows "fst f P \<le> fst g Q" 
  using assms
  by (simp add: prod_less_eq ap_def split: prod.split)

lemma ap_sndI:
  assumes "ap f P \<le> ap g Q" 
  shows "snd f P \<le> snd g Q" 
  using assms
  by (simp add: prod_less_eq ap_def split: prod.split)

lemma Rep_pt_mono : 
  "a \<le> b \<Longrightarrow> Rep_pt a X \<le> Rep_pt b X"
  by (simp add: less_eq_pt)

(* wp and wp_err are monotone *)
theorem wp_wp_err_mono :
  assumes " \<forall> p loc. env1 p loc \<le> env2 p loc"
  shows "\<And> P.  wp s loc P env1 \<le>  wp s loc P env2" 
  and "\<And>P Q.  P \<subseteq> Q \<Longrightarrow>  wp s loc P env1 \<le>  wp s loc Q env1" 
  and "\<And>P. wp_err s loc P env1 \<le>  wp_err s loc P env2" 
  and "\<And>P Q.  P \<subseteq> Q \<Longrightarrow>  wp_err s loc P env1 \<le>  wp_err s loc Q env1" 
  using assms 
proof (induct s arbitrary: env1 env2 loc)
  case SKIP
  {
    case 1
    then show ?case by simp
  next
    case 2
    then show ?case by auto
  next
    case 3
    then show ?case by simp
  next
    case 4
    then show ?case by auto
  }
next
  case ABORT
  {
    case 1
    then show ?case by simp
  next
    case 2
    then show ?case by simp
  next
    case 3
    then show ?case by simp
  next
    case 4
    then show ?case by simp
  }
next
  case (FixVar x)
  {
    case 1
    then show ?case by (simp add: less_eq_pt)
  next
    case 2
    then show ?case by (simp add: less_eq_pt mono_def)
  next
    case 3
    then show ?case by (simp add: less_eq_pt mono_def)
  next
    case 4
    then show ?case  by (simp add: less_eq_pt mono_def)
  }
next
  case (Atomic x)
  {
    case 1
    then show ?case by simp
  next
    case 2
    then show ?case 
      apply (clarsimp split: option.split)
      by blast
  next
    case 3
    then show ?case by simp
  next
    case 4
    then show ?case 
      apply (clarsimp split: option.split)
      by blast
  }
next
  case (Seq s1 s2)
  {
    case 1
    then show ?case 
      apply simp
      apply (rule order_trans)
       apply (rule Seq(2); simp?)
       apply (rule Seq(5), simp)
      apply (rule Seq(1), simp)
      done
  next
    case 2
    then show ?case 
      apply simp
      apply (rule Seq(2))
       apply (rule Seq(6), simp)
       apply simp
      apply simp
      done      
  next
    case 3
    then show ?case 
      apply simp
      apply (rule order_trans)
       apply (rule Seq(4); simp?)
       apply (rule Seq(7), simp)
      apply (rule Seq(3), simp)
      done
  next
    case 4
    then show ?case 
      apply simp
      apply (rule Seq(4))
       apply (rule Seq(8), simp)
       apply simp
      apply simp
      done
  }
next
  case (Left_Choice s1 s2)
  {
    case 1
    then show ?case 
      apply (simp only: wp.simps)
      apply (rule Un_mono)
       apply (rule Left_Choice(1), simp)
      apply (rule Int_mono)
       apply (rule Left_Choice(3), simp)
      apply (rule Left_Choice(5), simp)
      done
  next
    case 2
    then show ?case 
      apply (simp only: wp.simps)
      apply (rule Un_mono)
       apply (rule Left_Choice(2), simp, simp)
      apply (rule Int_mono)
       apply (rule Left_Choice(4), simp, simp)
      apply (rule Left_Choice(6), simp, simp)
      done
  next
    case 3
    then show ?case 
      apply (simp only: wp_err.simps)
      apply (rule Un_mono)
       apply (rule Left_Choice(1), simp)
      apply (rule Int_mono)
       apply (rule Left_Choice(3), simp)
      apply (rule Left_Choice(7), simp)
      done
  next
    case 4
    then show ?case 
      apply (simp only: wp_err.simps)
      apply (rule Un_mono)
       apply (rule Left_Choice(2), simp, simp)
      apply (rule Int_mono)
       apply (rule Left_Choice(4), simp, simp)
      apply (rule Left_Choice(8), simp, simp)
      done
  }
next
  case (Choice s1 s2)
  {
    case 1
    then show ?case 
      apply (simp only: wp.simps)
      apply (rule Un_mono)
       apply (rule Int_mono)
        apply (rule Choice(1), simp)
       apply (rule Choice(7), simp)
      apply (rule Int_mono)
       apply (rule Choice(3), simp)
      apply (rule Choice(5), simp)
      done
  next
    case 2
    then show ?case 
      apply (simp only: wp.simps)
      apply (rule Un_mono)
       apply (rule Int_mono)
        apply (rule Choice(2), simp, simp)
       apply (rule Choice(8), simp, simp)
      apply (rule Int_mono)
       apply (rule Choice(4), simp, simp)
      apply (rule Choice(6), simp, simp)
      done
  next
    case 3
    then show ?case
      apply (simp only: wp_err.simps)
      apply (rule Int_mono)
       apply (rule Choice(3), simp)
      apply (rule Choice(7), simp)
      done
  next
    case 4
    then show ?case 
      apply (simp only: wp_err.simps)
      apply (rule Int_mono)
       apply (rule Choice(4), simp, simp)
      apply (rule Choice(8), simp, simp)
      done
  }
next
  case (One s)
  {
    case 1
    then show ?case 
      apply (simp only: wp.simps)
      apply (rule Un_mono)
       apply (rule Int_mono)
        apply (rule One(3), simp)
       apply (rule One(1), simp)
      apply (rule Int_mono)
       apply (rule One(1), simp)
      apply (rule One(3), simp)
      done
  next
    case 2
    then show ?case 
      apply (simp only: wp.simps)
      apply (rule Un_mono)
       apply (rule Int_mono)
        apply (rule One(4), simp, simp)
       apply (rule One(2), simp, simp)
      apply (rule Int_mono)
       apply (rule One(2), simp, simp)
      apply (rule One(4), simp, simp)
      done
  next
    case 3
    then show ?case
      apply (simp only: wp_err.simps)
      apply (rule Un_mono, simp)
      apply (rule Int_mono)
       apply (rule One(3), simp)
      apply (rule One(3), simp)
      done
  next
    case 4
    then show ?case
      apply (simp only: wp_err.simps)
      apply (rule Un_mono, simp)
      apply (rule Int_mono)
       apply (rule One(4), simp, simp)
      apply (rule One(4), simp, simp)
      done
  }
next
  case (CSome s)
  {
    case 1
    then show ?case 
      apply (simp only: wp.simps)
      apply (rule Un_mono)
       apply (rule Un_mono)
        apply (rule Un_mono)
         apply (rule order_trans)
          apply (rule CSome(1), simp)
         apply (rule CSome(2), simp)
          apply (rule CSome(1), simp)
         apply auto[1]
        apply (rule order_trans)
         apply (rule CSome(1), simp)
        apply (rule CSome(2), simp)
         apply (rule CSome(1), simp)
        apply auto[1]
       apply (rule Int_mono)
        apply (rule CSome(1), simp)
       apply (rule order_trans)
        apply (rule CSome(1),simp)
       apply (rule CSome(2),simp)
        apply (rule CSome(3),simp)
       apply auto[1]
      apply (rule Int_mono)
       apply (rule CSome(1), simp)
      apply (rule order_trans)
       apply (rule CSome(1), simp)
      apply (rule CSome(2), simp)
       apply (rule CSome(3), simp)
      by auto
  next
    case 2
    then show ?case 
      apply (simp only: wp.simps)
      apply (rule Un_mono)
       apply (rule Un_mono)
        apply (rule Un_mono)
         apply (rule CSome(2), simp)
          apply (rule CSome(2), simp)
          apply simp
         apply simp
        apply (rule CSome(2), simp)
         apply (rule CSome(2), simp)
         apply simp
        apply simp
       apply (rule Int_mono)
        apply (rule CSome(2), simp)
        apply simp
       apply (rule CSome(2))
        apply (rule CSome(4))
         apply auto[1]
        apply simp
       apply simp
      apply (rule Int_mono)
       apply (rule CSome(2),simp)
       apply auto[1]
      apply (rule CSome(2), simp)
       apply (rule CSome(4), simp)
       apply simp
      by simp
  next
    case 3
    then show ?case 
      apply (simp only: wp_err.simps)
      apply (rule Un_mono)
       apply simp
      apply (rule Int_mono)
       apply (rule Int_mono)
        apply (rule Int_mono)
         apply (rule order_trans)
          apply (rule CSome(3), simp)
         apply (rule CSome(4), simp)
          apply (rule CSome(3), simp)
         apply auto[1]
        apply (rule order_trans)
         apply (rule CSome(3), simp)
        apply (rule CSome(4), rule CSome(3), simp)
        apply (clarsimp, rule order_refl)
       apply (rule order_trans)
        apply (rule Un_mono)
         apply (rule CSome(3), simp)
        apply (rule CSome(4), simp)
         apply blast
        apply auto[1]
       apply (rule Un_mono)
        apply (rule CSome(3), simp)
       apply (rule order_trans)
        apply (rule CSome(3), simp)
       apply (rule CSome(4), simp)
        apply (rule CSome(1), simp)
       apply auto[1]
      apply (rule Un_mono)
       apply (rule CSome(3), simp)
      apply (rule order_trans)
       apply (rule CSome(3), simp)
      apply (rule CSome(4), simp)
       apply (rule CSome(1), simp)
      by auto
  next
    case 4
    then show ?case 
      apply (simp only: wp_err.simps)
      apply (rule Un_mono)
       apply simp
      apply (rule Int_mono)
       apply (rule Int_mono)
        apply (rule Int_mono)
         apply (rule CSome(4), simp)
          apply (rule CSome(4), simp, simp)
         apply simp
        apply (rule CSome(4), rule CSome(4), simp, simp, simp)
       apply (rule Un_mono)
        apply (rule CSome(4), simp, simp)
       apply (rule CSome(4), simp)
        apply (rule CSome(2), simp)
        apply auto[1]
       apply simp
      apply (rule Un_mono)
       apply (rule CSome(4), simp, simp)
      apply (rule CSome(4), simp)
       apply (rule CSome(2), simp)
       apply auto[1]
      apply simp
      done
  }

next
  case (All s)
  {
    case 1
    then show ?case 
      apply simp
      apply (rule conjI)
       apply blast
      apply (rule conjI)
       apply (rule le_supI1)
       apply (rule le_supI2)
       apply (rule order_trans)
        apply (rule All(1), simp)
       apply (rule All(2))
        apply (rule All(1), simp)
       apply (clarsimp)
       apply (rule order_refl)
      apply (rule le_supI2)
      apply (rule order_trans)
       apply (rule All(1), simp)
      apply (rule All(2))
       apply (rule All(1), simp)
      apply (clarsimp)
      apply (rule order_refl)
      done
  next
    case 2
    then show ?case 
      apply simp
      apply (rule conjI)
       apply blast
      apply (rule conjI)
       apply (rule le_supI1)
       apply (rule le_supI2)
       apply (rule All(2))
        apply (rule All(2))
         apply (simp)
        apply (clarsimp)
        apply (rule order_refl)
       apply (clarsimp)
       apply (rule order_refl)
      apply (rule le_supI2)
      apply (rule All(2))
       apply (rule All(2))
        apply (simp)
       apply (clarsimp)
       apply (rule order_refl)
      apply (clarsimp)
      apply (rule order_refl)
      done
  next
    case 3
    then show ?case 
      apply simp
      apply (rule le_supI2)
      apply (rule Int_mono)
       apply (rule order_trans)
        apply (rule All(3), simp)
       apply (rule All(4))
        apply (rule All(3), simp)
       apply (clarsimp)
       apply (rule order_refl)
      apply (rule order_trans)
       apply (rule All(3), simp)
      apply (rule All(4))
       apply (rule All(3), simp)
      apply (clarsimp)
      apply (rule order_refl)
      done
  next
    case 4
    then show ?case
      apply simp
      apply (rule conjI)
       apply blast
      apply (rule le_supI2)
      apply (rule Int_mono)
       apply (rule All(4))
        apply (rule All(4))
         apply (simp)
        apply (clarsimp)
        apply (rule order_refl)
       apply (clarsimp)
       apply (rule order_refl)
      apply (rule All(4))
       apply (rule All(4))
        apply (simp)
       apply (clarsimp)
       apply (rule order_refl)
      apply (clarsimp)
      apply (rule order_refl)
      done
  }
next
  case (Mu x1 s)
  {
    case 1
    then show ?case 
      apply simp
      apply (rule Rep_pt_mono)
      apply (rule ap_fstI)
      apply (rule mu_wp_mono)
        apply (subst less_eq_pt)
        apply (intro conjI)
          apply (rule Rep_pt[simplified])
         apply (rule Rep_pt[simplified])
        apply (subst Abs_pt_inverse)
         apply simp
         apply (rule monoI)
         apply (rule Mu(2), simp, clarsimp, rule order_refl)
        apply (subst Abs_pt_inverse)
         apply simp
         apply (rule monoI)
         apply (rule Mu(2), simp, clarsimp, rule order_refl)
        apply (rule allI)
        apply (rule Mu(1))
        apply clarsimp
       apply (subst less_eq_pt)
       apply (intro conjI)
         apply (rule Rep_pt[simplified])
        apply (rule Rep_pt[simplified])
       apply (subst Abs_pt_inverse)
        apply simp
        apply (rule monoI)
        apply (rule Mu(4), simp, clarsimp, rule order_refl)
       apply (subst Abs_pt_inverse)
        apply simp
        apply (rule monoI)
        apply (rule Mu(4), simp, clarsimp, rule order_refl)
       apply (rule allI)
       apply (rule Mu(3))
       apply clarsimp
      apply clarsimp
      done
  next
    case 2
    then show ?case
      apply simp
      apply (rule Rep_pt[simplified mono_def, simplified, rule_format])
      by simp
  next
    case 3
    then show ?case 
      apply simp
      apply (rule Rep_pt_mono)
      apply (rule ap_sndI)
      apply (rule mu_wp_mono)
        apply (subst less_eq_pt)
        apply (intro conjI)
          apply (rule Rep_pt[simplified])
         apply (rule Rep_pt[simplified])
        apply (subst Abs_pt_inverse)
         apply simp
         apply (rule monoI)
         apply (rule Mu(2), simp, clarsimp, rule order_refl)
        apply (subst Abs_pt_inverse)
         apply simp
         apply (rule monoI)
         apply (rule Mu(2), simp, clarsimp, rule order_refl)
        apply (rule allI)
        apply (rule Mu(1))
        apply clarsimp
       apply (subst less_eq_pt)
       apply (intro conjI)
         apply (rule Rep_pt[simplified])
        apply (rule Rep_pt[simplified])
       apply (subst Abs_pt_inverse)
        apply simp
        apply (rule monoI)
        apply (rule Mu(4), simp, clarsimp, rule order_refl)
       apply (subst Abs_pt_inverse)
        apply simp
        apply (rule monoI)
        apply (rule Mu(4), simp, clarsimp, rule order_refl)
       apply (rule allI)
       apply (rule Mu(3))
       apply clarsimp
      apply clarsimp
      done
  next
    case 4
    then show ?case 
      apply simp
      apply (rule Rep_pt[simplified mono_def, simplified, rule_format])
      by simp
  }
qed

named_theorems mono_intros

lemma mono_prod [mono_intros] : 
  assumes "mono f"
    and     "mono g"
  shows   "mono (\<lambda>x. (f x, g x))"
  using assms by (simp add: mono_def prod_less_eq)

lemma mono_const [mono_intros] :
  shows "mono (\<lambda>x. P)" 
  by (simp add: mono_def)

lemma mono_id [mono_intros] :
  shows "mono (\<lambda>x. x)" 
  by (simp add: mono_def)

lemma mono_fun [mono_intros] : 
  assumes "\<And>x. mono (f x)" 
  shows   "mono (\<lambda>y. \<lambda>x. f x y)"
  using assms
  by (simp add: mono_def le_fun_def)

lemma mono_union [mono_intros]: 
  assumes "mono f" 
    and     "mono g"
  shows   "mono (\<lambda>x. f x \<union> g x)" 
  using assms unfolding mono_def
  apply (intro allI impI)
  by (rule Un_mono, force, force)

lemma mono_big_union_2 [mono_intros]: 
  assumes "\<And>xa. mono (f xa)"
  shows   "mono (\<lambda>x. \<Union>xa\<in>A. f xa x)"
  using assms unfolding mono_def
  by blast

lemma mono_inter [mono_intros]: 
  assumes "mono f" 
    and     "mono g"
  shows   "mono (\<lambda>x. f x \<inter> g x)" 
  using assms unfolding mono_def
  apply (intro allI impI)
  by (rule Int_mono, force, force)

lemma mono_Abs_pt [mono_intros]: 
  assumes "\<And>y. mono (\<lambda>x. f x y)" 
    and     "\<And>x. mono (\<lambda>y. f x y)"
  shows   "mono (\<lambda>y. Abs_pt (\<lambda>x. f x y))"
  by (simp add: assms Abs_pt_inverse less_eq_pt monoD monoI)

lemma mono_Rep_pt [mono_intros]:
  shows "mono (Rep_pt pt)"
  by (rule Rep_pt[simplified])

lemma mono_Rep_pt_app_const [mono_intros]:
  assumes "mono f"
  shows   "mono (\<lambda>x. Rep_pt (f x) P)" 
  using assms unfolding mono_def
  by (simp add: less_eq_pt)

lemma mono_fst [mono_intros]:
  assumes "mono f"
  shows   "mono (\<lambda>x. fst (f x))" 
  using assms unfolding mono_def
  by (simp add: prod_less_eq)

lemma mono_snd_app_const [mono_intros]:
  assumes "mono f"
  shows   "mono (\<lambda>x. snd (f x) c)" 
  using assms unfolding mono_def
  by (simp add: le_fun_def prod_less_eq)

lemma mono_fst_app_const [mono_intros]:
  assumes "mono f"
  shows   "mono (\<lambda>x. fst (f x) c)" 
  using assms unfolding mono_def
  by (simp add: le_fun_def prod_less_eq)

lemma mono_snd [mono_intros]:
  assumes "mono f"
  shows   "mono (\<lambda>x. snd (f x))" 
  using assms unfolding mono_def
  by (simp add: prod_less_eq)

lemma mono_env_update [mono_intros]:
  shows "mono (\<lambda>y. (env((v, Tot) := fst y, (v, Par) := snd y)))"
  unfolding mono_def
  by (clarsimp simp: le_fun_def prod_less_eq)

lemma mono_env_update_app_const [mono_intros]:
  shows "mono (\<lambda>y. (env((v, Tot) := fst y, (v, Par) := snd y)) c)"
  unfolding mono_def
  by (clarsimp simp: le_fun_def prod_less_eq)

lemma mono_env_update_app_const2 [mono_intros]:
  shows "mono (\<lambda>y. (env((v, Tot) := fst y, (v, Par) := snd y)) c1 c2)"
  unfolding mono_def
  by (clarsimp simp: le_fun_def prod_less_eq)

lemma mono_wp_intro [mono_intros]:
  assumes "mono f"
    and     "mono g"
  shows   "mono (\<lambda>x. wp s loc (f x) (g x))" 
  using assms unfolding mono_def
  apply (intro allI impI)
  by (metis le_funE order.trans  wp_wp_err_mono(1,2))

lemma mono_wp_err_intro [mono_intros]:
  assumes "mono f"
    and     "mono g"
  shows   "mono (\<lambda>x. wp_err s loc (f x) (g x))" 
  using assms unfolding mono_def
  apply (intro allI impI)
  by (metis le_funE order.trans  wp_wp_err_mono(3,4))


subsection \<open>The weakest preconditions for some strategies\<close>
theorem wp_try[simp] : "wp (try s) loc P env = wp s loc P env \<union> (wp_err s loc P env \<inter> (P \<inter> (defined loc)))"
  using Try_def by simp

theorem wp_err_try[simp] : "wp_err (try s) loc P env = wp s loc P env \<union> (wp_err s loc P env \<inter> (P \<inter> (defined loc)))"
  using Try_def by simp

theorem wp_repeat[simp] : "wp (repeat s) loc P env = wp (mu 0. try (s ;; \<lparr>0\<rparr>)) loc P env"
  using Repeat_def by simp

theorem wp_err_repeat[simp] : "wp_err (repeat s) loc P env = wp_err (mu 0. try (s ;; \<lparr>0\<rparr>)) loc P env"
  using Repeat_def by simp

theorem wp_topDown : "wp (topDown s) loc P env = wp (mu 0. (s <+ one \<lparr>0\<rparr>)) loc P env"
  using TopDown_def by simp

theorem wp_err_topDown : "wp_err (topDown s) loc P env = wp_err (mu 0. (s <+ one \<lparr>0\<rparr>)) loc P env"
  using TopDown_def by simp

text \<open>The weakest must succeed precondition and weakest may fail precondition for repeat are the same\<close>
(* We need to use the monotonicity proofs of wp/wp_err *)
theorem eq_wp_repeat_wp_err_repeat : "\<forall>loc P. wp (repeat s) loc P env = wp_err (repeat s) loc P env"
  apply (simp add: Repeat_def)
  apply (rule fixp_induct)
     apply (rule admissible_all)
     apply (rule admissible_all)
     apply (rule ccpo.admissibleI)
     apply (simp add: prod_Sup Sup_pt)
     apply (subst Abs_pt_inverse, simp)
      apply (intro mono_intros)
     apply (subst Abs_pt_inverse, simp)
      apply (intro mono_intros)
     apply force
    apply (intro mono_intros)
   apply (simp add: prod_Sup Sup_pt)
  by (simp add: Rep_pt_inject)
end

section \<open>The location-based weakest precondition calculus\<close>

theory Wp
  imports CCPO Denotational MonoDenotational
begin

datatype tag = Tot | Par
datatype pos = Left | Right
datatype location = empty ("\<epsilon>") | Lcons pos location ("_\<triangleleft>_"  [60, 61] 60)

fun append:: "location \<Rightarrow> pos \<Rightarrow> location" ("_\<triangleright>_"  [60, 61] 60)
  where
    "append \<epsilon> p = p \<triangleleft> \<epsilon>"
  | "append (i \<triangleleft> loc) p = i \<triangleleft> (append loc p) "


text 
 \<open> A predicate transformer is internally just a function from a set of expressions to a set of 
   expressions, with a side condition that it is monotonic \<close>
typedef pt = "{pt::exp set \<Rightarrow> exp set. mono pt}"
  using monoI by fastforce

text
 \<open> For predicate transformers @{term "a"} and @{term "b"}, @{term "a \<le> b"} not only requires that 
   they are equal pointwise, but also that a and b are both monotonic \<close> 
instantiation pt:: ccpo begin
definition less_eq_pt: 
  "(a:: pt) \<le> b \<longleftrightarrow> mono (Rep_pt a) \<and>  mono (Rep_pt b) \<and> (\<forall>x. Rep_pt a x \<subseteq> Rep_pt b x)"
definition less_pt [simp]: 
  "(a:: pt) < b \<longleftrightarrow> a \<le> b \<and> \<not> (b \<le> a)" 
definition Sup_pt: 
  "Sup (A:: pt set) \<equiv> Abs_pt (\<lambda>x. \<Union>t\<in>A. Rep_pt t x)"

lemma bigU_mono [simp]:
  assumes "\<forall> x \<in> A. mono x" 
  shows "mono (\<lambda>x. \<Union>t \<in> A. t x)"
  using assms
  unfolding mono_def
  by fastforce


instance 
proof 
  fix x::pt and y::pt and z::pt and A
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by fastforce
  show "x \<le> x"
    using Rep_pt less_eq_pt by fastforce
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    using less_eq_pt by fastforce
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (metis Rep_pt_inject le_fun_def less_eq_pt order_class.order_eq_iff)
  show "Complete_Partial_Order.chain (\<le>) A \<Longrightarrow> x \<in> A \<Longrightarrow> x \<le> Sup A"
    apply (simp add: Sup_pt less_eq_pt)
    apply (subst Abs_pt_inverse)
     using  Abs_pt_inverse Rep_pt apply (simp add: SUP_mono' monoD monoI)
    by (metis (no_types, lifting) Abs_pt_inverse Rep_pt SUP_mono' UN_I mem_Collect_eq monoD 
                                  monoI subsetI)
  show "Complete_Partial_Order.chain (\<le>) A \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> x \<le> z) \<Longrightarrow> Sup A \<le> z"
    apply (simp add: Sup_pt less_eq_pt)
    apply (subst Abs_pt_inverse)
     using  Abs_pt_inverse Rep_pt apply (simp add: SUP_mono' monoD monoI)
    by (metis (no_types, lifting) Abs_pt_inverse Rep_pt SUP_le_iff SUP_mono' mem_Collect_eq 
                                  monoD monoI)
 qed
end

text
 \<open> In the environment, we use the pt type to add the side condition we need that 
   every function in the environment is monotone \<close>
type_synonym lenv = "var \<times> tag \<Rightarrow> location \<Rightarrow> pt "

subsection \<open>Helper functions\<close>
fun update:: "location \<Rightarrow> exp \<Rightarrow> exp_err_div set \<Rightarrow> exp_err_div set" 
  where
    "update \<epsilon> e xs = xs"
  | "update (i\<triangleleft>loc) (Leaf l) xs = undefined"
  | "update (Left\<triangleleft>loc) (Node l e1 e2) xs = 
                        {E (Node l x e2) | x. E x \<in> (update loc e1 xs)} \<union> (xs \<inter> {Div, Err})"
  | "update (Right\<triangleleft>loc) (Node l e1 e2) xs = 
                        {E (Node l e1 x) | x. E x \<in> (update loc e2 xs)} \<union> (xs \<inter> {Div, Err})"

fun lookup:: "location \<Rightarrow> exp \<Rightarrow> exp"
  where
    "lookup \<epsilon> e = e"
  | "lookup (i\<triangleleft>loc) (Leaf l) = undefined"
  | "lookup (Left\<triangleleft>loc) (Node l e1 e2) = lookup loc e1"
  | "lookup (Right\<triangleleft>loc) (Node l e1 e2) = lookup loc e2"

fun defined:: "location \<Rightarrow> exp set"
  where
    "defined \<epsilon> = UNIV"
  | "defined (Left\<triangleleft>loc) = {Node l e1 e2 | l e1 e2. e1 \<in> defined loc}"
  | "defined (Right\<triangleleft>loc) = {Node l e1 e2 | l e1 e2. e2 \<in> defined loc}"

subsection \<open>Weakest must succeed and weakest may fail preconditions\<close>
fun wp_err:: "strategy \<Rightarrow> location \<Rightarrow> exp set \<Rightarrow> lenv \<Rightarrow> exp set" 
and wp:: "strategy \<Rightarrow> location \<Rightarrow> exp set \<Rightarrow> lenv \<Rightarrow> exp set"
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
  | "wp (s1 >< s2) loc P env = (wp s1 loc P env \<inter> wp_err s2 loc P env) 
                               \<union> (wp_err s1 loc P env \<inter> wp s2 loc P env)"
  | "wp_err (one s) loc P env = {e | e x. e \<in> defined loc \<and> lookup loc e = Leaf x } 
                                \<union> (wp_err s (loc \<triangleright> Left) P env \<inter> wp_err s (loc \<triangleright> Right) P env)"
  | "wp (one s) loc P env = (wp_err s (loc \<triangleright> Left) P env \<inter> wp s (loc \<triangleright> Right) P env) 
                            \<union> (wp s (loc \<triangleright> Left) P env \<inter> wp_err s (loc \<triangleright> Right) P env)"
(* wp and wp_err for the leaf case are like SKIP *)
  | "wp_err (all s) loc P env = (P \<inter> {e | e x. e \<in> defined loc \<and> lookup loc e = Leaf x}) 
                                \<union> (wp_err s (loc \<triangleright> Left) (wp_err s (loc \<triangleright> Right) P env) env 
                                   \<inter> wp_err s (loc \<triangleright> Right) (wp_err s (loc \<triangleright> Left) P env) env)"
  | "wp (all s) loc P env = (P \<inter> {e | e x. e \<in> defined loc \<and> lookup loc e = Leaf x})
                            \<union> wp s (loc \<triangleright> Left) (wp s (loc \<triangleright> Right) P env) env 
                            \<union> wp s (loc \<triangleright> Right) (wp s (loc \<triangleright> Left) P env) env"
  | "wp_err (some s) loc P env = {e | e x. e \<in> defined loc \<and> lookup loc e = Leaf x } \<union> 
                              (wp_err s (loc \<triangleright> Left) (wp_err s (loc \<triangleright> Right) P env) env
                               \<inter> wp_err s (loc \<triangleright> Right) (wp_err s (loc \<triangleright> Left) P env) env
                               \<inter> (wp_err s (loc \<triangleright> Left) P env 
                                  \<union> wp_err s (loc \<triangleright> Left) (wp s (loc \<triangleright> Right) P env) env)
                               \<inter> (wp_err  s (loc \<triangleright> Right) P env 
                                  \<union> wp_err s (loc \<triangleright> Right) (wp s (loc \<triangleright> Left) P env) env))"
  | "wp (some s) loc P env = wp s (loc \<triangleright> Left) (wp s (loc \<triangleright> Right) P env) env
                             \<union> wp s (loc \<triangleright> Right) (wp s (loc \<triangleright> Left) P env) env
                             \<union> (wp s (loc \<triangleright> Left) P env 
                                \<inter> wp s (loc \<triangleright> Left) (wp_err s (loc \<triangleright> Right) P env) env)
                             \<union> (wp s (loc \<triangleright> Right) P env 
                                \<inter> wp s (loc \<triangleright> Right) (wp_err s (loc \<triangleright> Left) P env) env)
                        "
    (* Fixed points and variables are computed with the pt type, not functions from sets to sets, 
       because we need to carry around monotonicity side conditions. *)
  | "wp \<lparr>X\<rparr> loc P env = Rep_pt (env (X, Tot) loc) P"
  | "wp_err \<lparr>X\<rparr> loc P env = Rep_pt (env (X, Par) loc) P"
  | "wp (mu X. s) loc P env = Rep_pt (fst 
          (\<mu> Delta. ( (\<lambda>loc. Abs_pt (\<lambda> P. wp s loc P (env((X, Tot):= fst Delta, (X, Par):= snd Delta)))),
                      (\<lambda>loc. Abs_pt (\<lambda>P. wp_err s loc P (env((X, Tot):= fst Delta, (X, Par):= snd Delta))))
                    )) loc) P" 
  | "wp_err (mu X. s) loc P env = Rep_pt (snd 
          (\<mu> Delta. ( (\<lambda>loc. Abs_pt (\<lambda> P. wp s loc P (env((X, Tot):= fst Delta, (X, Par):= snd Delta)))),
                      (\<lambda>loc. Abs_pt (\<lambda>P. wp_err s loc P (env((X, Tot):= fst Delta, (X, Par):= snd Delta))))
                    )) loc) P" 


subsection \<open> Monotonicity proofs for @{text "wp"} and @{text "wp_err"} \<close>

definition ap:: "('a \<Rightarrow> 'b) \<times> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> ('b \<times>'b)"
  where "ap \<equiv> \<lambda>fg a. (fst fg a, snd fg a)" 

theorem ap_mono: 
  assumes "\<forall>x y. x \<le> y \<longrightarrow> f x \<le> f' y" 
    and "\<forall>x y. (x::'a::ccpo) \<le> y \<longrightarrow> (g x::'b::ccpo) \<le> g' y" 
    and "x \<le> y"
  shows "ap (f, g) x \<le> ap (f', g') y"
  using assms 
  by (simp add: ap_def)

lemma Sup_mono_two:
  assumes "\<forall>x\<in>A. \<forall>P. (fst (fst x) P:: 'a:: ccpo) \<le> fst (snd x) P \<and> (snd (fst x) P:: 'b:: ccpo) \<le> snd (snd x) P"
  and     "Complete_Partial_Order.chain (\<le>) (fst ` A)"
  and     "Complete_Partial_Order.chain (\<le>) (snd ` A)"
  shows   "fst (fst (Sup A)) P \<le> fst (snd (Sup A)) P \<and> snd (fst (Sup A)) P \<le> snd (snd (Sup A))P"
  using assms apply (simp add: fst_Sup snd_Sup)
  apply (frule chain_fst_exist)
  apply (drule chain_snd_exist)
  apply (frule chain_fst_exist)
  apply (drule chain_snd_exist)
  apply (rule conjI)
   apply (subst Sup_below)
    apply (rule chain_imageI, simp, simp add: le_fun_def)
   apply clarsimp 
   apply (metis (mono_tags, lifting) below_Sup chain_imageI fst_conv image_eqI le_funE)
  apply (subst Sup_below)
   apply (rule chain_imageI, simp, simp add: le_fun_def)
  apply clarsimp
  by (metis (mono_tags, lifting) below_Sup chain_imageI fst_conv image_eqI le_funE snd_conv)

lemma Sup_fst: "Sup (fst ` A) = fst (Sup A)" 
  by (simp add: fst_Sup)

lemma Sup_snd: "Sup (snd ` A) = snd (Sup A)" 
  by (simp add: snd_Sup)

lemma 
  " \<forall>loc::location. ap (Sup {}::(location \<Rightarrow> pt) \<times> (location \<Rightarrow> pt)) loc \<le> ap (Sup {}) loc"
  apply (simp add: fst_Sup snd_Sup ap_def)
  oops
theorem mu_wp_mono: 
  assumes f_mono: "\<And> (env1:: lenv) env2 loc. \<forall> loc p. env1 p loc \<le> env2 p loc \<Longrightarrow> f loc env1 \<le> f loc env2"
    and g_mono: "\<And> (env1:: lenv) env2 loc. \<forall> loc p. env1 p loc \<le> env2 p loc \<Longrightarrow> g loc env1 \<le> g loc env2"
    and env_ordered: "\<forall>p loc. env1 p loc \<le> env2 p loc"
  shows "\<forall>loc. ap (\<mu> x. (\<lambda>loc. f loc (env1((x1, Tot):= fst x, (x1, Par):= snd x)),
                   \<lambda>loc. g loc (env1((x1, Tot):= fst x, (x1, Par):= snd x)))) loc
             \<le> ap (\<mu> x. (\<lambda>loc. f loc (env2((x1, Tot):= fst x, (x1, Par):= snd x)),
                   \<lambda>loc. g loc (env2((x1, Tot):= fst x, (x1, Par):= snd x)))) loc"
  apply (rule parallel_fixp_induct)
      apply (fastforce intro: chain_fst_exist chain_snd_exist ccpo.admissibleI
                       dest: Sup_mono_two
                       simp: fst_Sup snd_Sup ap_def)
     apply (simp add: fst_Sup snd_Sup ap_def)
    apply (fastforce intro: monoI 
                     simp: f_mono g_mono le_fun_def Product_Order.less_eq_prod_def)+
  by (fastforce intro: env_ordered less_eq_pt f_mono
                simp: env_ordered g_mono Rep_pt[simplified] ap_def Product_Order.less_eq_prod_def)


lemma ap_fstI:
  "ap f P \<le> ap g Q \<Longrightarrow> fst f P \<le> fst g Q"
  by (simp add: ap_def)

lemma ap_sndI:
  "ap f P \<le> ap g Q \<Longrightarrow> snd f P \<le> snd g Q" 
  by (simp add: ap_def)

lemma Rep_pt_mono: 
  "a \<le> b \<Longrightarrow> Rep_pt a X \<le> Rep_pt b X"
  by (simp add: less_eq_pt)

(* wp and wp_err are monotone *)
theorem wp_wp_err_mono:
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
    thus ?case by simp
  next
    case 2
    thus ?case by auto
  next
    case 3
    thus ?case by simp
  next
    case 4
    thus ?case by auto
  }
next
  case ABORT
  {
    case 1
    thus ?case by simp
  next
    case 2
    thus ?case by simp
  next
    case 3
    thus ?case by simp
  next
    case 4
    thus ?case by simp
  }
next
  case (FixVar x)
  {
    case 1
    thus ?case by (simp add: less_eq_pt mono_def)
  next
    case 2
    thus ?case by (simp add: less_eq_pt mono_def)
  next
    case 3
    thus ?case by (simp add: less_eq_pt mono_def)
  next
    case 4
    thus ?case  by (simp add: less_eq_pt mono_def)
  }
next
  case (Atomic x)
  {
    case 1
    thus ?case by simp
  next
    case 2
    thus ?case 
      apply (clarsimp split: option.split)
      by blast
  next
    case 3
    thus ?case by simp
  next
    case 4
    thus ?case 
      apply (clarsimp split: option.split)
      by blast
  }
next
  case (Seq s1 s2)
  {
    case 1
    show ?case 
      apply simp
      by (metis (full_types) "1" order_trans Seq.hyps(1,2,5))
  next
    case 2
    thus ?case 
      by (simp add: Seq.hyps(2,6))
  next
    case 3
    show ?case 
      apply (simp)
      by (metis "3" Seq.hyps(3) Seq.hyps(4) Seq.hyps(7) dual_order.trans)
  next
    case 4
    thus ?case 
      by (simp add: Seq.hyps(4,8))
  }
next
  case (Left_Choice s1 s2)
  {
    case 1
    thus ?case 
      apply (simp only: wp.simps)
      by (metis Int_mono Un_mono Left_Choice(1,3,5))
  next
    case 2
    thus ?case 
      apply (simp only: wp.simps)
      by (metis Int_mono Un_mono Left_Choice(2,4,6))
  next
    case 3
    thus ?case 
      apply (simp only: wp_err.simps)
      by (metis Int_mono Un_mono Left_Choice(1,3,7))
  next
    case 4
    thus ?case 
      apply (simp only: wp_err.simps)
      by (metis Int_mono Un_mono Left_Choice(2,4,8))
  }
next
  case (Choice s1 s2)
  {
    case 1
    thus ?case 
      apply (simp only: wp.simps)
      by (metis Int_mono Un_mono Choice(1,3,5,7))
  next
    case 2
    thus ?case 
      apply (simp only: wp.simps)
      by (metis Int_mono Un_mono Choice(2,4,6,8))
  next
    case 3
    thus ?case
      apply (simp only: wp_err.simps)
      by (metis Int_mono Choice(3,7))
  next
    case 4
    thus ?case 
      apply (simp only: wp_err.simps)
      by (metis Int_mono Choice(4,8))
  }
next
  case (One s)
  {
    case 1
    thus ?case 
      apply (simp only: wp.simps)   
      using One.hyps(1,3) Un_mono by blast
  next
    case 2
    thus ?case 
      apply (simp only: wp.simps) 
      by (metis Int_mono Un_mono One.hyps(2,4))
  next
    case 3
    thus ?case
      apply (simp only: wp_err.simps)
      using One.hyps(3) Un_mono by blast+
  next
    case 4
    thus ?case
      apply (simp only: wp_err.simps)
      using One.hyps(4) Un_mono by blast+
  }
next
  case (CSome s)
  {
    case 1
    thus ?case 
      apply (simp only: wp.simps)
      apply (rule Un_mono)+
         apply (metis order_trans CSome.hyps(1,2))
        apply (metis order_trans CSome.hyps(1,2))
       apply (metis Int_mono order_trans CSome.hyps(1,2,3))
      by (metis Int_mono order_trans CSome.hyps(1,2,3))
  next
    case 2
    thus ?case 
      apply (simp only: wp.simps)
      apply (rule Un_mono)+
         apply (simp add: CSome.hyps(2))
        apply (simp add: CSome.hyps(2))
       apply (metis Int_mono CSome.hyps(2,4))
      by (metis Int_mono CSome.hyps(2,4))
  next
    case 3
    thus ?case 
      apply (simp only: wp_err.simps)
      apply (rule Un_mono, blast)
      apply (rule Int_mono)+
         apply (metis CSome.hyps(3,4) subset_trans)
        apply (metis CSome.hyps(3,4) subset_trans)
       apply (metis "3" CSome.hyps(1,3,4) Un_mono order_refl order_trans)
      by (metis "3" CSome.hyps(1,3,4) Un_mono order_refl order_trans)
  next
    case 4
    thus ?case 
      apply (simp only: wp_err.simps)
      apply (rule Un_mono,blast)
      apply (rule Int_mono)+
         apply (simp add: CSome.hyps(4) subset_trans)
        apply (simp add: CSome.hyps(4) subset_trans)    
       apply (metis CSome.hyps(2,4) Un_mono)
      by (metis CSome.hyps(2,4) Un_mono)
  }

next
  case (All s)
  {
    case 1
    thus ?case 
      apply simp
      apply (rule conjI, blast)
      apply (rule conjI)
       apply (rule le_supI1)
       by (rule le_supI2, metis "1" All.hyps(1,2) dual_order.trans)+ (* takes a few seconds *)
  next
    case 2
    thus ?case 
      apply simp
      apply (rule conjI, blast)
      apply (rule conjI)
       apply (rule le_supI1)
        apply(fastforce intro!: le_supI2 simp: dest: All.hyps(2))+
      done
  next
    case 3
    thus ?case 
      apply simp
      apply (rule le_supI2)
      by (metis "3" All.hyps(3,4) Int_mono order_trans order_refl) (* takes soem time *)
  next
    case 4
    thus ?case
      apply simp
      apply (rule conjI, blast)
      by(fastforce intro!: le_supI2 simp: dest: All.hyps(4))
  }
next
  case (Mu x1 s)
  {
    case 1
    thus ?case 
      apply simp
      apply (rule Rep_pt_mono)
      apply (rule ap_fstI)
      apply (rule mu_wp_mono[rule_format])
        apply (metis Abs_pt_inverse less_eq_pt monoI Mu.hyps(1,2) dual_order.refl monoI Mu(2) mem_Collect_eq Rep_pt[simplified])
       apply (metis mem_Collect_eq order_eq_refl Abs_pt_inverse monoI Mu.hyps(3,4) Abs_pt_inverse monoI Mu.hyps(3,4) mem_Collect_eq order_eq_refl  less_eq_pt)
      by (simp add: "1")
  next
    case 2
    thus ?case
      apply simp
      by (fastforce intro!:  Rep_pt[simplified mono_def, simplified, rule_format])
  next
    case 3
    thus ?case 
      apply simp
      apply (rule Rep_pt_mono)
      apply (rule ap_sndI)
      apply (rule mu_wp_mono[rule_format])
        apply (metis Abs_pt_inverse less_eq_pt monoI Mu.hyps(1,2) dual_order.refl monoI Mu(2) mem_Collect_eq Rep_pt[simplified])
       apply (metis mem_Collect_eq order_eq_refl Abs_pt_inverse monoI Mu.hyps(3,4) Abs_pt_inverse monoI Mu.hyps(3,4) mem_Collect_eq order_eq_refl  less_eq_pt)
      by (simp add: "3")
  next
    case 4
    thus ?case 
      apply simp
      by (fastforce intro!:  Rep_pt[simplified mono_def, simplified, rule_format])
  }
qed

named_theorems mono_intros

lemma mono_prod [mono_intros]: 
  "\<lbrakk>mono f ; mono g\<rbrakk> \<Longrightarrow> mono (\<lambda>x. (f x, g x))"
  by (simp add: monoI monotoneD)

lemma mono_const [mono_intros]:
  "mono (\<lambda>x. P)" 
  by (simp add: mono_def)

lemma mono_id [mono_intros]:
  "mono (\<lambda>x. x)" 
  by (simp add: mono_def)

lemma mono_fun [mono_intros]: 
  assumes "\<And>x. mono (f x)" 
  shows   "mono (\<lambda>y. \<lambda>x. f x y)"
  using assms unfolding mono_def 
  by (simp add: le_funI)

lemma mono_union [mono_intros]: 
  "\<lbrakk>mono f ; mono g\<rbrakk> \<Longrightarrow> mono (\<lambda>x. f x \<union> g x)" 
  unfolding mono_def by blast

lemma mono_big_union_2 [mono_intros]: 
  assumes "\<And>xa. mono (f xa)"
  shows   "mono (\<lambda>x. \<Union>xa\<in>A. f xa x)"
  using assms unfolding mono_def
  by blast

lemma mono_inter [mono_intros]: 
  "\<lbrakk>mono f ; mono g\<rbrakk> \<Longrightarrow> mono (\<lambda>x. f x \<inter> g x)" 
  unfolding mono_def by blast

lemma mono_Abs_pt [mono_intros]: 
  assumes "\<And>y. mono (\<lambda>x. f x y)" 
  and     "\<And>x. mono (\<lambda>y. f x y)"
  shows   "mono (\<lambda>y. Abs_pt (\<lambda>x. f x y))"
  by (simp add: assms Abs_pt_inverse less_eq_pt monoD monoI)

lemma mono_Rep_pt [mono_intros]:
  "mono (Rep_pt pt)"
  by (rule Rep_pt[simplified])

lemma mono_Rep_pt_app_const [mono_intros]:
  "mono f \<Longrightarrow> mono (\<lambda>x. Rep_pt (f x) P)" 
  unfolding mono_def
  by (simp add: less_eq_pt)

lemma mono_fst [mono_intros]:
  "mono f \<Longrightarrow> mono (\<lambda>x. fst (f x))" 
  unfolding mono_def
  by (simp add: fst_mono)

lemma mono_snd [mono_intros]:
  "mono f \<Longrightarrow> mono (\<lambda>x. snd (f x))" 
  unfolding mono_def
  by (simp add: snd_mono)

lemma mono_fst_app_const [mono_intros]:
  "mono f \<Longrightarrow> mono (\<lambda>x. fst (f x) c)" 
  unfolding mono_def
  by (metis le_fun_def fst_mono)

lemma mono_snd_app_const [mono_intros]:
  "mono f \<Longrightarrow> mono (\<lambda>x. snd (f x) c)" 
  unfolding mono_def
  by (metis le_fun_def snd_mono)

lemma mono_env_update [mono_intros]:
  "mono (\<lambda>y. (env((v, Tot):= fst y, (v, Par):= snd y)))"
  unfolding mono_def le_fun_def
  by fastforce

lemma mono_env_update_app_const [mono_intros]:
  "mono (\<lambda>y. (env((v, Tot):= fst y, (v, Par):= snd y)) c)"
  unfolding mono_def
  by force

lemma mono_env_update_app_const2 [mono_intros]:
  "mono (\<lambda>y. (env((v, Tot):= fst y, (v, Par):= snd y)) c1 c2)"
  unfolding mono_def
  by (simp add: le_fun_def)

lemma mono_wp_intro [mono_intros]:
  "\<lbrakk>mono f ; mono g\<rbrakk> \<Longrightarrow> mono (\<lambda>x. wp s loc (f x) (g x))" 
  unfolding mono_def
  apply (intro allI impI)
  by (metis le_funE order.trans  wp_wp_err_mono(1,2))

lemma mono_wp_err_intro [mono_intros]:
  "\<lbrakk>mono f ; mono g\<rbrakk> \<Longrightarrow> mono (\<lambda>x. wp_err s loc (f x) (g x))" 
  unfolding mono_def
  apply (intro allI impI)
  by (metis le_funE order.trans  wp_wp_err_mono(3,4))


subsection \<open>The weakest preconditions for some strategies\<close>
theorem wp_try[simp]: 
  "wp (try s) loc P env = wp s loc P env \<union> (wp_err s loc P env \<inter> (P \<inter> (defined loc)))"
  using Try_def by simp

theorem wp_err_try[simp]: 
  "wp_err (try s) loc P env = wp s loc P env \<union> (wp_err s loc P env \<inter> (P \<inter> (defined loc)))"
  using Try_def by simp

theorem wp_repeat[simp]: 
  "wp (repeat s) loc P env = wp (mu 0. try (s ;; \<lparr>0\<rparr>)) loc P env"
  using Repeat_def by simp

theorem wp_err_repeat[simp]: 
  "wp_err (repeat s) loc P env = wp_err (mu 0. try (s ;; \<lparr>0\<rparr>)) loc P env"
  using Repeat_def by simp

theorem wp_topDown: 
  "wp (topDown s) loc P env = wp (mu 0. (s <+ one \<lparr>0\<rparr>)) loc P env"
  using TopDown_def by simp

theorem wp_err_topDown: 
 "wp_err (topDown s) loc P env = wp_err (mu 0. (s <+ one \<lparr>0\<rparr>)) loc P env"
  using TopDown_def by simp

text \<open>
  The weakest must succeed precondition and weakest may fail precondition for repeat are the same
\<close>

(* We need to use the monotonicity proofs of wp/wp_err *)
theorem eq_wp_repeat_wp_err_repeat: 
  "\<forall>loc P. wp (repeat s) loc P env = wp_err (repeat s) loc P env"
  apply (simp add: Repeat_def)
  apply (rule fixp_induct)
     apply (rule admissible_all)
     apply (rule admissible_all)
     apply (rule ccpo.admissibleI)
     apply (simp add: fst_Sup snd_Sup Sup_pt)
     apply (subst Abs_pt_inverse, simp)
      apply (intro mono_intros)
     apply (subst Abs_pt_inverse, simp)
      apply (intro mono_intros)
     apply force
    apply (intro mono_intros)
   apply (fastforce simp:fst_Sup snd_Sup Sup_pt)
  by (fastforce simp: Rep_pt_inject)

end


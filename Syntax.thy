theory Syntax
  imports CCPO
begin

(* The syntax of extended System S *)
type_synonym var = "int"
type_synonym env = "var \<Rightarrow> D"
datatype
  strategy = SKIP
  | ABORT
  | FixVar var              ("\<lparr>_\<rparr>")  
  | Atomic "exp \<Rightarrow> exp option" ("\<llangle>_\<rrangle>")
  | Seq strategy strategy            ("_;;/ _"  [60, 61] 60)
  | Left_Choice strategy strategy     ("_<+/ _"  [60, 61] 60)
  | Choice strategy strategy          ("_></ _"  [60, 61] 60) (* non-deterministic choice *)
  | One strategy                 ("one")
  | CSome strategy                ("some") (* I have to do this because isabelle option type is being ridiculous*)
  | All strategy                 ("all")
  | Mu var strategy              ("mu_._"   [60, 61] 60)


definition Try :: "strategy \<Rightarrow> strategy" ("try") where
  "Try s = s <+ SKIP"

definition Repeat :: "strategy \<Rightarrow> strategy" ("repeat") where
  "Repeat s = mu 0 . try (s ;; \<lparr>0\<rparr>)"

definition TopDown :: "strategy \<Rightarrow> strategy" ("topDown") where
  "TopDown s = mu 0 . (s <+ one \<lparr>0\<rparr>)"
end
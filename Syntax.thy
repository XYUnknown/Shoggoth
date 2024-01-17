(*  Title:         Syntax.thy
    Authors:       Xueying Qin, U Edinburgh; Liam O'Connor, U Edinburgh; Peter Hoefner, ANU
    Contributions: Ohad Kammar, U Edinburgh; Rob van Glabbeek, U Edinburgh; Michel Steuwer, U Edinburgh
    Maintainer:    Xueying Qin <xueying.qin@ed.ac.uk>
*)

section \<open>The syntax of extended System S\<close>
theory Syntax
  imports CCPO
begin

type_synonym var = "int"
type_synonym env = "var \<Rightarrow> D"
datatype
  strategy = SKIP
  | ABORT
  | FixVar var                    ("\<lparr>_\<rparr>")  
  | Atomic "exp \<Rightarrow> exp option"    ("\<llangle>_\<rrangle>")
  | Seq strategy strategy         ("_;;/ _"  [60, 61] 60)
  | Left_Choice strategy strategy ("_<+/ _"  [60, 61] 60)
  | Choice strategy strategy      ("_></ _"  [60, 61] 60) (* non-deterministic choice *)
  | One strategy                  ("one")
  | CSome strategy                ("some") (* avoid conflict with isabelle option type *)
  | All strategy                  ("all")
  | Mu var strategy               ("mu_._"   [60, 61] 60)

definition Try :: "strategy \<Rightarrow> strategy" ("try") where
  "Try s = s <+ SKIP"

definition Repeat :: "strategy \<Rightarrow> strategy" ("repeat") where
  "Repeat s = mu 0 . try (s ;; \<lparr>0\<rparr>)"

definition TopDown :: "strategy \<Rightarrow> strategy" ("topDown") where
  "TopDown s = mu 0 . (s <+ one \<lparr>0\<rparr>)"
end
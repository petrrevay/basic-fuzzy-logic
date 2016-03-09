(* Title:        Syntax of propositional Basic Fuzzy Logic (BL)
   Author:       Petr Révay <petr.revay at gmail.com>, 2016
*)

section "Syntax of propositional Basic Fuzzy Logic"

theory BL_Syntax
imports Main String
begin

text {*
  This theory provides a formalization of a syntax of propositional Basic Fuzzy Logic (BL)
  introduced by Petr Hájek in 1998 [REF. Hajek]. Taking a relation of provability in BL as a main
  objective, the theory presents a way how to formalize this (or any propositional) logic syntax,
  allowing then to formalize the Hilbert's style proofs within the logic and, actually, the proofs
  \textit{about} the logic, i.e. the provability itself.

  The work originates in the author's bachelor thesis written in 2014 at the Department of Logic,
  Faculty of Arts, Charles University in Prague /URL logika.ff.cuni.cz/.
*}

subsection "Formula of BL"

text {*
  A construction of a formula in BL follows the definition [REF. Handbook, pg.]. The constructor
  Var string represents an element of a potentially infinite set of the propositional variables
  and the "dot" notation was chosen to differ a variable from the names in /Isabelle/Isar?/.
*}

datatype formulaBL =
  Var string (".") --"REFCTR: replacement of char by string"
| Const_0 ("\<zero>\<^sub>B\<^sub>L") --"REFCTR: add zero symbol"
| Conjuction_BL_strong formulaBL formulaBL
  (infixr "&\<^sub>B\<^sub>L" 50)
| Implication_BL formulaBL formulaBL
  (infix "\<longrightarrow>\<^sub>B\<^sub>L" 35) 

value ".anyStringWithDotIsAPropVariableOfBL"

text {*
  Following the definitions in [REF. Handbook], another constant and the rest of the connectives are
  derived from the foregoing.
*}

type_synonym unary_conn =
  "formulaBL \<Rightarrow> formulaBL"
type_synonym binary_conn =
  "formulaBL \<Rightarrow> formulaBL \<Rightarrow> formulaBL"

definition Const_1 :: "formulaBL"
("\<one>\<^sub>B\<^sub>L") --"REFCTR: add symbol"
where
--\<open> "Hajek Def. 2.2.13 (p.41)" \<close>
  "\<one>\<^sub>B\<^sub>L \<equiv> (\<zero>\<^sub>B\<^sub>L \<longrightarrow>\<^sub>B\<^sub>L \<zero>\<^sub>B\<^sub>L)"

definition Conjuction_BL_weak :: binary_conn
(infixr "\<and>\<^sub>B\<^sub>L" 50)
where
  "Conjuction_BL_weak \<phi> \<psi> \<equiv> (\<phi> &\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>))"

definition Disjunction_BL_weak :: binary_conn
(infixr "\<or>\<^sub>B\<^sub>L" 50)
where
  "Disjunction_BL_weak \<phi> \<psi> \<equiv> ((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<and>\<^sub>B\<^sub>L ((\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>) \<longrightarrow>\<^sub>B\<^sub>L \<phi>)"

definition Equivalence_BL :: binary_conn
(infixr "\<longleftrightarrow>\<^sub>B\<^sub>L" 30)
where
  "Equivalence_BL \<phi> \<psi> \<equiv> ((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) &\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>))"

definition Negation_BL :: unary_conn
("\<not>\<^sub>B\<^sub>L")
where
  "Negation_BL \<phi> \<equiv> \<phi> \<longrightarrow>\<^sub>B\<^sub>L \<zero>\<^sub>B\<^sub>L"

text {*
  Note that the following definition  /ma vahu???/ since the strong conjunction is not
  idempotent in BL. 
*}

fun MultiConj_BL :: "formulaBL \<Rightarrow> nat \<Rightarrow> formulaBL"
(infixr "^\<^sup>B\<^sup>L" 60)
where
  "MultiConj_BL \<phi> 0 = \<one>\<^sub>B\<^sub>L"
| "MultiConj_BL \<phi> n = (\<phi> &\<^sub>B\<^sub>L (MultiConj_BL \<phi> (n - 1)))"

value ".p^\<^sup>B\<^sup>L3"

subsection "Relation of provability - a closure"

text {*
  Rather than formalize a proof as a sequence of formulas with some properties [REF. Handbook],
  a deductive closure of BL was preferred. Such a structure can be formalized as an inductive set
  \CnBL of formulas with parameter \Gamma. The set contains the axiomatic schemata, the elements
  of \Gamma and it is closed under the rule modus ponens. Therefore proving of
  \Gamma \proof_BL\ \phi, i.e. searching for a sequence of formulas satisfying the definition of
  proof, is now /reduced?/ to inspecting of a membership \phi \<in> CnBL \Gamma,  which seems to
  be handled easier in Isabelle/HOL.
*}

inductive_set
  CnBL :: "formulaBL set \<Rightarrow> formulaBL set"
  for \<Gamma>
where
  BL1:
    "((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L ((\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>))) \<in> CnBL \<Gamma>"
| BL4:
    "((\<phi> &\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>)) \<longrightarrow>\<^sub>B\<^sub>L (\<psi> &\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>))) \<in> CnBL \<Gamma>"
| BL5a:
    "((\<phi> &\<^sub>B\<^sub>L \<psi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>))) \<in> CnBL \<Gamma>"
| BL5b:
    "(((\<phi> \<longrightarrow>\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>)) \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> &\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L \<chi>))) \<in> CnBL \<Gamma>"
| BL6:
    "(((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L (((\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>) \<longrightarrow>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L \<chi>)) \<in> CnBL \<Gamma>"
| BL7:
    "(\<zero>\<^sub>B\<^sub>L \<longrightarrow>\<^sub>B\<^sub>L \<phi>) \<in> CnBL \<Gamma>"
| Assumption:
    "\<phi> \<in> \<Gamma> \<Longrightarrow> \<phi> \<in> CnBL \<Gamma>"
| MP:
    "\<psi> \<in> CnBL \<Gamma> \<and> (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>) \<in> CnBL \<Gamma> \<Longrightarrow> \<phi> \<in> CnBL \<Gamma>"

declare CnBL.intros [intro]

text {*
  For formal reasons, a definition of /proof_BL/ is mentioned, although it has no use since all
  the proofs would begin with unfolding this definition followed by investigation of the deductive
  closure.
*}

definition ProvRelBL :: "formulaBL set \<Rightarrow> formulaBL \<Rightarrow> bool"
(infixr "\<turnstile>\<^sub>B\<^sub>L" 10)
where
  "ProvRelBL \<Gamma> \<phi> \<equiv> \<phi> \<in> CnBL \<Gamma>"
end
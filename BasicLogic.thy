(*
Title:        BasicLogic.thy
Description:  Definitions of syntax and axiomatization of Basic Logic.
Author:       Petr Revay, Department of Logic, Faculty of Arts, Charles University in Prague
*)

theory BasicLogic
imports Main String
begin

datatype formulaBL =
  Var char (".") 
| Const_0
| Conjuction_BL_strong formulaBL formulaBL
  (infixr "&\<^sub>B\<^sub>L" 50)
| Implication_BL formulaBL formulaBL
  (infix "\<longrightarrow>\<^sub>B\<^sub>L" 35) 

type_synonym unary_conn =
  "formulaBL \<Rightarrow> formulaBL"
type_synonym binary_conn =
  "formulaBL \<Rightarrow> formulaBL \<Rightarrow> formulaBL"

definition Const_1 :: "formulaBL"
where
(*--"Hajek Def. 2.2.13 (str.41)"*)
  "Const_1 \<equiv> (Const_0 \<longrightarrow>\<^sub>B\<^sub>L Const_0)"

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
  "Negation_BL \<phi> \<equiv> \<phi> \<longrightarrow>\<^sub>B\<^sub>L Const_0"

fun MultiConj_BL :: "formulaBL \<Rightarrow> nat \<Rightarrow> formulaBL"
(infixr "^\<^sup>B\<^sup>L" 60)
where
  "MultiConj_BL \<phi> 0 = Const_1"
| "MultiConj_BL \<phi> n = (\<phi> &\<^sub>B\<^sub>L (MultiConj_BL \<phi> (n - 1)))"

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
    "(Const_0 \<longrightarrow>\<^sub>B\<^sub>L \<phi>) \<in> CnBL \<Gamma>"
| Assumption:
    "\<phi> \<in> \<Gamma> \<Longrightarrow> \<phi> \<in> CnBL \<Gamma>"
| MP:
    "\<psi> \<in> CnBL \<Gamma> \<and> (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>) \<in> CnBL \<Gamma> \<Longrightarrow> \<phi> \<in> CnBL \<Gamma>"

declare CnBL.intros [intro]
--"deklarace pravidel zavedeni CnBL"

definition ProvRelBL :: "formulaBL set \<Rightarrow> formulaBL \<Rightarrow> bool"
(infixr "\<turnstile>\<^sub>B\<^sub>L" 10)
where
  "ProvRelBL \<Gamma> \<phi> \<equiv> \<phi> \<in> CnBL \<Gamma>"

end

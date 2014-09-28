(*
Title:        BL_theorems.thy
Description:  Proving in Hilbert-like calculus of Basic Logic
Author:       Petr Revay, Department of Logic, Faculty of Arts, Charles University in Prague
*)

theory BL_theorems
imports BasicLogic

begin

lemma BL_transitivity_of_implication [rule_format, simp]:
"\<lbrakk>(\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<in> CnBL \<Gamma>; (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>) \<in> CnBL \<Gamma>\<rbrakk> \<Longrightarrow> (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>) \<in> CnBL \<Gamma>"
proof -
  assume
  1: "(\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<in> CnBL \<Gamma>"
  assume
  2: "(\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>) \<in> CnBL \<Gamma>"
  from 1 and 2 have
  3: "((\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>)) \<in> CnBL \<Gamma>"
    by (metis (full_types) CnBL.BL1 CnBL.MP)
  from 2 and 3 have
  4: "(\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>) \<in> CnBL \<Gamma>"
    by (metis CnBL.MP)
  then show ?thesis
    by metis
qed

text{*
Proofs by Karel Chvalovsky: On the independence of axioms in BL and MTL
*}

theorem TBL1 [simp]:
"\<forall>\<phi>. (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>) \<in> CnBL {}"
proof
  fix \<phi>
  from BL5b and BL6 have
  3: "((((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>)) \<longrightarrow>\<^sub>B\<^sub>L
       (((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>) &\<^sub>B\<^sub>L \<phi>) \<longrightarrow>\<^sub>B\<^sub>L \<phi>)) \<longrightarrow>\<^sub>B\<^sub>L
        (((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>) &\<^sub>B\<^sub>L \<phi>) \<longrightarrow>\<^sub>B\<^sub>L \<phi>)) \<in> CnBL {}"
    by (metis (full_types) CnBL.MP)
  from BL5b and 3 have
  4: "(((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>) &\<^sub>B\<^sub>L \<phi>) \<longrightarrow>\<^sub>B\<^sub>L \<phi>) \<in> CnBL {}"
    by (metis CnBL.MP)
  from 4 and BL5a have
  6: "((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>)) \<in> CnBL {}"
    by (metis (full_types) CnBL.MP)
  from 6 and BL6 have
  8: "(((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>)) \<longrightarrow>\<^sub>B\<^sub>L
       (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>)) \<in> CnBL {}"
    by (metis (full_types) CnBL.MP)
  from 6 and 8 show
  9: "(\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>) \<in> CnBL {}"
    by (metis (full_types) CnBL.MP)
qed

lemma Chvalovsky_4_4_b_13 [simp]:
"\<forall>\<phi>. ((\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L (((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) &\<^sub>B\<^sub>L \<phi>) \<longrightarrow>\<^sub>B\<^sub>L \<chi>)) \<in> CnBL {}"
proof
  fix \<phi>
  from TBL1 and BL5b have
  11: "(((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) &\<^sub>B\<^sub>L \<phi>) \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<in> CnBL {}"
    by (metis (full_types) CnBL.MP)
  from 11 and BL1 show
  13: "((\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L (((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) &\<^sub>B\<^sub>L \<phi>) \<longrightarrow>\<^sub>B\<^sub>L \<chi>)) \<in> CnBL {}"
    by (metis (full_types) CnBL.MP)
qed

lemma Chvalovsky_4_4_b_17 [simp]:
"\<forall>\<phi>. (((\<chi> \<longrightarrow>\<^sub>B\<^sub>L (Const_0 &\<^sub>B\<^sub>L \<psi>)) &\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L \<phi>) \<in> CnBL {}"
proof
  fix \<phi>
  from BL7 and BL5a have
  15: "((Const_0 &\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L \<phi>) \<in> CnBL {}"
    by (metis (full_types) CnBL.BL5b CnBL.MP)
  then show
  17: "(((\<chi> \<longrightarrow>\<^sub>B\<^sub>L (Const_0 &\<^sub>B\<^sub>L \<psi>)) &\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L \<phi>) \<in> CnBL {}"
    by (metis (full_types) Chvalovsky_4_4_b_13 CnBL.MP)
qed

lemma Chvalovsky_4_4_b_19 [simp]:
"\<forall>\<phi>. ((\<phi> \<longrightarrow>\<^sub>B\<^sub>L (Const_0 &\<^sub>B\<^sub>L \<psi>)) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>)) \<in> CnBL {}"
proof
  fix \<phi>
  have
  18: "((((\<phi> \<longrightarrow>\<^sub>B\<^sub>L (Const_0 &\<^sub>B\<^sub>L \<psi>)) &\<^sub>B\<^sub>L \<phi>) \<longrightarrow>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> \<longrightarrow>\<^sub>B\<^sub>L (Const_0 &\<^sub>B\<^sub>L \<psi>)) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>))) \<in> CnBL {}"
    by (metis CnBL.BL5a)
  from Chvalovsky_4_4_b_17 and 18 show
  19: "((\<phi> \<longrightarrow>\<^sub>B\<^sub>L (Const_0 &\<^sub>B\<^sub>L \<psi>)) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>)) \<in> CnBL {}"
    by (metis (full_types) CnBL.MP)
qed
  
lemma Chvalovsky_4_4_b [simp]:
"\<forall>\<phi>. (\<phi> &\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L Const_0) \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<in> CnBL {}"
proof
  fix \<phi>
  from Chvalovsky_4_4_b_19 have
  21: "(((\<phi> &\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L Const_0)) \<longrightarrow>\<^sub>B\<^sub>L (Const_0 &\<^sub>B\<^sub>L (Const_0 \<longrightarrow>\<^sub>B\<^sub>L \<phi>))) \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> &\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L Const_0)) \<longrightarrow>\<^sub>B\<^sub>L \<psi>)) \<in> CnBL {}"
    by metis
  from BL4 and 21 show
  22: "(\<phi> &\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L Const_0) \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<in> CnBL {}"
    by (metis (full_types) Chvalovsky_4_4_b_19 CnBL.MP)
qed

lemma Chvalovsky_4_4_c_25 [simp]:
"\<forall>\<phi>. ((((\<phi> \<longrightarrow>\<^sub>B\<^sub>L Const_0) \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>)) \<in> CnBL {}"
by (metis (full_types) Chvalovsky_4_4_b CnBL.BL1 CnBL.BL5a CnBL.MP)

lemma Chvalovsky_4_4_c_26 [simp]:
"\<forall>\<phi>. ((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L (Const_0 \<longrightarrow>\<^sub>B\<^sub>L \<psi>)) \<in> CnBL {}"
by (metis (full_types) CnBL.BL1 CnBL.BL7 CnBL.MP)

lemma Chvalovsky_4_4_c_28 [simp]:
"\<forall>\<phi>. (\<phi> \<longrightarrow>\<^sub>B\<^sub>L (Const_0 \<longrightarrow>\<^sub>B\<^sub>L \<psi>)) \<in> CnBL {}"
by (metis (full_types) Chvalovsky_4_4_c_25 Chvalovsky_4_4_c_26 CnBL.MP)

theorem TBL10 [simp]:
"\<forall>\<phi>. (\<phi> \<longrightarrow>\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L (\<phi> &\<^sub>B\<^sub>L \<psi>))) \<in> CnBL {}"
by (metis (full_types) CnBL.BL5a CnBL.MP TBL1)

lemma Chvalovsky_4_4_c_31 [simp]:
"\<forall>\<phi>. (\<psi> \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>) &\<^sub>B\<^sub>L \<psi>)) \<in> CnBL {}"
by (metis (full_types) CnBL.MP TBL1 TBL10)

lemma Chvalovsky_4_4_c_33 [simp]:
"\<forall>\<phi>. ((\<chi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>) &\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L (Const_0 \<longrightarrow>\<^sub>B\<^sub>L \<psi>))) \<in> CnBL {}"
by (metis (full_types) Chvalovsky_4_4_c_28 Chvalovsky_4_4_c_31 CnBL.MP)

lemma Chvalovsky_4_4_c_35 [simp]:
"\<forall>\<phi>. ((Const_0 \<longrightarrow>\<^sub>B\<^sub>L \<psi>) &\<^sub>B\<^sub>L ((Const_0 \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>))) \<in> CnBL {}"
proof
  fix \<phi>
  from Chvalovsky_4_4_c_33 show
  35: "((Const_0 \<longrightarrow>\<^sub>B\<^sub>L \<psi>) &\<^sub>B\<^sub>L ((Const_0 \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>))) \<in> CnBL {}"
    by (metis CnBL.simps)
qed

lemma Chvalovsky_4_4_c_39 [simp]:
"\<forall>\<phi>. (((\<psi> \<longrightarrow>\<^sub>B\<^sub>L (Const_0 \<longrightarrow>\<^sub>B\<^sub>L \<chi>)) \<longrightarrow>\<^sub>B\<^sub>L \<xi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<xi>)) \<in> CnBL {}"
by (metis (full_types) Chvalovsky_4_4_c_28 CnBL.BL1 CnBL.MP)

lemma Chvalovsky_4_4_c_42 [simp]:
"\<forall>\<phi>. (\<xi> \<longrightarrow>\<^sub>B\<^sub>L (((Const_0 \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>))) \<in> CnBL {}"
by (metis (full_types) Chvalovsky_4_4_c_39 CnBL.BL1 CnBL.MP)

lemma Chvalovsky_4_4_c_44 [simp]:
"\<forall>\<phi>. ((\<phi> &\<^sub>B\<^sub>L ((Const_0 \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L \<chi>)) \<longrightarrow>\<^sub>B\<^sub>L (\<xi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>)) \<in> CnBL {}"
by (metis (full_types) Chvalovsky_4_4_c_42 CnBL.BL5b CnBL.MP)

lemma Chvalovsky_4_4_c_45 [simp]:
"\<forall>\<phi>. (((Const_0 \<longrightarrow>\<^sub>B\<^sub>L \<phi>) &\<^sub>B\<^sub>L ((Const_0 \<longrightarrow>\<^sub>B\<^sub>L \<phi>) \<longrightarrow>\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>))) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>))) \<in> CnBL {}"
by (metis Chvalovsky_4_4_c_44)

lemma Chvalovsky_4_4_c [simp]:
"\<forall>\<phi>. ((\<phi> &\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<in> CnBL {}"
by (metis (full_types) Chvalovsky_4_4_c_35 Chvalovsky_4_4_c_44 CnBL.BL5b CnBL.MP)

lemma Chvalovsky_4_4_c_50 [simp]:
"\<forall>\<phi>. ((\<phi> \<longrightarrow>\<^sub>B\<^sub>L (\<psi> &\<^sub>B\<^sub>L \<chi>)) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>)) \<in> CnBL {}"
proof
  fix \<phi>
  from Chvalovsky_4_4_b_13 have
  48: "(((\<psi> &\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L (((\<phi> \<longrightarrow>\<^sub>B\<^sub>L (\<psi> &\<^sub>B\<^sub>L \<chi>)) &\<^sub>B\<^sub>L \<phi>) \<longrightarrow>\<^sub>B\<^sub>L \<chi>)) \<in> CnBL {}"
    by metis
  from Chvalovsky_4_4_c and 48 have
  49: "(((\<phi> \<longrightarrow>\<^sub>B\<^sub>L (\<psi> &\<^sub>B\<^sub>L \<chi>)) &\<^sub>B\<^sub>L \<phi>) \<longrightarrow>\<^sub>B\<^sub>L \<chi>) \<in> CnBL {}"
    by (metis (full_types) CnBL.MP)  
  from 49 and BL5a show
  50: "(((\<phi> \<longrightarrow>\<^sub>B\<^sub>L (\<psi> &\<^sub>B\<^sub>L \<chi>)) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>))) \<in> CnBL {}"
    by (metis (full_types) CnBL.MP)
qed

lemma Chvalovsky_4_4_54 [simp]:
"\<forall>\<phi>. ((((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>)) \<longrightarrow>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>)) \<in> CnBL {}"
proof
  fix \<phi> \<chi>
  from Chvalovsky_4_4_c_50 have
  51: "(((\<phi> &\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>)) \<longrightarrow>\<^sub>B\<^sub>L (\<psi> &\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>))) \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> &\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>)) \<longrightarrow>\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>))) \<in> CnBL {}" by simp
  from 51 have
  52: "((\<phi> &\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>)) \<longrightarrow>\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>)) \<in> CnBL {}"
    by (metis (full_types) BL_transitivity_of_implication Chvalovsky_4_4_c CnBL.BL4)
  from 52 have
  53: "(\<phi> \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>))) \<in> CnBL {}"
    by (metis (full_types) CnBL.BL5a CnBL.MP)
  from 53 show
  54: "((((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>)) \<longrightarrow>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>)) \<in> CnBL {}"
    by (metis (full_types) CnBL.BL1 CnBL.MP)
qed

theorem TBL2 [simp]:
"\<forall>\<phi>. (\<phi> \<longrightarrow>\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>)) \<in> CnBL {}"
proof
  fix \<phi>
  from TBL1 have
  56: "(((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>)) \<longrightarrow>\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>)) \<in> CnBL {}"
    by (metis (full_types) CnBL.BL6 CnBL.MP) 
  from 56 and Chvalovsky_4_4_54 show
  57: "(\<phi> \<longrightarrow>\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>)) \<in> CnBL {}"
    by (metis (full_types) CnBL.MP)
qed

theorem TBL6 [simp]:
"\<forall>\<phi>. (\<phi> &\<^sub>B\<^sub>L \<psi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>) \<in> CnBL {}"
by (metis (full_types) CnBL.BL5b CnBL.MP TBL2)

text{*
Proofs by Petr Cintula: Short note: On the redundancy of axiom (A3) in BL and MTL
*}

lemma Hajek_4 [simp]:
"\<forall>\<phi>. ((\<phi> &\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>)) \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<in> CnBL {}"
proof
  fix \<phi>
  from BL4 and BL1 have
  1: "(((\<psi> &\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>)) \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> &\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>)) \<longrightarrow>\<^sub>B\<^sub>L \<psi>)) \<in> CnBL {}"
    by (metis (full_types) CnBL.MP)
  from TBL6 and 1 show
  2: "((\<phi> &\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>)) \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<in> CnBL {}"
    by (metis CnBL.MP)
qed

lemma TBL5 [simp]:
"\<forall>\<phi>. (\<phi> \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L \<psi>)) \<in> CnBL {}"
proof
  fix \<phi>
  from Hajek_4 and BL5a show
  3: "(\<phi> \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L \<psi>)) \<in> CnBL {}"
    by (metis (full_types) CnBL.MP) 
qed

theorem TBL3 [simp]:
"\<forall>\<phi>. ((\<phi> \<longrightarrow>\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>)) \<longrightarrow>\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>))) \<in> CnBL {}"
proof
  fix \<phi>
  from TBL5 and BL1 have
  2: "((((\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>)) \<longrightarrow>\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>))) \<in> CnBL {}"
    by (metis (full_types) CnBL.MP)  
  from 2 show
  3: "((\<phi> \<longrightarrow>\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>)) \<longrightarrow>\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>))) \<in> CnBL {}"
    by (metis (full_types) BL_transitivity_of_implication CnBL.BL1)
qed

theorem TBL7 [simp]:
"\<forall>\<phi>. (\<phi> &\<^sub>B\<^sub>L \<psi> \<longrightarrow>\<^sub>B\<^sub>L \<psi> &\<^sub>B\<^sub>L \<phi>) \<in> CnBL {}"
proof
  fix \<phi> \<chi>
  from TBL1 and BL5a have 1:
    "(\<psi> \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L (\<psi> &\<^sub>B\<^sub>L \<phi>))) \<in> CnBL {}" by blast
  from 1 and TBL3 have 2:
    "(\<phi> \<longrightarrow>\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L (\<psi> &\<^sub>B\<^sub>L \<phi>))) \<in> CnBL {}" by blast
  from 2 and BL5b show
    "(\<phi> &\<^sub>B\<^sub>L \<psi> \<longrightarrow>\<^sub>B\<^sub>L \<psi> &\<^sub>B\<^sub>L \<phi>) \<in> CnBL {}" by blast
qed

text{*
The other proofs
*}

theorem TBL4 [simp]:
"\<forall>\<phi>. ((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L ((\<chi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>) \<longrightarrow>\<^sub>B\<^sub>L (\<chi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>))) \<in> CnBL {}"
by (metis CnBL.BL1 CnBL.MP TBL3)

lemma Hajek_20 [simp]:
"\<forall>\<phi>. (\<phi> \<longrightarrow>\<^sub>B\<^sub>L Const_1 &\<^sub>B\<^sub>L \<phi>) \<in> CnBL {}"
by (metis Chvalovsky_4_4_c_31 Const_1_def)

theorem TBL8 [simp]:
"\<forall>\<phi>. ((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> &\<^sub>B\<^sub>L \<chi> \<longrightarrow>\<^sub>B\<^sub>L \<psi> &\<^sub>B\<^sub>L \<chi>)) \<in> CnBL {}"
proof
  fix \<phi>
  from Hajek_4 and BL1 have
  1: "((\<psi> \<longrightarrow>\<^sub>B\<^sub>L (\<chi> \<longrightarrow>\<^sub>B\<^sub>L (\<psi> &\<^sub>B\<^sub>L \<chi>))) \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> &\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>)) \<longrightarrow>\<^sub>B\<^sub>L (\<chi> \<longrightarrow>\<^sub>B\<^sub>L (\<psi> &\<^sub>B\<^sub>L \<chi>)))) \<in> CnBL {}"
    by (metis (full_types) CnBL.MP)
  from TBL10 and 1 have
  2: "((\<phi> &\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>)) \<longrightarrow>\<^sub>B\<^sub>L (\<chi> \<longrightarrow>\<^sub>B\<^sub>L (\<psi> &\<^sub>B\<^sub>L \<chi>))) \<in> CnBL {}"
    by (metis CnBL.MP)
  from 2 and BL5a have
  3: "(\<phi> \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L (\<chi> \<longrightarrow>\<^sub>B\<^sub>L (\<psi> &\<^sub>B\<^sub>L \<chi>)))) \<in> CnBL {}"
    by (metis (full_types) CnBL.MP)
  from 3 and BL1 have
  4: "(((((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L (\<chi> \<longrightarrow>\<^sub>B\<^sub>L (\<psi> &\<^sub>B\<^sub>L \<chi>)))) \<longrightarrow>\<^sub>B\<^sub>L ((\<chi> \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L (\<psi> &\<^sub>B\<^sub>L \<chi>))))) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L (\<chi> \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L (\<psi> &\<^sub>B\<^sub>L \<chi>))))) \<in> CnBL {}"
    by (metis (full_types) CnBL.MP)
  from TBL3 and 4 have
  5: "((\<phi> \<longrightarrow>\<^sub>B\<^sub>L (\<chi> \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L (\<psi> &\<^sub>B\<^sub>L \<chi>))))) \<in> CnBL {}"
    by (metis CnBL.MP)
  from 5 and BL5b have
  6: "((\<phi> &\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L (\<psi> &\<^sub>B\<^sub>L \<chi>))) \<in> CnBL {}"
    by (metis (full_types) CnBL.MP)
  from 6 and TBL3 show
  7: "((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> &\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L (\<psi> &\<^sub>B\<^sub>L \<chi>))) \<in> CnBL {}"
    by (metis (full_types) CnBL.MP)
qed 

theorem TBL9a [simp]:
"\<forall>\<phi>. (((\<phi> &\<^sub>B\<^sub>L \<psi>) &\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> &\<^sub>B\<^sub>L (\<psi> &\<^sub>B\<^sub>L \<chi>))) \<in> CnBL {}"
proof
  fix \<phi>
  have
  1: "((\<phi> &\<^sub>B\<^sub>L (\<psi> &\<^sub>B\<^sub>L \<chi>)) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> &\<^sub>B\<^sub>L (\<psi> &\<^sub>B\<^sub>L \<chi>))) \<in> CnBL {}"
    by (metis TBL1)
  from 1 and BL5a  have
  2: "(\<phi> \<longrightarrow>\<^sub>B\<^sub>L ((\<psi> &\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> &\<^sub>B\<^sub>L (\<psi> &\<^sub>B\<^sub>L \<chi>)))) \<in> CnBL {}"
    by (metis TBL10)
  from 2 and BL1 have
  3: "((((\<psi> &\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> &\<^sub>B\<^sub>L (\<psi> &\<^sub>B\<^sub>L \<chi>))) \<longrightarrow>\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L (\<chi> \<longrightarrow>\<^sub>B\<^sub>L (\<phi> &\<^sub>B\<^sub>L (\<psi> &\<^sub>B\<^sub>L \<chi>))))) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L (\<chi> \<longrightarrow>\<^sub>B\<^sub>L (\<phi> &\<^sub>B\<^sub>L (\<psi> &\<^sub>B\<^sub>L \<chi>)))))) \<in> CnBL {}"
    by (metis (full_types) CnBL.MP)
  from BL5a and 3 have
  4: "(\<phi> \<longrightarrow>\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L (\<chi> \<longrightarrow>\<^sub>B\<^sub>L (\<phi> &\<^sub>B\<^sub>L (\<psi> &\<^sub>B\<^sub>L \<chi>))))) \<in> CnBL {}"
    by (metis CnBL.MP)
  from BL5b and 4 have
  5: "((\<phi> &\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L (\<chi> \<longrightarrow>\<^sub>B\<^sub>L (\<phi> &\<^sub>B\<^sub>L (\<psi> &\<^sub>B\<^sub>L \<chi>)))) \<in> CnBL {}"
    by (metis (full_types) CnBL.MP)
  from BL5b and 5 show
  6: "(((\<phi> &\<^sub>B\<^sub>L \<psi>) &\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> &\<^sub>B\<^sub>L (\<psi> &\<^sub>B\<^sub>L \<chi>))) \<in> CnBL {}"
    by (metis (full_types) CnBL.MP)
qed

theorem TBL9b [simp]:
"\<forall>\<phi>. ((\<phi> &\<^sub>B\<^sub>L (\<psi> &\<^sub>B\<^sub>L \<chi>)) \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> &\<^sub>B\<^sub>L \<psi>) &\<^sub>B\<^sub>L \<chi>)) \<in> CnBL {}"
proof
  fix \<phi>
  have
  1: "(((\<phi> &\<^sub>B\<^sub>L \<psi>) &\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> &\<^sub>B\<^sub>L \<psi>) &\<^sub>B\<^sub>L \<chi>)) \<in> CnBL {}"
    by (metis TBL1)
  from 1 and BL5a have
  2: "((\<phi> &\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L (\<chi> \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> &\<^sub>B\<^sub>L \<psi>) &\<^sub>B\<^sub>L \<chi>))) \<in> CnBL {}"
    by (metis TBL10)
  from 2 and BL5a have
  3: "(\<phi> \<longrightarrow>\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L (\<chi> \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> &\<^sub>B\<^sub>L \<psi>) &\<^sub>B\<^sub>L \<chi>)))) \<in> CnBL {}"
    by (metis BL_transitivity_of_implication TBL10 TBL8)
  from 3 and BL1 have
  4: "(((\<psi> \<longrightarrow>\<^sub>B\<^sub>L (\<chi> \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> &\<^sub>B\<^sub>L \<psi>) &\<^sub>B\<^sub>L \<chi>))) \<longrightarrow>\<^sub>B\<^sub>L ((\<psi> &\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> &\<^sub>B\<^sub>L \<psi>) &\<^sub>B\<^sub>L \<chi>))) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L ((\<psi> &\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> &\<^sub>B\<^sub>L \<psi>) &\<^sub>B\<^sub>L \<chi>)))) \<in> CnBL {}"
    by (metis CnBL.MP)
  from BL5b and 4 have
  5: "(\<phi> \<longrightarrow>\<^sub>B\<^sub>L ((\<psi> &\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> &\<^sub>B\<^sub>L \<psi>) &\<^sub>B\<^sub>L \<chi>))) \<in> CnBL {}"
    by (metis CnBL.MP)
  from 5 and BL5b show
  6: "((\<phi> &\<^sub>B\<^sub>L (\<psi> &\<^sub>B\<^sub>L \<chi>)) \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> &\<^sub>B\<^sub>L \<psi>) &\<^sub>B\<^sub>L \<chi>)) \<in> CnBL {}"
    by (metis (full_types) CnBL.MP)
qed

lemma Hajek_7 [simp]:
"\<forall>\<phi>1. (((\<phi>1 \<longrightarrow>\<^sub>B\<^sub>L \<psi>1) &\<^sub>B\<^sub>L (\<phi>2 \<longrightarrow>\<^sub>B\<^sub>L \<psi>2)) \<longrightarrow>\<^sub>B\<^sub>L ((\<phi>1 &\<^sub>B\<^sub>L \<phi>2) \<longrightarrow>\<^sub>B\<^sub>L (\<psi>1 &\<^sub>B\<^sub>L \<psi>2))) \<in> CnBL {}"
by (metis (full_types) BL_transitivity_of_implication CnBL.BL5b CnBL.MP TBL10 TBL3 TBL4)

theorem TBL11 [simp]:
"\<forall>\<phi>. (\<phi> &\<^sub>B\<^sub>L \<psi> \<longrightarrow>\<^sub>B\<^sub>L \<phi> \<and>\<^sub>B\<^sub>L \<psi>) \<in> CnBL {}"
apply (unfold Conjuction_BL_weak_def)
proof
  fix \<phi>
  from TBL2 and TBL8 have
  1: "(\<psi> &\<^sub>B\<^sub>L \<phi> \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) &\<^sub>B\<^sub>L \<phi>) \<in> CnBL {}"
    by (metis (full_types) CnBL.MP)
  from 1 and CnBL.BL1 have
  2: "(\<psi> &\<^sub>B\<^sub>L \<phi> \<longrightarrow>\<^sub>B\<^sub>L \<phi> &\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>)) \<in> CnBL {}"
    by (metis (full_types) CnBL.MP TBL7)
  from 2 and CnBL.BL1 show
  3: "(\<phi> &\<^sub>B\<^sub>L \<psi> \<longrightarrow>\<^sub>B\<^sub>L \<phi> &\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>)) \<in> CnBL {}"
    by (metis (full_types) CnBL.MP TBL7)
qed

theorem ConjWeakCommute [simp]:
"\<forall>\<phi>. (\<phi> \<and>\<^sub>B\<^sub>L \<psi> \<longrightarrow>\<^sub>B\<^sub>L \<psi> \<and>\<^sub>B\<^sub>L \<phi>) \<in> CnBL {}"
by (metis CnBL.BL4 Conjuction_BL_weak_def)

theorem DisjWeakCommute [simp]:
"(\<phi> \<or>\<^sub>B\<^sub>L \<psi> \<longrightarrow>\<^sub>B\<^sub>L \<psi> \<or>\<^sub>B\<^sub>L \<phi>) \<in> CnBL {}"
by (metis CnBL.BL4 Conjuction_BL_weak_def Disjunction_BL_weak_def)

theorem TBL12 [simp]:
"(\<phi> \<and>\<^sub>B\<^sub>L \<psi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>) \<in> CnBL {}"
by (metis Conjuction_BL_weak_def TBL6)

theorem TBL16a [simp]:
"\<forall>\<phi>. ((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<phi> \<and>\<^sub>B\<^sub>L \<psi>)) \<in> CnBL {}"
by (metis CnBL.MP Conjuction_BL_weak_def TBL10 TBL3)

theorem TBL16b [simp]:
"\<forall>\<phi>. ((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<and>\<^sub>B\<^sub>L \<psi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>)) \<in> CnBL {}"
by (metis CnBL.MP Conjuction_BL_weak_def TBL2 TBL6)

theorem TBL13a [simp]:
"\<forall>\<phi>. (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<phi> \<and>\<^sub>B\<^sub>L \<phi>) \<in> CnBL {}"
by (metis CnBL.MP TBL1 TBL16a)

theorem TBL13b [simp]:
"\<forall>\<phi>. (\<phi> \<and>\<^sub>B\<^sub>L \<phi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>) \<in> CnBL {}"
by (metis Conjuction_BL_weak_def Hajek_4)

lemma emptyAsm [simp]: "\<phi> \<in> CnBL {} \<Longrightarrow> \<phi> \<in> CnBL \<Gamma>"
apply (rule CnBL.induct)
by blast+
 
lemma BL_ConjWeak_adjunction [rule_format, simp]:
"\<lbrakk>\<phi> \<in> CnBL \<Gamma>; \<psi> \<in> CnBL \<Gamma>\<rbrakk> \<Longrightarrow> (\<phi> \<and>\<^sub>B\<^sub>L \<psi>) \<in> CnBL \<Gamma>"
proof -
  assume 1: "\<phi> \<in> CnBL \<Gamma>"
  assume 2: "\<psi> \<in> CnBL \<Gamma>"
  from 1 and 2 have
  3: "(\<phi> &\<^sub>B\<^sub>L \<psi>) \<in> CnBL \<Gamma>"
    by (metis (full_types) CnBL.MP TBL10 emptyAsm)
  have
  4: "(\<phi> &\<^sub>B\<^sub>L \<psi> \<longrightarrow>\<^sub>B\<^sub>L \<phi> \<and>\<^sub>B\<^sub>L \<psi>) \<in> CnBL \<Gamma>"
    by (metis (full_types) TBL11 emptyAsm)
  from 3 and 4 show
  ?thesis
    by (metis CnBL.MP)
qed

theorem TBL24b [simp]:
"\<forall>\<phi>. (((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<and>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>)) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi> \<and>\<^sub>B\<^sub>L \<chi>)) \<in> CnBL {}"
proof
  fix \<phi>
  have
  1: "((\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<psi> \<and>\<^sub>B\<^sub>L \<chi>)) \<in> CnBL {}"
    by (metis TBL16a)
  have
  2: "(((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<and>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>)) \<longrightarrow>\<^sub>B\<^sub>L ((\<psi> \<longrightarrow>\<^sub>B\<^sub>L (\<psi> \<and>\<^sub>B\<^sub>L \<chi>)) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi> \<and>\<^sub>B\<^sub>L \<chi>))) \<in> CnBL {}"
    apply (unfold Conjuction_BL_weak_def)
    by (metis (full_types) CnBL.BL1 CnBL.BL5b CnBL.MP TBL2 TBL3)
  then have
  3: "((\<psi> \<longrightarrow>\<^sub>B\<^sub>L (\<psi> \<and>\<^sub>B\<^sub>L \<chi>)) \<longrightarrow>\<^sub>B\<^sub>L (((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<and>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>)) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi> \<and>\<^sub>B\<^sub>L \<chi>))) \<in> CnBL {}"
    by (metis (full_types) CnBL.MP TBL3)
  from 1 have
  4: "(((\<psi> \<longrightarrow>\<^sub>B\<^sub>L (\<psi> \<and>\<^sub>B\<^sub>L \<chi>)) \<longrightarrow>\<^sub>B\<^sub>L (((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<and>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>)) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi> \<and>\<^sub>B\<^sub>L \<chi>))) \<longrightarrow>\<^sub>B\<^sub>L
       (((\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L (((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<and>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>)) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi> \<and>\<^sub>B\<^sub>L \<chi>))))) \<in> CnBL {}"
    by (metis CnBL.BL1 CnBL.MP)
  from 3 and 4 have
  5: "((\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L (((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<and>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>)) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi> \<and>\<^sub>B\<^sub>L \<chi>))) \<in> CnBL {}"
    by (metis CnBL.MP)
  have
  6: "((\<chi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) &\<^sub>B\<^sub>L \<chi> \<longrightarrow>\<^sub>B\<^sub>L \<psi> \<and>\<^sub>B\<^sub>L \<chi>) \<in> CnBL {}"
    by (metis (full_types) CnBL.BL4 CnBL.BL5a CnBL.BL5b CnBL.MP Conjuction_BL_weak_def TBL3)
  then have
  7: "((\<chi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L (\<chi> \<longrightarrow>\<^sub>B\<^sub>L \<psi> \<and>\<^sub>B\<^sub>L \<chi>)) \<in> CnBL {}"
    by (metis (full_types) CnBL.BL5a CnBL.MP)
  have
  8: "((\<chi> \<longrightarrow>\<^sub>B\<^sub>L \<psi> \<and>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L (((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<and>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>)) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi> \<and>\<^sub>B\<^sub>L \<chi>))) \<in> CnBL {}"
    apply (unfold Conjuction_BL_weak_def)
    by (metis (hide_lams, mono_tags) CnBL.BL1 CnBL.BL5b CnBL.MP TBL3 TBL4)
  from 7 have
  9: "(((\<chi> \<longrightarrow>\<^sub>B\<^sub>L \<psi> \<and>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L (((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<and>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>)) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi> \<and>\<^sub>B\<^sub>L \<chi>))) \<longrightarrow>\<^sub>B\<^sub>L
      ((\<chi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L (((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<and>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>)) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi> \<and>\<^sub>B\<^sub>L \<chi>)))) \<in> CnBL {}"
    by (metis CnBL.BL1 CnBL.MP)
  from 8 and 9 have
  10: "((\<chi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L (((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<and>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>)) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi> \<and>\<^sub>B\<^sub>L \<chi>))) \<in> CnBL {}"
    by (metis CnBL.MP)
  from 5 and 10 show
  11: "(((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<and>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>)) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi> \<and>\<^sub>B\<^sub>L \<chi>)) \<in> CnBL {}"
    by (metis (mono_tags) CnBL.BL6 CnBL.MP)
qed

theorem TBL24b' [simp]:
"\<forall>\<phi>. ((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) &\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi> \<and>\<^sub>B\<^sub>L \<chi>)) \<in> CnBL {}"
proof
  fix \<phi>
  have
  1: "(((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<and>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi> \<and>\<^sub>B\<^sub>L \<chi>)) \<longrightarrow>\<^sub>B\<^sub>L
      ((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) &\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi> \<and>\<^sub>B\<^sub>L \<chi>))) \<in> CnBL {}"
    by (metis (full_types) CnBL.BL1 CnBL.MP TBL11)
  then show
  2: "((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) &\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi> \<and>\<^sub>B\<^sub>L \<chi>)) \<in> CnBL {}"
    by (metis CnBL.MP TBL24b)
qed

theorem TBL24a [simp]:
"\<forall>\<phi>. ((\<chi> \<longrightarrow>\<^sub>B\<^sub>L \<phi> \<and>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L (\<chi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>) \<and>\<^sub>B\<^sub>L (\<chi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>)) \<in> CnBL {}"
proof
  fix \<phi>
  have
  1: "((\<chi> \<longrightarrow>\<^sub>B\<^sub>L \<phi> \<and>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L (\<chi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>)) \<in> CnBL {}"
    by (metis CnBL.MP TBL12 TBL4)
  have
  2: "((\<chi> \<longrightarrow>\<^sub>B\<^sub>L \<phi> \<and>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L (\<chi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>)) \<in> CnBL {}"
    by (metis (full_types) CnBL.MP Conjuction_BL_weak_def Hajek_4 TBL4)
  from 1 and 2 have
  3: "(((\<chi> \<longrightarrow>\<^sub>B\<^sub>L \<phi> \<and>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L (\<chi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>)) &\<^sub>B\<^sub>L ((\<chi> \<longrightarrow>\<^sub>B\<^sub>L \<phi> \<and>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L (\<chi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>))) \<in> CnBL {}"
    by (metis (full_types) CnBL.MP TBL10)
  from 3 and TBL24b' show
  4: "((\<chi> \<longrightarrow>\<^sub>B\<^sub>L \<phi> \<and>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L (\<chi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>) \<and>\<^sub>B\<^sub>L (\<chi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>)) \<in> CnBL {}"
    by (metis (full_types) CnBL.MP)
qed

theorem TBL15 [simp]:
"\<forall>\<phi>. ((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<and>\<^sub>B\<^sub>L \<chi> \<longrightarrow>\<^sub>B\<^sub>L \<psi> \<and>\<^sub>B\<^sub>L \<chi>)) \<in> CnBL {}"
proof
  fix \<phi>
  have
  1: "((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) &\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi> \<and>\<^sub>B\<^sub>L \<chi>)) \<in> CnBL {}"
    by (metis TBL24b')
  then have
  2: "((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi> \<and>\<^sub>B\<^sub>L \<chi>))) \<in> CnBL {}"
    by (metis (full_types) CnBL.BL5a CnBL.MP)
  have
  3: "(((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi> \<and>\<^sub>B\<^sub>L \<chi>))) \<longrightarrow>\<^sub>B\<^sub>L
       ((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L \<psi> \<and>\<^sub>B\<^sub>L \<chi>)))) \<in> CnBL {}"
    by (metis (full_types) CnBL.MP TBL3 TBL4)
  from 2 and 3 have
  4: "((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L \<psi> \<and>\<^sub>B\<^sub>L \<chi>))) \<in> CnBL {}"
    by (metis CnBL.MP)
  have
  5: "(((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L \<psi> \<and>\<^sub>B\<^sub>L \<chi>))) \<longrightarrow>\<^sub>B\<^sub>L
       ((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> &\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L \<psi> \<and>\<^sub>B\<^sub>L \<chi>))) \<in> CnBL {}"
    by (metis (full_types) CnBL.BL5b CnBL.MP TBL4)
  from 4 and 5 show
  6: "((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<and>\<^sub>B\<^sub>L \<chi> \<longrightarrow>\<^sub>B\<^sub>L \<psi> \<and>\<^sub>B\<^sub>L \<chi>)) \<in> CnBL {}"
    by (metis CnBL.MP Conjuction_BL_weak_def)
qed

theorem TBL14a [simp]:
"\<forall>\<phi>. ((\<phi> \<and>\<^sub>B\<^sub>L (\<psi> \<and>\<^sub>B\<^sub>L \<chi>)) \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> \<and>\<^sub>B\<^sub>L \<psi>) \<and>\<^sub>B\<^sub>L \<chi>)) \<in> CnBL {}"
proof
  fix \<phi>
  have
  1 [simp]: "((\<phi> \<and>\<^sub>B\<^sub>L (\<psi> \<and>\<^sub>B\<^sub>L \<chi>)) \<longrightarrow>\<^sub>B\<^sub>L \<phi>) \<in> CnBL {}"
    by (metis TBL12)
  have
  2: "((\<phi> \<and>\<^sub>B\<^sub>L (\<psi> \<and>\<^sub>B\<^sub>L \<chi>)) \<longrightarrow>\<^sub>B\<^sub>L (\<psi> \<and>\<^sub>B\<^sub>L \<chi>)) \<in> CnBL {}"
    by (metis Conjuction_BL_weak_def Hajek_4)
  have
  3: "(\<psi> \<and>\<^sub>B\<^sub>L \<chi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<in> CnBL {}"
    by (metis TBL12)
  from 2 have
  4: "((\<psi> \<and>\<^sub>B\<^sub>L \<chi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> \<and>\<^sub>B\<^sub>L (\<psi> \<and>\<^sub>B\<^sub>L \<chi>)) \<longrightarrow>\<^sub>B\<^sub>L \<psi>)) \<in> CnBL {}"
    by (metis (full_types) CnBL.BL1 CnBL.MP)
  from 4 have
  5: "(\<phi> \<and>\<^sub>B\<^sub>L (\<psi> \<and>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<in> CnBL {}"
    by (metis CnBL.MP Conjuction_BL_weak_def TBL6)
  from 1 and 5 have
  6: "(((\<phi> \<and>\<^sub>B\<^sub>L (\<psi> \<and>\<^sub>B\<^sub>L \<chi>)) \<longrightarrow>\<^sub>B\<^sub>L \<phi>) \<and>\<^sub>B\<^sub>L (\<phi> \<and>\<^sub>B\<^sub>L (\<psi> \<and>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L \<psi>)) \<in> CnBL {}"
    by (metis BL_ConjWeak_adjunction)
  then have
  7: "(\<phi> \<and>\<^sub>B\<^sub>L (\<psi> \<and>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L \<phi> \<and>\<^sub>B\<^sub>L \<psi>) \<in> CnBL {}"
    by (metis CnBL.MP TBL24b)
  from 2 have
  8: "((\<psi> \<and>\<^sub>B\<^sub>L \<chi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<and>\<^sub>B\<^sub>L (\<psi> \<and>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L \<chi>)) \<in> CnBL {}"
    by (metis CnBL.BL1 CnBL.MP)
  then have
  9: "(\<phi> \<and>\<^sub>B\<^sub>L (\<psi> \<and>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L \<chi>) \<in> CnBL {}"
    by (metis CnBL.MP Conjuction_BL_weak_def Hajek_4)
  from 7 and 9 have
  10: "((\<phi> \<and>\<^sub>B\<^sub>L (\<psi> \<and>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L \<phi> \<and>\<^sub>B\<^sub>L \<psi>) \<and>\<^sub>B\<^sub>L (\<phi> \<and>\<^sub>B\<^sub>L (\<psi> \<and>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L \<chi>)) \<in> CnBL {}"
    by (metis BL_ConjWeak_adjunction)
  from 10 show
  11: "((\<phi> \<and>\<^sub>B\<^sub>L (\<psi> \<and>\<^sub>B\<^sub>L \<chi>)) \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> \<and>\<^sub>B\<^sub>L \<psi>) \<and>\<^sub>B\<^sub>L \<chi>)) \<in> CnBL {}"
    by (metis CnBL.MP TBL24b)
qed

theorem TBL14b [simp]:
"\<forall>\<phi>. (((\<phi> \<and>\<^sub>B\<^sub>L \<psi>) \<and>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<and>\<^sub>B\<^sub>L (\<psi> \<and>\<^sub>B\<^sub>L \<chi>))) \<in> CnBL {}"
proof
  fix \<phi>
  have
  1: "(((\<phi> \<and>\<^sub>B\<^sub>L \<psi>) \<and>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L \<phi> \<and>\<^sub>B\<^sub>L \<psi>) \<in> CnBL {}"
    by (metis TBL12)
  have
  2: "(\<phi> \<and>\<^sub>B\<^sub>L \<psi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>) \<in> CnBL {}"
    by (metis TBL12)
  from 1 and 2 have
  3: "((\<phi> \<and>\<^sub>B\<^sub>L \<psi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>) \<longrightarrow>\<^sub>B\<^sub>L (((\<phi> \<and>\<^sub>B\<^sub>L \<psi>) \<and>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L \<phi>)) \<in> CnBL {}"
    by (metis CnBL.BL1 CnBL.MP)
  from 2 and 3 have
  4: "(((\<phi> \<and>\<^sub>B\<^sub>L \<psi>) \<and>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L \<phi>) \<in> CnBL {}"
    by (metis CnBL.MP)
  have
  5: "(\<phi> \<and>\<^sub>B\<^sub>L \<psi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<in> CnBL {}"
    by (metis Conjuction_BL_weak_def Hajek_4)
  then have
  6: "(((\<phi> \<and>\<^sub>B\<^sub>L \<psi>) \<and>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L (\<psi> \<and>\<^sub>B\<^sub>L \<chi>)) \<in> CnBL {}"
    by (metis CnBL.MP TBL15)
  from 4 and 6 have
  7: "((((\<phi> \<and>\<^sub>B\<^sub>L \<psi>) \<and>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L \<phi>) \<and>\<^sub>B\<^sub>L (((\<phi> \<and>\<^sub>B\<^sub>L \<psi>) \<and>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L (\<psi> \<and>\<^sub>B\<^sub>L \<chi>))) \<in> CnBL {}"
    by (metis BL_ConjWeak_adjunction)
  then show
  8: "(((\<phi> \<and>\<^sub>B\<^sub>L \<psi>) \<and>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<and>\<^sub>B\<^sub>L (\<psi> \<and>\<^sub>B\<^sub>L \<chi>))) \<in> CnBL {}"
    by (metis (full_types) CnBL.MP TBL24b)
qed

theorem TBL17 [simp]:
"\<forall>\<phi>. (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<phi> \<or>\<^sub>B\<^sub>L \<psi>) \<in> CnBL {}"
apply (unfold Disjunction_BL_weak_def)
proof
  fix \<phi>  
  from TBL2 and TBL5 have
  1: "((\<phi> \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L \<psi>)) \<and>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L ((\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>) \<longrightarrow>\<^sub>B\<^sub>L \<phi>))) \<in> CnBL {}"
    by (metis CnBL.MP TBL10 TBL11)
  then show
  2: "(\<phi> \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<and>\<^sub>B\<^sub>L ((\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>) \<longrightarrow>\<^sub>B\<^sub>L \<phi>)) \<in> CnBL {}"
    by (metis (full_types) CnBL.MP TBL24b)
qed

theorem TBL17' [simp]:
"\<forall>\<phi>. (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi> \<or>\<^sub>B\<^sub>L \<phi>) \<in> CnBL {}"
proof
  fix \<phi>
  have
  1: "((\<phi> \<or>\<^sub>B\<^sub>L \<psi> \<longrightarrow>\<^sub>B\<^sub>L \<psi> \<or>\<^sub>B\<^sub>L \<phi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi> \<or>\<^sub>B\<^sub>L \<phi>)) \<in> CnBL {}"
    by (metis (full_types) CnBL.BL1 CnBL.MP TBL17)
  then show
  2: "(\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi> \<or>\<^sub>B\<^sub>L \<phi>) \<in> CnBL {}"
    by (metis (full_types) CnBL.MP DisjWeakCommute)
qed

theorem TBL18a [simp]:
"\<forall>\<phi>. (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<phi> \<or>\<^sub>B\<^sub>L \<phi>) \<in> CnBL {}"
by (metis TBL17)

theorem TBL18b [simp]:
"\<forall>\<phi>. (\<phi> \<or>\<^sub>B\<^sub>L \<phi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>) \<in> CnBL {}"
by (metis (full_types) CnBL.BL5b CnBL.MP Conjuction_BL_weak_def Disjunction_BL_weak_def TBL2 TBL3)

theorem TBL19 [simp]:
"\<forall>\<phi>. (\<phi> \<or>\<^sub>B\<^sub>L \<psi> \<longrightarrow>\<^sub>B\<^sub>L \<psi> \<or>\<^sub>B\<^sub>L \<phi>) \<in> CnBL {}"
by (metis CnBL.BL4 Conjuction_BL_weak_def Disjunction_BL_weak_def)

lemma TBL27b [simp]:
"\<forall>\<phi>. (((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>) \<and>\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>)) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<or>\<^sub>B\<^sub>L \<psi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>)) \<in> CnBL {}"
proof
  fix \<phi>
  have
--"get the first assumption"
  1: "((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<or>\<^sub>B\<^sub>L \<psi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>)) \<in> CnBL {}"
    by (metis CnBL.MP Disjunction_BL_weak_def TBL12 TBL3)
  have
  2: "((\<phi> \<or>\<^sub>B\<^sub>L \<psi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L (((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>) \<and>\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>)) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<or>\<^sub>B\<^sub>L \<psi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>))) \<in> CnBL {}"
    by (metis (full_types) CnBL.BL5b CnBL.MP Conjuction_BL_weak_def TBL3 TBL4)
  from 1 and 2 have
  3: "(((\<phi> \<or>\<^sub>B\<^sub>L \<psi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L (((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>) \<and>\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>)) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<or>\<^sub>B\<^sub>L \<psi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>))) \<longrightarrow>\<^sub>B\<^sub>L
        ((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L (((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>) \<and>\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>)) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<or>\<^sub>B\<^sub>L \<psi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>)))) \<in> CnBL {}"
    by (metis (full_types) CnBL.BL1 CnBL.MP)
  from 2 and 3 have
  4: "((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L (((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>) \<and>\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>)) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<or>\<^sub>B\<^sub>L \<psi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>))) \<in> CnBL {}"
    by (metis CnBL.MP)
--"obtain the second one"
  have
  5: "(\<phi> \<or>\<^sub>B\<^sub>L \<psi> \<longrightarrow>\<^sub>B\<^sub>L ((\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>) \<longrightarrow>\<^sub>B\<^sub>L \<phi>)) \<in> CnBL {}"
    by (metis (full_types) Conjuction_BL_weak_def Disjunction_BL_weak_def Hajek_4)
  then have  
  6: "((\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<or>\<^sub>B\<^sub>L \<psi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>)) \<in> CnBL {}"
    by (metis (full_types) CnBL.MP TBL3)
  have
  7: "((\<phi> \<or>\<^sub>B\<^sub>L \<psi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>) \<longrightarrow>\<^sub>B\<^sub>L (((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>) \<and>\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>)) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<or>\<^sub>B\<^sub>L \<psi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>))) \<in> CnBL {}"
    by (metis (mono_tags) CnBL.BL5b CnBL.MP Conjuction_BL_weak_def TBL2 TBL3 TBL4)
  from 6 and 7 have
  8: "(((\<phi> \<or>\<^sub>B\<^sub>L \<psi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>) \<longrightarrow>\<^sub>B\<^sub>L (((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>) \<and>\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>)) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<or>\<^sub>B\<^sub>L \<psi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>))) \<longrightarrow>\<^sub>B\<^sub>L
        ((\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>) \<longrightarrow>\<^sub>B\<^sub>L (((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>) \<and>\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>)) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<or>\<^sub>B\<^sub>L \<psi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>)))) \<in> CnBL {}"
    by (metis (full_types) CnBL.BL1 CnBL.MP)
  from 7 and 8 have
  9: "(((\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>) \<longrightarrow>\<^sub>B\<^sub>L (((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>) \<and>\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>)) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<or>\<^sub>B\<^sub>L \<psi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>)))) \<in> CnBL {}"
    by (metis CnBL.MP)
--"use BL6 now"
  from 4 and 9 show
  10: "(((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>) \<and>\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>)) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<or>\<^sub>B\<^sub>L \<psi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>)) \<in> CnBL {}"
    by (metis (mono_tags) CnBL.BL6 CnBL.MP)
qed

lemma TBL27b' [simp]:
"\<forall>\<phi>. (((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>) &\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>)) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<or>\<^sub>B\<^sub>L \<psi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>)) \<in> CnBL {}"
proof
  fix \<phi>
  have
  1: "((((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>) &\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>)) \<longrightarrow>\<^sub>B\<^sub>L((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>) \<and>\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>))) \<longrightarrow>\<^sub>B\<^sub>L
       (((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>) &\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>)) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<or>\<^sub>B\<^sub>L \<psi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>))) \<in> CnBL {}"
    by (metis (full_types) CnBL.MP TBL27b TBL4)
  then show
  2: "(((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>) &\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>)) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<or>\<^sub>B\<^sub>L \<psi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>)) \<in> CnBL {}"
    by (metis CnBL.MP TBL11)
qed

theorem TBL20a [simp]:
"\<forall>\<phi>. ((\<phi> \<or>\<^sub>B\<^sub>L (\<psi> \<or>\<^sub>B\<^sub>L \<chi>)) \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> \<or>\<^sub>B\<^sub>L \<psi>) \<or>\<^sub>B\<^sub>L \<chi>)) \<in> CnBL {}"
proof
  fix \<phi>
  have
  1: "(((\<phi> \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> \<or>\<^sub>B\<^sub>L \<psi>) \<or>\<^sub>B\<^sub>L \<chi>)) &\<^sub>B\<^sub>L ((\<psi> \<or>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> \<or>\<^sub>B\<^sub>L \<psi>) \<or>\<^sub>B\<^sub>L \<chi>))) \<longrightarrow>\<^sub>B\<^sub>L
       (\<phi> \<or>\<^sub>B\<^sub>L (\<psi> \<or>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> \<or>\<^sub>B\<^sub>L \<psi>) \<or>\<^sub>B\<^sub>L \<chi>))) \<in> CnBL {}"
    by (metis TBL27b')
  have
  2: "(\<phi> \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> \<or>\<^sub>B\<^sub>L \<psi>) \<or>\<^sub>B\<^sub>L \<chi>)) \<in> CnBL {}"
    by (metis CnBL.MP TBL17 TBL4)
  have
  3: "(\<psi> \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<or>\<^sub>B\<^sub>L \<psi>)) \<in> CnBL {}"
    by (metis TBL17')
  have
  4:"((\<phi> \<or>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> \<or>\<^sub>B\<^sub>L \<psi>) \<or>\<^sub>B\<^sub>L \<chi>)) \<in> CnBL {}"
    by (metis TBL17)
  from 3 and 4 have
  5: "(\<psi> \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> \<or>\<^sub>B\<^sub>L \<psi>) \<or>\<^sub>B\<^sub>L \<chi>)) \<in> CnBL {}"
    by (metis CnBL.MP TBL4)
  have 
  6: "(\<chi> \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> \<or>\<^sub>B\<^sub>L \<psi>) \<or>\<^sub>B\<^sub>L \<chi>)) \<in> CnBL {}"
    by (metis TBL17')
  from 5 and TBL10 have
  7: "((\<chi> \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> \<or>\<^sub>B\<^sub>L \<psi>) \<or>\<^sub>B\<^sub>L \<chi>)) \<longrightarrow>\<^sub>B\<^sub>L
        ((\<psi> \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> \<or>\<^sub>B\<^sub>L \<psi>) \<or>\<^sub>B\<^sub>L \<chi>)) &\<^sub>B\<^sub>L (\<chi> \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> \<or>\<^sub>B\<^sub>L \<psi>) \<or>\<^sub>B\<^sub>L \<chi>)))) \<in> CnBL {}"
    by (metis (full_types) CnBL.MP)    
  from 6 and 7 have
  8: "((\<psi> \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> \<or>\<^sub>B\<^sub>L \<psi>) \<or>\<^sub>B\<^sub>L \<chi>)) &\<^sub>B\<^sub>L (\<chi> \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> \<or>\<^sub>B\<^sub>L \<psi>) \<or>\<^sub>B\<^sub>L \<chi>))) \<in> CnBL {}"
    by (metis CnBL.MP)
  from 8 have
  9: "((\<psi> \<or>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> \<or>\<^sub>B\<^sub>L \<psi>) \<or>\<^sub>B\<^sub>L \<chi>)) \<in> CnBL {}"
    by (metis (full_types) CnBL.MP TBL27b')
  from 2 and 9 have
  10: "((\<phi> \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> \<or>\<^sub>B\<^sub>L \<psi>) \<or>\<^sub>B\<^sub>L \<chi>)) &\<^sub>B\<^sub>L ((\<psi> \<or>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> \<or>\<^sub>B\<^sub>L \<psi>) \<or>\<^sub>B\<^sub>L \<chi>))) \<in> CnBL {}"
    by (metis CnBL.MP TBL10)
  from 10 show
  11: "((\<phi> \<or>\<^sub>B\<^sub>L (\<psi> \<or>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> \<or>\<^sub>B\<^sub>L \<psi>) \<or>\<^sub>B\<^sub>L \<chi>))) \<in> CnBL {}"
    by (metis (full_types) CnBL.MP TBL27b')
qed

theorem TBL20b [simp]:
"\<forall>\<phi>. (((\<phi> \<or>\<^sub>B\<^sub>L \<psi>) \<or>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<or>\<^sub>B\<^sub>L (\<psi> \<or>\<^sub>B\<^sub>L \<chi>))) \<in> CnBL {}"
proof
  fix \<phi>
  have
  1: "(((\<phi> \<or>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<or>\<^sub>B\<^sub>L (\<psi> \<or>\<^sub>B\<^sub>L \<chi>))) &\<^sub>B\<^sub>L ((\<chi> \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<or>\<^sub>B\<^sub>L (\<psi> \<or>\<^sub>B\<^sub>L \<chi>)))) \<longrightarrow>\<^sub>B\<^sub>L
       ((\<phi> \<or>\<^sub>B\<^sub>L \<psi>) \<or>\<^sub>B\<^sub>L \<chi> \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<or>\<^sub>B\<^sub>L (\<psi> \<or>\<^sub>B\<^sub>L \<chi>)))) \<in> CnBL {}"
    by (metis TBL27b')
  have
  2: "((\<phi> \<or>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<or>\<^sub>B\<^sub>L (\<psi> \<or>\<^sub>B\<^sub>L \<chi>))) \<in> CnBL {}"
    by (metis (mono_tags) CnBL.BL1 CnBL.MP TBL27b' TBL10 TBL17 TBL17')
  have
  3: "(\<chi> \<longrightarrow>\<^sub>B\<^sub>L \<psi> \<or>\<^sub>B\<^sub>L \<chi>) \<in> CnBL {}"
    by (metis TBL17')
  have
  4: "(\<psi> \<or>\<^sub>B\<^sub>L \<chi> \<longrightarrow>\<^sub>B\<^sub>L \<phi> \<or>\<^sub>B\<^sub>L (\<psi> \<or>\<^sub>B\<^sub>L \<chi>)) \<in> CnBL {}"
    by (metis TBL17')
  from 3 have
  5: "((\<psi> \<or>\<^sub>B\<^sub>L \<chi> \<longrightarrow>\<^sub>B\<^sub>L \<phi> \<or>\<^sub>B\<^sub>L (\<psi> \<or>\<^sub>B\<^sub>L \<chi>)) \<longrightarrow>\<^sub>B\<^sub>L (\<chi> \<longrightarrow>\<^sub>B\<^sub>L \<phi> \<or>\<^sub>B\<^sub>L (\<psi> \<or>\<^sub>B\<^sub>L \<chi>))) \<in> CnBL {}"
    by (metis (full_types) CnBL.BL1 CnBL.MP)
  from 4 and 5 have
  6: "(\<chi> \<longrightarrow>\<^sub>B\<^sub>L \<phi> \<or>\<^sub>B\<^sub>L (\<psi> \<or>\<^sub>B\<^sub>L \<chi>)) \<in> CnBL {}"
    by (metis CnBL.MP)
  from 2 and 6 have
  7: "(((\<phi> \<or>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<or>\<^sub>B\<^sub>L (\<psi> \<or>\<^sub>B\<^sub>L \<chi>))) &\<^sub>B\<^sub>L (\<chi> \<longrightarrow>\<^sub>B\<^sub>L \<phi> \<or>\<^sub>B\<^sub>L (\<psi> \<or>\<^sub>B\<^sub>L \<chi>))) \<in> CnBL {}"
    by (metis CnBL.MP TBL10)
  from 7 and 1 show
  8: "(((\<phi> \<or>\<^sub>B\<^sub>L \<psi>) \<or>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<or>\<^sub>B\<^sub>L (\<psi> \<or>\<^sub>B\<^sub>L \<chi>))) \<in> CnBL {}"
    by (metis (full_types) CnBL.MP)
qed

theorem TBL21 [simp]:
"\<forall>\<phi>. ((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<or>\<^sub>B\<^sub>L \<chi> \<longrightarrow>\<^sub>B\<^sub>L \<psi> \<or>\<^sub>B\<^sub>L \<chi>)) \<in> CnBL {}"
proof
  fix \<phi>
  have
  1: "((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi> \<or>\<^sub>B\<^sub>L \<chi>) \<and>\<^sub>B\<^sub>L (\<chi> \<longrightarrow>\<^sub>B\<^sub>L \<psi> \<or>\<^sub>B\<^sub>L \<chi>)) \<in> CnBL {}"
    by (metis BL_ConjWeak_adjunction CnBL.MP TBL17 TBL17' TBL2 TBL24b TBL4)
  have
  2: "((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi> \<or>\<^sub>B\<^sub>L \<chi>) \<and>\<^sub>B\<^sub>L (\<chi> \<longrightarrow>\<^sub>B\<^sub>L \<psi> \<or>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<or>\<^sub>B\<^sub>L \<chi> \<longrightarrow>\<^sub>B\<^sub>L \<psi> \<or>\<^sub>B\<^sub>L \<chi>)) \<in> CnBL {}"
    by (metis TBL27b)
  from 1 and 2 have
  3: "(((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi> \<or>\<^sub>B\<^sub>L \<chi>) \<and>\<^sub>B\<^sub>L (\<chi> \<longrightarrow>\<^sub>B\<^sub>L \<psi> \<or>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<or>\<^sub>B\<^sub>L \<chi> \<longrightarrow>\<^sub>B\<^sub>L \<psi> \<or>\<^sub>B\<^sub>L \<chi>)) \<longrightarrow>\<^sub>B\<^sub>L
      ((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<or>\<^sub>B\<^sub>L \<chi> \<longrightarrow>\<^sub>B\<^sub>L \<psi> \<or>\<^sub>B\<^sub>L \<chi>))) \<in> CnBL {}"
    by (metis (full_types) CnBL.BL1 CnBL.MP)
  from 2 and 3 show
  4: "((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<or>\<^sub>B\<^sub>L \<chi> \<longrightarrow>\<^sub>B\<^sub>L \<psi> \<or>\<^sub>B\<^sub>L \<chi>)) \<in> CnBL {}"
    by (metis CnBL.MP)
qed

theorem TBL22a [simp]:
"\<forall>\<phi>. ((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<phi> \<or>\<^sub>B\<^sub>L \<psi>)) \<in> CnBL {}"
by (metis (full_types) CnBL.MP TBL17' TBL2)

theorem TBL22b [simp]:
"\<forall>\<phi>. ((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<or>\<^sub>B\<^sub>L \<psi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>)) \<in> CnBL {}"
by (metis CnBL.MP Conjuction_BL_weak_def Disjunction_BL_weak_def TBL3 TBL6)

theorem TBL23 [simp]:
"\<forall>\<phi>. ((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<or>\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>)) \<in> CnBL {}"
proof
  fix \<phi>
  from CnBL.BL6 have
  1: "(((\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>) \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<or>\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>))) \<longrightarrow>\<^sub>B\<^sub>L
        ((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<or>\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>))) \<in> CnBL {}"
    by (metis (full_types) CnBL.MP TBL17)
  from TBL17' and 1 show
  2: "((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<or>\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>)) \<in> CnBL {}"
    by (metis CnBL.MP)
qed

theorem TBL32a [simp]:
"\<forall>\<phi>. (\<phi> &\<^sub>B\<^sub>L Const_1 \<longrightarrow>\<^sub>B\<^sub>L \<phi>) \<in> CnBL {}"
by (metis TBL6)

theorem TBL32b [simp]:
"\<forall>\<phi>. (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<phi> &\<^sub>B\<^sub>L Const_1) \<in> CnBL {}"
by (metis (full_types) Chvalovsky_4_4_c_31 CnBL.MP Const_1_def Hajek_4 TBL10 TBL3)

theorem TBL33a [simp]:
"\<forall>\<phi>. (\<phi> \<and>\<^sub>B\<^sub>L Const_1 \<longrightarrow>\<^sub>B\<^sub>L \<phi>) \<in> CnBL {}"
by (metis TBL12)

theorem TBL33b [simp]:
"\<forall>\<phi>. (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<phi> \<and>\<^sub>B\<^sub>L Const_1) \<in> CnBL {}"
by (metis Chvalovsky_4_4_c_28 CnBL.MP Const_1_def TBL16a)

theorem TBL34 [simp]:
"\<forall>\<phi>. (\<phi> &\<^sub>B\<^sub>L Const_0 \<longleftrightarrow>\<^sub>B\<^sub>L Const_0) \<in> CnBL {}"
by (metis CnBL.BL7 CnBL.simps Equivalence_BL_def TBL10 TBL3 emptyAsm)

theorem TBL35a [simp]:
"\<forall>\<phi>. (\<phi> \<and>\<^sub>B\<^sub>L Const_0 \<longrightarrow>\<^sub>B\<^sub>L Const_0) \<in> CnBL {}"
by (metis Conjuction_BL_weak_def Hajek_4)

theorem TBL35b [simp]:
"\<forall>\<phi>. (Const_0 \<longrightarrow>\<^sub>B\<^sub>L \<phi> \<and>\<^sub>B\<^sub>L Const_0) \<in> CnBL {}"
by (metis CnBL.BL7)

theorem TBL36a [simp]:
"\<forall>\<phi>. ((Const_1 \<longrightarrow>\<^sub>B\<^sub>L \<phi>) \<longrightarrow>\<^sub>B\<^sub>L \<phi>) \<in> CnBL {}"
by (metis (full_types) Chvalovsky_4_4_c_42 CnBL.MP Const_1_def TBL5)

theorem TBL36b [simp]:
"\<forall>\<phi>. (\<phi> \<longrightarrow>\<^sub>B\<^sub>L (Const_1 \<longrightarrow>\<^sub>B\<^sub>L \<phi>)) \<in> CnBL {}"
by (metis TBL2)

theorem TBL37 [simp]:
"\<forall>\<phi>. (\<not>\<^sub>B\<^sub>L\<phi> \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>)) \<in> CnBL {}"
by (metis (full_types) CnBL.BL7 CnBL.MP Negation_BL_def TBL4)

theorem TBL38 [simp]:
"\<forall>\<phi>. (\<not>\<^sub>B\<^sub>L(\<phi> &\<^sub>B\<^sub>L \<not>\<^sub>B\<^sub>L\<phi>)) \<in> CnBL {}"
by (metis Chvalovsky_4_4_b Negation_BL_def)

theorem TBL39 [simp]:
"\<forall>\<phi>. ((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L (\<not>\<^sub>B\<^sub>L\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<not>\<^sub>B\<^sub>L\<phi>)) \<in> CnBL {}"
by (metis CnBL.BL1 Negation_BL_def)

theorem TBL40 [simp]:
"\<forall>\<phi>. (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<not>\<^sub>B\<^sub>L(\<not>\<^sub>B\<^sub>L\<phi>)) \<in> CnBL {}"
by (metis Negation_BL_def TBL5)


theorem TBL42 [simp]:
"\<forall>\<phi>. (\<not>\<^sub>B\<^sub>L(\<phi> \<or>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L (\<not>\<^sub>B\<^sub>L\<phi> \<and>\<^sub>B\<^sub>L \<not>\<^sub>B\<^sub>L\<psi>)) \<in> CnBL {}"
by (metis BL_ConjWeak_adjunction CnBL.MP TBL17 TBL17' TBL24b TBL39)

theorem TBL43b [simp]:
"\<forall>\<phi>. ((\<phi> \<longleftrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L ((\<chi> \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L (\<chi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>))) \<in> CnBL {}"
by (metis (full_types) CnBL.BL5b CnBL.MP Equivalence_BL_def TBL2 TBL4)

theorem TBL44a [simp]:
"\<forall>\<phi>. ((\<phi> \<longleftrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>))) \<in> CnBL {}"
by (metis (full_types) CnBL.BL1 CnBL.BL5b CnBL.MP Equivalence_BL_def TBL2)

theorem TBL44b [simp]:
"\<forall>\<phi>. ((\<phi> \<longleftrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L ((\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>))) \<in> CnBL {}"
by (metis (full_types) CnBL.BL1 CnBL.BL5b CnBL.MP Equivalence_BL_def TBL2 TBL3)

theorem TBL45a [simp]:
"\<forall>\<phi>. ((\<phi> \<longleftrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> &\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L (\<psi> &\<^sub>B\<^sub>L \<chi>))) \<in> CnBL {}"
by (metis (full_types) CnBL.BL5b CnBL.MP Equivalence_BL_def TBL2 TBL3 TBL8)

theorem TBL45b [simp]:
"\<forall>\<phi>. ((\<phi> \<longleftrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L ((\<psi> &\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> &\<^sub>B\<^sub>L \<chi>))) \<in> CnBL {}"
by (metis (full_types) CnBL.BL5b CnBL.MP Equivalence_BL_def TBL2 TBL8)

lemma VL1 [simp]:
"\<forall>\<phi>. (((\<phi> &\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L (\<chi> &\<^sub>B\<^sub>L \<xi>)) \<longrightarrow>\<^sub>B\<^sub>L ((\<psi> &\<^sub>B\<^sub>L \<phi>) \<longrightarrow>\<^sub>B\<^sub>L (\<xi> &\<^sub>B\<^sub>L \<chi>))) \<in> CnBL {}"
proof
  fix \<phi>
  have
  1: "(((\<phi> &\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L (\<chi> &\<^sub>B\<^sub>L \<xi>))\<longrightarrow>\<^sub>B\<^sub>L ((\<psi> &\<^sub>B\<^sub>L \<phi>) \<longrightarrow>\<^sub>B\<^sub>L (\<chi> &\<^sub>B\<^sub>L \<xi>))) \<in> CnBL {}"
    by (metis (full_types) CnBL.BL1 CnBL.MP TBL7)
  then have
  2: "(((\<psi> &\<^sub>B\<^sub>L \<phi>) \<longrightarrow>\<^sub>B\<^sub>L (\<chi> &\<^sub>B\<^sub>L \<xi>))\<longrightarrow>\<^sub>B\<^sub>L ((\<psi> &\<^sub>B\<^sub>L \<phi>) \<longrightarrow>\<^sub>B\<^sub>L (\<xi> &\<^sub>B\<^sub>L \<chi>))) \<in> CnBL {}"
    by (metis (full_types) CnBL.MP TBL4 TBL7)
  from 1 and 2 show
  3: "(((\<phi> &\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L (\<chi> &\<^sub>B\<^sub>L \<xi>)) \<longrightarrow>\<^sub>B\<^sub>L ((\<psi> &\<^sub>B\<^sub>L \<phi>) \<longrightarrow>\<^sub>B\<^sub>L (\<xi> &\<^sub>B\<^sub>L \<chi>))) \<in> CnBL {}"
    by (metis BL_transitivity_of_implication)
qed

lemma VL2 [simp]:
"((\<phi> &\<^sub>B\<^sub>L \<psi> &\<^sub>B\<^sub>L \<chi> \<longrightarrow>\<^sub>B\<^sub>L \<xi>) \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> &\<^sub>B\<^sub>L \<psi>) &\<^sub>B\<^sub>L \<chi> \<longrightarrow>\<^sub>B\<^sub>L \<xi>)) \<in> CnBL {}"
by (metis (full_types) CnBL.BL1 CnBL.MP TBL9a)

lemma VL3[simp]:
"\<forall>\<phi>. ((\<xi> \<longrightarrow>\<^sub>B\<^sub>L \<phi> &\<^sub>B\<^sub>L \<psi> &\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L (\<xi> \<longrightarrow>\<^sub>B\<^sub>L  (\<phi> &\<^sub>B\<^sub>L \<psi>) &\<^sub>B\<^sub>L \<chi>)) \<in> CnBL {}"
by (metis (full_types) CnBL.MP TBL4 TBL9b)

lemma Hajek_25b [simp]:
"\<forall>\<phi>. ((\<phi> \<longleftrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>)) \<in> CnBL {}"
by (metis Chvalovsky_4_4_c Equivalence_BL_def)

lemma Hajek_19 [simp]: "Const_1 \<in> CnBL {}"
apply (unfold Const_1_def)
by simp 

end

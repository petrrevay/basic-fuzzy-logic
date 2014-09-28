(*
Title:        BL_LocalDeduction.thy
Description:  Formalization of the local deduction theorem from Basic Logic.
Author:       Petr Revay, Department of Logic, Faculty of Arts, Charles University in Prague 
*)

theory BL_LocalDeduction
imports BasicLogic BL_theorems
begin

thm CnBL.induct --"nahled schematu indukce vygenerovaneho z definice CnBL"

lemma MultiConjDistribution [simp]:
  "((\<phi> ^\<^sup>B\<^sup>L n &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m) \<longleftrightarrow>\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L n + m) \<in> CnBL {}"
proof (unfold Equivalence_BL_def, induct n, simp)
  have
  1: "((Const_1 &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m \<longrightarrow>\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m &\<^sub>B\<^sub>L Const_1) \<longrightarrow>\<^sub>B\<^sub>L
      ((\<phi> ^\<^sup>B\<^sup>L m &\<^sub>B\<^sub>L Const_1 \<longrightarrow>\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m) \<longrightarrow>\<^sub>B\<^sub>L (Const_1 &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m \<longrightarrow>\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m))) \<in> CnBL {}"
    by (metis CnBL.BL1) 
  have
  2: "(Const_1 &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m \<longrightarrow>\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m &\<^sub>B\<^sub>L Const_1) \<in> CnBL {}"
    by (metis TBL7)
  have
  3: "(\<phi> ^\<^sup>B\<^sup>L m &\<^sub>B\<^sub>L Const_1 \<longrightarrow>\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m) \<in> CnBL {}"
    by (metis TBL32a)
  from 2 and 1 have
  4: "((\<phi> ^\<^sup>B\<^sup>L m &\<^sub>B\<^sub>L Const_1 \<longrightarrow>\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m) \<longrightarrow>\<^sub>B\<^sub>L (Const_1 &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m \<longrightarrow>\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m)) \<in> CnBL {}"
    by (metis (full_types) CnBL.MP)
  from 3 and 4 have
  5: "(Const_1 &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m \<longrightarrow>\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m) \<in> CnBL {}"
    by (metis CnBL.MP)
  have
  6: "(\<phi> ^\<^sup>B\<^sup>L m \<longrightarrow>\<^sub>B\<^sub>L Const_1 &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m) \<in> CnBL {}"
    by (metis Hajek_20)
  have
  7: "((Const_1 &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m \<longrightarrow>\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m) \<longrightarrow>\<^sub>B\<^sub>L
       ((\<phi> ^\<^sup>B\<^sup>L m \<longrightarrow>\<^sub>B\<^sub>L Const_1 &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m) \<longrightarrow>\<^sub>B\<^sub>L
        ((Const_1 &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m \<longrightarrow>\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m) &\<^sub>B\<^sub>L (\<phi> ^\<^sup>B\<^sup>L m \<longrightarrow>\<^sub>B\<^sub>L Const_1 &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m)))) \<in> CnBL {}"
    by (metis TBL10)
  from 5 and 7 have
  8: "((\<phi> ^\<^sup>B\<^sup>L m \<longrightarrow>\<^sub>B\<^sub>L Const_1 &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m) \<longrightarrow>\<^sub>B\<^sub>L
      ((Const_1 &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m \<longrightarrow>\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m) &\<^sub>B\<^sub>L (\<phi> ^\<^sup>B\<^sup>L m \<longrightarrow>\<^sub>B\<^sub>L Const_1 &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m))) \<in> CnBL {}"
    by (metis (full_types) CnBL.MP)
  from 6 and 8 show
  9: "((Const_1 &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m \<longrightarrow>\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m) &\<^sub>B\<^sub>L
       (\<phi> ^\<^sup>B\<^sup>L m \<longrightarrow>\<^sub>B\<^sub>L Const_1 &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m)) \<in> CnBL {}"
    by (metis CnBL.MP)
next
  fix n
  assume
  1: "((\<phi> ^\<^sup>B\<^sup>L n &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m \<longrightarrow>\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L n + m) &\<^sub>B\<^sub>L (\<phi> ^\<^sup>B\<^sup>L n + m \<longrightarrow>\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L n &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m)) \<in> CnBL {}"
  have
  2: "((\<phi> ^\<^sup>B\<^sup>L n &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m \<longrightarrow>\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L n + m) &\<^sub>B\<^sub>L (\<phi> ^\<^sup>B\<^sup>L n + m \<longrightarrow>\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L n &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m) \<longrightarrow>\<^sub>B\<^sub>L
       (\<phi> ^\<^sup>B\<^sup>L n &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m \<longrightarrow>\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L n + m)) \<in> CnBL {}"
    by (metis TBL6)
  from 1 and 2 have
  3: "(\<phi> ^\<^sup>B\<^sup>L n &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m \<longrightarrow>\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L n + m) \<in> CnBL {}"
    by (metis (full_types) CnBL.MP) --"prvni cast konjunkce"
  have
  4: "((\<phi> ^\<^sup>B\<^sup>L n &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m \<longrightarrow>\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L n + m) \<longrightarrow>\<^sub>B\<^sub>L
       (((\<phi> ^\<^sup>B\<^sup>L n &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m) &\<^sub>B\<^sub>L \<phi>) \<longrightarrow>\<^sub>B\<^sub>L
        (\<phi> ^\<^sup>B\<^sup>L n + m &\<^sub>B\<^sub>L \<phi>))) \<in> CnBL {}" by simp --"(6)"
  from 3 and 4 have
  5: "(((\<phi> ^\<^sup>B\<^sup>L n &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m) &\<^sub>B\<^sub>L \<phi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> ^\<^sup>B\<^sup>L n + m &\<^sub>B\<^sub>L \<phi>)) \<in> CnBL {}"
    by (metis (full_types) CnBL.MP)
        --"now it is necessary to swap conjunctions"
  then have
  6: "((\<phi> &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L n &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L n + m)) \<in> CnBL {}"
    by (metis (full_types) CnBL.MP VL1)
  then have
  7: "(((\<phi> &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L n) &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m) \<longrightarrow>\<^sub>B\<^sub>L
       (\<phi> &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L n + m)) \<in> CnBL {}"
    by (metis (full_types) BL_transitivity_of_implication TBL9a)
  have
  8: "(\<phi> &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L n) = (\<phi> ^\<^sup>B\<^sup>L Suc n)"
    by simp
  have
  9: "(\<phi> &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L n + m) = (\<phi> ^\<^sup>B\<^sup>L Suc n + m)"
    by simp
  from 7 and 8 and 9 have
  10: "((\<phi> ^\<^sup>B\<^sup>L Suc n &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> ^\<^sup>B\<^sup>L Suc n + m)) \<in> CnBL {}"
        by metis --"1st part of conj. done!"

  have
  11: "((\<phi> ^\<^sup>B\<^sup>L n &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m \<longrightarrow>\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L n + m) &\<^sub>B\<^sub>L (\<phi> ^\<^sup>B\<^sup>L n + m \<longrightarrow>\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L n &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m) \<longrightarrow>\<^sub>B\<^sub>L
        (\<phi> ^\<^sup>B\<^sup>L n + m \<longrightarrow>\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L n &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m)) \<in> CnBL {}"
    by (metis Chvalovsky_4_4_c)
  from 1 and 11 have
  12: "(\<phi> ^\<^sup>B\<^sup>L n + m \<longrightarrow>\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L n &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m) \<in> CnBL {}"
    by (metis CnBL.MP)
  have
  13: "((\<phi> ^\<^sup>B\<^sup>L n + m \<longrightarrow>\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L n &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m) \<longrightarrow>\<^sub>B\<^sub>L
        ((\<phi> ^\<^sup>B\<^sup>L n + m &\<^sub>B\<^sub>L \<phi>) \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> ^\<^sup>B\<^sup>L n &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m) &\<^sub>B\<^sub>L \<phi>))) \<in> CnBL {}"
    by (metis TBL8)
  from 12 and 13 have
  14: "((\<phi> ^\<^sup>B\<^sup>L n + m &\<^sub>B\<^sub>L \<phi>) \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> ^\<^sup>B\<^sup>L n &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m) &\<^sub>B\<^sub>L \<phi>)) \<in> CnBL {}"
    by (metis CnBL.MP)
  then have
  15: "(\<phi> &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L n + m \<longrightarrow>\<^sub>B\<^sub>L \<phi> &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L n &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m) \<in> CnBL {}"
      by (metis BL_transitivity_of_implication TBL7)
  then have
  16: "(\<phi> &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L n + m \<longrightarrow>\<^sub>B\<^sub>L (\<phi> &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L n) &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m) \<in> CnBL {}"
      by (metis BL_transitivity_of_implication TBL9b)
  from 16 and 8 and 9 have
  17: "(\<phi> ^\<^sup>B\<^sup>L Suc n + m \<longrightarrow>\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L Suc n &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m) \<in> CnBL {}"
    by metis
      --"2nd part done! now just make the final conj."
  have
  18: "(((\<phi> ^\<^sup>B\<^sup>L Suc n &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> ^\<^sup>B\<^sup>L Suc n + m)) \<longrightarrow>\<^sub>B\<^sub>L
        ((\<phi> ^\<^sup>B\<^sup>L Suc n + m \<longrightarrow>\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L Suc n &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m) \<longrightarrow>\<^sub>B\<^sub>L
         ((\<phi> ^\<^sup>B\<^sup>L Suc n &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> ^\<^sup>B\<^sup>L Suc n + m)) &\<^sub>B\<^sub>L (\<phi> ^\<^sup>B\<^sup>L Suc n + m \<longrightarrow>\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L Suc n &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m))) \<in> CnBL {}"
    by (metis TBL10)
  from 10 and 18 have 
  19: "((\<phi> ^\<^sup>B\<^sup>L Suc n + m \<longrightarrow>\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L Suc n &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m) \<longrightarrow>\<^sub>B\<^sub>L
       ((\<phi> ^\<^sup>B\<^sup>L Suc n &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> ^\<^sup>B\<^sup>L Suc n + m)) &\<^sub>B\<^sub>L (\<phi> ^\<^sup>B\<^sup>L Suc n + m \<longrightarrow>\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L Suc n &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m)) \<in> CnBL {}"
          by (metis (full_types) CnBL.MP TBL10)
  from 17 and 19 show
  20: "(((\<phi> ^\<^sup>B\<^sup>L Suc n &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> ^\<^sup>B\<^sup>L Suc n + m)) &\<^sub>B\<^sub>L (\<phi> ^\<^sup>B\<^sup>L Suc n + m \<longrightarrow>\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L Suc n &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m)) \<in> CnBL {}"
    by (metis CnBL.MP)           
qed

theorem LocalDeductionBL1 [simp]:
"\<psi> \<in> CnBL (\<Gamma> \<union> {\<phi>}) \<Longrightarrow> (\<exists>n. ((\<phi> ^\<^sup>B\<^sup>L n) \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<in> CnBL \<Gamma>)"
proof (rule CnBL.induct)
  fix \<phi>' \<psi> \<chi>

--"the case of BL1"
  have
  1: "(\<phi> ^\<^sup>B\<^sup>L 0 \<longrightarrow>\<^sub>B\<^sub>L ((\<phi>' \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L ((\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi>' \<longrightarrow>\<^sub>B\<^sub>L \<chi>)))) \<in> CnBL \<Gamma>"
    by (metis (full_types) CnBL.BL1 CnBL.MP TBL2 emptyAsm)
  then show
  2: "\<exists>n. (\<phi> ^\<^sup>B\<^sup>L n \<longrightarrow>\<^sub>B\<^sub>L ((\<phi>' \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L ((\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi>' \<longrightarrow>\<^sub>B\<^sub>L \<chi>)))) \<in> CnBL \<Gamma>"
    by metis

--"the case of BL4"
  show
  3: "\<exists>n. (\<phi> ^\<^sup>B\<^sup>L n \<longrightarrow>\<^sub>B\<^sub>L (\<phi>' &\<^sub>B\<^sub>L (\<phi>' \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L \<psi> &\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>'))) \<in> CnBL \<Gamma>"
    by (metis (full_types) CnBL.BL4 CnBL.MP TBL2 emptyAsm)
--"the case of BL5a"
  show
  4: "\<exists>n. (\<phi> ^\<^sup>B\<^sup>L n \<longrightarrow>\<^sub>B\<^sub>L ((\<phi>' &\<^sub>B\<^sub>L \<psi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L (\<phi>' \<longrightarrow>\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>)))) \<in> CnBL \<Gamma>"
    by (metis (full_types) CnBL.BL5a CnBL.MP TBL2 emptyAsm)
--"the case of BL5b"
  show
  5: "\<exists>n. (\<phi> ^\<^sup>B\<^sup>L n \<longrightarrow>\<^sub>B\<^sub>L ((\<phi>' \<longrightarrow>\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>)) \<longrightarrow>\<^sub>B\<^sub>L (\<phi>' &\<^sub>B\<^sub>L \<psi> \<longrightarrow>\<^sub>B\<^sub>L \<chi>))) \<in> CnBL \<Gamma>"
    by (metis (full_types) CnBL.BL5b CnBL.MP TBL2 emptyAsm)

--"the case of BL6"
  show
  6: "\<exists>n. (\<phi> ^\<^sup>B\<^sup>L n \<longrightarrow>\<^sub>B\<^sub>L (((\<phi>' \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<longrightarrow>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L (((\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>') \<longrightarrow>\<^sub>B\<^sub>L \<chi>) \<longrightarrow>\<^sub>B\<^sub>L \<chi>))) \<in> CnBL \<Gamma>"
    by (metis (full_types) CnBL.BL6 CnBL.MP TBL2 emptyAsm)
--"case of BL7"
  show
  7: "\<exists>n. (\<phi> ^\<^sup>B\<^sup>L n \<longrightarrow>\<^sub>B\<^sub>L (Const_0 \<longrightarrow>\<^sub>B\<^sub>L \<phi>')) \<in> CnBL \<Gamma>"
    by (metis Chvalovsky_4_4_c_28 emptyAsm)
next
--"The case of an assumption"
  fix \<phi>'
  assume "\<phi>' \<in> (\<Gamma> \<union> {\<phi>})"
  then show
  9: "\<exists>n. (\<phi> ^\<^sup>B\<^sup>L n \<longrightarrow>\<^sub>B\<^sub>L \<phi>') \<in> CnBL \<Gamma>"
    proof
      assume "\<phi>' \<in> \<Gamma>"
      then show "\<exists>n. (\<phi> ^\<^sup>B\<^sup>L n \<longrightarrow>\<^sub>B\<^sub>L \<phi>') \<in> CnBL \<Gamma>"
        by (metis (full_types) CnBL.Assumption CnBL.MP TBL2 emptyAsm) 
    next
      assume "\<phi>' \<in> {\<phi>}"
      then have "\<phi>' = \<phi>"
        by simp
      hence "(\<phi> ^\<^sup>B\<^sup>L 1 \<longrightarrow>\<^sub>B\<^sub>L \<phi>') \<in> CnBL \<Gamma>"
        by simp 
      then show "\<exists>n. (\<phi> ^\<^sup>B\<^sup>L n \<longrightarrow>\<^sub>B\<^sub>L \<phi>') \<in> CnBL \<Gamma>"
        by (rule exI)
    qed
next
--"inductive step"
  fix \<phi>' \<psi>
  assume
  1: "(\<psi> \<in> CnBL (\<Gamma> \<union> {\<phi>}) \<and> (\<exists>n. (\<phi> ^\<^sup>B\<^sup>L n \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<in> CnBL \<Gamma>)) \<and>
      (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>') \<in> CnBL (\<Gamma> \<union> {\<phi>}) \<and> (\<exists>n. (\<phi> ^\<^sup>B\<^sup>L n \<longrightarrow>\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>')) \<in> CnBL \<Gamma>)"
  from 1 obtain n where
  2: "(\<phi> ^\<^sup>B\<^sup>L n \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<in> CnBL \<Gamma>"
    by metis
  from 1 obtain m where
  3: "(\<phi> ^\<^sup>B\<^sup>L m \<longrightarrow>\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>')) \<in> CnBL \<Gamma>"
    by metis
  from 2 have
  4: "((\<phi> ^\<^sup>B\<^sup>L m \<longrightarrow>\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>')) \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> ^\<^sup>B\<^sup>L n \<longrightarrow>\<^sub>B\<^sub>L \<psi>) &\<^sub>B\<^sub>L (\<phi> ^\<^sup>B\<^sup>L m \<longrightarrow>\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>')))) \<in> CnBL \<Gamma>"
    by (metis (full_types) CnBL.MP TBL10 emptyAsm)
  from 3 and 4 have
  5: "((\<phi> ^\<^sup>B\<^sup>L n \<longrightarrow>\<^sub>B\<^sub>L \<psi>) &\<^sub>B\<^sub>L (\<phi> ^\<^sup>B\<^sup>L m \<longrightarrow>\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>'))) \<in> CnBL \<Gamma>"
    by (metis CnBL.MP)
  have
  6: "((((\<phi> ^\<^sup>B\<^sup>L n) \<longrightarrow>\<^sub>B\<^sub>L \<psi>) &\<^sub>B\<^sub>L ((\<phi> ^\<^sup>B\<^sup>L m) \<longrightarrow>\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>'))) \<longrightarrow>\<^sub>B\<^sub>L
             (((\<phi> ^\<^sup>B\<^sup>L n) &\<^sub>B\<^sub>L (\<phi> ^\<^sup>B\<^sup>L m)) \<longrightarrow>\<^sub>B\<^sub>L (\<psi> &\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>')))) \<in> CnBL \<Gamma>"
    by (metis (full_types) Hajek_7 emptyAsm)
  from 5 and 6 have
  7: "((\<phi> ^\<^sup>B\<^sup>L n &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m) \<longrightarrow>\<^sub>B\<^sub>L (\<psi> &\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>'))) \<in> CnBL \<Gamma>"
    by (metis CnBL.MP)
  have
  8: "((\<psi> &\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>')) \<longrightarrow>\<^sub>B\<^sub>L \<phi>') \<in> CnBL \<Gamma>"
    by (metis (full_types) Hajek_4 emptyAsm) 
  have
  9: "(((\<phi> ^\<^sup>B\<^sup>L n &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m) \<longrightarrow>\<^sub>B\<^sub>L (\<psi> &\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>'))) \<longrightarrow>\<^sub>B\<^sub>L
             (((\<psi> &\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>')) \<longrightarrow>\<^sub>B\<^sub>L \<phi>') \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> ^\<^sup>B\<^sup>L n &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m) \<longrightarrow>\<^sub>B\<^sub>L \<phi>'))) \<in> CnBL \<Gamma>"
    by (metis CnBL.BL1)
  from 7 and 9 have
  10: "(((\<psi> &\<^sub>B\<^sub>L (\<psi> \<longrightarrow>\<^sub>B\<^sub>L \<phi>')) \<longrightarrow>\<^sub>B\<^sub>L \<phi>') \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> ^\<^sup>B\<^sup>L n &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m) \<longrightarrow>\<^sub>B\<^sub>L \<phi>')) \<in> CnBL \<Gamma>"
    by (metis (full_types) CnBL.MP)
  from 8 and 10 have
  11: "((\<phi> ^\<^sup>B\<^sup>L n &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m) \<longrightarrow>\<^sub>B\<^sub>L \<phi>') \<in> CnBL \<Gamma>"
    by (metis CnBL.MP)
  have
  12: "((\<phi> ^\<^sup>B\<^sup>L n &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m) \<longleftrightarrow>\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L n + m) \<in> CnBL \<Gamma>"
    by (metis MultiConjDistribution emptyAsm)
  have
  13: "(((\<phi> ^\<^sup>B\<^sup>L n &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m) \<longleftrightarrow>\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L n + m) \<longrightarrow>\<^sub>B\<^sub>L 
       ((\<phi> ^\<^sup>B\<^sup>L n + m) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> ^\<^sup>B\<^sup>L n &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m))) \<in> CnBL \<Gamma>"
    by (metis (full_types) Chvalovsky_4_4_c Equivalence_BL_def emptyAsm)
  from 12 and 13 have
  14: "((\<phi> ^\<^sup>B\<^sup>L n + m) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> ^\<^sup>B\<^sup>L n &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m)) \<in> CnBL \<Gamma>"
    by (metis CnBL.MP)
  have
  15: "(((\<phi> ^\<^sup>B\<^sup>L n + m) \<longrightarrow>\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L n &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m) \<longrightarrow>\<^sub>B\<^sub>L
             (((\<phi> ^\<^sup>B\<^sup>L n &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m) \<longrightarrow>\<^sub>B\<^sub>L \<phi>') \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> ^\<^sup>B\<^sup>L n + m) \<longrightarrow>\<^sub>B\<^sub>L \<phi>'))) \<in> CnBL \<Gamma>" 
    by (metis CnBL.BL1)
  from 14 and 15 have
  16: "(((\<phi> ^\<^sup>B\<^sup>L n &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L m) \<longrightarrow>\<^sub>B\<^sub>L \<phi>') \<longrightarrow>\<^sub>B\<^sub>L ((\<phi> ^\<^sup>B\<^sup>L n + m) \<longrightarrow>\<^sub>B\<^sub>L \<phi>')) \<in> CnBL \<Gamma>"
    by (metis (full_types) CnBL.MP)
  from 11 and 16 have
  17: "((\<phi> ^\<^sup>B\<^sup>L n + m) \<longrightarrow>\<^sub>B\<^sub>L \<phi>') \<in> CnBL \<Gamma>"
    by (metis CnBL.MP)
  from 17 show
  18: "\<exists>n. ((\<phi> ^\<^sup>B\<^sup>L n) \<longrightarrow>\<^sub>B\<^sub>L \<phi>') \<in> CnBL \<Gamma>"
    by metis
qed

lemma DerivabilityOfStrongConj [simp]:
  "(\<phi> ^\<^sup>B\<^sup>L n) \<in> CnBL (\<Gamma> \<union> {\<phi>})"
proof (induct n)
  case 0
  show ?case by simp
next
  have
    "\<forall>n. (\<phi> &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L n) = (\<phi> ^\<^sup>B\<^sup>L Suc n)"
      by simp
  then have
  1: "\<forall>n. ((\<phi> &\<^sub>B\<^sub>L \<phi> ^\<^sup>B\<^sup>L n) \<longrightarrow>\<^sub>B\<^sub>L (\<phi> ^\<^sup>B\<^sup>L Suc n)) \<in> CnBL (\<Gamma> \<union> {\<phi>})"
    by simp
  from 1 have
  2: "\<forall>n. (\<phi> \<longrightarrow>\<^sub>B\<^sub>L (\<phi> ^\<^sup>B\<^sup>L n \<longrightarrow>\<^sub>B\<^sub>L (\<phi> ^\<^sup>B\<^sup>L Suc n))) \<in> CnBL (\<Gamma> \<union> {\<phi>})"
    by simp
  from 2 have
  3: "\<forall>n. (\<phi> ^\<^sup>B\<^sup>L n \<longrightarrow>\<^sub>B\<^sub>L (\<phi> ^\<^sup>B\<^sup>L Suc n)) \<in> CnBL (\<Gamma> \<union> {\<phi>})"
    by blast
  case (Suc n)
  then show ?case using 3
    by blast
qed

thm CnBL.induct
lemma CnBLMonotonicity [simp]:
  "\<phi> \<in> CnBL \<Gamma> \<Longrightarrow> \<phi> \<in> CnBL (\<Gamma> \<union> \<Delta>)"
apply (rule CnBL.induct)
print_state
by blast+

theorem LocalDeductionBL2 [simp]:
  "(\<exists>n. (\<phi> ^\<^sup>B\<^sup>L n \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<in> CnBL \<Gamma>) \<Longrightarrow> \<psi> \<in> CnBL (\<Gamma> \<union> {\<phi>})"
apply (erule exE)
 apply (subgoal_tac "(\<phi> ^\<^sup>B\<^sup>L n \<longrightarrow>\<^sub>B\<^sub>L \<psi>) \<in> CnBL (\<Gamma> \<union> {\<phi>})")
 --"adds assumption"
 prefer 2 --"move subgoal 2 to 1st place"
 apply (rule CnBLMonotonicity)
apply metis
 apply (subgoal_tac "(\<phi> ^\<^sup>B\<^sup>L n) \<in> CnBL (\<Gamma> \<union> {\<phi>})")
 --"adds assumption"
 prefer 2
apply (rule DerivabilityOfStrongConj)
by blast

end


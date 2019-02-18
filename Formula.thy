(*  Title:      Separation-Logic-Formalization/Interpretation.thy
    Author:     Nicolas Amat, Mnacho Echenim, Nicolas Peltier
*)

section {* Formulas *}

text {* This section contains the syntax and semantics formalization of the separation logic formulas. *}

theory Formula
  imports Main Interpretation
begin


subsection {* Formulas Syntax *}

datatype 'a sl_formula =
  (* Boolean *)
    true
  | false
  (* Classical Logic *)
  | eq 'a 'a
  | not "'a sl_formula"
  | impl "'a sl_formula" "'a sl_formula"
  | conj "'a sl_formula" "'a sl_formula"
  | disj "'a sl_formula" "'a sl_formula"
  (* Quantifier *)
  | forall 'a "'a sl_formula"
  | exists 'a "'a sl_formula"
  (* Separation Logic *)
  | sl_emp
  | sl_mapsto 'a 'a
  | sl_conj "'a sl_formula" "'a sl_formula"
  | sl_magic_wand "'a sl_formula" "'a sl_formula"


subsection {* Formulas Semantics *}

primrec evaluation :: "(('a, 'b, 'c) interp) \<Rightarrow> 'a sl_formula \<Rightarrow> bool"
  where 
    "evaluation I true                = True"
  | "evaluation I false               = False" 
  | "evaluation I (eq x y)            = ((store I) x = (store I) y)"
  | "evaluation I (not P)             =  (\<not>(evaluation I P))"
  | "evaluation I (impl P Q)          = ((evaluation I P) \<longrightarrow> (evaluation I Q))"
  | "evaluation I (conj P Q)          = ((evaluation I P) \<and> (evaluation I Q))"
  | "evaluation I (disj P Q)          = ((evaluation I P) \<or> (evaluation I Q))"
  | "evaluation I (forall x P)        = (\<forall>u. (evaluation ((store I)(x:=u),(heap I)) P))"
  | "evaluation I (exists x P)        = (\<exists>u. (evaluation ((store I)(x:=u),(heap I)) P))"
  | "evaluation I (sl_emp)            = True"
  | "evaluation I (sl_mapsto E F)     = True"
  | "evaluation I (sl_conj P Q)       = (\<exists>h1 h2. (union_heaps h1 h2 = heap I)
                                               \<and> (disjoint_heaps h1 h2) 
                                               \<and> (evaluation ((store I), h1) P) 
                                               \<and> (evaluation ((store I), h2) Q))"
  | "evaluation I (sl_magic_wand P Q) = (\<forall>h. ((disjoint_heaps h (heap I)) \<and> (evaluation ((store I), h) P))
                                         \<longrightarrow> (evaluation ((store I), union_heaps (heap I) h)) Q)"


end
(*  Title:      Separation-Logic-Formalization/Interpretation.thy
    Author:     Nicolas Amat, Mnacho Echenim, Nicolas Peltier
*)

section {* Formulas *}

text {* This section contains the syntax and semantics formalization of the separation logic formulas. *}

theory Formula
  imports 
    Main 
    Interpretation
begin


subsection {* Formulas Syntax *}

datatype ('a, 'b) sl_formula =
  (* Boolean *)
    true
  | false
  (* Classical Logic *)
  | eq 'a 'a
  | not "('a, 'b) sl_formula"
  | conj "('a, 'b) sl_formula" "('a, 'b) sl_formula"
  | disj "('a, 'b) sl_formula" "('a, 'b) sl_formula"
  (* Quantifier *)
  | forall 'a "('a, 'b) sl_formula"
  | exists 'a "('a, 'b) sl_formula"
  (* Separation Logic *)
  | sl_emp
  | sl_mapsto 'a "('a, 'b) vec"
  | sl_conj "('a, 'b) sl_formula" "('a, 'b) sl_formula"
  | sl_magic_wand "('a, 'b) sl_formula" "('a, 'b) sl_formula"


subsection {* Formulas Semantics *}

(* NP: la définition de la semantique de sl_emp et sl_mapsto est incorrecte *)
(* pour sl_emp il faut vérifier que le domaine de la heap est vide et pour sl_mapsto il faut
   vérifier que le domaine est réduit à E et que heap I E = F *)

primrec evaluation :: "(('a, 'b, 'c) interp) \<Rightarrow> ('a, 'c) sl_formula \<Rightarrow> bool"
  where 
    "evaluation I true                = True"
  | "evaluation I false               = False" 
  | "evaluation I (eq x y)            = ((store I) x = (store I) y)"
  | "evaluation I (not P)             =  (\<not>(evaluation I P))"
  | "evaluation I (conj P Q)          = ((evaluation I P) \<and> (evaluation I Q))"
  | "evaluation I (disj P Q)          = ((evaluation I P) \<or> (evaluation I Q))"
  | "evaluation I (forall x P)        = (\<forall>u. (evaluation ((store I)(x:=u),(heap I)) P))"
  | "evaluation I (exists x P)        = (\<exists>u. (evaluation ((store I)(x:=u),(heap I)) P))"
  | "evaluation I (sl_emp)            = empty_heaps (heap I)"
  | "evaluation I (sl_mapsto x y)     = True"
  | "evaluation I (sl_conj P Q)       = (\<exists>h1 h2. (union_heaps h1 h2 = heap I)
                                               \<and> (disjoint_heaps h1 h2) 
                                               \<and> (evaluation (constructor_interp (store I) h1) P) 
                                               \<and> (evaluation (constructor_interp (store I) h2) Q))"
  | "evaluation I (sl_magic_wand P Q) = (\<forall>h. ((disjoint_heaps h (heap I)) \<and> (evaluation (constructor_interp (store I) h) P))
                                         \<longrightarrow> (evaluation (constructor_interp (store I) (union_heaps (heap I) h))) Q)"


end
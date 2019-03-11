(*  Title:      Separation-Logic-Formalization/Interpretation.thy
    Author:     Nicolas Amat, Mnacho Echenim, Nicolas Peltier
*)

section {* Formulas *}

text {* This section contains the syntax and semantics formalization of the separation logic formulas. *}

theory Formula
  imports 
    Interpretation
begin


subsection {* Formulas Syntax *}

datatype ('var, 'k::finite) sl_formula =
  (* Boolean *)
    true
  | false
  (* Classical Logic *)
  | eq 'var 'var
  | not "('var, 'k::finite) sl_formula"
  | conj "('var, 'k::finite) sl_formula" "('var, 'k::finite) sl_formula"
  (* Quantifier *)
  | exists 'var "('var, 'k::finite) sl_formula"
  (* Separation Logic *)
  | sl_emp
  | sl_mapsto 'var "('var, 'k::finite) vec"
  | sl_conj "('var, 'k::finite) sl_formula" "('var, 'k::finite) sl_formula"
  | sl_magic_wand "('var, 'k::finite) sl_formula" "('var, 'k::finite) sl_formula"


subsection {* Formulas Semantics *}

primrec evaluation :: "(('var, 'addr, 'k::finite) interp) \<Rightarrow> ('var, 'k::finite) sl_formula \<Rightarrow> bool"
  where 
    "evaluation I true                = True"
  | "evaluation I false               = False" 
  | "evaluation I (eq x y)            = ((store I) x = (store I) y)"
  | "evaluation I (not P)             = (\<not>(evaluation I P))"
  | "evaluation I (conj P Q)          = ((evaluation I P) \<and> (evaluation I Q))"
  | "evaluation I (exists x P)        = (\<exists>u. (evaluation (to_interp ((store I)(x:=u)) (heap I)) P))" 
  | "evaluation I (sl_emp)            = empty_heaps (heap I)"
  | "evaluation I (sl_mapsto x y)     = ((dom (heap I) = {(store I) x})
                                      \<and> (Rep_heaps (heap I) ((store I) x) = Some (store_vector (store I) y)))"
  | "evaluation I (sl_conj P Q)       = (\<exists>h1 h2. (union_heaps h1 h2 = heap I)
                                               \<and> (disjoint_heaps h1 h2) 
                                               \<and> (evaluation (to_interp (store I) h1) P) 
                                               \<and> (evaluation (to_interp (store I) h2) Q))"
  | "evaluation I (sl_magic_wand P Q) = (\<forall>h. ((disjoint_heaps h (heap I)) \<and> (evaluation (to_interp (store I) h) P))
                                         \<longrightarrow> (evaluation (to_interp (store I) (union_heaps (heap I) h))) Q)"


end
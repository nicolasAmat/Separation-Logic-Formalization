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

datatype ('var, 'k) sl_formula =
  (* Boolean *)
    true
  | false
  (* Classical Logic *)
  | eq 'var 'var
  | not "('var, 'k) sl_formula"
  | conj "('var, 'k) sl_formula" "('var, 'k) sl_formula"
  | disj "('var, 'k) sl_formula" "('var, 'k) sl_formula"
  (* Quantifier *)
  | exists 'var "('var, 'k) sl_formula"
  (* Separation Logic *)
  | sl_emp
  | sl_mapsto 'var "('var, 'k) vec"
  | sl_conj "('var, 'k) sl_formula" "('var, 'k) sl_formula"
  | sl_magic_wand "('var, 'k) sl_formula" "('var, 'k) sl_formula"


subsection {* Formulas Semantics *}

primrec evaluation :: "(('var, 'addr, 'k) interp) \<Rightarrow> ('var, 'k) sl_formula \<Rightarrow> bool"
  where 
    "evaluation I true                = True"
  | "evaluation I false               = False" 
  | "evaluation I (eq x y)            = ((store I) x = (store I) y)"
  | "evaluation I (not P)             =  (\<not>(evaluation I P))"
  | "evaluation I (conj P Q)          = ((evaluation I P) \<and> (evaluation I Q))"
  | "evaluation I (disj P Q)          = ((evaluation I P) \<or> (evaluation I Q))"
  | "evaluation I (exists x P)        = (\<exists>u. (evaluation (constructor_interp ((store I)(x:=u)) (heap I)) P))" 
  | "evaluation I (sl_emp)            = empty_heaps (heap I)"
  | "evaluation I (sl_mapsto x y)     = ((dom (heap I) = {(store I) x})) "
                                     (*  \<and> ( (Rep_heaps (heap I)) ((store I) x) = (store I) y))" *)
  | "evaluation I (sl_conj P Q)       = (\<exists>h1 h2. (union_heaps h1 h2 = heap I)
                                               \<and> (disjoint_heaps h1 h2) 
                                               \<and> (evaluation (constructor_interp (store I) h1) P) 
                                               \<and> (evaluation (constructor_interp (store I) h2) Q))"
  | "evaluation I (sl_magic_wand P Q) = (\<forall>h. ((disjoint_heaps h (heap I)) \<and> (evaluation (constructor_interp (store I) h) P))
                                         \<longrightarrow> (evaluation (constructor_interp (store I) (union_heaps (heap I) h))) Q)"


end
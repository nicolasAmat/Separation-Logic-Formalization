(*  Title:      Separation-Logic-Formalization/Interpretation.thy
    Author:     Nicolas Amat, Mnacho Echenim, Nicolas Peltier
*)

section \<open>Formulas\<close>

text \<open>This section contains the formulas syntax and semantic.\<close>

theory Formula
imports 
  Interpretation
begin


subsection \<open>Formulas Syntax\<close>

datatype ('var, 'k::finite) sl_formula =
  (* Boolean *)
    sl_true
  | sl_false
  (* Classical Logic *)
  | sl_not "('var, 'k) sl_formula"
  | sl_and "('var, 'k) sl_formula" "('var, 'k) sl_formula"
  (* Quantifier *)
  | sl_exists 'var "('var, 'k) sl_formula"
  (* Separation Logic *)
  | sl_emp
  | sl_eq 'var 'var
  | sl_mapsto 'var "('var, 'k) vec"
  | sl_conj "('var, 'k) sl_formula" "('var, 'k) sl_formula"
  | sl_magic_wand "('var, 'k) sl_formula" "('var, 'k) sl_formula"


subsection \<open>Formulas Semantics\<close>

fun evaluation :: "('var, 'addr, 'k) interp \<Rightarrow> ('var, 'k::finite) sl_formula \<Rightarrow> bool"
  where 
    "evaluation I sl_true             = True"
  | "evaluation I sl_false            = False" 
  | "evaluation I (sl_not P)          = (\<not>(evaluation I P))"
  | "evaluation I (sl_and P Q)        = ((evaluation I P) \<and> (evaluation I Q))"
  | "evaluation I (sl_exists x P)     = (\<exists>u. (evaluation (to_interp ((store I)(x:=u)) (heap I)) P))"
  | "evaluation I (sl_eq x y)         = ((store I) x = (store I) y)"
  | "evaluation I (sl_emp)            = empty_heap (heap I)"
  | "evaluation I (sl_mapsto x y)     = ((h_dom (heap I) = {(store I) x})
                                      \<and> ((store_and_heap I x) = Some (store_vector (store I) y)))"
  | "evaluation I (sl_conj P Q)       = (\<exists>h1 h2. (union_heaps h1 h2 = heap I)
                                               \<and> (disjoint_heaps h1 h2) 
                                               \<and> (evaluation (to_interp (store I) h1) P) 
                                               \<and> (evaluation (to_interp (store I) h2) Q))"
  | "evaluation I (sl_magic_wand P Q) = (\<forall>h. ((disjoint_heaps h (heap I)) \<and> (evaluation (to_interp (store I) h) P))
                                         \<longrightarrow> (evaluation (to_interp (store I) (union_heaps (heap I) h))) Q)"


subsection \<open>Formula Complement\<close>

fun sl_formula_complement :: "('var, 'k::finite) sl_formula \<Rightarrow> ('var ,'k) sl_formula"
  where "sl_formula_complement (sl_not l) = l"
      | "sl_formula_complement l = (sl_not l)"


subsection \<open>Formula Var Set\<close>

fun var_set :: "('var, 'k::finite) sl_formula \<Rightarrow> 'var set"
  where 
    "var_set sl_true = {}"
  | "var_set sl_false = {}"
  | "var_set (sl_not P) = var_set P"
  | "var_set (sl_and P Q) = var_set P \<union> var_set Q"
  | "var_set (sl_exists x P) = var_set P"
  | "var_set (sl_emp) = {}"
  | "var_set (sl_eq x y) = {x, y}"
  | "var_set (sl_mapsto x y) = {x} \<union> {y $ i | i. True}"
  | "var_set (sl_conj P Q) = var_set P \<union> var_set Q"
  | "var_set (sl_magic_wand P Q) = var_set P \<union> var_set Q"


end
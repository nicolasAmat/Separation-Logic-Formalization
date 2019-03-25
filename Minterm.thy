(*  Title:      Separation-Logic-Formalization/Minterm.thy
    Author:     Nicolas Amat, Mnacho Echenim, Nicolas Peltier
*)

section {* Minterms *}

text {* This section contains the minterms definition and some propositions related to them. *}

theory Minterm
imports
  Formula_Relation 
  Test_Formulae
begin


subsection {* Definition *}

typedef ('var, 'addr, 'k::finite) minterm 
  = "{S. (\<exists>!l\<in>S::('var, 'k::finite) literal set. \<exists>n. (equivalence (UNIV::'addr set) (to_sl_formula l) (ext_card_heap_superior_to n)))}"
proof 
  define x::"('var, 'k::finite) literal set" where "x = {to_literal (ext_card_heap_superior_to 0)}"
  show "x\<in>{S. \<exists>!l. l \<in> S \<and> (\<exists>n. equivalence UNIV (to_sl_formula l) (ext_card_heap_superior_to n))} "
  proof
oops

(*
definition minterm :: "'addr set \<Rightarrow> ('var, 'k::finite) literal set \<Rightarrow> bool"
  where "minterm env S = ((\<exists>!l\<in>S. \<exists>n. (equivalence env (to_sl_formula l) (ext_card_heap_superior_to n)))
                        \<and> (\<exists>!l\<in>S. \<exists>n. (equivalence env (to_sl_formula l) (not (ext_card_heap_superior_to n)))))"

definition e_minterm
  where ""
*)

(* 3 lemmes:
- si minterm \<Rightarrow> a
- si minterm \<Rightarrow> b
- si a et b \<Rightarrow> mintern
*)

end
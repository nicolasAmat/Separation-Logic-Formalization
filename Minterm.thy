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


subsection {* Minterms Definition *}

typedef ('var, 'addr, 'k::finite) minterm 
  = "{S. ((\<exists>!l\<in>S::('var, 'k::finite) literal set. \<exists>n. 
          (equivalence (UNIV::'addr set) (to_sl_formula l) (ext_card_heap_superior_to n)))
        \<and> (\<exists>!l\<in>S::('var, 'k::finite) literal set. \<exists>n. 
          (equivalence (UNIV::'addr set) (to_sl_formula l) (not (ext_card_heap_superior_to n)))))}"
proof
  define x::"('var, 'k::finite) literal set" 
    where "x = {to_literal (ext_card_heap_superior_to 0), 
                to_literal (not (ext_card_heap_superior_to 0))}"
  show "x \<in> {S. (\<exists>!l. l \<in> S \<and> (\<exists>n. equivalence UNIV (to_sl_formula l) (ext_card_heap_superior_to n))) 
              \<and> (\<exists>!l. l \<in> S \<and> (\<exists>n. equivalence UNIV (to_sl_formula l) (not (ext_card_heap_superior_to n))))}"
  proof
    define l1::"('var, 'k::finite) literal" where "l1 = to_literal (ext_card_heap_superior_to 0)"
    have "l1 \<in> x"
      by (simp add: l1_def x_def) 
    moreover have "equivalence UNIV (to_sl_formula l1) (ext_card_heap_superior_to 0)" unfolding l1_def
      by (simp add: literals_def test_formulae.intros(3) to_sl_formula_to_literal)
    define l2::"('var, 'k::finite) literal" where "l2 = to_literal (not (ext_card_heap_superior_to 0))"
    moreover have "l2 \<in> x"
      by (simp add: l2_def x_def)
    moreover have "equivalence UNIV (to_sl_formula l2) (not (ext_card_heap_superior_to 0))" unfolding l2_def
      by (simp add: literals_def test_formulae.intros(3) to_sl_formula_to_literal)
    ultimately show "(\<exists>!l. l \<in> x \<and> (\<exists>n. equivalence UNIV (to_sl_formula l) (ext_card_heap_superior_to n))) 
                   \<and> (\<exists>!l. l \<in> x \<and> (\<exists>n. equivalence UNIV (to_sl_formula l) (not (ext_card_heap_superior_to n))))"  
      oops


(*
definition e_minterm
  where ""
*)

(* 3 lemmes:
- si minterm \<Rightarrow> a
- si minterm \<Rightarrow> b
- si a et b \<Rightarrow> mintern
*)


end
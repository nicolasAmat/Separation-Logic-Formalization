(*  Title:      Separation-Logic-Formalization/Test_Formulae.thy
    Author:     Nicolas Amat, Mnacho Echenim, Nicolas Peltier
*)

section {* Test Formulae *}

text {* This section contains test formulae. *}

theory Test_Formulae
  imports
    Formula
    "HOL-Library.Extended_Nat"
begin


subsection {* Syntax *}

datatype ('var, 'addr, 'k::finite) test_formulae = 
  (* Points-to Relations in the Heap *)
    points_to 'var "('var, 'k::finite) vec"
  (* Allocation *)
  | alloc 'var
  (* Cardinality Constraint *)
  | size_heaps_superior_to "('addr, 'k) heaps" enat 


subsection {* Definitions *}

primrec tf_definition :: "('var, 'addr, 'k::finite) test_formulae \<Rightarrow> ('var, 'k::finite) sl_formula"
  where
    "tf_definition (points_to x y) = sl_conj (sl_mapsto x y) true"
  | "tf_definition (alloc x)       = sl_magic_wand (sl_mapsto x (vec x)) false"
(* TODO *)


end
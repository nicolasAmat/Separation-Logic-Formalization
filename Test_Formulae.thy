(*  Title:      Separation-Logic-Formalization/Test_Formulae.thy
    Author:     Nicolas Amat, Mnacho Echenim, Nicolas Peltier
*)

section {* Test Formulae *}

text {* This section contains test formulae. *}

theory Test_Formulae
  imports
    Formula
begin


subsection {* Syntax *}

datatype ('var, 'k::finite) test_formulae = 
  (* Points to *)
    points_to 'var "('var, 'k::finite) vec"
  (* Alloc *)
  | alloc 'var


subsection {* Definitions *}

primrec tf_definition :: "('var, 'k::finite) test_formulae \<Rightarrow> ('var, 'k::finite) sl_formula"
  where
    "tf_definition (points_to x y) = sl_conj (sl_mapsto x y) true"
  | "tf_definition (alloc x)       = sl_magic_wand (sl_mapsto x (vec x)) false"


end
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


subsection {* Points-to Relations in the Heap *}

definition points_to :: "'var \<Rightarrow> ('var, 'k) vec \<Rightarrow> ('var, 'k::finite) sl_formula"
  where "points_to x y =  sl_conj (sl_mapsto x y) true"


subsection {* Allocation *}

definition alloc :: "'var \<Rightarrow> ('var, 'k::finite) sl_formula"
  where "alloc x = sl_magic_wand (sl_mapsto x (vec x)) false"


subsection {* Cardinality Constraint *}

fun card_heaps_superior_to :: "('addr, 'k) heaps \<Rightarrow> enat \<Rightarrow> ('var, 'k::finite) sl_formula"
  where 
      "card_heaps_superior_to h (enat (Suc n)) = sl_conj (card_heaps_superior_to h n) (not sl_emp)"
    | "card_heaps_superior_to h (enat 0) = true"
    | "card_heaps_superior_to h \<infinity> = false"



end
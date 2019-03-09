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

primrec card_heaps_superior_to :: "('addr, 'k) heaps \<Rightarrow> nat \<Rightarrow> ('var, 'k::finite) sl_formula"
  where   
      "card_heaps_superior_to h (Suc n) = sl_conj (card_heaps_superior_to h n) (not sl_emp)"
    | "card_heaps_superior_to h 0 = true"

primrec extended_card_heaps_superior_to ::  "('addr, 'k) heaps \<Rightarrow> enat \<Rightarrow> ('var, 'k::finite) sl_formula"
  where
      "extended_card_heaps_superior_to h \<infinity> = false"
    | "extended_card_heaps_superior_to h n = card_heaps_superior_to h n"


end
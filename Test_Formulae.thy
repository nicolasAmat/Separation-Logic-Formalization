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

primrec ext_card_heaps_superior_to ::  "('addr, 'k) heaps \<Rightarrow> enat \<Rightarrow> ('var, 'k::finite) sl_formula"
  where
      "ext_card_heaps_superior_to h \<infinity> = false"
    | "ext_card_heaps_superior_to h n = card_heaps_superior_to h n"

(*
function other_way :: "('addr, 'k) heaps \<Rightarrow> enat \<Rightarrow> ('var, 'k::finite) sl_formula"
  where
       "other_way h (enat (Suc n)) = other_way h n"
     | "other_way h (enat 0) = true"
     | "other_way h \<infinity> = false"
  by pat_completeness auto
termination 
  proof -
    let ?R = "{((h, n::enat), (h, m::enat)). less_enat n m}"
    show ?thesis
    proof(relation ?R)
      show "wf ?R"
*)


subsection {* Inductive Set *}

(*
inductive_set test_forumulae :: "('var, 'k::finite) sl_formula set"
  where
  ""
*)


end
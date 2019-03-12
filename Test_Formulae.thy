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

primrec card_heaps_superior_to :: "nat \<Rightarrow> ('var, 'k::finite) sl_formula"
  where   
      "card_heaps_superior_to (Suc n) = sl_conj (card_heaps_superior_to n) (not sl_emp)"
    | "card_heaps_superior_to 0 = true"

primrec ext_card_heaps_superior_to ::  "enat \<Rightarrow> ('var, 'k::finite) sl_formula"
  where
      "ext_card_heaps_superior_to \<infinity> = false"
    | "ext_card_heaps_superior_to n = card_heaps_superior_to n"


subsection {* Inductive Set *}

inductive_set test_formulae :: "('var, 'k::finite) sl_formula set"
  where
    "(points_to x y) \<in> test_formulae"
  | "(alloc x) \<in> test_formulae"
  | "(ext_card_heaps_superior_to n) \<in> test_formulae"
  | "tf \<in> test_formulae \<Longrightarrow> (not tf) \<in> test_formulae"
  | "tf1 \<in> test_formulae \<and> tf2 \<in> test_formulae \<Longrightarrow> (conj tf1 tf2) \<in> test_formulae"


subsection {* Propositions *}

(* using à améliorer ? drafts... *)
lemma tf_prop_1:
  fixes I::"('var, 'addr, 'k::finite) interp"
    and x::"'var"
    and y::"('var, 'k::finite) vec"
  shows "(evaluation I (points_to x y)) 
     \<longleftrightarrow> (store_and_heap I x = Some (store_vector (store I) y))"
proof
  assume "evaluation I (points_to x y)"
  hence "evaluation I (sl_conj (sl_mapsto x y) true)"
    by (simp add: points_to_def)
  from this obtain h1 h2 where "(union_heaps h1 h2 = heap I) 
                              \<and> (disjoint_heaps h1 h2) 
                              \<and> (evaluation (to_interp (store I) h1) (sl_mapsto x y))
                              \<and> (evaluation (to_interp (store I) h2) (true))"
    using evaluation.simps(9) by blast
  hence "(store I x \<in> dom h1) \<and> (dom h1 \<subseteq> dom (heap I))"
    by (metis draft_1 draft_2 draft_3 evaluation.simps(8) insertI1)
  hence"store_and_heap I x = store_and_heap (to_interp (store I) h1) x"
    using \<open>union_heaps h1 h2 = heap I 
         \<and> disjoint_heaps h1 h2 
         \<and> evaluation (to_interp (store I) h1) (sl_mapsto x y) 
         \<and> evaluation (to_interp (store I) h2) true\<close> 
          Abs_heaps_inverse Rep_heaps a_heap_def commutative_union_disjoint_heaps draft_1 draft_2 
          evaluation.simps(8) finite_union_heaps map_add_find_right mem_Collect_eq 
          store_and_heap_def union_heaps_def
    by (metis (no_types, lifting))
  thus "(store_and_heap I x = Some (store_vector (store I) y))"
    using \<open>union_heaps h1 h2 = heap I 
         \<and> disjoint_heaps h1 h2 
         \<and> evaluation (to_interp (store I) h1) (sl_mapsto x y) 
         \<and> evaluation (to_interp (store I) h2) true\<close> 
          draft_1 evaluation.simps(8)
    by (simp add: draft_1)
next
  assume "(store_and_heap I x = Some (store_vector (store I) y))"
  from this obtain h1 h2 where ""
  (*TODO*)
  thus "(store_and_heap I x = Some (store_vector (store I) y))"
oops


lemma tf_prop_2:
  fixes I::"('var, 'addr, 'k::finite) interp"
    and x::"'var"
  shows "(evaluation I (alloc x)) 
     \<longleftrightarrow> store I x \<in> (Interpretation.dom (heap I))"
proof
  show "evaluation I (alloc x) \<Longrightarrow> store I x \<in> Interpretation.dom (heap I)"
oops

lemma tf_prop_3:
  fixes I::"('var, 'addr, 'k::finite) interp"
    and n::enat
  shows "evaluation I (ext_card_heaps_superior_to n)
    \<longleftrightarrow> card_heaps (heap I) \<ge> n"
proof
  show "evaluation I (ext_card_heaps_superior_to n) \<Longrightarrow> n \<le> card_heaps (heap I)"
oops


end
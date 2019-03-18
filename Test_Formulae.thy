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

lemma tf_prop_1:
  fixes I::"('var, 'addr, 'k::finite) interp"
    and x::"'var"
    and y::"('var, 'k) vec"
  shows "(evaluation I (points_to x y)) 
       = (store_and_heap I x = Some (store_vector (store I) y))"
proof
  assume "evaluation I (points_to x y)"
  hence "evaluation I (sl_conj (sl_mapsto x y) true)"
    by (simp add: points_to_def)
  from this obtain h1 h2 where def_0: "(union_heaps h1 h2 = heap I) 
                                     \<and> (disjoint_heaps h1 h2) 
                                     \<and> (evaluation (to_interp (store I) h1) (sl_mapsto x y))
                                     \<and> (evaluation (to_interp (store I) h2) (true))"
    using evaluation.simps(9) by blast
  hence "(store I x \<in> h_dom h1) \<and> (h_dom h1 \<subseteq> h_dom (heap I))"
    by (metis evaluation.simps(8) heap_on_to_interp singletonI store_on_to_interp sub_heap_included)
  hence "store_and_heap I x = store_and_heap (to_interp (store I) h1) x"
    by (metis (no_types, lifting) Abs_heaps_inverse Rep_heaps a_heap_def 
        commutative_union_disjoint_heaps def_0 dom_map_add evaluation.simps(8) 
        finite_Un heap_on_to_interp map_add_find_right mem_Collect_eq store_on_to_interp 
        store_and_heap_with_Rep_heaps union_heaps_def)
  thus "(store_and_heap I x = Some (store_vector (store I) y))"
    by (metis def_0 evaluation.simps(8) store_on_to_interp)
next
  assume asm: "(store_and_heap I x = Some (store_vector (store I) y))"
  define h1 where "h1 = add_to_heap h_empty (store I x) (store_vector (store I) y)"
  define h2 where "h2 = remove_from_heap (heap I) (store I x)"
  have dijsoint_heaps_from_h:"(union_heaps h1 h2 = heap I) \<and> (disjoint_heaps h1 h2)"
    unfolding h1_def h2_def
    by (metis asm disjoint_add_remove_element dom_store_and_heap store_and_heap_def 
        union_add_remove_element)
  hence "evaluation (to_interp (store I) h1) (sl_mapsto x y)" unfolding h1_def
    by (simp add: get_from_add_to_heap h_dom_add_not_contained_element h_dom_empty_heap 
                  heap_on_to_interp store_and_heap_h store_on_to_interp)
  moreover have "evaluation (to_interp (store I) h2) (true)"
    by simp
  ultimately show "evaluation I (points_to x y)"
    by (metis evaluation.simps(9) points_to_def dijsoint_heaps_from_h)
qed

lemma tf_prop_2:
  fixes I::"('var, 'addr, 'k::finite) interp"
    and x::"'var"
  shows "(evaluation I (alloc x)) 
       = ((store I) x \<in> (h_dom (heap I)))"
proof
  assume "evaluation I (alloc x)"
  show "(store I) x \<in> (h_dom (heap I))"
  proof (rule ccontr)
    assume asm:"(store I) x \<notin> (h_dom (heap I))"
    define h_L::"('addr, 'k) heaps" where "h_L = add_to_heap h_empty (store I x) (vec (store I x))"
    have "h_dom h_L = {store I x}"
      by (simp add: h_L_def h_dom_add_not_contained_element h_dom_empty_heap)
    hence "disjoint_heaps (heap I) h_L"
      by (simp add: asm disjoint_heaps_def)
    define h1 where "h1 = union_heaps (heap I) h_L"
     "evaluation (to_interp (store I) h1) false"
    


(*
  hence inta: "\<nexists>h1. (disjoint_heaps h1 (heap I)) 
                 \<and> (evaluation (to_interp (store I) h1) (sl_mapsto x (vec x)))"
    by (simp add: alloc_def)
  define h_L where "h_L = restricted_heap (heap I) ((store I) x)"
  have "evaluation (to_interp (store I) h_L) (sl_mapsto x (vec x))" unfolding h_L_def
*)
(*
  have "\<not>(disjoint_heaps (heap I) h_L)" unfolding h_L_def using inta

  thus "store I x \<in> (h_dom (heap I))"
*)
oops

lemma tf_prop_3:
  fixes I::"('var, 'addr, 'k::finite) interp"
    and n::enat
  shows "(evaluation I (ext_card_heaps_superior_to n))
       = (card_heaps (heap I) \<ge> n)"
proof
  assume "evaluation I (ext_card_heaps_superior_to n)"
  thus "card_heaps (heap I) \<ge> n"
oops


(*DRAFT *)
(*  have "union_heaps h1 h2 = heap I" unfolding h1_def h2_def 
    proof (rule union_add_remove_element)
      show "get_from_heap (heap I) (store I x) = Some (store_vector (store I) y)" using asm unfolding store_and_heap_def
        by auto
    next
      show "(store I) x \<in> h_dom (heap I)"
        by (simp add: asm dom_store_and_heap)
    qed
  moreover have "disjoint_heaps h1 h2" unfolding h1_def h2_def
    by (metis asm disjoint_add_remove_element dom_store_and_heap store_and_heap_def)*)

end
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

primrec card_heap_superior_to :: "nat \<Rightarrow> ('var, 'k::finite) sl_formula"
  where   
      "card_heap_superior_to (Suc n) = sl_conj (card_heap_superior_to n) (not sl_emp)"
    | "card_heap_superior_to 0 = true"

primrec ext_card_heap_superior_to ::  "enat \<Rightarrow> ('var, 'k::finite) sl_formula"
  where
      "ext_card_heap_superior_to \<infinity> = false"
    | "ext_card_heap_superior_to n = card_heap_superior_to n"


subsection {* Inductive Set *}

inductive_set test_formulae :: "('var, 'k::finite) sl_formula set"
  where
    "(points_to x y) \<in> test_formulae"
  | "(alloc x) \<in> test_formulae"
  | "(ext_card_heap_superior_to n) \<in> test_formulae"
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
  thus "(store I) x \<in> (h_dom (heap I))"
proof (rule rev_notE)
    let ?P = "evaluation I (alloc x)"
    assume asm: "(store I) x \<notin> (h_dom (heap I))"
    define h_L::"('addr, 'k) heaps" where "h_L = add_to_heap h_empty (store I x) (store_vector (store I) (vec x))"
    have dom_h_L: "h_dom h_L = {(store I) x}"
      by (simp add: h_L_def h_dom_add_not_contained_element h_dom_empty_heap)
    moreover have "store_and_heap (to_interp (store I) h_L) x = Some (store_vector (store I) (vec x))"
      by (simp add: get_from_add_to_heap h_L_def store_and_heap_h)
    ultimately have evl_mapsto: "evaluation (to_interp (store I) h_L) (sl_mapsto x (vec x))"
      by (simp add: heap_on_to_interp store_on_to_interp)
    have "disjoint_heaps (heap I) h_L"
      by (simp add: asm disjoint_heaps_def dom_h_L)
    have "evaluation (to_interp (store I) h_L) (sl_mapsto x (vec x))"
      using evl_mapsto by blast
    define h1 where "h1 = union_heaps (heap I) h_L"
    have "\<not>(evaluation (to_interp (store I) h1) false)"
      by simp
    thus "\<not>(evaluation I (alloc x))" unfolding alloc_def
      using evl_mapsto asm disjoint_heaps_def dom_h_L by fastforce
  qed
next
  assume "(store I) x \<in> (h_dom (heap I))"
  thus "evaluation I (alloc x)"
    by (simp add: alloc_def disjoint_heaps_def heap_on_to_interp store_on_to_interp)
qed

lemma tf_prop_3:
  fixes I::"('var, 'addr, 'k::finite) interp"
    and n::enat
  shows "(evaluation I (ext_card_heap_superior_to n))
       = (card_heap (heap I) \<ge> n)"
proof
  assume "evaluation I (ext_card_heap_superior_to n)"
  thus "card_heap (heap I) \<ge> n"
  proof (induct n arbitrary: I)
    case (enat nat)
    then show ?case
    proof (induct nat arbitrary: I)
      case 0
      then show ?case
        using zero_enat_def by auto 
    next
      case (Suc nat)
      have "evaluation I (sl_conj (card_heap_superior_to nat) (not sl_emp))"
        using Suc.prems by auto 
      from this obtain h1 h2 
        where def_0: "(disjoint_heaps h1 h2)
                    \<and> (union_heaps h1 h2 = heap I)
                    \<and> (evaluation (to_interp (store I) h1) (card_heap_superior_to nat))
                    \<and> (evaluation (to_interp (store I) h2) (not sl_emp))"
        using evaluation.simps(9) by blast
      hence "evaluation (to_interp (store I) h1) (ext_card_heap_superior_to nat)"
        by simp
      hence "card_heap h1 \<ge> nat"
        by (metis Suc.hyps heap_on_to_interp) 
      moreover have "card_heap h2 \<ge> 1" 
        using def_0 by (simp add: card_not_empty_heap heap_on_to_interp)  
      ultimately have "card_heap (union_heaps h1 h2) \<ge> (Suc nat)" using def_0
        by (metis add.commute card_union_disjoint_heaps of_nat_Suc of_nat_eq_enat)
      then show ?case
        by (simp add: def_0)
    qed
  next
    case infinity
    then show ?case
      by simp
  qed
next
  assume "card_heap (heap I) \<ge> n"
  thus "evaluation I (ext_card_heap_superior_to n)"
  proof (induction n arbitrary : I)
    case (enat nat)
    then show ?case
    proof (induction nat arbitrary : I)
      case 0
      then show ?case
        by simp 
    next
      case (Suc nat)
      then show ?case sorry
    qed
  next
    case infinity
    then show ?case sorry
  qed


end
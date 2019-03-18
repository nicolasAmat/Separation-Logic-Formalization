(*  Title:      Separation-Logic-Formalization/Interpretation.thy
    Author:     Nicolas Amat, Mnacho Echenim, Nicolas Peltier
*)

section {* Interpretations *}

text {* This section contains the formalization of an interpretations in the separation logic. *}

theory Interpretation
imports 
    "HOL.Map" 
    "HOL-Analysis.Finite_Cartesian_Product"
    "HOL-Library.Extended_Nat"
begin


subsection {* Heap *}

definition a_heap
  where "a_heap h \<longleftrightarrow> finite (dom h)"

typedef ('addr, 'k) heaps = "{(h::'addr \<Rightarrow> (('addr, 'k) vec) option). a_heap h}" 
  unfolding a_heap_def
  using finite_dom_map_of by auto


subsection {* Interpretation *}

type_synonym ('var, 'addr, 'k) interp = "('var \<Rightarrow> 'addr) \<times> (('addr, 'k) heaps)"


subsection {* Heap and Store from an Interpretation *}

definition store :: "('var, 'addr, 'k) interp \<Rightarrow> ('var \<Rightarrow> 'addr)" 
  where "store I = fst I"

definition heap :: "('var, 'addr, 'k) interp \<Rightarrow> ('addr, 'k) heaps"
  where "heap I = snd I"


subsection {* Interpretation from an Heap and a Store *}

definition to_interp :: "('var \<Rightarrow> 'addr) \<Rightarrow> (('addr, 'k) heaps) \<Rightarrow> ('var, 'addr, 'k) interp"
  where "to_interp s h = (s, h)"


subsection {* Consecutive Store and Heap on a variable *}

definition store_and_heap :: "('var, 'addr, 'k) interp \<Rightarrow> 'var => ('addr, 'k) vec option"
  where "store_and_heap I x = Rep_heaps (heap I) ((store I) x)"


subsection {* Get from Heap *}

definition get_from_heap :: "('addr, 'k) heaps \<Rightarrow> 'addr \<Rightarrow> ('addr, 'k) vec option"
  where "get_from_heap h x = Rep_heaps h x"


subsection {* Heap Constructors *}

definition h_empty :: "('addr, 'k) heaps"
  where "h_empty \<equiv> Abs_heaps(\<lambda>x. None)"

definition h_singleton :: "'addr \<Rightarrow> ('addr, 'k) vec \<Rightarrow> ('addr, 'k) heaps"
  where "h_singleton x y = Abs_heaps((\<lambda>x. None) (x := Some y))"

definition remove_from_heap :: "('addr, 'k) heaps \<Rightarrow> 'addr \<Rightarrow> ('addr, 'k) heaps"
  where "remove_from_heap h x = Abs_heaps ((Rep_heaps h) (x := None))"

definition add_to_heap :: "('addr, 'k) heaps \<Rightarrow> 'addr \<Rightarrow> ('addr, 'k) vec \<Rightarrow> ('addr, 'k) heaps"
  where "add_to_heap h x y = Abs_heaps ((Rep_heaps h) (x := Some y))"


subsection {* Heaps Operations *}

definition h_dom :: "('addr, 'k) heaps \<Rightarrow> 'addr set"
  where "h_dom h = {a. Rep_heaps h a \<noteq> None}"

definition disjoint_heaps :: "('addr, 'k) heaps \<Rightarrow> ('addr, 'k) heaps \<Rightarrow> bool"
  where "disjoint_heaps h1 h2 \<longleftrightarrow> (h_dom h1) \<inter> (h_dom h2) = {}"

definition union_heaps :: "('addr, 'k) heaps \<Rightarrow> ('addr, 'k) heaps \<Rightarrow> ('addr, 'k) heaps"
  where "union_heaps h1 h2 = Abs_heaps ((Rep_heaps h1) ++ (Rep_heaps h2))"

definition equal_heaps :: "('addr, 'k) heaps \<Rightarrow> ('addr, 'k) heaps \<Rightarrow> bool"
  where "equal_heaps h1 h2 = ((Rep_heaps h1 \<subseteq>\<^sub>m Rep_heaps h2) \<and> (Rep_heaps h2 \<subseteq>\<^sub>m Rep_heaps h1))"

definition empty_heap :: "('addr, 'k) heaps \<Rightarrow> bool"
  where "empty_heap h = (Rep_heaps h = Map.empty)"

definition card_heap :: "('addr, 'k) heaps \<Rightarrow> enat" 
  where "card_heap h = card (h_dom h)"


subsection {* Store Applied on a Vector *}

definition addr_from_var_vector :: "('var \<Rightarrow> 'addr) \<Rightarrow> ('var, 'k::finite) vec \<Rightarrow> 'k \<Rightarrow> 'addr"
  where "addr_from_var_vector s v k = (s (vec_nth v k))"

definition store_vector :: "('var \<Rightarrow> 'addr) \<Rightarrow> ('var, 'k::finite) vec \<Rightarrow> ('addr, 'k::finite) vec"
  where "store_vector s v =  vec_lambda (addr_from_var_vector s v)"


subsection {* DRAFT *}

lemma store_on_to_interp:
  fixes I::"('var, 'addr, 'k) interp"
    and x::"'var"
    and h::"('addr, 'k) heaps"
  shows "store (to_interp (store I) h) = store I"
  by (simp add: store_def to_interp_def)

lemma heap_on_to_interp:
  fixes I::"('var, 'addr, 'k) interp"
    and h::"('addr, 'k) heaps"
  shows "heap (to_interp (store I) h) = h"
  by (simp add: heap_def to_interp_def)

lemma sub_heap_included:
  fixes h::"('addr, 'k) heaps"
    and h1::"('addr, 'k) heaps"
    and h2::"('addr, 'k) heaps"
  assumes "union_heaps h1 h2 = h"
  shows "h_dom h1 \<subseteq> h_dom h"
  by (metis Abs_heaps_inverse Rep_heaps a_heap_def assms dom_def dom_map_add finite_Un h_dom_def 
      mem_Collect_eq sup_ge2 union_heaps_def)

lemma h_dom_empty_heap:
  "h_dom h_empty = {}"
  by (simp add: Abs_heaps_inverse a_heap_def h_dom_def h_empty_def)

lemma h_dom_add_element:
  fixes h::"('addr, 'k) heaps"
    and x::"'addr"
    and y::"('addr, 'k) vec"
  assumes "x \<notin> (h_dom h)"
  shows "h_dom (add_to_heap h x y) = ((h_dom h) \<union> {x})"
  by (metis Abs_heaps_inverse Rep_heaps Un_insert_right a_heap_def add_to_heap_def dom_def 
      dom_fun_upd finite_insert h_dom_def mem_Collect_eq option.distinct(1) sup_bot.comm_neutral)

lemma h_dom_remove_element:
  fixes h::"('addr, 'k) heaps"
    and x::"'addr"
  assumes "x \<in> (h_dom h)"
  shows "h_dom (remove_from_heap h x) = (h_dom h) - {x}"
  by (metis Abs_heaps_inverse Diff_subset Rep_heaps a_heap_def dom_def dom_fun_upd h_dom_def 
      infinite_super mem_Collect_eq remove_from_heap_def)

lemma disjoint_add_remove_element:
  fixes h::"('addr, 'k) heaps"
    and x::"'addr"
    and y::"('addr, 'k) vec"
  assumes "x \<in> (h_dom h)"
    and "get_from_heap h x = Some y"
  shows "disjoint_heaps (add_to_heap h_empty x y) (remove_from_heap h x)"
  by (simp add: assms(1) disjoint_heaps_def h_dom_add_element h_dom_empty_heap h_dom_remove_element)

lemma union_add_remove_element:
  fixes h::"('addr, 'k) heaps"
    and x::"'addr"
  assumes  "x \<in> (h_dom h)"
    and "get_from_heap h x = Some y"
  shows "union_heaps (add_to_heap h_empty x y) (remove_from_heap h x) = h"
  oops

subsection {* Useful Heaps Results *}

lemma finite_union_heaps:
  fixes h1::"('addr, 'k) heaps"
    and h2::"('addr, 'k) heaps"
  assumes "finite (h_dom h1)"
    and "finite (h_dom h2)"
  shows "finite (h_dom (union_heaps h1 h2))"
  by (metis Rep_heaps a_heap_def dom_def h_dom_def mem_Collect_eq)

lemma commutative_union_disjoint_heaps:
  fixes h1::"('addr, 'k) heaps"
    and h2::"('addr, 'k) heaps"
  assumes "disjoint_heaps h1 h2"
  shows "union_heaps h1 h2 = union_heaps h2 h1"
  by (metis (full_types) assms disjoint_heaps_def dom_def h_dom_def map_add_comm union_heaps_def) 


end
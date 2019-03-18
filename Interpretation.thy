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


subsection {* Get Elements from an Heap *}

definition get_from_heap :: "('addr, 'k) heaps \<Rightarrow> 'addr \<Rightarrow> ('addr, 'k) vec option"
  where "get_from_heap h x = Rep_heaps h x"


subsection {* Consecutive Store and Heap on a Variable *}

definition store_and_heap :: "('var, 'addr, 'k) interp \<Rightarrow> 'var => ('addr, 'k) vec option"
  where "store_and_heap I x = get_from_heap (heap I) ((store I) x)"


subsection {* Heap Constructors *}

definition h_empty :: "('addr, 'k) heaps"
  where "h_empty \<equiv> Abs_heaps(\<lambda>x. None)"

definition h_singleton :: "'addr \<Rightarrow> ('addr, 'k) vec \<Rightarrow> ('addr, 'k) heaps"
  where "h_singleton x y = Abs_heaps((\<lambda>x. None) (x := Some y))"

definition remove_from_heap :: "('addr, 'k) heaps \<Rightarrow> 'addr \<Rightarrow> ('addr, 'k) heaps"
  where "remove_from_heap h x = Abs_heaps ((Rep_heaps h) (x := None))"

definition add_to_heap :: "('addr, 'k) heaps \<Rightarrow> 'addr \<Rightarrow> ('addr, 'k) vec \<Rightarrow> ('addr, 'k) heaps"
  where "add_to_heap h x y = Abs_heaps ((Rep_heaps h) (x := Some y))"


subsection {* Heap Restriction *}

definition restricted_heap :: "('addr, 'k) heaps \<Rightarrow> 'addr \<Rightarrow> ('addr, 'k) heaps"
  where "restricted_heap h x = Abs_heaps ((\<lambda>x. None)(x := get_from_heap h x))"


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


subsection {* DRAFT *}

lemma store_on_to_interp:
  fixes I::"('var, 'addr, 'k) interp"
    and x::'var
    and h::"('addr, 'k) heaps"
  shows "store (to_interp (store I) h) = store I"
  by (simp add: store_def to_interp_def)

lemma heap_on_to_interp:
  fixes I::"('var, 'addr, 'k) interp"
    and h::"('addr, 'k) heaps"
  shows "heap (to_interp (store I) h) = h"
  by (simp add: heap_def to_interp_def)

(* remove? *)
lemma store_and_heap_on_to_interp:
  fixes I::"('var, 'addr, 'k) interp"
  shows "store_and_heap (to_interp (store I) (heap I)) = store_and_heap I"
  by (simp add: heap_def store_def to_interp_def)

(* remove? *)
lemma store_and_heap_h:
  fixes I::"('var, 'addr, 'k) interp"
    and h::"('addr, 'k) heaps"
    and x::'var
  shows "store_and_heap (to_interp (store I) h) x = get_from_heap h ((store I) x)"
  by (simp add: heap_on_to_interp store_and_heap_def store_on_to_interp)

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

lemma h_dom_add_not_contained_element:
  fixes h::"('addr, 'k) heaps"
    and x::'addr
    and y::"('addr, 'k) vec"
  assumes "x \<notin> (h_dom h)"
  shows "h_dom (add_to_heap h x y) = ((h_dom h) \<union> {x})"
  by (metis Abs_heaps_inverse Rep_heaps Un_insert_right a_heap_def add_to_heap_def dom_def 
      dom_fun_upd finite_insert h_dom_def mem_Collect_eq option.distinct(1) sup_bot.comm_neutral)

lemma h_dom_add_contained_element:
  fixes h::"('addr, 'k) heaps"
    and x::'addr
    and y::"('addr, 'k) vec"
  assumes "x \<in> (h_dom h)"
  shows "h_dom (add_to_heap h x y) = h_dom h"
  by (metis Abs_heaps_inverse Rep_heaps a_heap_def add_to_heap_def assms dom_def dom_fun_upd 
      h_dom_def insert_absorb mem_Collect_eq option.distinct(1))

lemma h_dom_remove_contained_element:
  fixes h::"('addr, 'k) heaps"
    and x::'addr
  assumes "x \<in> (h_dom h)"
  shows "h_dom (remove_from_heap h x) = (h_dom h) - {x}"
  by (metis Abs_heaps_inverse Diff_subset Rep_heaps a_heap_def dom_def dom_fun_upd h_dom_def 
      infinite_super mem_Collect_eq remove_from_heap_def)

lemma h_dom_remove_not_contained_element:
  fixes h::"('addr, 'k) heaps"
    and x::'addr
  assumes "x \<notin> (h_dom h)"
  shows "h_dom (remove_from_heap h x) = h_dom h"
  by (metis Rep_heaps_inverse assms domIff dom_def fun_upd_triv h_dom_def remove_from_heap_def)

lemma disjoint_add_remove_element:
  fixes h::"('addr, 'k) heaps"
    and x::'addr
    and y::"('addr, 'k) vec"
  assumes "x \<in> (h_dom h)"
    and "get_from_heap h x = Some y"
  shows "disjoint_heaps (add_to_heap h_empty x y) (remove_from_heap h x)"
  by (simp add: assms(1) disjoint_heaps_def h_dom_add_not_contained_element h_dom_empty_heap 
                h_dom_remove_contained_element)

lemma union_add_remove_element:
  fixes h::"('addr, 'k) heaps"
    and x::'addr
  assumes  "x \<in> (h_dom h)"
    and "get_from_heap h x = Some y"
  shows "union_heaps (add_to_heap h_empty x y) (remove_from_heap h x) = h" using assms unfolding add_to_heap_def h_empty_def remove_from_heap_def h_dom_def get_from_heap_def
proof -
assume a1: "Rep_heaps h x = Some y"
  assume "x \<in> {a. Rep_heaps h a \<noteq> None}"
have f2: "Rep_heaps h(x \<mapsto> y) = Rep_heaps h"
  using a1 by (metis (no_types) fun_upd_triv)
  have "((x \<notin> dom ((Rep_heaps h)(x := None)) \<and> a_heap [x \<mapsto> y]) \<and> a_heap ((Rep_heaps h)(x := None))) 
       \<and> a_heap (Map.empty::'addr \<Rightarrow> ('addr, 'k) vec option)"
    using Rep_heaps a_heap_def by fastforce
  then show "union_heaps (Abs_heaps (Rep_heaps (Abs_heaps Map.empty)(x \<mapsto> y))) (Abs_heaps ((Rep_heaps h)(x := None))) = h"
    using f2 by (simp add: Abs_heaps_inverse Rep_heaps_inverse map_add_upd_left union_heaps_def)
qed

lemma dom_store_and_heap:
  fixes I::"('var, 'addr , 'k) interp"
    and x::'var
    and y::"('addr , 'k) vec"
  assumes "store_and_heap I x = Some y"
  shows "((store I) x) \<in> h_dom (heap I)"
  by (metis assms domIff dom_def get_from_heap_def h_dom_def option.simps(3) store_and_heap_def)

lemma store_and_heap_with_Rep_heaps:
  fixes I::"('var, 'addr, 'k) interp"
    and x::'var
  shows "store_and_heap I x = Rep_heaps (heap I) (store I x)"
  by (simp add: get_from_heap_def store_and_heap_def)

lemma get_from_add_to_heap:
  fixes x::'addr
    and y::"('addr, 'k) vec"
  shows "get_from_heap (add_to_heap h_empty x y) x = Some y"
  by (simp add: Abs_heaps_inverse a_heap_def add_to_heap_def get_from_heap_def h_empty_def)

lemma dom_restricted_heap:
  fixes h::"('addr, 'k) heaps"
    and x::'addr
  assumes "x \<in> h_dom h"
  shows "h_dom (restricted_heap h x) = {x}"
proof -
  have f1: "\<forall>f z a. ((z::('addr, 'k) vec option) = None \<or> a_heap (f(a::'addr := z))) \<or> infinite (insert a {a. f a \<noteq> None})"
    by (metis a_heap_def dom_def dom_fun_upd)
  have "Rep_heaps h x \<noteq> None"
    using assms h_dom_def by fastforce
  then have "{a. (Map.empty(x := Rep_heaps h x)) a \<noteq> None} = {x} \<and> a_heap (Map.empty(x := Rep_heaps h x))"
    using f1 by force
  then show ?thesis
    by (simp add: Abs_heaps_inverse get_from_heap_def h_dom_def restricted_heap_def)
qed


end
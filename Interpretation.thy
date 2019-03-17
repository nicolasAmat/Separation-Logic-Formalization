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


subsection {* Heaps Operations *}

definition h_dom :: "('addr, 'k) heaps \<Rightarrow> 'addr set"
  where "h_dom h = {a. Rep_heaps h a \<noteq> None}"

definition disjoint_heaps :: "('addr, 'k) heaps \<Rightarrow> ('addr, 'k) heaps \<Rightarrow> bool"
  where "disjoint_heaps h1 h2 \<longleftrightarrow> (h_dom h1) \<inter> (h_dom h2) = {}"

definition union_heaps :: "('addr, 'k) heaps \<Rightarrow> ('addr, 'k) heaps \<Rightarrow> ('addr, 'k) heaps"
  where "union_heaps h1 h2 = Abs_heaps ((Rep_heaps h1) ++ (Rep_heaps h2))"

definition equal_heaps :: "('addr, 'k) heaps \<Rightarrow> ('addr, 'k) heaps \<Rightarrow> bool"
  where "equal_heaps h1 h2 = ((Rep_heaps h1 \<subseteq>\<^sub>m Rep_heaps h2) \<and> (Rep_heaps h2 \<subseteq>\<^sub>m Rep_heaps h1))"

definition empty_heaps :: "('addr, 'k) heaps \<Rightarrow> bool"
  where "empty_heaps h = (Rep_heaps h = Map.empty)"

definition card_heaps :: "('addr, 'k) heaps \<Rightarrow> enat" 
  where "card_heaps h = card (h_dom h)"


subsection {* Store Applied on a Vector *}

definition addr_from_var_vector :: "('var \<Rightarrow> 'addr) \<Rightarrow> ('var, 'k::finite) vec \<Rightarrow> 'k \<Rightarrow> 'addr"
  where "addr_from_var_vector s v k = (s (vec_nth v k))"

definition store_vector :: "('var \<Rightarrow> 'addr) \<Rightarrow> ('var, 'k::finite) vec \<Rightarrow> ('addr, 'k::finite) vec"
  where "store_vector s v =  vec_lambda (addr_from_var_vector s v)"

(* Reprendre les lemmes draft *)
(* renommer dom en dom_heaps (Map.dom \<Rightarrow> dom et Interpretation.dom \<Rightarrow> dom_heaps)*)
(* reprendre les differentes preuves par conséquent *)
subsection {* DRAFT *}

lemma draft_1:
  fixes I::"('var, 'addr, 'k) interp"
    and x::"'var"
    and h::"('addr, 'k) heaps"
  shows "store (to_interp (store I) h) = store I"
  by (simp add: store_def to_interp_def)

lemma draft_2:
  fixes I::"('var, 'addr, 'k) interp"
    and h::"('addr, 'k) heaps"
  shows "heap (to_interp (store I) h) = h"
  by (simp add: heap_def to_interp_def)

lemma draft_3:
  fixes h::"('addr, 'k) heaps"
    and h1::"('addr, 'k) heaps"
    and h2::"('addr, 'k) heaps"
  assumes "union_heaps h1 h2 = h"
  shows "h_dom h1 \<subseteq> h_dom h"
proof
  fix x
  assume "x \<in> h_dom h1"
  hence "x \<in> (h_dom (union_heaps h1 h2))"
    proof -
      have f1: "x \<in> dom (Rep_heaps h1)"
    using h_dom_def \<open>x \<in> h_dom h1\<close> by fastforce
      have f2: "a_heap (Rep_heaps h1)"
    using Rep_heaps by blast
      have "a_heap (Rep_heaps h2)"
        using Rep_heaps by blast
      then show ?thesis
        using f2 f1 by (simp add: Abs_heaps_inverse h_dom_def a_heap_def domIff union_heaps_def)
    qed
  thus "x \<in> h_dom h"
    by (simp add: assms)
qed

lemma dom_empty_heaps:
  fixes h::"('addr, 'k) heaps"
  assumes "empty_heaps h"
  shows "h_dom h = {}"
  using h_dom_def assms empty_heaps_def by force

lemma dom_update_add_element:
  fixes h::"('addr, 'k) heaps"
    and x::"'addr"
    and y::"('addr, 'k) vec"
  assumes "x \<notin> (h_dom h)"
  shows "h_dom (Abs_heaps((Rep_heaps h)(x := (Some y)))) = ((h_dom h) \<union> {x})"
  by (metis Abs_heaps_inverse h_dom_def dom_def Rep_heaps Un_insert_right a_heap_def dom_fun_upd 
      finite_insert mem_Collect_eq option.simps(3) sup_bot.comm_neutral)

lemma dom_update_remove_element:
  fixes h::"('addr, 'k) heaps"
    and x::"'addr"
  assumes "x \<in> (h_dom h)"
  shows "h_dom (Abs_heaps((Rep_heaps h)(x := None))) \<union> {x} = (h_dom h)"
  by (metis Abs_heaps_inverse h_dom_def dom_def Rep_heaps Un_insert_right a_heap_def assms 
      dom_fun_upd finite_insert insert_Diff mem_Collect_eq sup_bot.comm_neutral)


subsection {* Useful Heaps Results *}

lemma finite_union_heaps:
  fixes h1::"('addr, 'k) heaps"
    and h2::"('addr, 'k) heaps"
  assumes "finite (h_dom h1)"
    and "finite (h_dom h2)"
  shows "finite (h_dom (union_heaps h1 h2))"
proof -
  have finite_union_domains: "finite ((h_dom h1) \<union> (h_dom h2))"
    by (simp add: assms(1) assms(2))
  have union_inlude_into_union_domains:"h_dom (union_heaps h1 h2) \<subseteq> (h_dom h1) \<union> (h_dom h2)"
    by (metis Abs_heaps_inverse Rep_heaps a_heap_def dom_def dom_map_add h_dom_def infinite_Un 
        le_sup_iff mem_Collect_eq sup_ge1 sup_ge2 union_heaps_def)
  from finite_union_domains and union_inlude_into_union_domains 
  show "finite (h_dom (union_heaps h1 h2))"
    using infinite_super by blast
qed

lemma commutative_union_disjoint_heaps:
  fixes h1::"('addr, 'k) heaps"
    and h2::"('addr, 'k) heaps"
  assumes "disjoint_heaps h1 h2"
  shows "union_heaps h1 h2 = union_heaps h2 h1"
  by (metis h_dom_def dom_def assms disjoint_heaps_def map_add_comm union_heaps_def)


end
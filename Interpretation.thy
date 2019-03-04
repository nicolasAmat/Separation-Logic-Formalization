(*  Title:      Separation-Logic-Formalization/Interpretation.thy
    Author:     Nicolas Amat, Mnacho Echenim, Nicolas Peltier
*)

section {* Interpretations *}

text {* This section contains the formalization of an interpretations in the separation logic. *}

theory Interpretation
  imports 
    Main 
    "HOL.Map" 
    "HOL-Analysis.Finite_Cartesian_Product"
begin


subsection {* Heap *}

definition a_heap  where
  "a_heap h \<longleftrightarrow> finite (dom h)"

typedef ('addr, 'k) heaps = "{(h::'addr \<Rightarrow> (('addr, 'k) vec) option). a_heap h}" unfolding a_heap_def
  using finite_dom_map_of by auto


subsection {* Interpretation *}

type_synonym ('var, 'addr, 'k) interp = "('var \<Rightarrow> 'addr) \<times> (('addr, 'k) heaps)"


subsection {* Heap and Store from an Interpretation *}

definition store :: "('var, 'addr, 'k) interp \<Rightarrow> ('var \<Rightarrow> 'addr)" 
  where "store I = fst I"

definition heap :: "('var, 'addr, 'k) interp \<Rightarrow> ('addr, 'k) heaps"
  where "heap I = snd I"


subsection {* Interpretation from an Heap and a Store *}

definition constructor_interp :: "('var \<Rightarrow> 'addr) \<Rightarrow> (('addr, 'k) heaps) \<Rightarrow> ('var, 'addr, 'k) interp"
  where "constructor_interp s h = (s, h)"


subsection {* Heaps Operations *}

definition dom::"('addr, 'k) heaps \<Rightarrow> 'addr set" where
  "dom h = {a. Rep_heaps h a \<noteq> None}"

definition disjoint_heaps :: "('addr, 'k) heaps \<Rightarrow> ('addr, 'k) heaps \<Rightarrow> bool" where
  "disjoint_heaps h1 h2 \<longleftrightarrow> (dom h1) \<inter> (dom h2) = {}"

definition union_heaps :: "('addr, 'k) heaps \<Rightarrow> ('addr, 'k) heaps \<Rightarrow> ('addr, 'k) heaps" where
  "union_heaps h1 h2 = Abs_heaps ((Rep_heaps h1) ++ (Rep_heaps h2))"

definition equal_heaps :: "('addr, 'k) heaps \<Rightarrow> ('addr, 'k) heaps \<Rightarrow> bool" where
  "equal_heaps h1 h2 = ((Rep_heaps h1 \<subseteq>\<^sub>m Rep_heaps h2) \<and> (Rep_heaps h2 \<subseteq>\<^sub>m Rep_heaps h1))"

definition empty_heaps :: "('addr, 'k) heaps \<Rightarrow> bool" where
  "empty_heaps h \<equiv> Rep_heaps h = Map.empty"


subsection {* Store Applied on a Vector *}

definition addr_from_var_vector :: "('var \<Rightarrow> 'addr) \<Rightarrow> ('var, 'k::finite) vec \<Rightarrow> 'k::finite \<Rightarrow> 'addr" where 
"addr_from_var_vector s v k = (s (vec_nth v k))"

definition store_vector :: "('var \<Rightarrow> 'addr) \<Rightarrow> ('var, 'k::finite) vec \<Rightarrow> ('addr, 'k::finite) vec" where
  "store_vector s v =  vec_lambda (addr_from_var_vector s v)"


subsection {* Useful Heaps Results *}

lemma finite_union_heaps:
  assumes "finite (Map.dom (h1::'addr \<Rightarrow> (('addr,'k) vec) option))"
    and "finite (Map.dom h2)"
  shows "finite (Map.dom (h1 ++ h2))"
proof -
  have finite_union_domains: "finite ((Map.dom h1) \<union> (Map.dom h2))"
    by (simp add: assms(1) assms(2))
  have union_inlude_into_union_domains:"Map.dom(h1 ++ h2) \<subseteq> (Map.dom h1) \<union> (Map.dom h2)"
    by simp
  from finite_union_domains and union_inlude_into_union_domains show "finite (Map.dom(h1 ++ h2))"
    by auto
qed


end
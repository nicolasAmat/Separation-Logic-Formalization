(*  Title:      Separation-Logic-Formalization/Interpretation.thy
    Author:     Nicolas Amat, Mnacho Echenim, Nicolas Peltier
*)

section {* Interpretations *}

text {* This section contains the formalization of an interpretations in the separation logic. *}

theory Interpretation
  imports Main HOL.Map
begin


subsection {* Heap *}

definition a_heap  where
  "a_heap h \<longleftrightarrow> finite (dom h)"

typedef ('a, 'b) heaps = "{(h::'a \<Rightarrow> 'b option). a_heap h}" unfolding a_heap_def
  using finite_dom_map_of by auto


subsection {* Interpretation *}

type_synonym ('a, 'b, 'c) interp = "('a \<Rightarrow> 'b) \<times> (('b, 'c) heaps)"


subsection {* Heap and Store from an Interpretation *}

definition store :: "('a, 'b, 'c) interp => 'a \<Rightarrow> 'b" 
  where "store I = fst I"

definition heap :: "('a, 'b, 'c) interp \<Rightarrow> ('b, 'c) heaps"
  where "heap I = snd I"


subsection {* Heaps Operations *}

definition dom::"('a, 'b) heaps \<Rightarrow> 'a set" where
  "dom h = {a. Rep_heaps h a \<noteq> None}"

definition disjoint_heaps :: "('a, 'b) heaps \<Rightarrow> ('a, 'b) heaps \<Rightarrow> bool" where
  "disjoint_heaps h1 h2 \<longleftrightarrow> (dom h1) \<inter> (dom h2) = {}"

definition union_heaps :: "('a, 'b) heaps \<Rightarrow> ('a, 'b) heaps \<Rightarrow> ('a, 'b) heaps" where
  "union_heaps h1 h2 = Abs_heaps ((Rep_heaps h1)++(Rep_heaps h2))"

definition equal_heaps :: "('a, 'b) heaps \<Rightarrow> ('a, 'b) heaps \<Rightarrow> bool" where
  "equal_heaps h1 h2 = ((Rep_heaps h1 \<subseteq>\<^sub>m Rep_heaps h2) \<and> (Rep_heaps h2 \<subseteq>\<^sub>m Rep_heaps h1))"


subsection {* Useful Heaps Results *}

lemma finite_union_heaps:
  assumes "finite (Map.dom (h1::('a \<Rightarrow> 'b option)))"
    and "finite (Map.dom h2)"
  shows "finite (Map.dom (h1++h2))"
proof -
  have finite_union_domains: "finite ((Map.dom h1) \<union> (Map.dom h2))"
    by (simp add: assms(1) assms(2))
  have union_inlude_into_union_domains:"Map.dom(h1 ++ h2) \<subseteq> (Map.dom h1) \<union> (Map.dom h2)"
    by simp
  from finite_union_domains and union_inlude_into_union_domains show "finite (Map.dom(h1++h2))"
    by auto
qed


end
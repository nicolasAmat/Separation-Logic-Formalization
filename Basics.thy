(*  Title:      Separation-Logic-Formalization/Basics.thy
    Author:     Nicolas Amat
*)

section {* Formalization *}
theory Basics
  imports Main HOL.Map
begin                                            

text {* Definition of the Syntax and Semantics *}

subsection {* Some Types Definitions *}

definition a_heap  where
  "a_heap h \<longleftrightarrow> finite (dom h)"

typedef ('a, 'b) heaps = "{(h::'a \<Rightarrow> 'b option). a_heap h}" unfolding a_heap_def
  using finite_dom_map_of by auto

type_synonym ('a, 'b, 'c) interp = "('a \<Rightarrow> 'b) \<times> (('b, 'c) heaps)"

definition store :: "('a, 'b, 'c) interp => 'a \<Rightarrow> 'b" 
  where "store I = fst I"

definition heap :: "('a, 'b, 'c) interp \<Rightarrow> ('b, 'c) heaps"
  where "heap I = snd I"


definition dom::"('a, 'b) heaps \<Rightarrow> 'a set" where
  "dom h = {a. Rep_heaps h a \<noteq> None}"

definition disjoint_heaps :: "('a, 'b) heaps \<Rightarrow> ('a, 'b) heaps \<Rightarrow> bool" where
  "disjoint_heaps h1 h2 \<longleftrightarrow> (dom h1) \<inter> (dom h2) = {}"

definition union_heaps :: "('a, 'b) heaps \<Rightarrow> ('a, 'b) heaps \<Rightarrow> ('a, 'b) heaps" where
  "union_heaps h1 h2 = Abs_heaps ((Rep_heaps h1)++(Rep_heaps h2))"

definition equal_heaps :: "('a, 'b) heaps \<Rightarrow> ('a, 'b) heaps \<Rightarrow> bool" where
  "equal_heaps h1 h2 = ((Rep_heaps h1 \<subseteq>\<^sub>m Rep_heaps h2) \<and> (Rep_heaps h2 \<subseteq>\<^sub>m Rep_heaps h1))"

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

(* Formula Syntax *)
datatype 'a sl_formula =
  (* Boolean *)
    true
  | false
  (* Classical Logic *)
  | eq 'a 'a
  | not "'a sl_formula"
  | impl "'a sl_formula" "'a sl_formula"
  | conj "'a sl_formula" "'a sl_formula"
  | disj "'a sl_formula" "'a sl_formula"
  (* Quantifier *)
  | forall 'a "'a sl_formula"
  | exists 'a "'a sl_formula"
  (* Separation Logic *)
  | sl_emp
  | sl_mapsto 'a 'a
  | sl_conj "'a sl_formula" "'a sl_formula"
  | sl_magic_wand "'a sl_formula" "'a sl_formula"
  
primrec evaluation :: "(('a, 'b, 'c) interp) \<Rightarrow> 'a sl_formula \<Rightarrow> bool"
  where 
    "evaluation I true                = True"
  | "evaluation I false               = False" 
  | "evaluation I (eq x y)            = ((store I) x = (store I) y)"
  | "evaluation I (not P)             =  (\<not>(evaluation I P))"
  | "evaluation I (impl P Q)          = ((evaluation I P) \<longrightarrow> (evaluation I Q))"
  | "evaluation I (conj P Q)          = ((evaluation I P) \<and> (evaluation I Q))"
  | "evaluation I (disj P Q)          = ((evaluation I P) \<or> (evaluation I Q))"
  | "evaluation I (forall x P)        = (\<forall>u. (evaluation ((store I)(x:=u),(heap I)) P))"
  | "evaluation I (exists x P)        = (\<exists>u. (evaluation ((store I)(x:=u),(heap I)) P))"
  | "evaluation I (sl_emp)            = True"
  | "evaluation I (sl_mapsto E F)     = True"
  | "evaluation I (sl_conj P Q)       = (\<exists>h1 h2. (union_heaps h1 h2 = heap I)
                                               \<and> (disjoint_heaps h1 h2) 
                                               \<and> (evaluation ((store I), h1) P) 
                                               \<and> (evaluation ((store I), h2) Q))"
  | "evaluation I (sl_magic_wand P Q) = (\<forall>h. ((disjoint_heaps h (heap I)) \<and> (evaluation I P))
                                         \<longrightarrow> (evaluation ((store I), union_heaps (heap I) h)) Q)"

end
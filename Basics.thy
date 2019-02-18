(*  Title:      Separation-Logic-Formalization/Basics.thy
    Author:     Nicolas Amat
*)

section {* Formalization *}
theory Basics
  imports Main HOL.Map
begin                                            

text {* Definition of the Syntax and Semantics *}

subsection {* Some Types Definitions *}

(* Stores, Heaps, States *)
type_synonym var = string
type_synonym addr = nat
type_synonym val = int
type_synonym store = "var \<Rightarrow> val"

(*type_synonym heap = "addr \<rightharpoonup> val"
type_synonym state = "(store \<times> heap)"
 *)

definition a_heap  where
  "a_heap h \<longleftrightarrow> finite (dom h)"

typedef ('a, 'b) heaps = "{(h::'a \<Rightarrow> 'b option). a_heap h}" unfolding a_heap_def
  using finite_dom_map_of by auto

definition heap_func::"('a, 'b) heaps \<Rightarrow> ('a \<Rightarrow> 'b option)" where
"heap_func h = Rep_heaps h"

type_synonym ('a, 'b, 'c) interp = "('a \<Rightarrow> 'b) \<times> (('b, 'c) heaps)"

definition store :: "('a, 'b, 'c) interp => 'a \<Rightarrow> 'b" 
  where "store I = fst I"

definition heap :: "('a, 'b, 'c) interp \<Rightarrow> ('b, 'c) heaps"
  where "heap I = snd I"

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

definition dom::"('a, 'b) heaps \<Rightarrow> 'a set" where
  "dom h = {a. heap_func h a \<noteq> None}"

definition disjoint_heaps :: "('a, 'b) heaps \<Rightarrow> ('a, 'b) heaps \<Rightarrow> bool" where
  "disjoint_heaps h1 h2 \<longleftrightarrow> (dom h1) \<inter> (dom h2) = {}"

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
  
definition union_heaps :: "('a, 'b) heaps \<Rightarrow> ('a, 'b) heaps \<Rightarrow> ('a, 'b) heaps" where
  "union_heaps h1 h2 = Abs_heaps ((heap_func h1)++(heap_func h2))"

definition equal_heaps where
  "equal_heaps h1 h2 = ((h1 \<subseteq>\<^sub>m h2) \<and> (h2 \<subseteq>\<^sub>m h1))"


  
primrec evaluation :: "(('a, 'b, 'c) interp) \<Rightarrow> 'a sl_formula \<Rightarrow> bool"
  where 
    "evaluation I true                = True"
  | "evaluation I false               = False" 
  | "evaluation I (eq x y)            = ((store I) x = (store I) y)"
  | "evaluation I (not f)             =  (\<not>(evaluation I f))"
  | "evaluation I (impl f g)          = ((evaluation I f) \<longrightarrow> (evaluation I g))"
  | "evaluation I (conj f g)          = ((evaluation I f) \<and> (evaluation I g))"
  | "evaluation I (disj f g)          = ((evaluation I f) \<or> (evaluation I g))"
  | "evaluation I (forall x f)        = (\<forall>u. (evaluation ((store I)(x:=u),(heap I)) f))"
  | "evaluation I (exists x f)        = (\<exists>u. (evaluation ((store I)(x:=u),(heap I)) f))"
  | "evaluation I (sl_emp)            = True"
  | "evaluation I (sl_mapsto x y)     = True"
  | "evaluation I (sl_conj f g)       =  (\<exists>h1::(('b, 'c) heaps). \<exists>h2::(('b, 'c) heaps). (union_heaps (heap_func h1) (heap_func h2) = heap_func (heap I)))"  (* TODO *)
  | "evaluation I (sl_magic_wand f g) \<longleftrightarrow> False" (*(\<exists>h1 h2. ((union_heaps h1 h2) =  (heap I)) \<and> disjoint_heaps )*) (* TODO *)


subsection {* Some Functions Definitions *}

(* abbreviation empty_heap :: heap where
  "empty_heap \<equiv> Map.empty" *)

(* definition disjoint_heaps  where
  "disjoint_heaps h1 h2 \<longleftrightarrow> (dom h1) \<inter> (dom h2) = {}"

definition union_heaps where
  "union_heaps h1 h2 = h1 ++ h2"*)


end
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

typedef ('a, 'b) heaps = "{(h::'a \<Rightarrow> 'b option). a_heap h}"
  unfolding a_heap_def using finite_dom_map_of by auto

type_synonym ('a, 'b, 'c) interp = "('a \<Rightarrow> 'b) \<times> (('b, 'c) heaps)"

definition store::"('a, 'b, 'c) interp => 'a \<Rightarrow> 'b" 
  where "store I = fst I"

definition heap::"('a, 'b, 'c) interp \<Rightarrow> ('b, 'c) heaps"
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


fun evaluation::"(('a, 'b, 'c) interp) \<Rightarrow> 'd sl_formula \<Rightarrow> bool"
where 
    "evaluation I true         = True"
  | "evaluation I false        = False" 
  | "evaluation I (eq x y)     \<longleftrightarrow> (x = y)"
  | "evaluation I (not f)      \<longleftrightarrow> \<not>(evaluation I f)"
  | "evaluation I (impl f g)   \<longleftrightarrow> ((evaluation I f) \<longrightarrow> (evaluation I g))"
  | "evaluation I (conj f g)   \<longleftrightarrow> ((evaluation I f) \<and> (evaluation I g))"
  | "evaluation I (disj f g)   \<longleftrightarrow> ((evaluation I f) \<or> (evaluation I g))"


subsection {* Some Functions Definitions *}

(* abbreviation empty_heap :: heap where
  "empty_heap \<equiv> Map.empty" *)

definition disjoint_heaps  where
  "disjoint_heaps h1 h2 \<longleftrightarrow> (dom h1) \<inter> (dom h2) = {}"

definition union_heaps where
  "union_heaps h1 h2 = h1 ++ h2"


end
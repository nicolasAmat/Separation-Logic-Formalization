(*  Title:      Separation-Logic-Formalization/Basics.thy
    Author:     Nicolas Amat
*)

section {* Formalization *}
theory Basics
  imports Main HOL.Map "HOL-Imperative_HOL.Heap"
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

definition a_heap :: "addr set \<Rightarrow> val \<Rightarrow> bool" where
  "a_heap A V \<longleftrightarrow> A \<noteq> UNIV"

typedef ('a, 'v) heaps = "{(s, v::val). a_heap s v}"

(* Formula Syntax *)
datatype 'a sl_formula =
  (* Boolean *)
    true
  | false
  (* Classical Logic *)
  | not "'a sl_formula"
  | impl "'a sl_formula" "'a sl_formula"
  | conj "'a sl_formula" "'a sl_formula"
  | disj "'a sl_formula" "'a sl_formula"
  | eq 'a 'a
  (* Quantifier *)
  | forall 'a "'a sl_formula"
  | exists 'a "'a sl_formula"
  (* Separation Logic *)
  | sl_emp
  | sl_mapsto 'a 'a
  | sl_conj "'a sl_formula" "'a sl_formula"
  | sl_magic_wand "'a sl_formula" "'a sl_formula"


subsection {* Some Functions Definitions *}

(* abbreviation empty_heap :: heap where
  "empty_heap \<equiv> Map.empty" *)

definition disjoint_heaps  where
  "disjoint_heaps h1 h2 \<longleftrightarrow> (dom h1) \<inter> (dom h2) = {}"

definition union_heaps where
  "union_heaps h1 h2 = h1 ++ h2"


end
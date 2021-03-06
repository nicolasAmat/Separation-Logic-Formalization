(*  Title:      Separation-Logic-Formalization/Interpretation.thy
    Author:     Nicolas Amat, Mnacho Echenim, Nicolas Peltier
*)

section \<open>Interpretations\<close>

text \<open>This section contains the interpretations.\<close>

theory Interpretation
imports 
  "HOL.Map" 
  "HOL-Analysis.Finite_Cartesian_Product"
  "HOL-Library.Extended_Nat"
begin


subsection \<open>Heaps\<close>

definition a_heap :: "('addr \<Rightarrow> (('addr, 'k) vec) option) \<Rightarrow> bool"
  where "a_heap h \<longleftrightarrow> finite (dom h)"

typedef ('addr, 'k) heaps = "{(h::'addr \<Rightarrow> (('addr, 'k) vec) option). a_heap h}" 
  unfolding a_heap_def
  using finite_dom_map_of by auto


subsection \<open>Interpretations\<close>

type_synonym ('var, 'addr, 'k) interp = "('var \<Rightarrow> 'addr) \<times> (('addr, 'k) heaps)"


subsection \<open>Heap and Store from an Interpretation\<close>

definition store :: "('var, 'addr, 'k) interp \<Rightarrow> ('var \<Rightarrow> 'addr)" 
  where "store I = fst I"

definition heap :: "('var, 'addr, 'k) interp \<Rightarrow> ('addr, 'k) heaps"
  where "heap I = snd I"


subsection \<open>Interpretation from an Heap and a Store\<close>

definition to_interp :: "('var \<Rightarrow> 'addr) \<Rightarrow> (('addr, 'k) heaps) \<Rightarrow> ('var, 'addr, 'k) interp"
  where "to_interp s h = (s, h)"


subsection \<open>Get Elements from an Heap\<close>

definition get_from_heap :: "('addr, 'k) heaps \<Rightarrow> 'addr \<Rightarrow> ('addr, 'k) vec option"
  where "get_from_heap h x = Rep_heaps h x"


subsection \<open>Consecutive Store and Heap on a Variable\<close>

definition store_and_heap :: "('var, 'addr, 'k) interp \<Rightarrow> 'var => ('addr, 'k) vec option"
  where "store_and_heap I x = get_from_heap (heap I) ((store I) x)"


subsection \<open>Heap Operations\<close>

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


subsection \<open>Heap Constructors\<close>

definition h_empty :: "('addr, 'k) heaps"
  where "h_empty \<equiv> Abs_heaps(\<lambda>x. None)"

definition h_singleton :: "'addr \<Rightarrow> ('addr, 'k) vec \<Rightarrow> ('addr, 'k) heaps"
  where "h_singleton x y = Abs_heaps((Rep_heaps h_empty) (x := Some y))"

definition remove_from_heap :: "('addr, 'k) heaps \<Rightarrow> 'addr \<Rightarrow> ('addr, 'k) heaps"
  where "remove_from_heap h x = Abs_heaps ((Rep_heaps h) (x := None))"

definition add_to_heap :: "('addr, 'k) heaps \<Rightarrow> 'addr \<Rightarrow> ('addr, 'k) vec \<Rightarrow> ('addr, 'k) heaps"
  where "add_to_heap h x y = Abs_heaps ((Rep_heaps h) (x := Some y))"


subsection \<open>Heap Restriction\<close>

definition restricted_heap :: "('addr, 'k) heaps \<Rightarrow> 'addr \<Rightarrow> ('addr, 'k) heaps"
  where "restricted_heap h x = Abs_heaps ((Rep_heaps h_empty)(x := get_from_heap h x))"


subsection \<open>Heap Cast\<close>

definition to_heap :: "('addr \<Rightarrow> (('addr, 'k) vec) option) \<Rightarrow> ('addr, 'k) heaps"
  where "to_heap h = (if (finite (dom h)) then Abs_heaps h else h_empty)"


subsection \<open>Store Applied on a Vector\<close>

definition addr_from_var_vector :: "('var \<Rightarrow> 'addr) \<Rightarrow> ('var, 'k::finite) vec \<Rightarrow> 'k \<Rightarrow> 'addr"
  where "addr_from_var_vector s v k = (s (vec_nth v k))"

definition store_vector :: "('var \<Rightarrow> 'addr) \<Rightarrow> ('var, 'k::finite) vec \<Rightarrow> ('addr, 'k) vec"
  where "store_vector s v =  vec_lambda (addr_from_var_vector s v)"


subsection \<open>Store Applied on a Set\<close>

definition store_set :: "('var \<Rightarrow> 'addr) \<Rightarrow> 'var set \<Rightarrow> 'addr set"
  where "store_set s X = {s x | x. x \<in> X}"


subsection \<open>Useful Results\<close>

subsubsection \<open>Heap and Store from an Interpretation\<close>

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


subsubsection \<open>Get Elements from an Heap\<close>

lemma get_from_add_to_heap:
  fixes x::'addr
    and y::"('addr, 'k) vec"
  shows "get_from_heap (add_to_heap h_empty x y) x = Some y"
  by (simp add: Abs_heaps_inverse a_heap_def add_to_heap_def get_from_heap_def h_empty_def)


subsubsection \<open>Consecutive Store and Heap on a Variable\<close>

lemma store_and_heap_on_to_interp:
  fixes I::"('var, 'addr, 'k) interp"
  shows "store_and_heap (to_interp (store I) (heap I)) = store_and_heap I"
  by (simp add: heap_def store_def to_interp_def)

lemma store_and_heap_h:
  fixes I::"('var, 'addr, 'k) interp"
    and h::"('addr, 'k) heaps"
    and x::'var
  shows "store_and_heap (to_interp (store I) h) x = get_from_heap h ((store I) x)"
  by (simp add: heap_on_to_interp store_and_heap_def store_on_to_interp)

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


subsubsection \<open>Heap Operations\<close>

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

lemma sub_heap_included:
  fixes h::"('addr, 'k) heaps"
    and h1::"('addr, 'k) heaps"
    and h2::"('addr, 'k) heaps"
  assumes "union_heaps h1 h2 = h"
  shows "h_dom h1 \<subseteq> h_dom h"
  by (metis Abs_heaps_inverse Rep_heaps a_heap_def assms dom_def dom_map_add finite_Un h_dom_def 
      mem_Collect_eq sup_ge2 union_heaps_def)

lemma card_heap_inf_infty:
  fixes h::"('addr, 'k) heaps"
  shows "card_heap h < \<infinity>"
  by (simp add: card_heap_def)

lemma card_not_empty_heap:
  fixes h::"('addr, 'k) heaps"
  assumes "\<not>(empty_heap h)"
  shows "card_heap h \<ge> 1"
proof -
  have "card (h_dom h) \<ge> 1"
    by (metis (mono_tags) One_nat_def Rep_heaps Suc_leI a_heap_def assms card_0_eq dom_def 
        empty_heap_def empty_iff h_dom_def mem_Collect_eq neq0_conv)
  thus "card_heap h \<ge> 1"
    by (simp add: card_heap_def one_enat_def)
qed

lemma card_union_disjoint_heaps:
  fixes h1::"('addr, 'k) heaps"
    and h2::"('addr, 'k) heaps"
  assumes "disjoint_heaps h1 h2" 
    and "card_heap h1 \<ge> n"
    and "card_heap h2 \<ge> m"
  shows "card_heap (union_heaps h1 h2) \<ge> (n + m)"
proof -
  have disjoint_def:"h_dom h1 \<inter> h_dom h2 = {}"
    by (meson assms(1) disjoint_heaps_def)
  hence "h_dom (union_heaps h1 h2) = (h_dom h1) \<union> (h_dom h2)"
    by (metis Abs_heaps_inverse Rep_heaps a_heap_def dom_def dom_map_add h_dom_def infinite_Un 
        map_add_comm mem_Collect_eq union_heaps_def)
  hence "card_heap (union_heaps h1 h2) = card ((h_dom h1) \<union> (h_dom h2))"
    by (simp add: card_heap_def)
  hence "card_heap (union_heaps h1 h2) = card (h_dom h1) + card(h_dom h2) - card(h_dom h1 \<inter> h_dom h2)"
    by (metis Rep_heaps a_heap_def add_diff_cancel_right' card_Un_Int dom_def h_dom_def mem_Collect_eq)
  hence "card_heap (union_heaps h1 h2) = card_heap h1 + card_heap h2"
    by (simp add: card_heap_def disjoint_def)
  thus "card_heap (union_heaps h1 h2) \<ge> (n + m)"
    by (simp add: add_mono assms(2) assms(3))
qed


subsubsection \<open>Heap Constructors\<close>

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
  shows "union_heaps (add_to_heap h_empty x y) (remove_from_heap h x) = h" 
  using assms unfolding add_to_heap_def h_empty_def remove_from_heap_def h_dom_def get_from_heap_def
proof -
  assume a1: "Rep_heaps h x = Some y"
  assume "x \<in> {a. Rep_heaps h a \<noteq> None}"
  have f2: "Rep_heaps h = (Rep_heaps h)(x := None)(x \<mapsto> y)"
    using a1 by fastforce
  have "a_heap (Rep_heaps h)"
    using Rep_heaps by blast
  then show "union_heaps (Abs_heaps (Rep_heaps (Abs_heaps Map.empty)(x \<mapsto> y))) (Abs_heaps ((Rep_heaps h)(x := None))) = h"
    using f2 by (simp add: Abs_heaps_inverse Rep_heaps_inverse a_heap_def map_add_upd_left union_heaps_def)
qed

lemma h_singleton_add_to_heap:
  "h_singleton x y = add_to_heap (h_empty) x y"
  by (simp add: add_to_heap_def h_singleton_def)

lemma union_remove_from_heap_restricted_heap:
  fixes h::"('addr, 'k) heaps"
    and x::'addr
  assumes "x \<in> h_dom h"
  shows "h = union_heaps (remove_from_heap h x) (restricted_heap h x)"
proof -
  have "Rep_heaps h x \<noteq> None"
    using assms h_dom_def by fastforce
  then show ?thesis
    by (metis add_to_heap_def assms commutative_union_disjoint_heaps disjoint_add_remove_element 
        get_from_heap_def not_None_eq restricted_heap_def union_add_remove_element)
qed

lemma disjoint_remove_from_heap_restricted_heap:
  fixes h::"('addr, 'k) heaps"
    and x::'addr
  assumes "x \<in> h_dom h"
  shows "disjoint_heaps (remove_from_heap h x) (restricted_heap h x)"
  by (metis add_to_heap_def assms disjoint_add_remove_element disjoint_heaps_def empty_iff 
      h_dom_empty_heap h_dom_remove_not_contained_element inf_bot_right inf_commute not_Some_eq 
      remove_from_heap_def restricted_heap_def)

lemma empty_heap_h_empty:
  "empty_heap h_empty"
  using empty_heap_def h_dom_def h_dom_empty_heap by fastforce

lemma card_empty_heap:
  "card_heap h_empty = 0"
proof -
  have "card (h_dom h_empty) = 0"
    by (simp add: h_dom_empty_heap)
  thus "card_heap h_empty = 0"
    by (simp add: card_heap_def zero_enat_def)
qed

lemma card_remove_from_heap:
  fixes h::"('addr, 'k) heaps"
    and x::'addr
  assumes "x \<in> h_dom h"
    and "card_heap h \<ge> Suc n"
  shows "card_heap (remove_from_heap h x) \<ge> n"
proof -
  have "x \<in> h_dom h"
    by (simp add: assms)
  have "x \<notin> h_dom (remove_from_heap h x)"
    by (simp add: assms h_dom_remove_contained_element)
  hence "card (h_dom (remove_from_heap h x)) \<ge> n"
    by (metis (no_types, lifting) assms(1) assms(2) card.insert card_heap_def card_infinite 
        enat_ord_simps(1) finite_insert h_dom_remove_contained_element insert_Diff less_Suc_eq_le 
        not_le zero_less_Suc)
  thus "card_heap (remove_from_heap h x) \<ge> n"
    by (simp add: card_heap_def one_enat_def)
qed


subsubsection \<open>Heap Restriction\<close>

lemma dom_restricted_heap:
  fixes h::"('addr, 'k) heaps"
    and x::'addr
  assumes "x \<in> h_dom h"
  shows "h_dom (restricted_heap h x) = {x}"
  by (metis Un_insert_right add_to_heap_def assms domIff dom_def empty_iff get_from_heap_def 
      h_dom_add_not_contained_element h_dom_def h_dom_empty_heap not_Some_eq restricted_heap_def 
      sup_bot.right_neutral)

lemma restricted_heap_not_empty:
  fixes h::"('addr, 'k) heaps"
    and x::'addr
  assumes "x \<in> h_dom h"
  shows "\<not>(empty_heap (restricted_heap h x))"
  proof -
  have "Rep_heaps (restricted_heap h x) \<noteq> Map.empty"
    by (metis (no_types) Rep_heaps_inverse assms dom_restricted_heap empty_not_insert 
        h_dom_empty_heap h_empty_def)
    then show ?thesis
      by (simp add: empty_heap_def)
qed


subsubsection \<open>Heap Cast\<close>

lemma to_heap_domain:
  assumes "finite (dom h)"
  shows "h_dom (to_heap h) = dom h" unfolding h_dom_def dom_def to_heap_def using assms
  by (simp add: Abs_heaps_inverse a_heap_def dom_def)


subsubsection \<open>Store Applied on a Vector\<close>

lemma equality_store_vector:
  assumes "(store_vector s y1) = (store_vector s y2)"
  shows "\<forall>i. s (y1 $ i) = s (y2 $ i)"
proof
  have "addr_from_var_vector s y2 = addr_from_var_vector s y2"
    by simp
  fix i
  have "s (vec_nth y1 i) = s (vec_nth y2 i)"
    by (metis UNIV_I addr_from_var_vector_def assms store_vector_def vec_lambda_inverse)
  thus "s (y1 $ i) = s (y2 $ i)"
    by simp
qed


subsubsection \<open>Store Applied on a Set\<close>

lemma antecedent_store_set:
  fixes I::"('var, 'addr, 'k) interp"
    and X::"'var set"
    and l::"'addr"
  assumes "l \<in> (store_set (store I) X)"
  shows "\<exists>x. l = store I x \<and> x \<in> X"
proof -
  have "l \<in> {store I x |x. x \<in> X}"
    using assms store_set_def by force
  then show ?thesis
    by blast
qed


end
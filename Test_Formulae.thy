(*  Title:      Separation-Logic-Formalization/Test_Formulae.thy
    Author:     Nicolas Amat, Mnacho Echenim, Nicolas Peltier
*)

section {* Test Formulae *}

text {* This section contains the test formulas and literals. *}

theory Test_Formulae
imports
  Formula
  Formula_Relation
  "HOL-Library.Extended_Nat"
begin


subsection {* Points-to Relations in the Heap *}

definition points_to :: "'var \<Rightarrow> ('var, 'k) vec \<Rightarrow> ('var, 'k::finite) sl_formula"
  where "points_to x y =  sl_conj (sl_mapsto x y) sl_true"


subsection {* Allocation *}

definition alloc :: "'var \<Rightarrow> ('var, 'k::finite) sl_formula"
  where "alloc x = sl_magic_wand (sl_mapsto x (vec x)) sl_false"


subsection {* Cardinality Constraint *}

fun card_heap_ge :: "nat \<Rightarrow> ('var, 'k::finite) sl_formula"
  where   
      "card_heap_ge (Suc n) = sl_conj (card_heap_ge n) (sl_not sl_emp)"
    | "card_heap_ge 0 = sl_true"

fun ext_card_heap_ge ::  "enat \<Rightarrow> ('var, 'k::finite) sl_formula"
  where
      "ext_card_heap_ge \<infinity> = sl_false"
    | "ext_card_heap_ge n = card_heap_ge n"


subsection {* Test Formulae Set *}

inductive_set test_formulae :: "('var, 'k::finite) sl_formula set"
  where
    "(points_to x y) \<in> test_formulae"
  | "(alloc x) \<in> test_formulae"
  | "(ext_card_heap_ge n) \<in> test_formulae"
  | "(sl_eq x y) \<in> test_formulae"


subsection {* Proposition 1 *}

subsubsection {* Proposition 1 Part 1 *}

lemma tf_prop_1_1:
  fixes I::"('var, 'addr, 'k::finite) interp"
    and x::"'var"
    and y::"('var, 'k) vec"
  shows "(evaluation I (points_to x y)) 
       = (store_and_heap I x = Some (store_vector (store I) y))"
proof
  assume "evaluation I (points_to x y)"
  hence "evaluation I (sl_conj (sl_mapsto x y) sl_true)"
    by (simp add: points_to_def)
  from this obtain h1 h2 where def_0: "(union_heaps h1 h2 = heap I) 
                                     \<and> (disjoint_heaps h1 h2) 
                                     \<and> (evaluation (to_interp (store I) h1) (sl_mapsto x y))
                                     \<and> (evaluation (to_interp (store I) h2) (sl_true))"
    using evaluation.simps(9) by blast
  hence "(store I x \<in> h_dom h1) \<and> (h_dom h1 \<subseteq> h_dom (heap I))"
    by (metis evaluation.simps(8) heap_on_to_interp singletonI store_on_to_interp sub_heap_included)
  hence "store_and_heap I x = store_and_heap (to_interp (store I) h1) x"
    by (metis (no_types, lifting) Abs_heaps_inverse Rep_heaps a_heap_def 
        commutative_union_disjoint_heaps def_0 dom_map_add evaluation.simps(8) 
        finite_Un heap_on_to_interp map_add_find_right mem_Collect_eq store_on_to_interp 
        store_and_heap_with_Rep_heaps union_heaps_def)
  thus "(store_and_heap I x = Some (store_vector (store I) y))"
    by (metis def_0 evaluation.simps(8) store_on_to_interp)
next
  assume asm: "(store_and_heap I x = Some (store_vector (store I) y))"
  define h1 where "h1 = h_singleton (store I x) (store_vector (store I) y)"
  define h2 where "h2 = remove_from_heap (heap I) (store I x)"
  have dijsoint_heaps_from_h:"(union_heaps h1 h2 = heap I) \<and> (disjoint_heaps h1 h2)"
    unfolding h1_def h2_def
    by (metis asm disjoint_add_remove_element dom_store_and_heap h_singleton_add_to_heap 
        store_and_heap_def union_add_remove_element)
  hence "evaluation (to_interp (store I) h1) (sl_mapsto x y)" unfolding h1_def
    by (simp add: get_from_add_to_heap h_dom_add_not_contained_element h_dom_empty_heap 
                  heap_on_to_interp store_and_heap_h store_on_to_interp h_singleton_add_to_heap)
  moreover have "evaluation (to_interp (store I) h2) (sl_true)"
    by simp
  ultimately show "evaluation I (points_to x y)"
    by (metis evaluation.simps(9) points_to_def dijsoint_heaps_from_h)
qed


subsubsection {* Proposition 1 Part 2 *}

lemma tf_prop_1_2:
  fixes I::"('var, 'addr, 'k::finite) interp"
    and x::"'var"
  shows "(evaluation I (alloc x)) 
       = ((store I) x \<in> (h_dom (heap I)))"
proof
  assume "evaluation I (alloc x)"
  thus "(store I) x \<in> (h_dom (heap I))"
proof (rule rev_notE)
    let ?P = "evaluation I (alloc x)"
    assume asm: "(store I) x \<notin> (h_dom (heap I))"
    define h_L::"('addr, 'k) heaps" where "h_L = add_to_heap h_empty (store I x) (store_vector (store I) (vec x))"
    have dom_h_L: "h_dom h_L = {(store I) x}"
      by (simp add: h_L_def h_dom_add_not_contained_element h_dom_empty_heap)
    moreover have "store_and_heap (to_interp (store I) h_L) x = Some (store_vector (store I) (vec x))"
      by (simp add: get_from_add_to_heap h_L_def store_and_heap_h)
    ultimately have evl_mapsto: "evaluation (to_interp (store I) h_L) (sl_mapsto x (vec x))"
      by (simp add: heap_on_to_interp store_on_to_interp)
    have "disjoint_heaps (heap I) h_L"
      by (simp add: asm disjoint_heaps_def dom_h_L)
    have "evaluation (to_interp (store I) h_L) (sl_mapsto x (vec x))"
      using evl_mapsto by blast
    define h1 where "h1 = union_heaps (heap I) h_L"
    have "\<not>(evaluation (to_interp (store I) h1) sl_false)"
      by simp
    thus "\<not>(evaluation I (alloc x))" unfolding alloc_def
      using evl_mapsto asm disjoint_heaps_def dom_h_L by fastforce
  qed
next
  assume "(store I) x \<in> (h_dom (heap I))"
  thus "evaluation I (alloc x)"
    by (simp add: alloc_def disjoint_heaps_def heap_on_to_interp store_on_to_interp)
qed


subsubsection {* Proposition 1 Part 3 *}

lemma tf_prop_1_3:
  fixes I::"('var, 'addr, 'k::finite) interp"
    and n::enat
  shows "(evaluation I (ext_card_heap_ge n))
       = (card_heap (heap I) \<ge> n)"
proof
  assume "evaluation I (ext_card_heap_ge n)"
  thus "card_heap (heap I) \<ge> n"
  proof (induct n arbitrary: I)
    case (enat nat)
    then show ?case
    proof (induct nat arbitrary: I)
      case 0
      then show ?case
        using zero_enat_def by auto 
    next
      case (Suc nat)
      have "evaluation I (sl_conj (card_heap_ge nat) (sl_not sl_emp))"
        using Suc.prems by auto 
      from this obtain h1 h2 
        where def_0: "(disjoint_heaps h1 h2)
                    \<and> (union_heaps h1 h2 = heap I)
                    \<and> (evaluation (to_interp (store I) h1) (card_heap_ge nat))
                    \<and> (evaluation (to_interp (store I) h2) (sl_not sl_emp))"
        using evaluation.simps(9) by blast
      hence "evaluation (to_interp (store I) h1) (ext_card_heap_ge nat)"
        by simp
      hence "card_heap h1 \<ge> nat"
        by (metis Suc.hyps heap_on_to_interp) 
      moreover have "card_heap h2 \<ge> 1" 
        using def_0 by (simp add: card_not_empty_heap heap_on_to_interp)  
      ultimately have "card_heap (union_heaps h1 h2) \<ge> (Suc nat)" using def_0
        by (metis add.commute card_union_disjoint_heaps of_nat_Suc of_nat_eq_enat)
      then show ?case
        by (simp add: def_0)
    qed
  next
    case infinity
    then show ?case
      by simp
  qed
next
  assume "card_heap (heap I) \<ge> n"
  thus "evaluation I (ext_card_heap_ge n)"
  proof (induction n arbitrary : I)
    case (enat nat)
    then show ?case
    proof (induction nat arbitrary : I)
      case 0
      then show ?case
        by simp 
    next
      case (Suc nat)
      have "h_dom (heap I) \<noteq> {}"
        by (metis Suc.prems card_empty card_heap_def enat_0_iff(1) ile0_eq old.nat.distinct(2))
      from this obtain l where l_def: "l \<in> h_dom (heap I)"
        by blast
      define h1::"('addr, 'k) heaps" where "h1 = remove_from_heap (heap I) l"
      define h2::"('addr, 'k) heaps" where "h2 = restricted_heap (heap I) l"
      have h_res: "heap I = (union_heaps h1 h2) \<and> (disjoint_heaps h1 h2)" unfolding h1_def h2_def
        by (simp add: disjoint_remove_from_heap_restricted_heap l_def 
            union_remove_from_heap_restricted_heap)
      hence "card_heap h1 \<ge> nat" unfolding h1_def using Suc.prems l_def
        by (simp add: card_remove_from_heap)
      hence h1_res:"evaluation (to_interp (store I) h1) (ext_card_heap_ge nat)"
        by (metis Suc.IH heap_on_to_interp)
      have "\<not>(empty_heap h2)" unfolding h2_def
        by (simp add: l_def restricted_heap_not_empty)
      hence h2_res:"evaluation (to_interp (store I) h2) (sl_not sl_emp)"
        by (simp add: heap_on_to_interp)
      from h_res and h1_res and h2_res show ?case
        by auto
    qed
  next
    case infinity
    then show ?case
      by (simp add: card_heap_def)   
  qed
qed


subsection {* Literals Definition *}

typedef ('var, 'k::finite) literal 
  = "{f::('var, 'k) sl_formula. f \<in> test_formulae} \<union> {(sl_not f)|f. f \<in> test_formulae}"
  using test_formulae.intros(1) by fastforce


subsection {* Literal Casts *}

definition to_sl_formula :: "('var, 'k::finite) literal \<Rightarrow> ('var, 'k) sl_formula"
  where "to_sl_formula f = Rep_literal f"

definition to_literal :: "('var, 'k::finite) sl_formula \<Rightarrow> ('var, 'k) literal"
  where "to_literal f = Abs_literal f"

definition to_literal_set :: "('var, 'k::finite) sl_formula set \<Rightarrow> ('var, 'k) literal set"
  where "to_literal_set S = {to_literal x|x. True}"


subsection {* Literal Atom *}

fun remove_first_not :: "('var, 'k::finite) sl_formula \<Rightarrow> ('var ,'k) sl_formula"
  where "remove_first_not (sl_not l) = l"
      | "remove_first_not l = l"

definition to_atom :: "('var, 'k::finite) literal \<Rightarrow> ('var ,'k) sl_formula"
  where "to_atom l = remove_first_not (to_sl_formula l)"


subsection {* Literal Complement *}

definition literal_complement :: "('var, 'k::finite) literal \<Rightarrow> ('var, 'k) literal"
  where "literal_complement l = to_literal (sl_formula_complement (to_sl_formula l))"


subsection {* Literal Var Set *}

definition literal_var_set :: "('var, 'k::finite) literal \<Rightarrow> 'var set"
  where "literal_var_set l =  var_set (to_sl_formula l)"


subsection {* Literals Evaluation *}

definition literal_evl :: "('var , 'addr, 'k::finite) interp \<Rightarrow> ('var, 'k) literal \<Rightarrow> bool"
  where "literal_evl I l = evaluation I (to_sl_formula l)"

definition literal_set_evl :: "('var , 'addr, 'k::finite) interp \<Rightarrow> ('var, 'k) literal set \<Rightarrow> bool"
  where "literal_set_evl I S = (\<forall>l\<in>S. literal_evl I l)"


subsection {* Literal Footprint *}

definition av :: "('var, 'k::finite) literal set \<Rightarrow> 'var set"
  where "av T = {x1 | x1 x2. (to_literal (sl_eq x1 x2) \<in> T)
                           \<and> (T \<inter> ({to_literal (alloc x2)} \<union> {to_literal (points_to x2 y) | y. True})) \<noteq> {}}"

definition nv :: "('var, 'k::finite) literal set \<Rightarrow> 'var set"
  where "nv T = {x1 | x1 x2. (to_literal (sl_eq x1 x2) \<in> T)
                           \<and> (to_literal (sl_not (alloc x2))) \<in> T}"

definition fp :: "'var set \<Rightarrow> ('var, 'k::finite) literal set \<Rightarrow> ('var, 'k) literal set"
  where "fp X T = T \<inter> ({to_literal (alloc x) | x. x \<in> X}
                     \<union> {to_literal (sl_not (alloc x)) | x. x \<in> X}
                     \<union> {to_literal (points_to x y) | x y. x \<in> X}
                     \<union> {to_literal (sl_not (points_to x y)) | x y. x \<in> X})"


subsection {* Useful Results *}

subsubsection {* Cardinality Constraint *}

lemma heap_card_domain_card:
  fixes A::"'addr set"
  assumes "finite A" and "n \<le> card A"
  shows "{I::('var, 'addr, 'k::finite) interp. evaluation I (ext_card_heap_ge (enat n))} \<noteq> {}"
proof -
  define hfct::"'addr \<Rightarrow> (('addr, 'k) vec) option" where "hfct = (\<lambda> a. (if a\<in> A then (Some (vec a)) else None))"
  have "dom hfct = A" unfolding hfct_def dom_def by simp
  define mheap where "mheap = to_heap hfct"
  have "h_dom mheap = A" using assms to_heap_domain \<open>dom hfct = A\<close> by (metis mheap_def)
  define addr::'addr where "addr = (SOME x. x\<in> UNIV)"
  define store::"('var\<Rightarrow>'addr)" where "store = (\<lambda>x. addr)"
  define I where "I = to_interp store mheap"
  have "evaluation I (ext_card_heap_ge (enat n))" 
  proof (rule tf_prop_1_3[THEN iffD2])
    have "card_heap (heap I) = card (h_dom mheap)" unfolding card_heap_def unfolding I_def
      by (simp add: heap_def to_interp_def)
    also have "... = card A" using \<open>h_dom mheap = A\<close> by simp
    also have "... \<ge>  n" using assms by simp
    finally have "card_heap (heap I) \<ge>  n" .
    thus "enat n \<le> card_heap (heap I)" by simp
  qed
  thus ?thesis by blast
qed

lemma heap_card_infinite_universe:
  assumes "\<not>finite (UNIV::'addr set)"
  shows "{I::('var, 'addr, 'k::finite) interp. evaluation I (ext_card_heap_ge (enat n))} \<noteq> {}"
proof -
  have "\<exists> A::'addr set. finite A\<and> card A = n" using assms
    using infinite_arbitrarily_large by blast
  from this obtain A::"'addr set" where "finite A" and "card A = n" by auto
  thus ?thesis using heap_card_domain_card[of A n] by simp
qed

lemma not_heap_card:
  assumes "Suc 0 \<le> n"
  shows "{I::('var, 'addr, 'k::finite) interp. evaluation I (sl_not (ext_card_heap_ge (enat n)))} \<noteq> {}"
proof -
  define addr::'addr where "addr = (SOME x. x\<in> UNIV)"
  define store::"('var\<Rightarrow>'addr)" where "store = (\<lambda>x. addr)"
  define I::"('var, 'addr, 'k::finite) interp" where "I = to_interp store h_empty"
  have "card_heap (heap I) = card (h_dom h_empty)" unfolding card_heap_def unfolding I_def
    by (simp add: h_dom_empty_heap heap_def to_interp_def)
  also have "card (h_dom h_empty) = 0" by (simp add: h_dom_empty_heap) 
  finally have "card_heap (heap I) = 0" by (simp add: zero_enat_def)
  hence "\<not> evaluation I (ext_card_heap_ge (enat n))" using tf_prop_1_3 assms
    by (metis enat_ord_simps(1) not_less_eq_eq zero_enat_def)
  hence "evaluation I (sl_not (ext_card_heap_ge (enat n)))" by simp
  thus ?thesis by blast
qed

lemma card_heap_bounded:
  assumes "evaluation I (ext_card_heap_ge n1)"
    and "evaluation I (sl_not (ext_card_heap_ge n2))"
  shows "n1 < n2"
proof -
  have "evaluation I (ext_card_heap_ge n1)"
    by (simp add: assms(1))
  moreover have "\<not>(evaluation I (ext_card_heap_ge n2))"
    using assms(2) by auto
  ultimately show "n1 < n2"
    by (simp add: tf_prop_1_3)
qed


subsubsection {* Test Formulae Set *}

lemma test_formulae_charact:
  "test_formulae = {(sl_eq x y)|x y. True} 
                 \<union> {(alloc x)|x. True}
                 \<union> {(points_to x y)|x y. True} 
                 \<union> {ext_card_heap_ge n|n. True}"
proof
  show "test_formulae \<subseteq> {sl_eq x y |x y. True} \<union> {alloc x |x. True} \<union> {points_to x y |x y. True} \<union> {ext_card_heap_ge n |n. True}"
    by (simp add: subset_iff test_formulae.simps)
next
  show "{sl_eq x y |x y. True} \<union> {alloc x |x. True} \<union> {points_to x y |x y. True} \<union> {ext_card_heap_ge n |n. True} \<subseteq> test_formulae"
    using test_formulae.simps by fastforce
qed


subsubsection {* Literal Casts *}

lemma pos_literal_inv[simp]:
  fixes f::"('var, 'k::finite) sl_formula"
  assumes "f\<in> test_formulae"
  shows "(to_sl_formula (to_literal f)) = f"
by (simp add: Abs_literal_inverse assms to_literal_def to_sl_formula_def)

lemma neg_literal_inv[simp]:
  fixes f::"('var, 'k::finite) sl_formula"
  assumes "f \<in> test_formulae"
  shows "(to_sl_formula (to_literal (sl_not f))) = sl_not f"
by (simp add: Abs_literal_inverse assms to_literal_def to_sl_formula_def)


subsubsection {* Literal Atom *}

lemma literal_atom_cases_tmp:
  "(to_literal (to_atom l) = l) \<or> to_literal (sl_not (to_atom l)) = l"
  by (metis Rep_literal_inverse remove_first_not.simps(1) remove_first_not.simps(10) 
      remove_first_not.simps(2) remove_first_not.simps(3) remove_first_not.simps(4) 
      remove_first_not.simps(5) remove_first_not.simps(6) remove_first_not.simps(7) 
      remove_first_not.simps(8) remove_first_not.simps(9) sl_formula.exhaust 
      to_atom_def to_literal_def to_sl_formula_def)

lemma literal_atom_cases:
  obtains l where "l = to_literal (to_atom l)" | "l = to_literal (sl_not (to_atom l))" 
proof (cases "l = to_literal (to_atom l)")
  case True
  thus ?thesis 
  proof -
  have f1: "\<And>s. (s::('a, 'b) sl_formula) \<notin> Collect (sup (\<lambda>s. s \<in> {s. s \<in> test_formulae}) (\<lambda>s. s \<in> {sl_not s |s. s \<in> test_formulae})) \<or> Rep_literal (Abs_literal s) = s"
  using Abs_literal_inverse by blast
    have "(sl_false::('a, 'b) sl_formula) \<in> test_formulae"
      by (metis (no_types) ext_card_heap_ge.simps(1) test_formulae.intros(3))
    then have "(sl_false::('a, 'b) sl_formula) \<in> Collect (sup (\<lambda>s. s \<in> {s. s \<in> test_formulae}) (\<lambda>s. s \<in> {sl_not s |s. s \<in> test_formulae}))"
      by blast
    then show ?thesis
      using f1 by (metis (lifting) remove_first_not.simps(3) that(1) to_atom_def to_literal_def to_sl_formula_def)
  qed
next
  case False
  hence "l = to_literal (sl_not (to_atom l))" using literal_atom_cases_tmp[of l] by simp
  thus ?thesis using that(2) by auto 
qed

lemma to_atom_is_test_formula:
  fixes l::"('var, 'k::finite) literal"
  shows "(to_atom l) \<in> test_formulae"
proof (cases "to_sl_formula l \<in> test_formulae")
  case False
  have "\<And>l. (\<exists>s. Rep_literal (l::('var, 'k) literal) = sl_not s \<and> s \<in> test_formulae) \<or> Rep_literal l \<in> test_formulae"
    using Rep_literal by blast
  then show ?thesis
    by (metis (no_types) False remove_first_not.simps(1) to_atom_def to_sl_formula_def)
next
  case True
  have "to_atom l = to_sl_formula l" using True
  proof
    {
      fix x y
      assume "to_sl_formula l = points_to x y"
      show "to_atom l = to_sl_formula l"
        by (simp add: \<open>to_sl_formula l = points_to x y\<close> points_to_def to_atom_def)
    }
    {
      fix x
      assume "to_sl_formula l = alloc x"
      show "to_atom l = to_sl_formula l"
        by (simp add: \<open>to_sl_formula l = alloc x\<close> alloc_def to_atom_def)
    }
    {
      fix n
      assume "to_sl_formula l = (ext_card_heap_ge n::(('var, 'k::finite) sl_formula))"
      show "to_atom l = to_sl_formula l"
      proof (cases "n = \<infinity>")
        case True
        then show ?thesis
          by (simp add: \<open>to_sl_formula l = ext_card_heap_ge n\<close> to_atom_def) 
      next
        case False
        show ?thesis
        proof (cases "n = 0")
          case True
          then show ?thesis
            by (simp add: \<open>to_sl_formula l = ext_card_heap_ge n\<close> to_atom_def zero_enat_def) 
        next
          case False
          then show ?thesis
            by (metis \<open>to_sl_formula l = ext_card_heap_ge n\<close> card_heap_ge.elims 
                ext_card_heap_ge.simps(1) ext_card_heap_ge.simps(2) not_infinity_eq 
                remove_first_not.simps(2) remove_first_not.simps(3) remove_first_not.simps(9) to_atom_def) 
        qed
      qed
    }
    {
      fix x y
      assume "to_sl_formula l = sl_eq x y"
      thus "to_atom l = to_sl_formula l"
        by (simp add: to_atom_def)
    }
  qed
  thus ?thesis using True
    by simp
qed


subsection {* Propostions *}

subsubsection {* Propostion 3 *}

lemma extended_heap_alloc:
  assumes "\<not>(evaluation (to_interp (store I) (union_heaps (heap I) h)) (alloc x))"
  shows "\<not>(evaluation I (alloc x))"
proof -
  have "h_dom (heap I) \<subseteq> h_dom (union_heaps (heap I) h)"
    by (simp add: sub_heap_included)
  thus "\<not>(evaluation I (alloc x))"
    by (metis assms heap_on_to_interp set_mp store_on_to_interp tf_prop_1_2)
qed

lemma union_heaps_associative:
  fixes h1::"('addr, 'k) heaps"
   and h2::"('addr, 'k) heaps"
   and h3::"('addr, 'k) heaps"
 shows "(union_heaps h1 (union_heaps h2 h3)) = (union_heaps (union_heaps h1 h2) h3)"
proof -
  have "\<And>h. finite (dom (Rep_heaps (h::('addr, 'k) heaps)))"
    using Rep_heaps a_heap_def by blast
  then show ?thesis
    by (simp add: Abs_heaps_inverse a_heap_def union_heaps_def)
qed

lemma h_dom_union_heaps:
  "h_dom (union_heaps h1 h2) = h_dom h1 \<union> h_dom h2"
proof
  show "h_dom (union_heaps h1 h2) \<subseteq> h_dom h1 \<union> h_dom h2"
  proof
    fix x
    assume "x \<in> h_dom (union_heaps h1 h2)"
    hence "x \<in> dom ((Rep_heaps h1) ++ (Rep_heaps h2))"
      by (metis CollectD Rep_heaps a_heap_def dom_map_add finite_Un to_heap_def to_heap_domain 
          union_heaps_def)
    hence "x \<in> dom (Rep_heaps h1) \<or> x \<in> dom (Rep_heaps h2)"
      by auto
    hence "x \<in> h_dom h1 \<or> x \<in> h_dom h2"
      by (metis CollectD Rep_heaps Rep_heaps_inverse a_heap_def to_heap_def to_heap_domain)
    hence "x \<in> (h_dom h1 \<union> h_dom h2)"
      by simp
    thus "\<And>x. x \<in> h_dom (union_heaps h1 h2) \<Longrightarrow> x \<in> h_dom h1 \<union> h_dom h2"
      by (metis CollectD Rep_heaps Rep_heaps_inverse Un_commute a_heap_def dom_map_add finite_Un 
          to_heap_def to_heap_domain union_heaps_def)
  qed
next
  show " h_dom h1 \<union> h_dom h2 \<subseteq> h_dom (union_heaps h1 h2)"
  proof
    fix x
    assume "x \<in> h_dom h1 \<union> h_dom h2"
    hence "x \<in> dom (Rep_heaps h1) \<union> dom (Rep_heaps h2)"
      by (metis CollectD Rep_heaps Rep_heaps_inverse a_heap_def to_heap_def to_heap_domain)
    hence "x \<in> dom ((Rep_heaps h1) ++ (Rep_heaps h2))"
      by auto
    hence "x \<in> h_dom (Abs_heaps ((Rep_heaps h1) ++ (Rep_heaps h2)))"
      by (metis CollectD Rep_heaps a_heap_def dom_map_add finite_UnI to_heap_def to_heap_domain)
    hence "x \<in> h_dom (union_heaps h1 h2)"
      by (simp add: union_heaps_def)
    thus "\<And>x. x \<in> h_dom h1 \<union> h_dom h2 \<Longrightarrow> x \<in> h_dom (union_heaps h1 h2)"
      sorry
  qed
qed

lemma h_dom_union_heaps_in_one_h_dom:
  assumes "x \<in> h_dom (union_heaps h1 h2)"
  shows "x \<in> h_dom h1 \<or> x \<in> h_dom h2"
proof (rule ccontr)
  assume asm:"\<not>(x \<in> h_dom h1 \<or> x \<in> h_dom h2)"
  hence "x \<notin> h_dom h1 \<and> x \<notin> h_dom h2"
    by auto
  moreover have "h_dom (union_heaps h1 h2) = h_dom h1 \<union> h_dom h2"
    by (simp add: h_dom_union_heaps)
  ultimately show False
    using assms by blast
qed

lemma disjoint_heaps_union_heaps:
  assumes "disjoint_heaps (union_heaps h1 h2) h3"
    and "disjoint_heaps h1 h2"
  shows "disjoint_heaps h1 (union_heaps h2 h3)"
proof (rule ccontr)
  assume asm:"\<not>(disjoint_heaps h1 (union_heaps h2 h3))"
  obtain x where in_1:"x \<in> h_dom h1"
             and in_2:"x \<in> h_dom (union_heaps h2 h3)"
    by (meson Int_emptyI asm disjoint_heaps_def)
  hence "x \<in> (h_dom h2) \<or> x \<in> (h_dom h3)"
    by (simp add: h_dom_union_heaps_in_one_h_dom)  
  moreover have "x \<in> (h_dom h2) \<longrightarrow> \<not>(disjoint_heaps h1 h2)"
    by (meson disjoint_heaps_def disjoint_iff_not_equal in_1)
  moreover have "x \<in> (h_dom h3) \<longrightarrow> \<not>(disjoint_heaps (union_heaps h1 h2) h3)"
    by (meson contra_subsetD disjoint_heaps_def disjoint_iff_not_equal in_1 sub_heap_included)
  ultimately show False
    using assms(1) assms(2) by blast
qed
  
lemma extended_heap_points_to:
  assumes "\<not>(evaluation (to_interp (store I) (union_heaps (heap I) h)) (points_to x y))"
    and "disjoint_heaps (heap I) h"
  shows "\<not>(evaluation I (points_to x y))"
proof (rule ccontr)
  assume "\<not>(\<not>(evaluation I (points_to x y)))"
  hence "evaluation I (points_to x y)"
    by auto
  from this obtain h1 h2 where def_1:"(union_heaps h1 h2 = heap I)
                                    \<and> (disjoint_heaps h1 h2)
                                    \<and> (evaluation (to_interp (store I) h1) (sl_mapsto x y))
                                    \<and> (evaluation (to_interp (store I) h2) sl_true)"
    by (metis evaluation.simps(9) points_to_def)
  define h3 where "h3 = union_heaps h2 h"
  have union_heaps_h1_h3:"(union_heaps h1 h3) = (union_heaps (heap I) h)"
    by (simp add: def_1 h3_def union_heaps_associative)
  have "disjoint_heaps h1 h3" unfolding h3_def
    by (simp add: assms(2) def_1 disjoint_heaps_union_heaps) 
  hence def_2:"(union_heaps h1 h3 = union_heaps (heap I) h)
       \<and> (disjoint_heaps h1 h3)
       \<and> (evaluation (to_interp (store I) h1) (sl_mapsto x y))
       \<and> (evaluation (to_interp (store I) h3) sl_true)"
    using union_heaps_h1_h3  def_1 evaluation.simps(1) by blast
  have  "evaluation (to_interp (store I) (union_heaps (heap I) h)) (points_to x y)"
    by (metis (no_types, lifting) def_2 evaluation.simps(9) heap_on_to_interp points_to_def store_on_to_interp)
  thus False
    using assms by blast
qed

lemma tf_prop_3:
  fixes T::"('var, 'k::finite) literal set"
    and I::"('var, 'addr, 'k) interp"
  assumes "literal_set_evl I (fp (av T) T)"
  shows "\<forall>h. (disjoint_heaps (heap I) h) \<longrightarrow> literal_set_evl (to_interp (store I) (union_heaps (heap I) h)) (fp (av T) T)"
proof (rule ccontr)
  assume "\<not> (\<forall>h.  (disjoint_heaps (heap I) h) \<longrightarrow> literal_set_evl (to_interp (store I) (union_heaps (heap I) h)) (fp (av T) T))"
  from this obtain h where "\<not>(literal_set_evl (to_interp (store I) (union_heaps (heap I) h)) (fp (av T) T))"
                      and disoint_h:"disjoint_heaps (heap I) h"
    by blast
  from this obtain l where l_in_fp: "l \<in> (fp (av T) T)"
                      and l_evl: "\<not>(literal_evl (to_interp (store I) (union_heaps (heap I) h)) l)"
    using literal_set_evl_def by blast
  have case_1: "\<exists>x. l = to_literal (alloc x) \<longrightarrow> \<not>(literal_evl I l)"
    by (metis extended_heap_alloc l_evl literal_evl_def pos_literal_inv test_formulae.intros(2))
  have case_2: "\<exists>x y. l = to_literal (points_to x y) \<longrightarrow> \<not>(literal_evl I l)"
    by (metis disoint_h extended_heap_points_to l_evl literal_evl_def pos_literal_inv test_formulae.intros(1))
  from case_1 and case_2 have "\<not>(literal_set_evl I (fp (av T) T))"
    sorry
  thus False
    using assms by blast
  oops


end
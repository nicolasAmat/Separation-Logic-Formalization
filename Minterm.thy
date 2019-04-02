(*  Title:      Separation-Logic-Formalization/Minterm.thy
    Author:     Nicolas Amat, Mnacho Echenim, Nicolas Peltier
*)

section {* Minterms *}

text {* This section contains the minterms definition and some propositions related to them. *}

theory Minterm
imports 
  Test_Formulae
begin

subsection {* Minterms Definition *}

typedef ('var, 'k::finite) minterm 
  = "{S. ((\<exists>!l\<in>S::('var, 'k::finite) literal set. \<exists>n. 
          (to_sl_formula l) = (ext_card_heap_ge n))
        \<and> (\<exists>!l\<in>S::('var, 'k::finite) literal set. \<exists>n. 
          (to_sl_formula l) = (not (ext_card_heap_ge n))))}"
proof
  define l1::"('var, 'k::finite) sl_formula" where "l1 = ext_card_heap_ge 0"
  have "l1\<in> test_formulae" unfolding l1_def using test_formulae.simps by auto
  define x::"('var, 'k::finite) literal set"
    where "x = {to_literal l1, to_literal (not l1)}"
  show "x \<in> {S. ((\<exists>!l\<in>S::('var, 'k::finite) literal set. \<exists>n. 
            (to_sl_formula l) = (ext_card_heap_ge n))
          \<and> (\<exists>!l\<in>S::('var, 'k::finite) literal set. \<exists>n. 
            (to_sl_formula l) = (not (ext_card_heap_ge n))))}"
  proof (intro CollectI conjI ex1I)
    show "to_literal l1 \<in> x" by (simp add: l1_def x_def) 
    show "\<exists>n. to_sl_formula (to_literal l1) = ext_card_heap_ge n"
    proof
      show "to_sl_formula (to_literal l1) = ext_card_heap_ge 0" using \<open>l1\<in> test_formulae\<close>
        unfolding l1_def by simp     
    qed
    show "\<And>l. l \<in> x \<and> (\<exists>n. to_sl_formula l = ext_card_heap_ge n) \<Longrightarrow> l = to_literal l1"
    proof -
      fix l
      assume lprop: "l \<in> x \<and> (\<exists>n. to_sl_formula l = ext_card_heap_ge n)"
      hence "\<exists>n. to_sl_formula l = ext_card_heap_ge n" by simp
      from this obtain n where ndef: "to_sl_formula l = ext_card_heap_ge n" by auto
      have "l = to_literal l1 \<or> l = to_literal (not l1)" using lprop unfolding x_def by simp
      moreover have "l\<noteq> to_literal (not l1)"
      proof (rule ccontr)
        assume "\<not> l \<noteq> to_literal (not l1)"
        hence "l = to_literal (not l1)" by simp
        hence "to_sl_formula l = (not l1)" by (simp add: \<open>l1 \<in> test_formulae\<close>)
        hence "((ext_card_heap_ge n)::('var, 'k::finite) sl_formula) = not l1" using ndef by simp
        also have "... = ((not (ext_card_heap_ge 0))::('var, 'k::finite) sl_formula)" using  l1_def by simp
        finally have "((ext_card_heap_ge n)::('var, 'k::finite) sl_formula) = not (ext_card_heap_ge 0)" .
        thus False 
        proof (cases "n = \<infinity>")
          case True
          hence "ext_card_heap_ge n = sl_false" by simp
          thus ?thesis using  sl_formula.distinct
          proof -
            show ?thesis
              by (metis \<open>ext_card_heap_ge (n::enat) = not (ext_card_heap_ge (0::enat))\<close> 
                  \<open>ext_card_heap_ge (n::enat) = sl_false\<close> sl_formula.distinct(22))
          qed
        next
          case False
          show ?thesis
          proof (cases "n = 0")
            case True
            hence "ext_card_heap_ge n = sl_true"
              by (simp add: enat_defs(1)) 
            thus ?thesis
            proof -
              show ?thesis
                by (metis \<open>ext_card_heap_ge n = not l1\<close> \<open>ext_card_heap_ge n = sl_true\<close> sl_formula.distinct(5))
            qed
          next
            case False
            hence "\<exists>m. n = Suc m" using \<open>n\<noteq> \<infinity>\<close> using list_decode.cases zero_enat_def by auto 
            from this obtain m where "n = Suc m" by auto
            hence "ext_card_heap_ge (n::enat) = sl_conj (ext_card_heap_ge (m)) (not sl_emp)"
              by simp
            thus ?thesis
            proof -
              show ?thesis
                by (metis (no_types) \<open>ext_card_heap_ge (n::enat) = 
                  sl_conj (ext_card_heap_ge (enat (m::nat))) (not sl_emp)\<close> 
                    \<open>to_sl_formula (l::('var, 'k) literal) = not (l1::('var, 'k) sl_formula)\<close> ndef 
                    sl_formula.distinct(57))
            qed
          qed
        qed
      qed
      ultimately show "l = to_literal l1" by simp
    qed
    show "to_literal (not l1) \<in> x" by (simp add: l1_def x_def) 
    show "\<exists>n. to_sl_formula (to_literal (not l1)) = not (ext_card_heap_ge n)"
    proof
      show "to_sl_formula (to_literal (not l1)) = not (ext_card_heap_ge 0)" using \<open>l1\<in> test_formulae\<close>
        unfolding l1_def by simp     
    qed
    show "\<And>l. l \<in> x \<and> (\<exists>n. to_sl_formula l = not (ext_card_heap_ge n)) \<Longrightarrow> l = to_literal (not l1)"
    proof -
      fix l
      assume lprop: "l \<in> x \<and> (\<exists>n. to_sl_formula l = not (ext_card_heap_ge n))"
      hence "\<exists>n. to_sl_formula l = not (ext_card_heap_ge n)" by simp
      from this obtain n where ndef: "to_sl_formula l = not (ext_card_heap_ge n)" by auto
      have "l = to_literal l1 \<or> l = to_literal (not l1)" using lprop unfolding x_def by simp
      moreover have "l\<noteq> to_literal (l1)"
      proof (rule ccontr)
        assume "\<not> l \<noteq> to_literal (l1)"
        hence "l = to_literal (l1)" by simp
        hence "to_sl_formula l = (l1)" by (simp add: \<open>l1 \<in> test_formulae\<close>)
        hence "((not (ext_card_heap_ge n))::('var, 'k::finite) sl_formula) = l1" using ndef by simp
        also have "... = (((ext_card_heap_ge 0))::('var, 'k::finite) sl_formula)" using  l1_def by simp
        also have "... = (sl_true::('var, 'k::finite) sl_formula)" by (simp add: enat_defs)
        finally have "((not (ext_card_heap_ge n))::('var, 'k::finite) sl_formula) = (sl_true)" .
        thus False 
        proof (cases "n = \<infinity>")
          case True
          hence "ext_card_heap_ge n = sl_false" by simp
          hence "not (ext_card_heap_ge n) = not sl_false" by simp
          thus ?thesis using  sl_formula.distinct \<open>not (ext_card_heap_ge n) = sl_true\<close> by simp
        next
          case False
          show ?thesis
          proof (cases "n = 0")
            case True
            hence "ext_card_heap_ge n = sl_true"
              by (simp add: enat_defs(1)) 
            hence "not (ext_card_heap_ge n) = not sl_true" by simp
            thus ?thesis using sl_formula.distinct \<open>not (ext_card_heap_ge n) = sl_true\<close> by simp
          next
            case False
            hence "\<exists>m. n = Suc m" using \<open>n\<noteq> \<infinity>\<close> using list_decode.cases zero_enat_def by auto 
            from this obtain m where "n = Suc m" by auto
            hence "ext_card_heap_ge (n::enat) = sl_conj (ext_card_heap_ge (m)) (not sl_emp)"
              by simp
            hence "not (ext_card_heap_ge n) = not (sl_conj (ext_card_heap_ge (m)) (not sl_emp))" by simp
            thus ?thesis using sl_formula.distinct \<open>not (ext_card_heap_ge n) = sl_true\<close> by simp
          qed
        qed
      qed
      ultimately show "l = to_literal (not l1)" by simp
    qed
  qed
qed


subsection {* Minterms Functions *}

definition minterm_to_literal_set :: "('var, 'k::finite) minterm \<Rightarrow> ('var, 'k) literal set"
  where "minterm_to_literal_set M = Rep_minterm M"

definition minterm_to_sl_formula_set ::  "('var, 'k::finite) minterm \<Rightarrow> ('var, 'k) sl_formula set"
  where "minterm_to_sl_formula_set M =  {(to_sl_formula l)|l. l \<in> (minterm_to_literal_set M)}"

lemma minterm_to_literal_set_composed_by_test_formula:
  "\<forall>l \<in> (minterm_to_literal_set M). (to_sl_formula (l::(('var, 'k::finite) literal)) \<in> test_formulae) \<or> (\<exists>l_prim. (l_prim \<in> test_formulae))"
  oops

subsection {* Minterms Lemmas *}

lemma minterm_have_ext_card_heap_ge:
  "\<exists>l\<in>(minterm_to_literal_set M). \<exists>n. ((to_sl_formula l) = (ext_card_heap_ge n))"
  using Rep_minterm minterm_to_literal_set_def by fastforce

lemma minterm_have_not_ext_card_heap_ge:
  "\<exists>l\<in>(minterm_to_literal_set M). \<exists>n. ((to_sl_formula l) = (not (ext_card_heap_ge n)))"
  using Rep_minterm minterm_to_literal_set_def by fastforce


subsection {* Some Sets Definitions *}

subsubsection {* Intersections Sets *}

definition e_literals :: "('var, 'k::finite) literal set"
  where "e_literals = {to_literal (eq x y)|x y. True} 
                    \<union> {to_literal (not (eq x y))|x y. True}"

definition a_literals :: "('var, 'k::finite) literal set"
  where "a_literals = {to_literal (alloc x)|x. True} 
                    \<union> {to_literal (not (alloc x))|x. True}"

definition p_literals :: "('var, 'k::finite) literal set"
  where "p_literals = {to_literal (points_to x y)|x y. True} 
                    \<union> {to_literal (not (points_to x y))|x y. True}"

subsubsection {* Minterms Sets Composed by an Intersection *}

definition e_minterm :: "('var, 'k::finite) minterm \<Rightarrow> ('var, 'k) literal set"
  where "e_minterm M = minterm_to_literal_set M \<inter> e_literals"

definition a_minterm :: "('var, 'k::finite) minterm \<Rightarrow> ('var, 'k) literal set"
  where "a_minterm M = minterm_to_literal_set M \<inter> a_literals"

definition p_minterm :: "('var, 'k::finite) minterm \<Rightarrow> ('var, 'k) literal set"
  where "p_minterm M = minterm_to_literal_set M \<inter> p_literals"


subsection {* Minterms Evaluation *}

definition minterm_evl :: "('var, 'addr, 'k::finite) interp \<Rightarrow> ('var, 'k) minterm \<Rightarrow> bool"
  where "minterm_evl I M = literal_set_evl I (minterm_to_literal_set M)"


subsection {* Minterms Sets Equality *}

lemma test_formulae_charact:
  "test_formulae = {(eq x y)|x y. True} 
                 \<union> {(alloc x)|x. True}
                 \<union> {(points_to x y)|x y. True} 
                 \<union> {ext_card_heap_ge n|n. True}"
proof
  show "test_formulae \<subseteq> {eq x y |x y. True} \<union> {alloc x |x. True} \<union> {points_to x y |x y. True} \<union> {ext_card_heap_ge n |n. True}"
    by (simp add: subset_iff test_formulae.simps)
next
  show "{eq x y |x y. True} \<union> {alloc x |x. True} \<union> {points_to x y |x y. True} \<union> {ext_card_heap_ge n |n. True} \<subseteq> test_formulae"
    using test_formulae.simps by fastforce
qed

lemma to_atom_minterms_sets:
  fixes M::"('var , 'k::finite) literal set"
  assumes "\<And>l::(('var, 'k) literal). (l \<in> M) \<Longrightarrow> (to_sl_formula l) \<in> test_formulae \<Longrightarrow> to_literal (not (to_sl_formula l)) \<in> M"
    and "to_literal (to_atom l) \<in> M"  
  shows "l \<in> M"
  by (metis assms(1) assms(2) literal_atom_cases pos_literal_inv to_atom_is_test_formula)

lemma from_to_atom_in_e_minterm:
  fixes M::"('var , 'k::finite) minterm"
  assumes "\<And>l::(('var, 'k) literal). (l \<in> (e_minterm M)) \<Longrightarrow> (to_sl_formula l) \<in> test_formulae \<Longrightarrow> to_literal (not (to_sl_formula l)) \<in> (e_minterm M)"
    and "to_literal (to_atom l) \<in> (e_minterm M)"
  shows "l \<in> (e_minterm M)"
  using assms(1) assms(2) to_atom_minterms_sets by auto

lemma from_to_atom_in_a_minterm:
  fixes M::"('var , 'k::finite) minterm"
  assumes "\<And>l::(('var, 'k) literal). (l \<in> (a_minterm M)) \<Longrightarrow> (to_sl_formula l) \<in> test_formulae \<Longrightarrow> to_literal (not (to_sl_formula l)) \<in> (a_minterm M)"
    and "to_literal (to_atom l) \<in> (a_minterm M)"
  shows "l \<in> (a_minterm M)"
  using assms(1) assms(2) to_atom_minterms_sets by auto

lemma from_to_atom_in_p_minterm:
  fixes M::"('var , 'k::finite) minterm"
  assumes "\<And>l::(('var, 'k) literal). (l \<in> (p_minterm M)) \<Longrightarrow> (to_sl_formula l) \<in> test_formulae \<Longrightarrow> to_literal (not (to_sl_formula l)) \<in> (p_minterm M)"
    and "to_literal (to_atom l) \<in> (p_minterm M)"
  shows "l \<in> (p_minterm M)"
  using assms(1) assms(2) to_atom_minterms_sets by auto

lemma minterms_sets_equality:
  fixes M::"('var, 'k::finite) minterm"
  shows  "minterm_to_literal_set M = e_minterm M \<union> a_minterm M \<union> p_minterm M \<union> 
   {l \<in> (minterm_to_literal_set M). (\<exists>n. (to_sl_formula l) = (ext_card_heap_ge n)) \<or> (\<exists>n. (to_sl_formula l) = (not (ext_card_heap_ge n)))}"
proof
  define min_set::"('var, 'k::finite) literal set" 
    where "min_set = e_minterm M \<union> a_minterm M \<union> p_minterm M \<union> 
   {l \<in> (minterm_to_literal_set M). (\<exists>n. (to_sl_formula l) = (ext_card_heap_ge n)) \<or> (\<exists>n. (to_sl_formula l) = (not (ext_card_heap_ge n)))}"
  show "minterm_to_literal_set M \<subseteq> min_set"
  proof
    fix l
    assume asm:"l \<in> (minterm_to_literal_set M)"
    from this obtain l_1 where "l_1 = to_atom l" and "l_1 \<in> test_formulae"
      by (simp add: to_atom_is_test_formula)
    hence "l_1 \<in> {eq x y |x y. True} \<union> {alloc x |x. True} \<union> {points_to x y |x y. True} \<union> {ext_card_heap_ge n |n. True}" using test_formulae_charact
      by blast
    hence "l \<in> e_literals \<union> a_literals \<union> p_literals \<union>  {l \<in> (minterm_to_literal_set M). (\<exists>n. (to_sl_formula l) = (ext_card_heap_ge n)) \<or> (\<exists>n. (to_sl_formula l) = (not (ext_card_heap_ge n)))}"
      using to_atom_minterms_sets
      oops
      hence "l \<in> min_set" unfolding min_set_def using to_atom_minterms_sets e_minterm_def a_minterm_def p_minterm_def
      sorry

(*
next
  show "e_minterm M \<union> a_minterm M \<union> p_minterm M \<union>
        {l \<in> minterm_to_literal_set M. (\<exists>n. to_sl_formula l = ext_card_heap_ge n) \<or> (\<exists>n. to_sl_formula l = not (ext_card_heap_ge n))}
        \<subseteq> minterm_to_literal_set M"
    by (simp add: a_minterm_def e_minterm_def p_minterm_def subset_iff)
qed
*)
      oops

subsection {* Minterms Propositions *}

subsubsection {* Proposition 5 *}

lemma minterm_prop_5:
  fixes I_1::"('var, 'addr, 'k::finite) interp"
    and I_2::"('var, 'addr, 'k::finite) interp"
    and M::"('var, 'k) minterm"
  assumes "store I_1 = store I_2"
  shows "literal_set_evl I_1 (e_minterm M)
     \<Longrightarrow> literal_set_evl I_2 (e_minterm M)"
proof -
  assume asm: "literal_set_evl I_1 (e_minterm M)"
  show "literal_set_evl I_2 (e_minterm M)" unfolding literal_set_evl_def
  proof (intro ballI)
    fix l
    assume asm_l: "l \<in> (e_minterm M)"
    hence l_evl: "literal_evl I_1 l"
      using asm literal_set_evl_def by blast
    hence "l \<in> e_literals"
      using asm_l e_minterm_def by auto 
    hence "\<exists>x y. l = to_literal (eq x y) \<or> l = to_literal (not (eq x y))"
      using asm_l e_literals_def by force
    thus "literal_evl I_2 l"
      by (metis assms evaluation.simps(3) evaluation.simps(4) l_evl literal_evl_def neg_literal_inv 
          pos_literal_inv test_formulae.intros(4))
  qed
qed
  

end
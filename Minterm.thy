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
          (to_sl_formula l) = (not (ext_card_heap_ge n)))
        \<and> finite S)}"
proof
  define l1::"('var, 'k::finite) sl_formula" where "l1 = ext_card_heap_ge 0"
  have "l1\<in> test_formulae" unfolding l1_def using test_formulae.simps by auto
  define x::"('var, 'k::finite) literal set"
    where "x = {to_literal l1, to_literal (not l1)}"
  show "x \<in> {S. ((\<exists>!l\<in>S::('var, 'k::finite) literal set. \<exists>n. 
            (to_sl_formula l) = (ext_card_heap_ge n))
          \<and> (\<exists>!l\<in>S::('var, 'k::finite) literal set. \<exists>n. 
            (to_sl_formula l) = (not (ext_card_heap_ge n)))
          \<and> finite S)}"
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
  next
    show "finite x"
      by (simp add: x_def)
  qed
qed


subsection {* Minterms Functions *}

definition to_literal_set :: "('var, 'k::finite) minterm \<Rightarrow> ('var, 'k) literal set"
  where "to_literal_set M = Rep_minterm M"

definition to_minterm :: "('var, 'k::finite) literal set \<Rightarrow> ('var, 'k) minterm"
  where "to_minterm S = Abs_minterm S"

definition to_sl_formula_set ::  "('var, 'k::finite) minterm \<Rightarrow> ('var, 'k) sl_formula set"
  where "to_sl_formula_set M =  {(to_sl_formula l)|l. l \<in> (to_literal_set M)}"

lemma to_literal_set_composed_by_test_formula:
  "\<forall>l \<in> (to_literal_set M). 
    (to_sl_formula (l::(('var, 'k::finite) literal)) \<in> test_formulae) 
  \<or> (\<exists>l_prim. (l = to_literal (not l_prim)) \<and> (l_prim \<in> test_formulae))"
  by (metis literal_atom_cases_tmp pos_literal_inv to_atom_is_test_formula)


subsection {* Minterm Complement *}

definition minterm_complement :: "('var, 'k::finite) minterm \<Rightarrow> ('var, 'k) minterm"
  where "minterm_complement M = (to_minterm {(literal_complement l) | l. l\<in>(to_literal_set M)})"


subsection {* Minterm Var Set *}

definition minterm_var_set :: "('var, 'k::finite) minterm \<Rightarrow> 'var set"
  where "minterm_var_set M = {x. \<exists>l\<in>(to_literal_set M). x\<in>(literal_var_set l)}"


subsection {* Minterms Lemmas *}

lemma minterm_have_ext_card_heap_ge:
  fixes M::"('var, 'k::finite) minterm"
  shows "\<exists>!l\<in>(to_literal_set M). \<exists>n. ((to_sl_formula l) = (ext_card_heap_ge n))"
proof -
  have "to_literal_set M \<in> {S. ((\<exists>!l\<in>S::('var, 'k::finite) literal set. \<exists>n. 
                              (to_sl_formula l) = (ext_card_heap_ge n))
                          \<and> (\<exists>!l\<in>S::('var, 'k::finite) literal set. \<exists>n. 
                              (to_sl_formula l) = (not (ext_card_heap_ge n)))
                          \<and> finite S)}"
    by (metis (no_types) Rep_minterm to_literal_set_def)
  hence "(\<exists>!l\<in>(to_literal_set M). \<exists>n. (to_sl_formula l) = (ext_card_heap_ge n))
       \<and> (\<exists>!l\<in>(to_literal_set M). \<exists>n. (to_sl_formula l) = (not (ext_card_heap_ge n)))"
    by simp
  thus ?thesis
    by simp
qed

lemma minterm_have_not_ext_card_heap_ge:
  fixes M::"('var, 'k::finite) minterm"
  shows "\<exists>!l\<in>(to_literal_set M). \<exists>n. ((to_sl_formula l) = (not (ext_card_heap_ge n)))"
proof -
  have "to_literal_set M \<in> {S. ((\<exists>!l\<in>S::('var, 'k::finite) literal set. \<exists>n. 
                              (to_sl_formula l) = (ext_card_heap_ge n))
                          \<and> (\<exists>!l\<in>S::('var, 'k::finite) literal set. \<exists>n. 
                              (to_sl_formula l) = (not (ext_card_heap_ge n)))
                          \<and> finite S)}"
    by (metis (no_types) Rep_minterm to_literal_set_def)
  hence "(\<exists>!l\<in>(to_literal_set M). \<exists>n. (to_sl_formula l) = (ext_card_heap_ge n))
       \<and> (\<exists>!l\<in>(to_literal_set M). \<exists>n. (to_sl_formula l) = (not (ext_card_heap_ge n)))"
    by simp
  thus ?thesis
    by (simp add: to_literal_set_def)
qed


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

definition h_literals :: "('var, 'k::finite) literal set"
  where "h_literals = {to_literal (ext_card_heap_ge n) |n. True}
                    \<union> {to_literal (not (ext_card_heap_ge n)) |n. True}"

subsubsection {* Minterms Sets Composed by an Intersection *}

definition e_minterm :: "('var, 'k::finite) minterm \<Rightarrow> ('var, 'k) literal set"
  where "e_minterm M = to_literal_set M \<inter> e_literals"

definition a_minterm :: "('var, 'k::finite) minterm \<Rightarrow> ('var, 'k) literal set"
  where "a_minterm M = to_literal_set M \<inter> a_literals"

definition p_minterm :: "('var, 'k::finite) minterm \<Rightarrow> ('var, 'k) literal set"
  where "p_minterm M = to_literal_set M \<inter> p_literals"

definition h_minterm :: "('var, 'k::finite) minterm \<Rightarrow> ('var, 'k) literal set"
  where "h_minterm M = to_literal_set M \<inter> h_literals"



subsection {* Minterms Evaluation *}

definition minterm_evl :: "('var, 'addr, 'k::finite) interp \<Rightarrow> ('var, 'k) minterm \<Rightarrow> bool"
  where "minterm_evl I M = literal_set_evl I (to_literal_set M)"


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

lemma to_atom_charact:
  assumes "to_atom l \<in> test_formulae"
  shows "l\<in> a_literals \<union> e_literals \<union> p_literals \<union> h_literals"
proof -
  have atm: "to_atom l \<in> {(eq x y)|x y. True} \<union> {(alloc x)|x. True}  \<union> {(points_to x y)|x y. True} 
                 \<union> {ext_card_heap_ge n|n. True}" using test_formulae_charact assms by auto
  show ?thesis
  proof (cases "l = to_literal (to_atom l)")
    case True
    thus ?thesis using atm unfolding a_literals_def e_literals_def p_literals_def h_literals_def by force
  next 
    case False
    hence "l = to_literal (not (to_atom l))" using literal_atom_cases_tmp[of l] by simp
    thus ?thesis using atm unfolding a_literals_def e_literals_def p_literals_def h_literals_def by force
  qed
qed

lemma to_atom_minterms_sets:
  fixes M::"('var , 'k::finite) literal set"
  assumes "\<And>l::(('var, 'k) literal). ((l \<in> M) \<Longrightarrow> (to_sl_formula l) \<in> test_formulae) \<Longrightarrow> to_literal (not (to_sl_formula l)) \<in> M"
    and "to_literal (to_atom l) \<in> M"  
  shows "l \<in> M"
  by (metis assms(1) assms(2) literal_atom_cases_tmp pos_literal_inv to_atom_is_test_formula)

lemma from_to_atom_in_e_minterm:
  fixes M::"('var , 'k::finite) minterm"
  assumes "\<And>l::(('var, 'k) literal). (l \<in> (e_minterm M)) \<Longrightarrow> (to_sl_formula l) \<in> test_formulae \<Longrightarrow> to_literal (not (to_sl_formula l)) \<in> (e_minterm M)"
    and "to_literal (to_atom l) \<in> (e_minterm M)"
  shows "l \<in> (e_minterm M)"
  by (metis assms(1) assms(2) literal_atom_cases_tmp pos_literal_inv to_atom_is_test_formula)

lemma from_to_atom_in_a_minterm:
  fixes M::"('var , 'k::finite) minterm"
  assumes "\<And>l::(('var, 'k) literal). (l \<in> (a_minterm M)) \<Longrightarrow> (to_sl_formula l) \<in> test_formulae \<Longrightarrow> to_literal (not (to_sl_formula l)) \<in> (a_minterm M)"
    and "to_literal (to_atom l) \<in> (a_minterm M)"
  shows "l \<in> (a_minterm M)"
  by (metis assms(1) assms(2) literal_atom_cases_tmp pos_literal_inv to_atom_is_test_formula)

lemma from_to_atom_in_p_minterm:
  fixes M::"('var , 'k::finite) minterm"
  assumes "\<And>l::(('var, 'k) literal). (l \<in> (p_minterm M)) \<Longrightarrow> (to_sl_formula l) \<in> test_formulae \<Longrightarrow> to_literal (not (to_sl_formula l)) \<in> (p_minterm M)"
    and "to_literal (to_atom l) \<in> (p_minterm M)"
  shows "l \<in> (p_minterm M)"
  by (metis assms(1) assms(2) literal_atom_cases_tmp pos_literal_inv to_atom_is_test_formula)

lemma minterms_sets_equality:
  fixes M::"('var, 'k::finite) minterm"
  shows  "to_literal_set M = e_minterm M \<union> a_minterm M \<union> p_minterm M \<union> h_minterm M"
proof
  define min_set::"('var, 'k::finite) literal set" 
    where "min_set = e_minterm M \<union> a_minterm M \<union> p_minterm M \<union> h_minterm M"
  show "to_literal_set M \<subseteq> min_set"
  proof
    fix l
    assume asm:"l \<in> (to_literal_set M)"
    hence "to_atom l\<in> test_formulae" by (simp add: to_atom_is_test_formula)
    hence "l \<in> e_literals \<union> a_literals \<union> p_literals \<union> h_literals" using to_atom_charact by auto
    thus "l\<in> min_set" unfolding min_set_def using asm
      by (simp add: a_minterm_def e_minterm_def h_minterm_def p_minterm_def)
  qed
next
    show "e_minterm M \<union> a_minterm M \<union> p_minterm M \<union> h_minterm M \<subseteq> to_literal_set M"
      by (simp add: a_minterm_def e_minterm_def h_minterm_def p_minterm_def)
qed
  

subsection {* Completeness Definitions *}

subsubsection {* E-complete *}

definition E_complete :: "'var set \<Rightarrow> ('var, 'k::finite) minterm \<Rightarrow> bool"
  where "E_complete S M 
  = (\<forall>x\<in>S. \<forall>y\<in>S.
    (to_literal (eq x y)) \<in> (to_literal_set M)
  \<or> (to_literal (not (eq x y))) \<in> (to_literal_set M))"


subsubsection {* A-complete *}

definition A_complete :: "'var set \<Rightarrow> ('var, 'k::finite) minterm \<Rightarrow> bool"
  where "A_complete S M
  = (\<forall>x\<in>S.
    (to_literal (alloc x)) \<in> (to_literal_set M)
  \<or> (to_literal (not (alloc x))) \<in> (to_literal_set M))"


subsubsection {* Sat *}

definition minterm_sat :: "('var, 'k::finite) minterm \<Rightarrow> bool"
  where "minterm_sat M = (\<forall>l\<in>(to_literal_set M). (literal_complement l) \<notin> (to_literal_set M))"


subsection {* Closures Definitions *}

subsubsection {* Complement Closure *}

definition cc :: "('var, 'k::finite) minterm \<Rightarrow> ('var, 'k) literal set"
  where "cc M = (to_literal_set M) \<union> {literal_complement l | l. l\<in>(to_literal_set M)}"


subsubsection {* Points-to Closure *}

definition pc :: "('var, 'k::finite) minterm \<Rightarrow> bool"
  where "pc M = (\<forall>x1. \<forall>y1. \<forall>x2. \<forall>y2.
                 (((to_literal (points_to x1 y1)) \<in> (to_literal_set M))
               \<and> ((to_literal (points_to x2 y2)) \<in> (to_literal_set M))
               \<and> ((to_literal (eq x1 x2)) \<in> (to_literal_set M))
             \<longrightarrow> (\<forall>i::'k. (to_literal (eq (y1 $ i) (y2 $ i))) \<in> (to_literal_set M))))"


subsubsection {* Domain Closure *}

definition dc :: "('var, 'k::finite) minterm \<Rightarrow> bool"
  where "dc M = (\<forall>n1 n2.
                ((to_literal (ext_card_heap_ge n1)) \<in> (to_literal_set M)
              \<and> (to_literal (not (ext_card_heap_ge n2))) \<in> (to_literal_set M))
            \<longrightarrow> (n1 < n2))"


subsection {* Footprint-Consistency *}

definition footprint_consistent :: "('var, 'k::finite) minterm \<Rightarrow> bool"
  where "footprint_consistent M = (\<forall>x1 x2 y1 y2.
                                  (to_literal (eq x1 x2) \<in> (to_literal_set M))
                                \<and> (\<forall>i::'k. to_literal (eq (y1 $ i) (y2 $ i)) \<in> (to_literal_set M))
                                \<and> (to_literal (alloc x1) \<in> (to_literal_set M) \<longrightarrow> to_literal (not (alloc x2)) \<notin> (to_literal_set M))
                                \<and> (to_literal (points_to x1 y1) \<in> (to_literal_set M) \<longrightarrow> (to_literal (not (alloc x2)) \<notin> (to_literal_set M) 
                                                                                        \<and> to_literal (not (points_to x2 y2)) \<notin> (to_literal_set M))))"


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


subsubsection {* Proposition 7 *}

lemma points_to_var_set:
  assumes "to_literal (points_to x y) \<in> to_literal_set M"
  shows "\<forall>i. (y $ i) \<in> (minterm_var_set M)"
proof
  fix i
  have "to_literal (sl_conj (sl_mapsto x y) sl_true) \<in> to_literal_set M"
    by (metis assms points_to_def)
  hence "literal_var_set  (to_literal (sl_conj (sl_mapsto x y) sl_true)) \<subseteq> (minterm_var_set M)"
    using minterm_var_set_def by fastforce
  hence "var_set (sl_mapsto x y) \<subseteq> (minterm_var_set M)"
    by (metis Un_subset_iff literal_var_set_def points_to_def pos_literal_inv test_formulae.intros(1) var_set.simps(9))
  hence "({x} \<union> {y $ i | i. True}) \<subseteq> (minterm_var_set M)"
    by auto
  thus "(y $ i) \<in> (minterm_var_set M)"
    by blast
qed

lemma minterm_prop_7_pc:
  fixes I::"('var, 'addr, 'k::finite) interp"
    and M::"('var, 'k) minterm"
  assumes "minterm_evl I M"
    and "E_complete (minterm_var_set M) M"
  shows "pc M" unfolding pc_def
proof (intro allI impI)
  fix x1 y1 x2 y2 i
  assume asm: "to_literal (points_to x1 y1) \<in> to_literal_set M
             \<and> to_literal (points_to x2 y2) \<in> to_literal_set M
             \<and> to_literal (eq x1 x2) \<in> to_literal_set M"
  have "literal_evl I (to_literal (points_to x1 y1))"
    using asm assms(1) literal_set_evl_def minterm_evl_def by blast
  hence points_to_1: "(store_and_heap I x1) = Some (store_vector (store I) y1)"
    by (simp add: literal_evl_def test_formulae.intros(1) tf_prop_1_1)
  have "literal_evl I (to_literal (points_to x2 y2))"
    using asm assms(1) literal_set_evl_def minterm_evl_def by blast
  hence points_to_2: "(store_and_heap I x2) = Some (store_vector (store I) y2)"
    by (simp add: literal_evl_def test_formulae.intros(1) tf_prop_1_1)
  have equality_x: "store I x1 = store I x2"
    by (metis asm assms(1) evaluation.simps(3) literal_evl_def literal_set_evl_def 
        minterm_evl_def pos_literal_inv test_formulae.intros(4))
  from points_to_1 and points_to_2 and equality_x have "(store_vector (store I) y1) = (store_vector (store I) y2)"
    by (simp add: store_and_heap_def)
  hence "(store I) (y1 $ i) = (store I) (y2 $ i)"
    using equality_store_vector by blast
  hence "\<not>(literal_evl I (to_literal (not (eq (y1 $ i) (y2 $ i)))))"
    by (simp add: literal_evl_def test_formulae.intros(4))
  moreover have "(y1 $ i) \<in> (minterm_var_set M)" using asm
    by (meson points_to_var_set)
  ultimately show "to_literal (eq (y1 $ i) (y2 $ i)) \<in> to_literal_set M"
    by (meson E_complete_def asm assms(1) assms(2) literal_set_evl_def minterm_evl_def points_to_var_set)
qed

lemma card_heap_bounded:
  assumes "evaluation I (ext_card_heap_ge n1)"
    and "evaluation I (not (ext_card_heap_ge n2))"
  shows "n1 < n2"
proof -
  have "evaluation I (ext_card_heap_ge n1)"
    by (simp add: assms(1))
  moreover have "\<not>(evaluation I (ext_card_heap_ge n2))"
    using assms(2) by auto
  ultimately show "n1 < n2"
    by (simp add: tf_prop_1_3)
qed

lemma minterm_prop_7_dc:
  fixes I::"('var, 'addr, 'k::finite) interp"
    and M::"('var, 'k) minterm"
  assumes "minterm_evl I M"
    and "E_complete (minterm_var_set M) M"
  shows "dc M"
proof -
  obtain l1 and n1 where l1_in_M :"l1 \<in> (to_literal_set M)" 
                     and l1_def: "l1 = to_literal (ext_card_heap_ge n1)"
    by (metis Rep_literal_inverse minterm_have_ext_card_heap_ge to_literal_def to_sl_formula_def) 
  obtain l2 and n2 where l2_in_M: "l2 \<in> (to_literal_set M)"
                     and l2_def: "l2 = to_literal (not (ext_card_heap_ge n2))"
    by (metis literal_atom_cases_tmp minterm_have_not_ext_card_heap_ge neg_literal_inv pos_literal_inv to_atom_is_test_formula)  
  have "literal_evl I l1"
    using assms(1) l1_in_M literal_set_evl_def minterm_evl_def by blast
  moreover have "literal_evl I l2"
    using assms(1) l2_in_M literal_set_evl_def minterm_evl_def by blast
  ultimately have "n1 < n2"
    by (simp add: card_heap_bounded l1_def l2_def literal_evl_def test_formulae.intros(3))
  thus "dc M"
    by (metis assms(1) card_heap_bounded dc_def literal_evl_def literal_set_evl_def minterm_evl_def 
        neg_literal_inv pos_literal_inv test_formulae.intros(3))
qed

lemma minterm_prop7:
  fixes I::"('var, 'addr, 'k::finite) interp"
    and M::"('var, 'k) minterm"
  assumes "minterm_evl I M"
    and "E_complete (minterm_var_set M) M"
  shows "pc M \<and> dc M"
  using assms(1) assms(2) minterm_prop_7_dc minterm_prop_7_pc by blast


subsubsection {* Proposition 9 *}

lemma minterm_prop_9_not_E_complete:
  fixes M::"('var, 'k::finite) minterm"
  assumes "footprint_consistent M"
  shows "nv (to_literal_set M) \<inter> av (to_literal_set M) = {}"
proof (rule ccontr)
  assume asm: "nv (to_literal_set M) \<inter> av (to_literal_set M) \<noteq> {}"
  from asm obtain x x1 where nv_1: "x \<in> (nv (to_literal_set M)) \<inter> av (to_literal_set M)"
                         and nv_2: "to_literal (eq x x1) \<in> (to_literal_set M)"
                         and nv_3: "to_literal (not (alloc x1)) \<in> (to_literal_set M)"
    unfolding nv_def
    by blast
  from asm and nv_1 and nv_2 and nv_3 obtain x2 where av_1: "to_literal (eq x x2) \<in> (to_literal_set M)" 
      and av_2:"(to_literal_set M)\<inter>({to_literal (alloc x2)} \<union> {to_literal (points_to x2 y) | y. True}) \<noteq> {}"
    unfolding av_def
    by auto
  hence "\<not>(footprint_consistent M)"
    using footprint_consistent_def nv_3 by fastforce
  thus False
    using assms by simp
qed

lemma eq_var_set:
  assumes "to_literal (eq x y) \<in> to_literal_set M"
  shows "(x \<in> (minterm_var_set M)) \<and> (y \<in> (minterm_var_set M))"
proof -
  have "x \<in> var_set (eq x y) \<and> y \<in> var_set (eq x y)"
    by simp
  hence "x \<in> literal_var_set (to_literal (eq x y)) \<and> y \<in> literal_var_set (to_literal (eq x y))"
    by (simp add: literal_var_set_def test_formulae.intros(4))
  thus "x \<in> (minterm_var_set M) \<and> y \<in> (minterm_var_set M)"
    using assms minterm_var_set_def by fastforce
qed

lemma three_eq_sat:
  fixes M::"('var, 'k::finite) minterm"
    and I::"('var, 'addr, 'k) interp"
    and x1::'var
    and x2::'var
    and x3::'var
  assumes "to_literal (eq x1 x2) \<in> (to_literal_set M)"
    and "to_literal (eq x2 x3) \<in> (to_literal_set M)"
    and "minterm_evl I M"
    and "E_complete (minterm_var_set M) M"
  shows "to_literal (eq x1 x3) \<in> (to_literal_set M)"
proof -
  have "x1 \<in> (minterm_var_set M)"
    by (meson assms(1) eq_var_set)
  moreover have "x2 \<in> (minterm_var_set M)"
    by (meson assms(1) eq_var_set)
  moreover have "E_complete (minterm_var_set M) M"
    by (simp add: assms(4))
  ultimately have "to_literal (eq x1 x3) \<in> (to_literal_set M) \<or> to_literal (not (eq x1 x3)) \<in> (to_literal_set M)"
    by (meson E_complete_def assms(2) eq_var_set)
  moreover have "evaluation I (eq x1 x3)"
    by (metis assms(1) assms(2) assms(3) evaluation.simps(3) literal_evl_def literal_set_evl_def
        minterm_evl_def pos_literal_inv test_formulae.intros(4))
  moreover have "minterm_evl I M"
    by (simp add: assms(3))
  ultimately show "to_literal (eq x1 x3) \<in> (to_literal_set M)"
    by (metis evaluation.simps(4) literal_evl_def literal_set_evl_def minterm_evl_def 
        neg_literal_inv test_formulae.intros(4))
qed

lemma eq_av:
  fixes M::"('var, 'k::finite) minterm"
    and I::"('var, 'addr, 'k) interp"
    and x1::'var
    and x2::'var
  assumes "to_literal (eq x1 x2) \<in> (to_literal_set M)"
    and "x2 \<in> av (to_literal_set M)"
    and "minterm_evl I M"
    and "E_complete (minterm_var_set M) M"
  shows "x1 \<in> av (to_literal_set M)"
proof -
  have "x2 \<in> av (to_literal_set M)"
    by (simp add: assms(2))
  from this obtain x3 
    where "to_literal (eq x2 x3) \<in> (to_literal_set M)"
      and alloc_points_to_x3: "((to_literal_set M) \<inter> ({to_literal (alloc x3)} 
                                                    \<union> {to_literal (points_to x3 y) | y. True})) \<noteq> {}"
    unfolding av_def
    by blast
  hence eq_x3: "to_literal (eq x1 x3) \<in> (to_literal_set M)"
    by (meson assms(1) assms(3) assms(4) three_eq_sat)
  thus  "x1 \<in> av (to_literal_set M)" using av_def alloc_points_to_x3
    by force
qed

lemma minterm_prop_9_E_complete:
  fixes M::"('var, 'k::finite) minterm"
  assumes "footprint_consistent M"
    and "E_complete (minterm_var_set M) M"
    and "X \<inter> (av (to_literal_set M)) = {}"
    and "minterm_evl I M"
  shows "(store_set (store I) X) \<inter> (store_set (store I) (av (to_literal_set M))) = {}"
proof (rule ccontr)
  assume "(store_set (store I) X) \<inter> (store_set (store I) (av (to_literal_set M))) \<noteq> {}"
  from this obtain l where "l \<in> (store_set (store I) X)"
                       and "l \<in> (store_set (store I) (av (to_literal_set M)))"
    by blast
  from this obtain x1 x2 where x1_in: "x1 \<in> X"
                           and x2_in: "x2 \<in> (av (to_literal_set M))"
                           and x1_def: "store I x1 = l"
                           and x2_def: "store I x2 = l"
    by (metis antecedent_store_set)
  have e_com:"E_complete (minterm_var_set M) M"
    by (simp add: assms(2))
  hence cases: "to_literal (eq x1 x2) \<in> (to_literal_set M) \<or> to_literal (not (eq x1 x2)) \<in> (to_literal_set M)"
    using assms(1) footprint_consistent_def by force
  from x2_in and e_com have case_1: "to_literal (eq x1 x2) \<in> (to_literal_set M) \<longrightarrow> x1 \<in> (av (to_literal_set M))"
    by (meson assms(4) eq_av)
  have case_2: "to_literal (not (eq x1 x2)) \<in> (to_literal_set M) \<longrightarrow> \<not>(minterm_evl I M)"
    by (metis evaluation.simps(3) evaluation.simps(4) literal_evl_def literal_set_evl_def 
        minterm_evl_def neg_literal_inv test_formulae.intros(4) x1_def x2_def)
  from cases and case_1 and case_2 show False
    using assms(3) assms(4) x1_in by blast
qed


end
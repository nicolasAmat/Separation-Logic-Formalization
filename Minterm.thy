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


subsection {* Minterms Lemmas *}

lemma minterm_have_ext_card_heap_ge:
  "\<exists>l\<in>(minterm_to_literal_set M). \<exists>n. ((to_sl_formula l) = (ext_card_heap_ge n))"
  using Rep_minterm minterm_to_literal_set_def by fastforce

lemma minterm_have_not_ext_card_heap_ge:
  "\<exists>l\<in>(minterm_to_literal_set M). \<exists>n. ((to_sl_formula l) = (not (ext_card_heap_ge n)))"
  using Rep_minterm minterm_to_literal_set_def by fastforce


subsection {* Some Sets Definitions *}

definition e_minterm :: "('var, 'k::finite) minterm \<Rightarrow> ('var, 'k) literal set"
  where "e_minterm M = (minterm_to_literal_set M) 
                     \<inter> ({to_literal (eq x y)|x y. True} \<union> {to_literal(not (eq x y))|x y. True})"

definition a_minterm :: "('var, 'k::finite) minterm \<Rightarrow> ('var, 'k) literal set"
  where "a_minterm M = (minterm_to_literal_set M) 
                     \<inter> {to_literal (alloc x)|x. True}"

definition u_minterm :: "('var, 'k::finite) minterm \<Rightarrow> ('var, 'k) literal set"
  where "u_minterm M = (minterm_to_literal_set M)"
                 
definition p_minterm :: "('var, 'k::finite) minterm \<Rightarrow> ('var, 'k) literal set"
  where "p_minterm M = (minterm_to_literal_set M) 
                     \<inter> ({to_literal (points_to x y)|x y. True} \<union> {to_literal (not (points_to x y))|x y. True})"


subsection {* Minterms Sets Equality *}

lemma minterms_sets_equality:
  "minterm_to_literal_set M = 
   e_minterm M \<union> a_minterm M \<union> u_minterm M \<union> p_minterm M \<union> 
   {l \<in> (minterm_to_literal_set M). (\<exists>n. (to_sl_formula l) = (ext_card_heap_ge n)) \<or> (\<exists>n. (to_sl_formula l) = (not (ext_card_heap_ge n)))}"
proof
  have "minterm_to_literal_set M \<subseteq> (u_minterm M)"
    by (simp add: u_minterm_def)
  thus "minterm_to_literal_set M
        \<subseteq> e_minterm M \<union> a_minterm M \<union> u_minterm M \<union> p_minterm M \<union>
        {l \<in> minterm_to_literal_set M. (\<exists>n. to_sl_formula l = ext_card_heap_ge n) \<or> (\<exists>n. to_sl_formula l = not (ext_card_heap_ge n))}"
    by (simp add: sup.coboundedI1 u_minterm_def)
next
  show "e_minterm M \<union> a_minterm M \<union> u_minterm M \<union> p_minterm M \<union>
        {l \<in> minterm_to_literal_set M. (\<exists>n. to_sl_formula l = ext_card_heap_ge n) \<or> (\<exists>n. to_sl_formula l = not (ext_card_heap_ge n))}
        \<subseteq> minterm_to_literal_set M"
  proof -
  have f1: "\<And>m. a_minterm (m::('a, 'b) minterm) = Rep_minterm m \<inter> {l. \<exists>a. l = to_literal (alloc a)}"
    by (simp add: a_minterm_def minterm_to_literal_set_def)
  have f2: "\<And>m. p_minterm (m::('a, 'b) minterm) = Rep_minterm m \<inter> ({l. \<exists>a v. l = to_literal (points_to a v)} \<union> {l. \<exists>a v. l = to_literal (not (points_to a v))})"
    by (simp add: minterm_to_literal_set_def p_minterm_def)
    have f3: "\<And>m. e_minterm (m::('a, 'b) minterm) = Rep_minterm m \<inter> ({l. \<exists>a aa. l = to_literal (eq a aa)} \<union> {l. \<exists>a aa. l = to_literal (not (eq a aa))})"
      by (simp add: e_minterm_def minterm_to_literal_set_def)
    obtain ll :: "('a, 'b) literal set \<Rightarrow> ('a, 'b) literal set \<Rightarrow> ('a, 'b) literal" where
      f4: "\<And>L La. (L \<subseteq> La \<or> ll L La \<in> L) \<and> (ll L La \<notin> La \<or> L \<subseteq> La)"
  by (metis (no_types) subsetI)
    moreover
  { assume "ll {l. l \<in> minterm_to_literal_set M \<and> ((\<exists>e. to_sl_formula l = ext_card_heap_ge e) \<or> (\<exists>e. to_sl_formula l = not (ext_card_heap_ge e))) \<or> l \<in> {l \<in> Rep_minterm M. l \<in> {l. (\<exists>a v. l = to_literal (not (points_to a v))) \<or> (\<exists>a v. l = to_literal (points_to a v))}} \<or> l \<in> Rep_minterm M} (Rep_minterm M) \<notin> Rep_minterm M"
    moreover
  { assume "(ll {l. l \<in> minterm_to_literal_set M \<and> ((\<exists>e. to_sl_formula l = ext_card_heap_ge e) \<or> (\<exists>e. to_sl_formula l = not (ext_card_heap_ge e))) \<or> l \<in> {l \<in> Rep_minterm M. l \<in> {l. (\<exists>a v. l = to_literal (not (points_to a v))) \<or> (\<exists>a v. l = to_literal (points_to a v))}} \<or> l \<in> Rep_minterm M} (Rep_minterm M) \<notin> minterm_to_literal_set M \<or> (\<forall>e. to_sl_formula (ll {l. l \<in> minterm_to_literal_set M \<and> ((\<exists>e. to_sl_formula l = ext_card_heap_ge e) \<or> (\<exists>e. to_sl_formula l = not (ext_card_heap_ge e))) \<or> l \<in> {l \<in> Rep_minterm M. l \<in> {l. (\<exists>a v. l = to_literal (not (points_to a v))) \<or> (\<exists>a v. l = to_literal (points_to a v))}} \<or> l \<in> Rep_minterm M} (Rep_minterm M)) \<noteq> ext_card_heap_ge e) \<and> (\<forall>e. to_sl_formula (ll {l. l \<in> minterm_to_literal_set M \<and> ((\<exists>e. to_sl_formula l = ext_card_heap_ge e) \<or> (\<exists>e. to_sl_formula l = not (ext_card_heap_ge e))) \<or> l \<in> {l \<in> Rep_minterm M. l \<in> {l. (\<exists>a v. l = to_literal (not (points_to a v))) \<or> (\<exists>a v. l = to_literal (points_to a v))}} \<or> l \<in> Rep_minterm M} (Rep_minterm M)) \<noteq> not (ext_card_heap_ge e))) \<and> ll {l. l \<in> minterm_to_literal_set M \<and> ((\<exists>e. to_sl_formula l = ext_card_heap_ge e) \<or> (\<exists>e. to_sl_formula l = not (ext_card_heap_ge e))) \<or> l \<in> {l \<in> Rep_minterm M. l \<in> {l. (\<exists>a v. l = to_literal (not (points_to a v))) \<or> (\<exists>a v. l = to_literal (points_to a v))}} \<or> l \<in> Rep_minterm M} (Rep_minterm M) \<notin> {l \<in> Rep_minterm M. l \<in> {l. (\<exists>a v. l = to_literal (not (points_to a v))) \<or> (\<exists>a v. l = to_literal (points_to a v))}} \<and> ll {l. l \<in> minterm_to_literal_set M \<and> ((\<exists>e. to_sl_formula l = ext_card_heap_ge e) \<or> (\<exists>e. to_sl_formula l = not (ext_card_heap_ge e))) \<or> l \<in> {l \<in> Rep_minterm M. l \<in> {l. (\<exists>a v. l = to_literal (not (points_to a v))) \<or> (\<exists>a v. l = to_literal (points_to a v))}} \<or> l \<in> Rep_minterm M} (Rep_minterm M) \<notin> Rep_minterm M"
    then have "ll {l. l \<in> minterm_to_literal_set M \<and> ((\<exists>e. to_sl_formula l = ext_card_heap_ge e) \<or> (\<exists>e. to_sl_formula l = not (ext_card_heap_ge e))) \<or> l \<in> {l \<in> Rep_minterm M. l \<in> {l. (\<exists>a v. l = to_literal (not (points_to a v))) \<or> (\<exists>a v. l = to_literal (points_to a v))}} \<or> l \<in> Rep_minterm M} (Rep_minterm M) \<notin> {l. l \<in> minterm_to_literal_set M \<and> ((\<exists>e. to_sl_formula l = ext_card_heap_ge e) \<or> (\<exists>e. to_sl_formula l = not (ext_card_heap_ge e))) \<or> l \<in> {l \<in> Rep_minterm M. l \<in> {l. (\<exists>a v. l = to_literal (not (points_to a v))) \<or> (\<exists>a v. l = to_literal (points_to a v))}} \<or> l \<in> Rep_minterm M}"
          by blast
        then have "{l. l \<in> minterm_to_literal_set M \<and> ((\<exists>e. to_sl_formula l = ext_card_heap_ge e) \<or> (\<exists>e. to_sl_formula l = not (ext_card_heap_ge e))) \<or> l \<in> {l \<in> Rep_minterm M. l \<in> {l. (\<exists>a v. l = to_literal (not (points_to a v))) \<or> (\<exists>a v. l = to_literal (points_to a v))}} \<or> l \<in> Rep_minterm M} \<subseteq> Rep_minterm M"
          using f4 by meson }
      ultimately have "ll {l. l \<in> minterm_to_literal_set M \<and> ((\<exists>e. to_sl_formula l = ext_card_heap_ge e) \<or> (\<exists>e. to_sl_formula l = not (ext_card_heap_ge e))) \<or> l \<in> {l \<in> Rep_minterm M. l \<in> {l. (\<exists>a v. l = to_literal (not (points_to a v))) \<or> (\<exists>a v. l = to_literal (points_to a v))}} \<or> l \<in> Rep_minterm M} (Rep_minterm M) \<in> Rep_minterm M \<or> {l. l \<in> minterm_to_literal_set M \<and> ((\<exists>e. to_sl_formula l = ext_card_heap_ge e) \<or> (\<exists>e. to_sl_formula l = not (ext_card_heap_ge e))) \<or> l \<in> {l \<in> Rep_minterm M. l \<in> {l. (\<exists>a v. l = to_literal (not (points_to a v))) \<or> (\<exists>a v. l = to_literal (points_to a v))}} \<or> l \<in> Rep_minterm M} \<subseteq> Rep_minterm M"
        by (simp add: minterm_to_literal_set_def) }
    ultimately have "{l. l \<in> minterm_to_literal_set M \<and> ((\<exists>e. to_sl_formula l = ext_card_heap_ge e) \<or> (\<exists>e. to_sl_formula l = not (ext_card_heap_ge e))) \<or> l \<in> {l \<in> Rep_minterm M. l \<in> {l. (\<exists>a v. l = to_literal (not (points_to a v))) \<or> (\<exists>a v. l = to_literal (points_to a v))}} \<or> l \<in> Rep_minterm M} \<subseteq> Rep_minterm M"
      by meson
    then have "e_minterm M \<union> a_minterm M \<union> Rep_minterm M \<union> p_minterm M \<union> {l \<in> minterm_to_literal_set M. (\<exists>e. to_sl_formula l = ext_card_heap_ge e) \<or> (\<exists>e. to_sl_formula l = not (ext_card_heap_ge e))} \<subseteq> Rep_minterm M"
      using f3 f2 f1 by auto
    then show ?thesis
      by (simp add: minterm_to_literal_set_def u_minterm_def)
  qed
qed


end
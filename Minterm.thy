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


subsection {* Some Sets Definitions *}

definition e_minterm::"('var, 'k::finite) minterm \<Rightarrow> ('var, 'k) sl_formula set"
  where "e_minterm M = {(Rep_literal l)|l. l \<in> (Rep_minterm M)} 
                     \<inter> ({eq x y|x y. True} \<union> {not (eq x y)|x y. True})"

definition a_minterm::"('var, 'k::finite) minterm \<Rightarrow> ('var, 'k) sl_formula set"
  where "a_minterm M = {(Rep_literal l)|l. l \<in> (Rep_minterm M)} 
                     \<inter> {alloc x|x. True}"

definition u_minterm::"('var, 'k::finite) minterm \<Rightarrow> ('var, 'k) sl_formula set"
  where "u_minterm M = {(Rep_literal l)|l. l \<in> (Rep_minterm M)} 
                     \<inter> ({ext_card_heap_ge n|n. True} \<union> {not (ext_card_heap_ge n)|n. True})"

definition p_minterm::"('var, 'k::finite) minterm \<Rightarrow> ('var, 'k) sl_formula set"
  where "p_minterm M = {(Rep_literal l)|l. l \<in> (Rep_minterm M)} 
                     \<inter> ({points_to x y|x y. True} \<union> {not (points_to x y)|x y. True})"


(* 3 lemmes:
- si minterm \<Rightarrow> a
- si minterm \<Rightarrow> b
- si a et b \<Rightarrow> mintern
*)

(* M = e_minter \<union> a_minterm \<union> u_minterm \<union> p_minterm *)

end
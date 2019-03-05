(*  Title:      Separation-Logic-Formalization/Modus_Ponens.thy
    Author:     Nicolas Amat, Mnacho Echenim, Nicolas Peltier
*)

section {* Modus Ponens *}

text {* This section contains the Modus Ponens like for the sepration logic. *}

theory Modus_Ponens
  imports  
    Interpretation
    Formula
begin


subsection {* Proof *}

lemma modus_ponens:
  fixes I::"('var, 'addr, 'k::finite) interp" 
    and P::"('var, 'k::finite) sl_formula" 
    and Q::"('var, 'k::finite) sl_formula"
  assumes  "evaluation I (sl_conj P (sl_magic_wand P Q))"
  shows "evaluation I Q"
proof -
  have def_1:"\<exists>h1::('addr, 'k) heaps. 
        \<exists>h2::('addr, 'k) heaps. (union_heaps h1 h2 = heap I)
                              \<and> (disjoint_heaps h1 h2)
                              \<and> (evaluation (constructor_interp (store I) h1) P) 
                              \<and> (evaluation (constructor_interp (store I) h2) (sl_magic_wand P Q))"
    using assms evaluation.simps(10) by blast
  then have def_2: "\<exists>h2::('addr, 'k) heaps. 
                  \<forall>h3::('addr, 'k) heaps. ((disjoint_heaps h3 h2) \<and> (evaluation (constructor_interp (store I) h3) P))
                                          \<longrightarrow> (evaluation (constructor_interp (store I) (union_heaps h2  h3)) Q)"
    by (metis constructor_interp_def evaluation.simps(11) fst_conv store_def)
  from def_1 and def_2 show "evaluation I Q"
    by (metis commutative_union_disjoint_heaps constructor_interp_def eq_fst_iff evaluation.simps(11) heap_def snd_conv store_def)
qed


end
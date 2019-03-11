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
  have "\<exists>h1::('addr, 'k) heaps. 
              \<exists>h2::('addr, 'k) heaps. (union_heaps h1 h2 = heap I)
                                    \<and> (disjoint_heaps h1 h2)
                                    \<and> (evaluation (to_interp (store I) h1) P) 
                                    \<and> (evaluation (to_interp (store I) h2) (sl_magic_wand P Q))"
    using assms by simp
  moreover hence "\<exists>h2::('addr, 'k) heaps. 
                    \<forall>h3::('addr, 'k) heaps. ((disjoint_heaps h3 h2) \<and> (evaluation (to_interp (store I) h3) P))
                                         \<longrightarrow> (evaluation (to_interp (store I) (union_heaps h2  h3)) Q)"
    by (metis to_interp_def evaluation.simps(10) fst_conv store_def)
  ultimately show "evaluation I Q"
    by (metis commutative_union_disjoint_heaps to_interp_def eq_fst_iff evaluation.simps(10) heap_def snd_conv store_def)
qed


end
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
  have def_1: "\<exists>h1::('addr, 'k) heaps. 
               \<exists>h2::('addr, 'k) heaps. (union_heaps h1 h2 = heap I)
                                     \<and> (disjoint_heaps h1 h2)
                                     \<and> (evaluation (to_interp (store I) h1) P) 
                                     \<and> (evaluation (to_interp (store I) h2) (sl_magic_wand P Q))"
    using assms evaluation.simps(9) by blast 
  hence def_2: "\<exists>h2::('addr, 'k) heaps. 
                \<forall>h3::('addr, 'k) heaps. ((disjoint_heaps h3 h2) 
                                       \<and> (evaluation (to_interp (store I) h3) P))
                                    \<longrightarrow> (evaluation (to_interp (store I) (union_heaps h2  h3)) Q)"
    by (metis draft_1 evaluation.simps(10))
  from def_1 and def_2  show "evaluation I Q"
    by (metis commutative_union_disjoint_heaps draft_1 draft_2 evaluation.simps(10) prod.exhaust_sel 
        store_def to_interp_def) 
qed


end
(*  Title:      Separation-Logic-Formalization/Modus_Ponens.thy
    Author:     Nicolas Amat, Mnacho Echenim, Nicolas Peltier
*)

section \<open>Modus Ponens\<close>

text \<open>This section contains the Modus Ponens like for the sepration logic.\<close>

theory Modus_Ponens
imports  
  Interpretation
  Formula
begin


subsection \<open>Proof\<close>

lemma modus_ponens:
  fixes I::"('var, 'addr, 'k::finite) interp" 
    and P::"('var, 'k) sl_formula" 
    and Q::"('var, 'k) sl_formula"
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
    by (metis evaluation.simps(10) store_on_to_interp)
  from def_1 and def_2  show "evaluation I Q"
    by (metis commutative_union_disjoint_heaps evaluation.simps(10) heap_def heap_on_to_interp 
        prod.exhaust_sel store_def store_on_to_interp)
qed


end
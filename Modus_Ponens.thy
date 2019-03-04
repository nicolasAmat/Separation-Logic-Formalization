(*  Title:      Separation-Logic-Formalization/Modus_Ponens.thy
    Author:     Nicolas Amat, Mnacho Echenim, Nicolas Peltier
*)

section {* Modus Ponens *}

text {* This section contains the Modus Ponens like for the sepration logic. *}

theory Modus_Ponens
  imports 
    Main 
    Interpretation
    Formula
begin


subsection {* Proof *}

lemma modus_ponens:
  fixes I::"('var, 'addr, 'k) interp" and P::"('var, 'k) sl_formula" and Q::"('var, 'k) sl_formula"
  assumes  "evaluation I (sl_conj P (sl_magic_wand P Q))"
  shows "evaluation I Q"
proof -
  oops


end
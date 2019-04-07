(*  Title:      Separation-Logic-Formalization/Formula_Relation.thy
    Author:     Nicolas Amat, Mnacho Echenim, Nicolas Peltier
*)

section {* Relations *}

text {* This section contains the logical consequence and the equivalence. *}

theory Formula_Relation
imports
  Interpretation
  Formula
begin

subsection {* Logical Consequence *}

definition logical_consequence :: "'addr set \<Rightarrow> ('var, 'k::finite) sl_formula \<Rightarrow> ('var, 'k) sl_formula \<Rightarrow> bool" 
  where "logical_consequence env f g = (\<forall>I::('var, 'addr, 'k) interp. (evaluation I f) \<longrightarrow> (evaluation I g))"


subsection {* Equivalence *}

definition equivalence :: "'addr set \<Rightarrow> ('var, 'k::finite) sl_formula \<Rightarrow> ('var, 'k) sl_formula \<Rightarrow> bool" 
  where "equivalence env f g = ((logical_consequence env f g) \<and> (logical_consequence env g f))"

end
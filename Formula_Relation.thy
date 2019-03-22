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

definition logical_consequence :: "'addr \<Rightarrow> ('var, 'k::finite) sl_formula \<Rightarrow> ('var, 'k::finite) sl_formula \<Rightarrow> bool" 
  where "logical_consequence addr f g = (\<forall>I::('var, 'addr, 'k) interp. (evaluation I f) \<longrightarrow> (evaluation I g))"


subsection {* Equivalence *}

definition equivalence :: "'addr \<Rightarrow> ('var, 'k::finite) sl_formula \<Rightarrow> ('var, 'k::finite) sl_formula \<Rightarrow> bool" 
  where "equivalence addr f g = ((logical_consequence addr f g) \<and> (logical_consequence addr g f))"


end
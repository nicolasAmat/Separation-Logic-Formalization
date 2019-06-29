(*  Title:      Separation-Logic-Formalization/Formula_Relation.thy
    Author:     Nicolas Amat, Mnacho Echenim, Nicolas Peltier
*)

section \<open>Relations\<close>

text \<open>This section contains the logical consequence and the equivalence.\<close>

theory Formula_Relation
imports
  Interpretation
  Formula
begin

subsection \<open>Logical Consequence\<close>

definition logical_consequence :: "'addr set \<Rightarrow> ('var, 'k::finite) sl_formula \<Rightarrow> ('var, 'k) sl_formula \<Rightarrow> bool" 
  where "logical_consequence env f g = (\<forall>I::('var, 'addr, 'k) interp. (evaluation I f) \<longrightarrow> (evaluation I g))"


subsection \<open>Equivalence\<close>

definition equivalence :: "'addr set \<Rightarrow> ('var, 'k::finite) sl_formula \<Rightarrow> ('var, 'k) sl_formula \<Rightarrow> bool" 
  where "equivalence env f g = ((logical_consequence env f g) \<and> (logical_consequence env g f))"

end
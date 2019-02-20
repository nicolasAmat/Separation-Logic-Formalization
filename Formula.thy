(*  Title:      Separation-Logic-Formalization/Interpretation.thy
    Author:     Nicolas Amat, Mnacho Echenim, Nicolas Peltier
*)

section {* Formulas *}

text {* This section contains the syntax and semantics formalization of the separation logic formulas. *}

theory Formula
  imports Main Interpretation
begin


subsection {* Formulas Syntax *}

(* NP: mettre impl et conj et disj comme constructeurs de base risque de compliquer
   certaines preuves, car il y aura plus de cas à considerer. Peut-etre il faut mieux se limiter
   à un ensemble minimal de constructeurs et définir les autres des fonctions 
   (eg (imp x y) = (disj (not x) y) ) *)

(* NP: pour le cas mapsto, tel que c'est défini tu ne traites que le cas où les adresses 
   pointent vers d'autres adresses (SL with 1 "record field"). 
   En principe une adresse pointe vers un vecteur d'adresses... 
   et il faut vérifier quelque part qu'on a bien des vecteurs de la bonne longueur. 
   Cela ne peut être codé dans le datatype (me semble-t-il) puisqu'on a pas de type dépendent
   en Isabelle *)

datatype 'a sl_formula =
  (* Boolean *)
    true
  | false
  (* Classical Logic *)
  | eq 'a 'a
  | not "'a sl_formula"
  | impl "'a sl_formula" "'a sl_formula"
  | conj "'a sl_formula" "'a sl_formula"
  | disj "'a sl_formula" "'a sl_formula"
  (* Quantifier *)
  | forall 'a "'a sl_formula"
  | exists 'a "'a sl_formula"
  (* Separation Logic *)
  | sl_emp
  | sl_mapsto 'a 'a
  | sl_conj "'a sl_formula" "'a sl_formula"
  | sl_magic_wand "'a sl_formula" "'a sl_formula"


subsection {* Formulas Semantics *}

(* NP:  ci-dessous, il pourrait etre utile d'ajouter une fonction qui construit une 
        interpretation à partir d'un store et heap (pour la modularité, cela permet de
        changer la représentation des interprétations ci-besoin) *)

(* NP: la définition de la semantique de sl_emp et sl_mapsto est incorrecte *)
(* pour sl_emp il faut vérifier que le domaine de la heap est vide et pour sl_mapsto il faut
   vérifier que le domaine est réduit à E et que heap I E = F *)

(* NP: il semble plus cohérent d'utiliser plutot x et y à la place de E et F *)

primrec evaluation :: "(('a, 'b, 'c) interp) \<Rightarrow> 'a sl_formula \<Rightarrow> bool"
  where 
    "evaluation I true                = True"
  | "evaluation I false               = False" 
  | "evaluation I (eq x y)            = ((store I) x = (store I) y)"
  | "evaluation I (not P)             =  (\<not>(evaluation I P))"
  | "evaluation I (impl P Q)          = ((evaluation I P) \<longrightarrow> (evaluation I Q))"
  | "evaluation I (conj P Q)          = ((evaluation I P) \<and> (evaluation I Q))"
  | "evaluation I (disj P Q)          = ((evaluation I P) \<or> (evaluation I Q))"
  | "evaluation I (forall x P)        = (\<forall>u. (evaluation ((store I)(x:=u),(heap I)) P))"
  | "evaluation I (exists x P)        = (\<exists>u. (evaluation ((store I)(x:=u),(heap I)) P))"
  | "evaluation I (sl_emp)            = True"
  | "evaluation I (sl_mapsto E F)     = True"
  | "evaluation I (sl_conj P Q)       = (\<exists>h1 h2. (union_heaps h1 h2 = heap I)
                                               \<and> (disjoint_heaps h1 h2) 
                                               \<and> (evaluation ((store I), h1) P) 
                                               \<and> (evaluation ((store I), h2) Q))"
  | "evaluation I (sl_magic_wand P Q) = (\<forall>h. ((disjoint_heaps h (heap I)) \<and> (evaluation ((store I), h) P))
                                         \<longrightarrow> (evaluation ((store I), union_heaps (heap I) h)) Q)"


end
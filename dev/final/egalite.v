Add LoadPath "C:\Users\21692\ParcoursRecherche\dossier_final\coq_parcours_recherche\znaidi22\dev\final" as lp.


Load Verbose fonctions.


Require Import Bool Arith PeanoNat Coq.Arith.Peano_dec.

Locate "=".

Print eq.

(*

Inductive eq (A : Type) (x : A) : A -> Prop :=  eq_refl : x = x.

----- [eq_reflex]
x = x
*)

(** * A. Reflet bool/Prop *)

Print eqb.

Locate "=?".

Search((_ =? _ = false) -> ~(_ = _)).
Print beq_nat_false.

Search((_ =? _ = true) -> (_ = _)).
Print beq_nat_true.


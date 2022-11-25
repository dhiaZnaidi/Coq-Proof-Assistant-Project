Add LoadPath "C:\Users\21692\ParcoursRecherche\dossier_final\coq_parcours_recherche\znaidi22\dev\final" as lp.


Load Verbose fonctions.




(* Isomorphisme

       ∀ x : X, (A x) iso (B x)
   ---------------------------------
   { x : X & A x} iso { x : X & B x}

 *)

Section iso.

Hypothesis X : Type.
Hypothesis A : X -> Type.
Hypothesis B : X -> Type.
Hypothesis f : forall x, (A x) -> (B x).
Hypothesis g : forall x, (B x) -> (A x).
Hypothesis iso_AB : forall x, fonction_egalite ((f x);; (g x)) (@id (A x)). 
Hypothesis iso_BA : forall x, fonction_egalite ((g x);; (f x)) (@id (B x)). 

Definition typeExistentiel_iso_SommeASommeB(u : { x : X & A x}) : { x : X & B x}. 
case u as [x ax].
exists x.
exact (f x ax).
Defined.

Definition typeExistentiel_iso_SommeBSommeA(u : { x : X & B x}) : { x : X & A x}. 
case u as [x bx].
exists x.
exact (g x bx).
Defined.

Proposition typeExistentiel_isomorphisme_A :
  fonction_egalite
    (typeExistentiel_iso_SommeASommeB ;;
     typeExistentiel_iso_SommeBSommeA)
    (@id { x : X & A x}).
Proof.
  intros [x ax].
  cbn.
  pose (egAx := iso_AB x ax).
  unfold fonction_sequence in egAx.
  rewrite egAx.
  reflexivity.
Qed.

Proposition typeExistentiel_isomorphisme_B :
  fonction_egalite
    (typeExistentiel_iso_SommeBSommeA ;;
     typeExistentiel_iso_SommeASommeB)
    (@id { x : X & B x}).
Proof.
  intros [x bx].
  cbn.
  pose (egBx := iso_BA x bx).
  unfold fonction_sequence in egBx.
  rewrite egBx.
  reflexivity.
Qed.

End iso.

Print typeExistentiel_iso_SommeASommeB.

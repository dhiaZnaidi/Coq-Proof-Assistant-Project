Definition fonction_egalite{A B : Type}(f g : A -> B) : Prop :=
  forall x, f x = g x.

Proposition fonction_egalite_reflexivite : 
  forall (A B : Type)(f : A -> B),
    fonction_egalite f f.
Proof.
  intros.
  intro x.  
  reflexivity.
Qed.

Proposition fonction_egalite_symetrie : 
  forall (A B : Type)(f g : A -> B),
    fonction_egalite f g
    -> fonction_egalite g f.
Proof.
  intros A B f g H.
  intro x.
  symmetry.
  apply H.
Qed.

Proposition fonction_egalite_transitivite : 
  forall (A B : Type)(f g h: A -> B),
    fonction_egalite f g
    -> fonction_egalite g h
    -> fonction_egalite f h.
Proof.
  intros A B f g h egFG egGH.
  intro x.
  transitivity (g x).
  apply egFG.
  apply egGH.
Qed.

Definition fonction_sequence{A B C : Type}(f : A -> B)(g : B -> C) : A -> C.
Proof.
  exact (fun x => g (f x)).
Defined.

Notation "f ;; g" := (fonction_sequence f g) (at level 60, right associativity).

Proposition fonction_sequence_compatibiliteEgaliteFonctionnelle  :
  forall (A B C : Type)(f1 f2 : A -> B)(g1 g2 : B -> C),
    (fonction_egalite f1 f2)
    -> (fonction_egalite g1 g2)
    -> (fonction_egalite (f1 ;; g1) (f2 ;; g2)).
Proof.
  intros A B C f1 f2 g1 g2 egF egG x.
  unfold fonction_sequence.
  rewrite egF.
  rewrite egG.
  reflexivity.
Qed.

Proposition fonction_sequence_associativiteAnterieurAPosterieur :
  forall (A B C D: Type)(f : A -> B)(g : B -> C)(h : C -> D),
    (f ;; g) ;; h = f ;; (g ;; h).
Proof.
  intros A B C D f g h.
  unfold fonction_sequence.
  reflexivity.
Qed.

Proposition fonction_sequence_associativitePosterieurAAnterieur :
  forall (A B C D: Type)(f : A -> B)(g : B -> C)(h : C -> D),
    f ;; (g ;; h) = (f ;; g) ;; h. 
Proof.
  intros A B C D f g h.
  unfold fonction_sequence.
  reflexivity.
Qed.

Proposition fonction_sequence_neutraliteAnterieure :
  forall (A B : Type)(f : A -> B),
    (@id A) ;; f = f.
Proof.
  intros A B f.
  unfold fonction_sequence.
  reflexivity.
Qed.

Proposition fonction_sequence_neutralitePosterieure :
  forall (A B : Type)(f : A -> B),
    f ;; (@id B) = f.
Proof.
  intros A B f.
  unfold fonction_sequence.
  reflexivity.
Qed.


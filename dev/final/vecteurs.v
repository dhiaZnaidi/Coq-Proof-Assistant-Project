(* Version courante
- définition des vecteurs
- 'Vecteur _ n' est un foncteur qui préserve les produits.
 *)
Add LoadPath "C:\Users\21692\ParcoursRecherche\dossier_final\coq_parcours_recherche\znaidi22\dev\final" as lp.



Load Verbose produitCartesien.

Load Verbose modulo.


(* Bibliothèque standard pour les vecteurs *)
Require Import List Arith Bool Decidable PeanoNat Coq.Arith.Peano_dec.
Import ListNotations.

Require Import Vector.
Import VectorNotations.

(* TODO Une tactique apply permettant de transmettre un à un les arguments *)
(* Ltac appliquer f :=
  unshelve (eapply f).
*)

(** *Vecteur *)

(* Un type indexé décrivant les vecteurs (des listes avec leur taille) *)

Print Vector.t. (* Type correspondant dans la bibliothèque standard *)

(*

Vecteur (A : Type) : nat -> Type - une paramétrisation par un type, indexation par un nat

                           (p : nat)  A  (Vecteur A p)
----------- [vecteur_vide]  --------------------------- [vecteur_cons]
Vecteur A 0                    (Vecteur A (S p))

*)

Inductive Vecteur(A : Type) : nat -> Type :=
| vecteur_vide : Vecteur A 0
| vecteur_cons : forall p, A -> Vecteur A p -> Vecteur A (S p).

(** * Règles d'élimination ou gauches pour les vecteurs *)

(* 1. P : forall (v : Vecteur A 0), Sorte - Sorte := Prop | Type 

- Elimination de (v : Vecteur A 0) pour P

   Γ ⊢ (v : Vecteur A 0)  Γ ⊢ P vide 
   ---------------------------------
             Γ ⊢ P v

- Règle gauche pour un (Vecteur A (S n))  

       Γ ⊢ P vide
   --------------------------
   Γ, (v : Vecteur A 0) ⊢ P v

2. P : forall n (v : Vecteur A (S n)), Sorte - Sorte := Prop | Type 

- Elimination de (v : Vecteur A (S n)) pour P

   Γ ⊢ (v : Vecteur A (S n))     
     Γ ⊢ forall (m : nat)(t : A)(r : Vecteur A m), P m (cons t r) 
   --------------------------------------------------------------
                          Γ ⊢ P n v

- Règle gauche pour un (Vecteur A (S n))  

   Γ, (n : nat), (t : A), (r : Vecteur A n) ⊢ P n (cons t r) 
   ---------------------------------------------------------
         Γ, (n : nat), (v : Vecteur A (S n)) ⊢ P n v

Mais du fait de l'indexation, ces règles ne peuvent être obtenues par la tactique 'case'.
Pour les obtenir, on utilise la technique de paramétrisation du but : elle vise à remplacer
les index par des paramètres. Dans ce cas, la tactique 'case' ne perd pas d'information. *)

Check Vector.caseS.
(* Principe dans la bibliothèque standard 
caseS
     : forall P : forall n : nat, t ?A (S n) -> Type,
       (forall (h : ?A) (n : nat) (t : t ?A n), P n (h :: t)) ->
       forall (n : nat) (v : t ?A (S n)), P n v
where
?A : [ |- Type] *)

Check Vector.case0.
(* Principe dans la bibliothèque standard 
case0
     : forall P : t ?A 0 -> Type, P [] -> forall v : t ?A 0, P v
where
?A : [ |- Type] *)

(* Technique de paramétrisation du but *)

(* Cas des propositions *)

(* P1. Extension d'un prédicat sur le vecteur vide aux vecteurs non vides *)
Definition vecteur_extensionPredicatVecteurVide
           {A : Type}(P : Vecteur A 0 -> Prop):
  forall n, Vecteur A n -> Prop.
  intros n v.
  case n as [ | pn].
  - exact (P v).
  - exact True.
Defined.

(* P2.a Equivalence de l'extension - cas de la spécialisation *)
Lemma vecteur_extensionPredicatVecteurVide_specialisation :
  forall (A : Type)(P : Vecteur A 0 -> Prop),
  (forall n (v : Vecteur A n), (vecteur_extensionPredicatVecteurVide P n v))
  -> (forall (v : Vecteur A 0), P v).
  intros A P H v.
  apply (H 0 v).
Qed.

(* P2.b Equivalence de l'extension - cas de la généralisation *)
Lemma vecteur_extensionPredicatVecteurVide_generalisation :
  forall (A : Type)(P : Vecteur A 0 -> Prop),
  (forall (v : Vecteur A 0), P v)
  -> (forall n (v : Vecteur A n), (vecteur_extensionPredicatVecteurVide P n v)).
  intros A P H n v.
  case n as [ | pn].
  - cbn.
    exact (H v).
  - cbn.
    exact I.
Qed.

(* P3. Proposition à appliquer pour obtenir 
les règles d'élimination ou gauche dans le cas d'un prédicat
 appliqué à un vecteur vide. *)
Proposition vecteur_regleGaucheProp_vecteurVide :
  forall (A : Type)(P : Vecteur A 0 -> Prop),
    (P (vecteur_vide A)) -> forall v, P v.
Proof.
  intros A P H.
  apply vecteur_extensionPredicatVecteurVide_specialisation. (* paramétrisation du but *)
  intros n v.
  case v as [ | pn tv rv]. (* décomposition sans perte ni d'informations ni de typage *) 
  - cbn.
    exact H.
  - cbn.
    exact I.
Qed.

Print vecteur_regleGaucheProp_vecteurVide.

(* P1. Extension d'un prédicat sur des vecteurs non vides au vecteur vide *)
Definition vecteur_extensionPredicatVecteursNonVides
           {A : Type}(P : forall n, Vecteur A (S n) -> Prop):
  forall n, Vecteur A n -> Prop.
  intros n v.
  case n as [ | pn].
  - exact True.
  - exact (P pn v).
Defined.

(* P2.a Equivalence de l'extension - cas de la spécialisation *)
Lemma vecteur_extensionPredicatVecteursNonVides_specialisation :
  forall (A : Type)(P : forall n, Vecteur A (S n) -> Prop),
  (forall n (v : Vecteur A n), (vecteur_extensionPredicatVecteursNonVides P n v))
  -> (forall n (v : Vecteur A (S n)), P n v).
  intros A P H n v.
  apply (H (S n) v).
Qed.

(* P2.b Equivalence de l'extension - cas de la généralisation *)
Lemma vecteur_extensionPredicatVecteursNonVides_generalisation :
  forall (A : Type)(P : forall n, Vecteur A (S n) -> Prop),
  (forall n (v : Vecteur A (S n)), P n v)
  -> (forall n (v : Vecteur A n), (vecteur_extensionPredicatVecteursNonVides P n v)).
  intros A P H n v.
  case n as [ | pn].
  - cbn.
    exact I.
  - apply (H pn v).
Qed.

(* P3. Proposition à appliquer pour obtenir 
les règles d'élimination ou gauche dans le cas d'un prédicat
 appliqué à un vecteur non vide. *)
Proposition vecteur_regleGaucheProp_vecteurNonVide :
  forall (A : Type)(P : forall n, Vecteur A (S n) -> Prop),
    (forall n t r, P n (vecteur_cons A n t r))
    -> forall n v, P n v.
Proof.
  intros A P H.
  apply vecteur_extensionPredicatVecteursNonVides_specialisation. (* paramétrisation du but *)
  intros n v.
  case v as [ | pn tv rv]. (* décomposition sans perte ni d'informations ni de typage *) 
  - cbn. exact I.
  - cbn.
    exact (H pn tv rv).
Qed.

Print vecteur_regleGaucheProp_vecteurNonVide.

(* Cas des types *)

(* T1. Extension d'une famille de types paramétrée par le vecteur vide
aux vecteurs non vides *)
Definition vecteur_extensionFamilleTypesVecteurVide
           {A : Type}(R : Vecteur A 0 -> Type):
  forall n, Vecteur A n -> Type.
  intros n v.
  case n as [ | pn].
  - exact (R v).
  - exact unit.  
Defined.

(* T2.a Equivalence de l'extension - cas de la spécialisation *)
Definition vecteur_extensionFamilleTypesVecteurVide_specialisation 
           {A : Type}{R : Vecteur A 0 -> Type} :
  (forall n v, (vecteur_extensionFamilleTypesVecteurVide R n v))
  -> (forall v, R v).
  intros H v.
  apply (H 0 v).
Defined.

(* T2.b Equivalence de l'extension - cas de la généralisation *)
Definition vecteur_extensionFamilleTypesVecteurVide_generalisation 
  {A : Type}{R : Vecteur A 0 -> Type} :
  (forall v, R v)
  -> (forall n v, (vecteur_extensionFamilleTypesVecteurVide R n v)).
  intros H n v.
  case n as [ | pn].
  - cbn.
    apply (H v).
  - cbn.
    exact tt.    
Defined.

(* T3. Definiition à appliquer pour obtenir 
   les règles d'élimination ou gauche dans le cas d'une famille de types
   paramétrée par le vecteur vide. *)
Definition vecteur_regleGaucheType_vecteurVide 
           {A : Type}(R : Vecteur A 0 -> Type)
           (f : R (vecteur_vide A)) :
  forall v, R v.  
  apply (@vecteur_extensionFamilleTypesVecteurVide_specialisation A). (* paramétrisation du but *)
  intros n v.
  case v as [ | pn tv rv]. (* décomposition sans perte ni d'informations ni de typage *) 
  - cbn.
    exact f.
  - cbn.
    exact tt.
Defined.

(* T1. Extension d'une famille de types paramétrée par des vecteurs non vides
au vecteur vide *)
Definition vecteur_extensionFamilleTypesVecteursNonVides
           {A : Type}(R : forall n, Vecteur A (S n) -> Type):
  forall n, Vecteur A n -> Type.
  intros n v.
  case n as [ | pn].
  - exact unit.
  - exact (R pn v).
Defined.

(* T2.a Equivalence de l'extension - cas de la spécialisation *)
Definition vecteur_extensionFamilleTypesVecteursNonVides_specialisation 
           {A : Type}{R : forall n, Vecteur A (S n) -> Type} :
  (forall n v, (vecteur_extensionFamilleTypesVecteursNonVides R n v))
  -> (forall n v, R n v).
  intros H n v.
  apply (H (S n) v).
Defined.

(* T2.b Equivalence de l'extension - cas de la généralisation *)
Definition vecteur_extensionFamilleTypesVecteursNonVides_generalisation 
  {A : Type}{R : forall n, Vecteur A (S n) -> Type} :
  (forall n v, R n v)
  -> (forall n v, (vecteur_extensionFamilleTypesVecteursNonVides R n v)).
  intros H n v.
  case n as [ | pn].
  - cbn.
    exact tt.
  - cbn.
    apply (H pn v).
Defined.

(* T3. Definiition à appliquer pour obtenir 
   les règles d'élimination ou gauche dans le cas d'une famille de types
   paramétrée par des vecteurs non vides. *)
Definition vecteur_regleGaucheType_vecteurNonVide 
           {A : Type}(R : forall n, Vecteur A (S n) -> Type)
           (f : forall n t r, R n (vecteur_cons A n t r)) :
  forall n v, R n v.  
  apply (@vecteur_extensionFamilleTypesVecteursNonVides_specialisation A). (* paramétrisation du but *)
  intros n v.
  case v as [ | pn tv rv]. (* décomposition sans perte ni d'informations ni de typage *) 
  - cbn. exact tt.
  - cbn.
    exact (f pn tv rv).
Defined.

(** *Applications *)

Print hd. (* Première projection du vecteur donnant la tête (bibliothèque standard).
Utilisation du principe caseS.
hd = 
fun A : Type =>
@caseS A (fun (n : nat) (_ : t A (S n)) => A) (fun (h : A) (n : nat) (_ : t A n) => h)
     : forall (A : Type) (n : nat) (v : t A (S n)),
       (fun (n0 : nat) (_ : t A (S n0)) => A) n v
*)

Definition vecteur_tete{A : Type} : forall {n : nat}, Vecteur A (S n) -> A.
  apply (@vecteur_regleGaucheType_vecteurNonVide A).
  intros n t r.
  exact t.
Defined.

(* Variante utilisant la spécialisation. *)
Definition vecteur_tete_bis{A : Type} : forall {n : nat}, Vecteur A (S n) -> A.
  apply (@vecteur_extensionFamilleTypesVecteursNonVides_specialisation A).
  intros n v.
  case v as [ | pn tv rv].
  - cbn.
    Print unit. (* Inductive unit : Set :=  tt : unit. *)
    Print True.    (* Inductive True : Prop :=  I : True. *)
    exact tt.
  - cbn.
    exact tv.
Defined.

Print vecteur_tete.
Print vecteur_tete_bis.

(* Les fonctions précédentes ne sont pas présentées sous la forme habituelle,
   avec les paramètres déjà introduits. En effet, dans ce cas, la tactique
   'apply' n'arrive pas à inférer certains arguments.*)

Definition vecteur_tete_ter{A : Type}{n : nat}(v : Vecteur A (S n)) : A.
  Print vecteur_regleGaucheType_vecteurNonVide.
  Check (@vecteur_regleGaucheType_vecteurNonVide A).
  (* apply (@vecteur_regleGaucheType_vecteurNonVide A). 
     Error: Unable to find an instance for the variable n. *)
  (* Type (avec les -> transformées en forall):
    'forall
        (R : forall n : nat, Vecteur A (S n) -> Type),
        (H : forall (n : nat) (t : A) (r : Vecteur A n), R n (vecteur_cons A n t r)),
        (n : nat)
        (v : Vecteur A (S n)),
           R n v'
     Coq infère :
     - R := fun n v => A, une fonction constante égale à 'A', le but. Cette solution
       est la plus simple, mais n'est pas la plus générale puisqu'elle donne 'A'
       pour tous arguments 'n' et 'v'. Si elle ne convenait pas (par exemple
       pour une hypothèse dépendante de 'R' comme 'H'), il faudrait explicitement
       donner le prédicat comme argument.
     En revanche, à partir de 'A', Coq ne peut inférer
     ni (n : nat) ni (v : Vecteur A (S n))),
     qui doivent être fournis par l'utilisateur, tout comme 'H'.
     Bien sûr, il pourrait les deviner grâce à une tactique, mais ce n'est pas le rôle de
     la tactique 'apply' qui est seulement d'inférer les arguments déterminés
     par le but (précisément, la conséquence du séquent formant le but). *)
  (* La solution est d'utiliser une variante de la tactique 'apply'
     qui demande tous les arguments. *)
  unshelve (eapply (@vecteur_regleGaucheType_vecteurNonVide A)).
  - exact n.
  - intros m t r.
    exact t.
  - exact v.
Defined.

(* Il est possible de définir une tactique pour cette variante de la tactique 'apply'.
   Elle permet de transmettre un à un les arguments *)
Ltac appliquer f :=
  unshelve (eapply f).

Print vecteur_tete_ter.

Print tl. (*  Seconde projection du vecteur donnant le reste (bibliothèque standard).
Utilisation du principe caseS.
tl = 
fun A : Type =>
@caseS A (fun (n : nat) (_ : t A (S n)) => t A n) (fun (_ : A) (n : nat) (t : t A n) => t)
     : forall (A : Type) (n : nat) (v : t A (S n)),
       (fun (n0 : nat) (_ : t A (S n0)) => t A n0) n v
*)

Definition vecteur_reste{A : Type} : forall {n : nat}, Vecteur A (S n) -> Vecteur A n.
  apply (@vecteur_regleGaucheType_vecteurNonVide A). (* paramétrisation du but *)
  intros n t r.
  exact r.
Defined.


(* Definition vecteur_reste{A : Type} : forall {n : nat}, Vecteur A (S n) -> Vecteur A n.
  appliquer (@vecteur_specialisationExtensionType_enSuccesseur A). (* paramétrisation du but *)
  intros n v.
  case v as [ | pn tv rv].
  - cbn.
    exact tt.
  - cbn.
    exact rv.
Defined. *)

Print vecteur_reste.

Check eta. (* Correction de la décomposition (bibliothèque standard).
eta
     : forall v : VectorDef.t ?A (S ?n), v = VectorDef.hd v :: VectorDef.tl v
where
?A : [ |- Type]
?n : [ |- nat]
            *)
Print eta. (* Utilisation du principe caseS.
eta = 
fun (A : Type) (n : nat) (v : VectorDef.t A (S n)) =>
VectorDef.caseS
  (fun (n0 : nat) (v0 : VectorDef.t A (S n0)) => v0 = VectorDef.hd v0 :: VectorDef.tl v0)
  (fun (h : A) (n0 : nat) (t : VectorDef.t A n0) => eq_refl) v
     : forall (A : Type) (n : nat) (v : VectorDef.t A (S n)),
       v = VectorDef.hd v :: VectorDef.tl v
*)

Proposition vecteur_decomposition :
  forall A n (v : Vecteur A (S n)), v = vecteur_cons A n (vecteur_tete v) (vecteur_reste v).
Proof.
  intro A.
  apply (@vecteur_regleGaucheProp_vecteurNonVide A). (* paramétrisation du but *)
  intros n t r.
  cbn.
  reflexivity.
Qed.

Print vecteur_decomposition.

Print nth. (* n-ième projection en utilisant un indice.
Utilisation du principe inductif caseS.
nth = 
fun A : Type =>
fix nth_fix (m : nat) (v' : t A m) (p : Fin.t m) {struct v'} : A :=
  match p in (Fin.t m') return (t A m' -> A) with
  | @Fin.F1 n =>
      caseS (fun (n0 : nat) (_ : t A (S n0)) => A)
        (fun (h : A) (n0 : nat) (_ : t A n0) => h)
  | @Fin.FS n p' =>
      fun v : t A (S n) =>
      caseS (fun (n0 : nat) (_ : t A (S n0)) => Fin.t n0 -> A)
        (fun (_ : A) (n0 : nat) (t : t A n0) (p0 : Fin.t n0) => nth_fix n0 t p0) v p'
  end v'
     : forall (A : Type) (m : nat), t A m -> Fin.t m -> A
*)

Definition vecteur_suffixeBrut{A : Type} : forall {n h : nat}, 
    (ModuloBrut n h) ->  (Vecteur A (S n)) -> (Vecteur A (S h)).
  fix REC 3.
  intros n h ib v.
  case ib as [ | h pib].
  - exact v.
  - exact (vecteur_reste (REC _ _ pib v)).
Defined.

Definition vecteur_suffixe{A : Type}{n : nat}(m : Modulo n)
    (v : Vecteur A (S n)) : (Vecteur A (S (modulo_complementaire m))).
  case m as [h mb].
  cbn.
  exact (vecteur_suffixeBrut mb v).
Defined.

Definition vecteur_valeur{A : Type}{n : nat}(m : Modulo n)(v : Vecteur A (S n)) : A.
Proof.
  exact (vecteur_tete (vecteur_suffixe m v)).
Defined.

Definition vecteur_projection{A : Type}{n : nat}(m : nat)(v : Vecteur A (S n)) : A.
Proof.
  exact (vecteur_valeur (modulo_morphismeNat n m) v). 
Defined.

(* 'Vecteur _ n' est un foncteur. *)
(* Partie fonctionnelle du foncteur :
                       f : A -> B
   ----------------------------------------
   Vecteur f n : Vecteur A n -> Vecteur B n
Notation : app n f := Vecteur f n (app pour application, map en anglais, nom traditionnel) 
- app 0 f v := vide
- app (S n) f (t.r) := (f t).(app n f r) *)
Fixpoint vecteur_application{A B : Type}{n : nat}(f : A -> B)(v : Vecteur A n) : Vecteur B n.
Proof.
  case n as [ | pn].
  - exact (vecteur_vide B).
  - apply vecteur_cons.
    + exact (f (vecteur_tete v)).
    + exact (vecteur_application _ _ _ f (vecteur_reste v)).
Defined.

(* Comptibilité avec l'égalité fonctionnelle. *)
Proposition vecteur_application_compatibiliteEgaliteFonctionnelle :
  forall (A B : Type){n : nat}(f g: A -> B),
    (fonction_egalite f g) ->
    (@fonction_egalite (Vecteur A n) (Vecteur B n)
       (vecteur_application f) (vecteur_application g)).
Proof.
  unfold fonction_egalite.
  fix HR 7.
  intros A B n f g egFG v.
  case v as [ | pn tv rv].
  - cbn.
    reflexivity.
  - simpl vecteur_application.
    f_equal.
    apply egFG.
    apply HR.
    assumption.
Qed.
  
(* Variante due au fait que le foncteur 'Vecteur _ n' préserve les produits.
                               f : A * B -> C
   ------------------------------------------------------
   app2 n fn : Vecteur A n * Vecteur B n -> Vecteur C n
- app2 0 f v := vide
- app2 (S n) f (t1.r1, t2.r2) := (f (t1, t2)).(app2 n f (r1, r2)) *)
Fixpoint vecteur_biApplication{A B C : Type}{n : nat}(f : A * B -> C)
  (c : (Vecteur A n) * (Vecteur B n)){struct n} : Vecteur C n.
Proof.
  case n as [ | pn].
  - exact (vecteur_vide C).
  - case c as [a b].
    apply vecteur_cons.
    + exact (f (vecteur_tete a, vecteur_tete b)).
    + exact (vecteur_biApplication A B C pn f (vecteur_reste a, vecteur_reste b)).    
Defined.

(* Comptibilité avec l'égalité fonctionnelle. *)
Proposition vecteur_biApplication_compatibiliteEgaliteFonctionnelle :
  forall (A B C : Type){n : nat}(f g: A * B -> C),
    (fonction_egalite f g) ->
    (@fonction_egalite ((Vecteur A n) * (Vecteur B n)) (Vecteur C n)
       (vecteur_biApplication f) (vecteur_biApplication g)).
Proof.
  unfold fonction_egalite.
  fix HR 4.
  intros A B C n f g egFG [vA vB].
  case n as [ | pn].
  - Check vecteur_regleGaucheProp_vecteurVide.
    apply (vecteur_regleGaucheProp_vecteurVide
             A
             (fun v => (vecteur_biApplication f (v, vB) = vecteur_biApplication g (v, vB)))).
    apply (vecteur_regleGaucheProp_vecteurVide
             B
             (fun v => (vecteur_biApplication f (vecteur_vide A, v)
                     = vecteur_biApplication g (vecteur_vide A, v)))).
    cbn.
    reflexivity.
  - simpl vecteur_biApplication.
    f_equal.
    apply egFG.
    apply HR.
    assumption.
Qed.

(* Notations inspirées des listes. *)
Notation "[[ ]]" := (vecteur_vide _).
Notation "t ::: r" := (vecteur_cons _ _ t r) (at level 60, right associativity).
Notation "[[ x ]]" := (x ::: [[]]).
Notation "[[ x ; y ; .. ; z ]]" :=
  (vecteur_cons _ _ x (vecteur_cons _ _ y .. (vecteur_cons _ _ z (vecteur_vide _)) ..)).
Notation "v [@ m ]" := (@vecteur_projection _ _ m v) (at level 1, format "v [@ m ]").

Example testProjection3En2 :
  [[1 ; 4 ; 6]] [@2] = 6.
Proof.
  cbn.
  reflexivity.
Qed.

Example testProjection3En5 :
  [[1 ; 4 ; 6]] [@5] = 6.
Proof.
  cbn.
  reflexivity.
Qed.

Print id.
Print ID.

(* Vecteur : un foncteur.
   Il préserve les identités et la composition.
   Ci-dessous, dans les commentaires, l'égalité fonctionnelle est entendue
   comme l'égalité extensionnelle:
   - F égal à G G si ∀x, F x = G x. On peut avoir ¬(F = G).
 *)
(* app id = id *)
Proposition vecteur_application_preservationIdentite :
  forall A n,
    fonction_egalite
      (vecteur_application (@id A))
      (@id (Vecteur A n)).
Proof.
  unfold fonction_egalite.
  unfold id.
  fix HR 3.
  intros A n v.
  case v as [ | pn tv rv].
  - cbn.
    reflexivity.
  - simpl vecteur_application.
    f_equal.
    apply HR.
Qed.

(* app (f ; g) = (app f) ; (app g) *)
Print fonction_egalite.
Proposition vecteur_application_preservationSequence :
  forall A B C n (f : A -> B)(g : B -> C),
    @fonction_egalite (Vecteur A n) (Vecteur C n)
      (vecteur_application (f ;; g))
      ((vecteur_application f) ;; (vecteur_application g)).
Proof.
  unfold fonction_egalite.
  fix HR 7.
  intros A B C n f g v.
  case v as [ | pn tv rv].
  - cbn.
    reflexivity.
  - cbn.
    f_equal.
    apply HR.
Qed.


(* 'Vecteur _ n' : foncteur préservant le produit cartésien.
   Isomorphisme entre 'Vecteur (A * B) n' et '(Vecteur A n) * (Vecteur B n)'.
 *)

(* isomorphisme 1 : [app _ fst, app _ snd] *)
Definition vecteur_preservationProduit_coupleVecteurs{A B : Type}{n : nat} :
  (Vecteur (A * B)  n) -> (Vecteur A n) * (Vecteur B n) :=
  produitCartesien_produitFonctionnel
     (vecteur_application fst) (vecteur_application snd). 

Print id.

(* isomorphisme 2 : (app2 _ id) *)
Definition vecteur_preservationProduit_vecteurCouples{A B : Type}{n : nat} :
  ((Vecteur A n) * (Vecteur B n)) -> Vecteur (A * B)  n
  := vecteur_biApplication (@id _).


(* Vérification de l'isomorphisme
- cas 0 : ([app fst, app snd] ; (app2 id)) v = [] et v = []
- cas (S pn) :
  - ([app fst, app snd] ; (app2 id)) (t.r)
  = app2 id ([app fst, app snd] (t.r))
  = app2 id (app fst (t.r), app snd (t.r))
  = app2 id ((fst t).(app fst r), (snd t).(app snd r))      
  = (id (fst t, snd t)).(app2 id (app fst r, app snd r))
  = t.(([app fst, app snd] ; (app2 id)) r) = t.r par HR      
*)
Proposition vecteur_preservationProduit_deVecteurAVecteur :
  forall A B n,
    @fonction_egalite (Vecteur (A * B)  n) (Vecteur (A * B) n)
      (vecteur_preservationProduit_coupleVecteurs
       ;; vecteur_preservationProduit_vecteurCouples)
      id.
Proof.
  unfold fonction_egalite.
  unfold id.
  fix HR 3.
  intros A B n v.
  case n as [ | pn].
  - cbn.
    apply vecteur_regleGaucheProp_vecteurVide.
    reflexivity.
  - unfold fonction_sequence.
    unfold vecteur_preservationProduit_coupleVecteurs.
    unfold produitCartesien_produitFonctionnel.
    simpl vecteur_application. (* La tactique 'simpl f' permet de simplifier
                                  une fonction récursive, en dépliant sa
                                  définition récursive. *)
    unfold vecteur_preservationProduit_vecteurCouples.
    simpl vecteur_biApplication.
    rewrite (vecteur_decomposition _ _ v) at 5.
    case (vecteur_tete v) as [tv1 tv2].
    f_equal.
    apply HR.
Qed.

(* Vérification de l'isomorphisme
- cas 0 : ((app2 id) ; [app fst, app snd]) (c1, c2) = ([], [])
          et c1 = [], c2 = []
- cas (S pn) :
  - ((app2 id) ; [app fst, app snd]) (t1.r1, t2.r2)
  = [app fst, app snd] (id (t1, t2)).(app2 id (r1, r2))
  = (app fst (id (t1, t2)).(app2 id (r1, r2)),
     app snd (id (t1, t2)).(app2 id (r1, r2)))
  = (t1.(app fst (app2 id (r1, r2)),
     t2.(app snd (app2 id (r1, r2)))
  = (t1.r1, t2.r2) par HR
*)
Proposition vecteur_preservationProduit_deCoupleACouple :
  forall A B n,
    @fonction_egalite ((Vecteur A n) * (Vecteur B n)) ((Vecteur A n) * (Vecteur B n))
      (vecteur_preservationProduit_vecteurCouples
       ;; (vecteur_preservationProduit_coupleVecteurs))
      id.
Proof.
  unfold fonction_egalite.
  unfold id.
  fix HR 3.
  intros A B n c.
  unfold fonction_sequence.
  case c as [c1 c2].
  case n as [ | pn].
  - compute. (* 'cbn' ne déplie pas les fonctions sauf pour faire des calculs.
                Ici, préférer la tactique 'compute' qui calcule la forme normale.
                Attention : ne l'utiliser que lorsque la forme normale est simple,
                sinon on obtient un terme illisible ! Règle pratique : l'utiliser
                si on sait calculer de tête la forme normale.*)
    f_equal.
    + apply vecteur_regleGaucheProp_vecteurVide. 
      reflexivity.
    + apply vecteur_regleGaucheProp_vecteurVide.
      reflexivity.
  - unfold vecteur_preservationProduit_vecteurCouples.
    simpl vecteur_biApplication.
    unfold vecteur_preservationProduit_coupleVecteurs.
    unfold produitCartesien_produitFonctionnel.
    simpl vecteur_application.
    rewrite (vecteur_decomposition _ _ c1) at 4.
    rewrite (vecteur_decomposition _ _ c2) at 4.
    pose (hr := HR _ _ pn (vecteur_reste c1, vecteur_reste c2)).
    injection hr as eg1 eg2.
    f_equal.
    f_equal.
    exact eg1.
    f_equal.
    exact eg2.
Qed.

(*                     f : A -> B     g : A -> C
   --------------------------------------------------------------
     app [f, g] : Vecteur A n -> Vecteur (B * C) n
   ~ [app f, app g] : Vecteur A n -> (Vecteur B n) * (Vecteur C n)
   // ~ : égalité à isomorphisme près
- cas 0 : [] ~ ([], []) 
- cas (S pn) :
  - app [f, g] t.r = (f t, g t).(app [f, g] r)
  - [app f, app g] t.r = (app f t.r, app g t.r)
                       = ((f t).(app f r), (g t).(app g r))
  - égalité à isomorphisme près par HR  
 *)
Proposition vecteur_application_distributionSurProduitFonctionnel :
  forall (A B C : Type)(f : A -> B)(g : A -> C),
  forall n,
    @fonction_egalite (Vecteur A n) ((Vecteur B n) * (Vecteur C n))
      ((vecteur_application (produitCartesien_produitFonctionnel f g)) ;;  
       vecteur_preservationProduit_coupleVecteurs) 
      (produitCartesien_produitFonctionnel
         (vecteur_application f) (vecteur_application g)).
Proof.
  fix HR 6.
  intros A B C f g n a.
  case n as [ | pn].
  - reflexivity.
  - unfold fonction_sequence.
    simpl vecteur_application at 1.
    unfold produitCartesien_produitFonctionnel at 1.
    unfold vecteur_preservationProduit_coupleVecteurs.
    unfold produitCartesien_produitFonctionnel at 1 3.
    simpl vecteur_application at 1 3.
    simpl vecteur_application at 5 6.
    pose (hr := HR A B C f g pn (vecteur_reste a)).
    injection hr as eg1 eg2.
    f_equal.
    f_equal.
    exact eg1.
    f_equal.
    exact eg2.
Qed.

(*                  f : A * B -> C
   ---------------------------------------------------
     app2 f : Vecteur n A * Vecteur B n -> Vecteur C n
   ~  app f : Vecteur n (A * B) -> Vecteur C n 
   // ~ : égalité à isomorphisme près
- cas 0 : app2 f c = [], app f ([], []) = []
- cas (S pn)
  - app2 f (t1.r1, t2.r2) = (f (t1, t2)).(app2 f (r1, r2))
  - app f (iso (t1.r1, t2.r2)) = app f (t1, t2).(iso (r1, r2))
                                = (f (t1, t2)).(app f (iso (r1, r2))
  - égalité par HR 
*) 
Proposition vecteur_biApplication_equivalenceApplication :
  forall (A B C : Type)(f : A * B -> C),
  forall n,
    @fonction_egalite ((Vecteur A n) * (Vecteur B n)) (Vecteur C n)
      (vecteur_biApplication f) 
      (vecteur_preservationProduit_vecteurCouples ;;
       vecteur_application f).
Proof.
  fix HR 5.
  intros A B C f n c.
  case c as [c1 c2].
  case n as [ | pn].
  - cbn.
    reflexivity.
  - unfold fonction_sequence.
    unfold vecteur_preservationProduit_vecteurCouples.
    simpl vecteur_biApplication.
    simpl vecteur_application.
    f_equal.
    apply HR.
Qed.

Proposition vecteur_biApplicationProjection1 :
  forall A B n,
    @fonction_egalite ((Vecteur A n) * (Vecteur B n)) (Vecteur A n)
      (vecteur_biApplication fst) fst.
Proof.
  fix HR 3.
  intros A B n [vA vB].
  case n as [ | pn].
  - cbn.
    apply vecteur_regleGaucheProp_vecteurVide.
    reflexivity.
  - simpl vecteur_biApplication.
    cbn.
    rewrite (vecteur_decomposition _ _ vA) at 3.
    f_equal.
    apply HR.
Qed.

Proposition vecteur_biApplicationProjection2 :
  forall A B n,
    @fonction_egalite ((Vecteur A n) * (Vecteur B n)) (Vecteur B n)
      (vecteur_biApplication snd) snd.
Proof.
  fix HR 3.
  intros A B n [vA vB].
  case n as [ | pn].
  - cbn.
    apply vecteur_regleGaucheProp_vecteurVide.
    reflexivity.
  - simpl vecteur_biApplication.
    cbn.
    rewrite (vecteur_decomposition _ _ vB) at 3.
    f_equal.
    apply HR.
Qed.


Add LoadPath "C:\Users\21692\ParcoursRecherche\dossier_final\coq_parcours_recherche\znaidi22\dev\final" as lp.

Load Verbose fonctions.


(* Produit cartésien : un bifoncteur (un foncteur sur la catégorie produit).
   (f : A1 -> A2) (g : B1 -> B2)
   -----------------------------
   app f g : A1 * B1 -> A2 * B2   // Notation : f * g := app f g
 *)
Definition produitCartesien_application{A1 A2 B1 B2 : Type}(f : A1 -> A2)(g : B1 -> B2) :
  (A1 * B1) -> (A2 * B2).
Proof.
  intro x.
  case x as [a b].
  exact (f a, g b).
Defined.

(* Il préserve les identités et la composition. *)
(* id * id = id *)
Locate "*".

Proposition produitCartesien_application_preservationIdentite :
  forall A B, fonction_egalite (produitCartesien_application (@id A) (@id B)) (@id (A * B)%type).
  intros A B x.
  case x as [a b].
  cbn.
  reflexivity.
Qed.

(* (f1 ; f2) * (g1 ; g2) = (f1 * g1) ; (f2 ; g2) *)
Proposition produitCartesien_application_preservationSequence :
  forall A1 A2 A3 B1 B2 B3 (f1 : A1 -> A2)(f2 : A2 -> A3)(g1 : B1 -> B2)(g2 : B2 -> B3),
    fonction_egalite
      (produitCartesien_application (f1 ;; f2) (g1 ;; g2))
      ((produitCartesien_application f1 g1) ;; (produitCartesien_application f2 g2)).
Proof.
  intros A1 A2 A3 B1 B2 B3 f1 f2 g1 g2 x.
  case x as [a b].
  cbn.
  reflexivity.
Qed.

Proposition produitCartesien_application_compatibiliteEgaliteFonctionnelle :
  forall (A1 A2 B1 B2 : Type)(fa fb : A1 -> A2)(ga gb : B1 -> B2),
    (fonction_egalite fa fb)
    -> (fonction_egalite ga gb)
    -> (fonction_egalite
         (produitCartesien_application fa ga)
         (produitCartesien_application fb gb)).
Proof.
  intros A1 A2 B1 B2 fa fb ga gb egF egG x.
  unfold produitCartesien_application.
  case x as [a b].
  rewrite egF.
  rewrite egG.
  reflexivity.
Qed.
  
Print fst.

(* 'fst' : définition directe de la première projection. *)
Definition produitCartesien_projection1{A B : Type}(x : A * B) : A.
Proof.
  case x as [a b].
  exact a.
Defined.

Print produitCartesien_projection1.

Print snd.

(* 'snd' : définition directe de la seconde projection. *)
Definition produitCartesien_projection2{A B : Type}(x : A * B) : B.
Proof.
  case x as [a b].
  exact b.
Defined.

(* Diagramme commutatif pour le produit cartésien.
   ---------- A ----------
   |          |          |
   f        [f, g]       g  (avec uncité de la flèche [f, g])
   |          |          |
   ∨          ∨          ∨
   B <-fst- B * C -snd-> C
*) 
Definition produitCartesien_produitFonctionnel{A B1 B2 : Type}(f : A -> B1)(g : A -> B2) :
  A -> (B1 * B2).
Proof.
  intro x.
  exact (f x, g x).
Defined.

Proposition produitCartesien_produitFonctionnel_compatibiliteEgaliteFonctionnelle :
  forall (A B1 B2 : Type)(fi fj: A -> B1)(gi gj: A -> B2),
      (fonction_egalite fi fj)
    -> (fonction_egalite gi gj)
    -> (fonction_egalite
         (produitCartesien_produitFonctionnel fi gi)
         (produitCartesien_produitFonctionnel fj gj)).
Proof.
  intros A B1 B2 fi fj gi gj egF egG x.
  unfold produitCartesien_produitFonctionnel.
  rewrite egF.
  rewrite egG.
  reflexivity.
Qed.  
  
(* (f : A -> B1)(g : A -> B2)
   --------------------------
   [f, g] ; fst = f : A -> B1  *)
Proposition produitCartesien_proprieteUniverselle1 :
  forall (A B1 B2 : Type)(f : A -> B1)(g : A -> B2),
    fonction_egalite ((produitCartesien_produitFonctionnel f g) ;; fst) f. 
Proof.
  intros A B1 B2 f g x.
  cbn.
  reflexivity.
Qed.

(* (f : A -> B1)(g : A -> B2)
   --------------------------
   [f, g] ; snd = g : A -> B2 *)
Proposition produitCartesien_proprieteUniverselle2 :
  forall (A B1 B2 : Type)(f : A -> B1)(g : A -> B2),
    fonction_egalite ((produitCartesien_produitFonctionnel f g) ;; snd) g . 
Proof.
  intros A B1 B2 f g x.
  cbn.
  reflexivity.
Qed.

(* [f, g] est unique. *)
Proposition produitCartesien_proprieteUniverselle_unicite :
  forall (A B1 B2 : Type)(f : A -> B1)(g : A -> B2)(h : A -> B1 * B2),
    (fonction_egalite (h ;; fst) f)
    -> (fonction_egalite (h ;; snd) g)
    -> (fonction_egalite h (produitCartesien_produitFonctionnel f g)). 
Proof.
  intros A B1 B2 f g h p1 p2 x.
  unfold produitCartesien_produitFonctionnel.
  case (p1 x).
  case (p2 x).
  unfold fonction_sequence.
  case (h x) as [h1 h2].
  cbn.
  reflexivity.
Qed.

(* Propriété :
  (f : A -> B)    (g : B -> C1)    (h : B -> C2)
  ----------------------------------------------
  f ; [g, h] = [(f ; g), (f ; h)] : A -> C1 * C2  *)
Proposition fonction_distributionSequenceSurProduit :
  forall (A B C1 C2 : Type)(f : A -> B)(g : B -> C1)(h : B -> C2),
    fonction_egalite
      (f ;; (produitCartesien_produitFonctionnel g h))
      (produitCartesien_produitFonctionnel (f ;; g) (f;; h)).
Proof.
  intros A B C1 C2 f g h a.
  reflexivity.
Qed.


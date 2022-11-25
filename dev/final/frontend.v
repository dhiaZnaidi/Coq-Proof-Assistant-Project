Add LoadPath "C:\Users\21692\ParcoursRecherche\dossier_final\coq_parcours_recherche\znaidi22\dev\final" as lp.

Require Import  String.

Load Verbose vecteurs.

Load Verbose alphabets.



(* Bibliothèque standard pour les chaînes de caractères : voir la section
"Strings Implementation of string as list of ascii characters" de
https://coq.inria.fr/distrib/current/stdlib/
- Ascii.ascii : type inductif avec un constructeur acceptant huit booléeens
 *)

(* Front end : un plongement, un isomorphisme
 - plongement : string -> {n : nat & Vecteur Ascii n}
                          // (type existentiel ou union dépendante)
 - isomorphisme : Vecteur Ascii n -> Vecteur (Modulo MA) n
   // MA : max des codes ascii (255)
- D'après 'typeExistentiel.v', on déduit un isomorphisme entre
  {n : nat & Vecteur Ascii n} et {n : nat & Vecteur (Modulo MA) n}.
*)
Print existT.

Fixpoint ascii_traduction_String_VecteurAscii(s : string) : Vecteur Ascii.ascii (String.length s).
Proof.
  case s as [ | t r].
  - exact (vecteur_vide _) . 
  - apply vecteur_cons.
    -- exact t.
    -- exact (ascii_traduction_String_VecteurAscii r).
Defined.

Definition ascii_traduction_String_UnionVecteursAscii(s : string)
  : {n : nat & Vecteur Ascii.ascii n}.
Proof.
  exists (String.length s).
  exact (ascii_traduction_String_VecteurAscii s).
Defined.

Fixpoint ascii_traduction_VecteurAscii_String{n : nat}(v : Vecteur Ascii.ascii n)
  : string.
Proof.
  case v as [ | pn tv rv].
  - exact String.EmptyString.
  - apply String.
    -- exact tv.
    -- exact (ascii_traduction_VecteurAscii_String _ rv).
Defined.

Definition ascii_traduction_UnionVecteursAscii_String
  (ve : {n : nat & Vecteur Ascii.ascii n}) : string.
Proof.
  case ve as [n v].
  exact (ascii_traduction_VecteurAscii_String v).
Defined.

Proposition ascii_plongement_String_UnionVecteursAscii :
  @fonction_egalite string string 
    (ascii_traduction_String_UnionVecteursAscii
     ;; ascii_traduction_UnionVecteursAscii_String)
    id.
Proof.
  unfold fonction_egalite.
  fix HR 1.
  intro s.
  case s as [ | t r].
  - cbn.
    reflexivity.
  - unfold fonction_sequence.
    cbn.
    unfold id.
    f_equal.
    apply HR.
Qed.

(* Il n'y a pas d'isomorphisme mais seulement un plongement.
- (v : Vecteur A n) --> (s : string) --> (v' : Vecteur A (length s))
                                     --> (v : Vecteur A n) ??

Même si (length s = n), on ne peut convertir v' en (Vecteur A n).
En effet, la règle de subsomption suivante n'est pas vailde en Coq.

x : A   A = B
-------------
   x : B

Si elle l'était, la relation de typage ne serait plus décidable. *)

Definition ascii_traduction_VecteurAscii_VecteurModulo{n : nat} :
  (Vecteur Ascii.ascii n) -> (Vecteur (Modulo MAX_ASCII) n) :=
    vecteur_application (Ascii.nat_of_ascii ;; (modulo_morphismeNat MAX_ASCII)).

Definition ascii_traduction_VecteurModulo_VecteurAscii{n : nat} :
  (Vecteur (Modulo MAX_ASCII) n) -> (Vecteur Ascii.ascii n) :=
  vecteur_application ( modulo_valeur ;; Ascii.ascii_of_nat).

Proposition ascii_isomorphisme_VecteurModulo_VecteurAscii :
  forall (n : nat),
    @fonction_egalite (Vecteur (Modulo MAX_ASCII) n) (Vecteur (Modulo MAX_ASCII) n) 
      (ascii_traduction_VecteurModulo_VecteurAscii
       ;; ascii_traduction_VecteurAscii_VecteurModulo)
      id.
Proof.
  unfold ascii_traduction_VecteurAscii_VecteurModulo.
  unfold ascii_traduction_VecteurModulo_VecteurAscii.
  intro n.
  Check vecteur_application_preservationSequence.
  eapply fonction_egalite_transitivite.
  apply fonction_egalite_symetrie.
  apply vecteur_application_preservationSequence.
  apply fonction_egalite_transitivite with (vecteur_application id).
  apply vecteur_application_compatibiliteEgaliteFonctionnelle.
  intro x.
  unfold fonction_sequence.
  rewrite (Ascii.nat_ascii_embedding (modulo_valeur x)
             (modulo_valeur_majoration _ x)).
  apply modulo_morphismeNat_inversibiliteAnterieure.
  apply vecteur_application_preservationIdentite.
Qed.

  (* Theorem ascii_nat_embedding :
  forall a : ascii, ascii_of_nat (nat_of_ascii a) = a.

Theorem nat_ascii_embedding :
  forall n : nat, n < 256 -> nat_of_ascii (ascii_of_nat n) = n.

Theorem nat_ascii_bounded :
  forall a : ascii, nat_of_ascii a < 256.

Proposition divEuclidienne_caracterisationReste :
  forall d, (0 < d) ->
       forall n q r, (n = q * d + r) -> (r < d)
                -> (reste n d = r).
   *)
  
Proposition ascii_isomorphisme_VecteurAscii_VecteurModulo :
  forall (n : nat),
    @fonction_egalite (Vecteur Ascii.ascii n) (Vecteur Ascii.ascii n) 
      (ascii_traduction_VecteurAscii_VecteurModulo
       ;; ascii_traduction_VecteurModulo_VecteurAscii)
      id.
Proof.
  unfold ascii_traduction_VecteurAscii_VecteurModulo.
  unfold ascii_traduction_VecteurModulo_VecteurAscii.
  intro n.
  Check vecteur_application_preservationSequence.
  eapply fonction_egalite_transitivite.
  apply fonction_egalite_symetrie.
  apply vecteur_application_preservationSequence.
  apply fonction_egalite_transitivite with (vecteur_application id).
  apply vecteur_application_compatibiliteEgaliteFonctionnelle.
  intro x.
  unfold fonction_sequence.
  rewrite modulo_morphismeNat_valeur.
  assert(reste (Ascii.nat_of_ascii x) (S MAX_ASCII) = Ascii.nat_of_ascii x) as egR.
  {
    apply divEuclidienne_caracterisationReste with 0.
    Search(0 < S _).
    apply PeanoNat.Nat.lt_0_succ.
    reflexivity.
    apply Ascii.nat_ascii_bounded.
  }
  rewrite egR.
  apply Ascii.ascii_nat_embedding.
  apply vecteur_application_preservationIdentite.
Qed.


Add LoadPath "C:\Users\21692\ParcoursRecherche\dossier_final\coq_parcours_recherche\znaidi22\dev\final" as lp.

Require Import  String.

Load Verbose vecteurs.

Load Verbose alphabets.

Definition masquage{d : nat}(c : (Modulo d) * (Modulo d)) : Modulo d.
Proof.
  exact (modulo_somme (fst c) (snd c)).
Defined.

Definition chiffrement{d n : nat} :
  (Vecteur (Modulo d) n) * (Vecteur (Modulo d) n) -> (Vecteur (Modulo d) n)
  := vecteur_biApplication masquage.

Definition demasquage{d : nat}(c : (Modulo d) * (Modulo d)) : Modulo d.
Proof.
  exact (modulo_somme (fst c) (modulo_opposeSomme (snd c))).
Defined.

Definition dechiffrement{d n : nat} :
  (Vecteur (Modulo d) n) * (Vecteur (Modulo d) n) -> (Vecteur (Modulo d) n)
  := vecteur_biApplication demasquage.

(* Lemme : le masquage suivi du démasquage produit la première projection (soit le
nombre modulo en entrée).  *)
Theorem masquage_correction :
  forall d,
    @fonction_egalite
      ((Modulo d) * (Modulo d)) (Modulo d)
      (produitCartesien_produitFonctionnel masquage snd ;; demasquage)
      fst.
Proof.
  intros d [m k].
  unfold fonction_sequence.
  unfold masquage.
  unfold demasquage.
  cbn.
  rewrite modulo_somme_associativite_gaucheADroite.
  rewrite modulo_opposeSomme_correction.
  rewrite modulo_somme_neutraliteDroite.
  reflexivity.
Qed.

(* Thèorème fondamental : la correction du chiffrement.
Le chiffrement suivi du déchiffrement produit la première projection
(soit le message en entrée).
Démonstration longue utilisant des propriétés abstraites élémentaires.
Une automatisation de la preuve en utilisant le langage de tactiques serait
bienvenu. L'associativité pose cependant problème puisqu'elle impose de recombiner
la composition fonctionnelle de manière à faire apparaître le terme à traiter.
En Mathématiques, ce raisonnement est oublié, étant évident.*) 
Theorem chiffrement_masquage_correction :
  forall (d n : nat),
    @fonction_egalite
      ((Vecteur (Modulo d) n) * (Vecteur (Modulo d) n))
      (Vecteur (Modulo d) n)
      ((produitCartesien_produitFonctionnel chiffrement snd)
       ;; dechiffrement)
      fst. 
Proof.  
  intros d n.
  apply fonction_egalite_transitivite with
    ((produitCartesien_produitFonctionnel chiffrement (vecteur_biApplication snd))
     ;; dechiffrement).
  {
    apply fonction_sequence_compatibiliteEgaliteFonctionnelle.
    apply produitCartesien_produitFonctionnel_compatibiliteEgaliteFonctionnelle.
    apply fonction_egalite_reflexivite.
    apply fonction_egalite_symetrie.
    apply vecteur_biApplicationProjection2.
    apply fonction_egalite_reflexivite.
  }
  unfold chiffrement.
  apply fonction_egalite_transitivite with
    ((produitCartesien_produitFonctionnel
        (vecteur_preservationProduit_vecteurCouples ;;
         vecteur_application masquage)
        (vecteur_preservationProduit_vecteurCouples ;;
         vecteur_application snd))
     ;; dechiffrement).
  {
    apply fonction_sequence_compatibiliteEgaliteFonctionnelle.
    apply produitCartesien_produitFonctionnel_compatibiliteEgaliteFonctionnelle.
    apply vecteur_biApplication_equivalenceApplication.
    apply vecteur_biApplication_equivalenceApplication.
    apply fonction_egalite_reflexivite.
  }
  apply fonction_egalite_transitivite with
    ((vecteur_preservationProduit_vecteurCouples
     ;;
     (produitCartesien_produitFonctionnel
        (vecteur_application masquage)
        (vecteur_application snd)))
     ;;
     dechiffrement).
  {
    apply fonction_sequence_compatibiliteEgaliteFonctionnelle.
    apply fonction_egalite_symetrie.
    apply fonction_distributionSequenceSurProduit.
    apply fonction_egalite_reflexivite.
  }
  unfold dechiffrement.
  (* Plutôt que récrire le terme intermédiaire en entier, on
     peut le décrire partiellement en utilisant '_'.
   Utiliser alors la tactique 'eapply' (existential apply). *)
  eapply fonction_egalite_transitivite with
    (_ ;; (vecteur_preservationProduit_vecteurCouples ;;
           vecteur_application demasquage)).
  {
    apply fonction_sequence_compatibiliteEgaliteFonctionnelle.
    apply fonction_egalite_reflexivite.
    apply vecteur_biApplication_equivalenceApplication.
  }
  eapply fonction_egalite_transitivite with
    (( _ ;;
       ((vecteur_application (produitCartesien_produitFonctionnel masquage snd)) ;;  
       vecteur_preservationProduit_coupleVecteurs)
     ) ;; _ ;; _ ).
  {
    apply fonction_sequence_compatibiliteEgaliteFonctionnelle.
    apply fonction_sequence_compatibiliteEgaliteFonctionnelle.
    apply fonction_egalite_reflexivite.
    apply fonction_egalite_symetrie.
    apply vecteur_application_distributionSurProduitFonctionnel.
    apply fonction_egalite_reflexivite.
  }
  eapply fonction_egalite_transitivite with
    ((_ ;; _ ) ;; _).
  {
    rewrite fonction_sequence_associativitePosterieurAAnterieur.
    apply fonction_sequence_compatibiliteEgaliteFonctionnelle;
      apply fonction_egalite_reflexivite.
  }
  eapply fonction_egalite_transitivite with
    ((((_ ;; _) ;; _) ;; _) ;; _).
  {
    apply fonction_sequence_compatibiliteEgaliteFonctionnelle.
    apply fonction_sequence_compatibiliteEgaliteFonctionnelle.
    rewrite fonction_sequence_associativitePosterieurAAnterieur.
    apply fonction_egalite_reflexivite.
    apply fonction_egalite_reflexivite.
    apply fonction_egalite_reflexivite.
  }
  eapply fonction_egalite_transitivite with
    ((_ ;; (_ ;; _)) ;; _).
  {
    apply fonction_sequence_compatibiliteEgaliteFonctionnelle.
    rewrite fonction_sequence_associativiteAnterieurAPosterieur.
    apply fonction_egalite_reflexivite.
    apply fonction_egalite_reflexivite.
  }
  eapply fonction_egalite_transitivite with
    ((_ ;; id) ;; _).
  {
    apply fonction_sequence_compatibiliteEgaliteFonctionnelle.
    apply fonction_sequence_compatibiliteEgaliteFonctionnelle.
    apply fonction_egalite_reflexivite.
    apply vecteur_preservationProduit_deVecteurAVecteur.
    apply fonction_egalite_reflexivite.
  }
  eapply fonction_egalite_transitivite with
    (_ ;; _).
  {
    apply fonction_sequence_compatibiliteEgaliteFonctionnelle.
    rewrite fonction_sequence_neutralitePosterieure.
    apply fonction_egalite_reflexivite.
    apply fonction_egalite_reflexivite.
  }
  rewrite fonction_sequence_associativiteAnterieurAPosterieur.
  eapply fonction_egalite_transitivite with
    (_ ;; _).
  {
    apply fonction_sequence_compatibiliteEgaliteFonctionnelle.
    apply fonction_egalite_reflexivite.
    apply fonction_egalite_symetrie.
    apply vecteur_application_preservationSequence.
  }
  eapply fonction_egalite_transitivite with
    (_ ;; (vecteur_application fst)).
  {
    apply fonction_sequence_compatibiliteEgaliteFonctionnelle.
    apply fonction_egalite_reflexivite.
    apply vecteur_application_compatibiliteEgaliteFonctionnelle.
    apply masquage_correction.
  }
  eapply fonction_egalite_transitivite with
    (vecteur_biApplication fst).
  apply fonction_egalite_symetrie.
  apply vecteur_biApplication_equivalenceApplication.
  apply vecteur_biApplicationProjection1.
Qed.



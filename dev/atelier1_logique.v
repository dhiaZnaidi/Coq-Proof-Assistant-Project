(* Paramètres : des types et des valeurs *)
Parameter A B C R : Type.

Print All. (* Affichage de tout l'environnement. *)

(*
- Fonction de signature `(x : A) : B` 
- Séquent A ⊢ B 
*)
Definition de_A_seDeduit_B(x : A) : B.
Admitted.

Print de_A_seDeduit_B.

(*
- Fonction de signature `(x : A) : C`  
- Séquent A ⊢ C 
*)
Definition de_A_seDeduit_C(x : A) : C.
Admitted.

(*
- Fonction de signature `(x : B) : C`   
- Séquent B ⊢ C 
*)
Definition de_B_seDeduit_C(x : B) : C.
Admitted.

(* Localiser une notation, *)
Locate "+".
Locate "*".
(* puis récupérer une définition. *)
Print sum.
Print prod.

(* Règle droite pour ∧
    A ⊢ B    A ⊢ C
    -------------- [∧ D]
      A ⊢ B ∧ C
*)
Definition regleDroite_deA_seDeduit_BetC(x : A) : B * C.
    apply pair. (* Ou : split. *)
  - exact (de_A_seDeduit_B x).
  - exact (de_A_seDeduit_C x).
  (* ou : exact ((de_A_seDeduit_B x), (de_A_seDeduit_C x)). *)
Defined.

Print All.

Print sum.

(* Règle droite pour ∨ - choix à gauche
    A ⊢ B 
    --------- [∨ D g]
    A ⊢ B ∨ C
*)
Definition regleDroiteChoixGauche_deA_seDeduit_BouC(x : A) : B + C.
    left. (* Ou : apply inl. *)
    exact (de_A_seDeduit_B x).
    (* Ou : exact (inl (de_A_seDeduit_B x)). *)
Defined.

(* Règle droite pour ∨ - choix à droite
    A ⊢ C 
    --------- [∨ D d]
    A ⊢ B ∨ C
*)
Definition regleDroiteChoixDroite_deA_seDeduit_BouC(x : A) : B + C.
    right. (* Ou : apply inr. *)
    exact (de_A_seDeduit_C x).
    (* exact (inr (de_A_seDeduit_C x)).*)
Defined.

(* Exercice *)

(* Définir la fonction la plus simple possible, de paramètre (x : A), 
   sans utiliser de définitions pré-existantes. *)

Definition identite(x : A) : A.
exact x.
Defined.

Print identite.

(* Définir une fonction de `(A + B)` vers `C`, 
   en utilisant les fonctions de `A` vers `C` et de `B` vers `C` déjà définies.*)

Definition regleGauche_de_AouB_seDeduit_C(x : A + B) : C.
    (* Pour déterminer si x est dans A ou dans B, 
    on peut utiliser la tactique `case`. Si on programmait,
    on écrirait : 
    si x est dans A, 
    - alors..., 
    - sinon (x est dans B) ...
    *)
    case x as [xA | xB]. (* xA et xB sont les noms choisis pour x 
                            lorsque x est dans A et dans B respectivement. *)
Admitted. (* à remplacer par `Defined.` une fois la définition terminée.*)

(* 
- Fonction de signature `(x : A, y : B) : C` 
  (ce qui correspond au type `(A -> B -> C)`). 
Remarque : la notation pour plusieurs paramètres 
diffère en Coq; on concatène les déclarations, entourées de parenthèses. 
- Séquent : A, B ⊢ C  
*)   
Definition de_A_et_B_seDeduit_C(x : A)(y : B) : C.
Admitted.

(* En utilisant la fonction précédente, définir une fonction de `A * B` vers `C`. *)
Definition regleGauche_de_AetB_seDeduit_C(x : A * B) : C.
    (* Pour décomposer `x` en un couple `(xA, xB)`, on peut utiliser la tactique `case`.
    *)
    case x as [xA xB].
Admitted.

Print regleGauche_de_AetB_seDeduit_C.

(*
- Fonction de signature `(x : A, y : B) : R` 
- Séquent A, B ⊢ R 
*)
Definition de_A_et_B_seDeduit_R(x : A)(y : B) : R.
Admitted.

(*
- Fonction de signature `(x : A, y : C) : R` 
- Séquent A, C ⊢ R 
*)
Definition de_A_et_C_seDeduit_R(x : A)(y : C) : R.
Admitted.

(*
- Fonction de signature `(x : A) : B + C` 
- Séquent A ⊢ B ∨ C 
*)
Definition de_A_seDeduit_BouC(x : A) : B + C.
Admitted.

(* A l'aide des trois fonctions précédentes, 
   définir une fonction de `A`  dans `R`. 
   Indication : on pourra faire un `case` 
   sur le résultat de l'application d'une des fonctions précédentes à 
   un argument judicieusement choisi, se trouvant dans l'environnement. *)

Definition regleElimination_de_A_seDeduit_BouC(x : A) : R.
Admitted.

(*
- Fonction de signature `(x : A) : B * C` 
- Séquent A ⊢ B ∧ C 
*)
Definition de_A_seDeduit_BetC(x : A) : B * C.
Admitted.

(* Définir une fonction de `A` vers `B` en utilisant la fonction précédente 
   de `A` vers `B * C`. Indication : on pourra utiliser la tactique `case`.*)
Definition regleEliminitationChoixGauche_de_A_seDeduit_BetC(x : A) : B.
Admitted.

(* Définir une valeur de type `(A -> B)` à partir 
    d'une fonction déjà définie. Indication :  
    utiliser la tactique `exact`. *)
Definition regleDroite_seDeduit_AimpliqueB : A -> B.
Admitted.

(* Alternative. Définir une valeur de type `(A -> B)` à partir 
   d'une fonction déjà définie. Indication :     
   pour introduire l'hypothèse `(x : A)`, utiliser d'abord la tactique 
   `intro x`. Utiliser la tactique `exact` ensuite. *)
Definition regleDroite_seDeduit_AimpliqueB_bis : A -> B.
Admitted.

(* Définir une fonction de signature `(x : A) : C` en utilisant 
une fonction de `B` vers `C` déjà définie et une fonction de signature `(x : A) : B`. *)   
Definition regleElimination_BimpliqueC(x : A) : C.
Admitted.

(* Définir une fonction de signature `(x : A, f : B -> C) : R`, 
   en utilisant les fonctions précédemment définies de signature
   `(x : A) : B` et  `(x : A, y : C) : R`. *)
Definition regleGauche_de_AimpliqueB_seDeduit_C(x : A)(f : B -> C) : R.
Admitted.

(* Récapituler toutes les règles logiques vues dans cet exercice, 
   en formalisant les règles utilisées 
   pour définir les fonctions et les valeurs à partir des signatures.*)

(* 
 *******************************
 Les quantificateurs
 *******************************
 *)

(* Une famille de types, indexée par I (pour individus). *)
Parameter I : Type.
Parameter T : I -> Type. 

Definition de_unI_et_A_seDeduit_TduI(x : I)(y : A) : (T x).
Admitted.  

Check de_unI_et_A_seDeduit_TduI.

(* Définir une fonction de signature `(y : A) : (∀(x : I), (T x))`,
   en utilisant la fonction précédemment définie. *)

(* Explications concernant le type `(∀(x : I), (T x))`. La quantification universelle 
   généralise le type fonctionnel `I -> T`, en rajoutant une dépendance relativement 
   au type `I` : c'est le type des familles de valeurs indexées par `I`, la valeur 
   associée à `(x : I)` appartenant à `(T x)`. 
   C'est une généralisation de la généricité : la dépendance est possible relativement 
   à un type (si `I` vaut `Type`) mais aussi à une valeur (si `I` différent de `Type` est 
   un type particulier de données).   
 *)

Definition regleDroite_de_A_seDeduit_pourToutI_TdeI(y : A):  forall x : I, T x.
Admitted.

(*
(x : I), A ⊢ (T x)
------------------ [∀ D] (x variable fraîche)
A ⊢ ∀(x : I), T x
*)

(* Fraîcheur ? *)
Definition regleDroite_de_A_seDeduit_pourToutI_TdeI_fraicheur(x : A) :  forall x : I, T x.
Admitted.

Definition unI : I.
Admitted.

Definition de_A_et_TdunI_seDeduit_C(a : A)(t : (T unI)): C.
Admitted.

(* Définir une fonction de signature `(x : A, q : (∀(y : I), (T y)) : C`,
   en utilisant la fonction précédemment définie. 
*)
Definition regleGauche_de_A_et_pourToutI_TdeI_seDeduit_C(x :A)(q : forall y : I, T y): C.
Admitted.

(*
⊢ i : I    A, (T i) ⊢ C
------------------------- [∀ G]
 A, (∀(x : I), T x) ⊢ C 
*)

Definition de_A_seDeduit_pourToutI_TdeI(x : A) : forall (y : I), T y.
Admitted.  

(* Définir une fonction de signature `(x : A) : (T unI)` 
   en utilisant la fonction précédente. *)   
Definition regleElimination_pourToutI_TdeI(x : A) : (T unI).
Admitted.

(*
A ⊢ (∀(x : I), T x)   ⊢ i : I
----------------------------- [∀ Elim]
          A ⊢ (T i)
*)

Definition de_A_seDeduit_TdunI(x : A) : (T unI).
Admitted.

(* Définir une fonction de signature `(x : A) : (∃(x : I), (T x))`,
   en utilisant la fonction précédemment définie. 
   Indication : pour fournir le témoin de type `I`, utiliser la tactique
   `exists`.
*)

(* Explications concernant le type `(∃(x : I), (T x))`. La quantification existentielle 
   est duale de la quantification universelle. Elle permet d'abstraire (et de cacher) le 
   témoin `i` vérifiant `(T i)`. 
   C'est une généralisation du joker en Java : `(T ?)` correspond à `(∃(X : Type), (T X))`.
   Il est possible d'abstraire un type mais aussi une valeur.

   En Coq, il existe deux notations pour la quantification existentielle : 
   - l'une pour les propositions (de sorte `Prop`) : `exists (x:I), ...`,
   - l'autre pour les types de données (de sorte `Type`) : `{ x : I & ... }`. 
 *)

Print existT.
Locate "{ _ & _ }".

Definition regleDroite_de_A_seDeduit_existeI_TdeI(x : A): {y : I & (T y)}.
Admitted.

(*
⊢ i : I     A ⊢ (T i)
--------------------- [∃ D] 
 A ⊢ ∃(y : I), (T y)
*)

Definition de_A_et_dunIquelconque_telQue_TdeI_seDeduit_C(x : A)(y : I)(h : (T y)) : C.
Admitted.

(* Définir une fonction de signature `(x : A, q : (∀(y : I), (T y)) : C`,
   en utilisant la fonction précédente. 
*)
Definition regleGauche_de_A_et_existeI_TdeI_seDeduit_C(x :A)(q : { y : I & (T y)}) : C.
Admitted.

(*
 A, (x : I), (T x) ⊢ C
---------------------- [∃ G] (x variable fraîche)
A, (∃(x : I), T x) ⊢ C 
*)

(* Fraîcheur ? *)
Definition regleGauche_de_A_et_existeI_TdeI_seDeduit_C_fraicheur(x :A)(q : { x : I & (T x)}) : C.
Admitted.


Definition de_A_seDeduit_existeI_TdeI(x : A) : { y : I & (T y)}.
Admitted.  

(* Définir une fonction de signature `(x : A) : C` 
   en utilisant la fonction précédente et une autre fonction admise. *)   
Definition regleElimination_existeI_TdeI(x : A) : C.
Admitted.

(*
A ⊢ (∃(x : I), T x)   A, (x : I), (T x) ⊢ C
------------------------------------------- [∃ Elim]
                  A ⊢ C
*)











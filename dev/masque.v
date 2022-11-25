Require Import List Arith Bool Decidable PeanoNat Coq.Arith.Peano_dec.
Import ListNotations.
Require Extraction.

(** * A. Reflet bool/Prop *)

Print eqb.

Locate "=?".

Search((_ =? _ = false) -> ~(_ = _)).
Print beq_nat_false.

Search((_ =? _ = true) -> (_ = _)).
Print beq_nat_true.

(** * B. Relations d'ordre *)

(** * B.1 Supérieur ou égal dans Type *)

(*
n      m = n
^       /
|      /
|     x 
|    /x
|   / x   m >= n
|  /  x
| /   
|-----------------------> m
                          m >= S n 
------ [diagonale]        -------- [descenteVerticale]
m >= m                    m >= n

 *)
(* Sorte Type car utilisé dans des calculs. *)
(* Paramétrisation par 'm : nat', indexation par un 'nat'. *)
Inductive SuperieurOuEgal(m : nat) : nat -> Prop :=
| diagonale : SuperieurOuEgal m m
| descenteVerticale : forall n, SuperieurOuEgal m (S n)  -> SuperieurOuEgal m n.

Proposition superieurOuEgal_Scroissante :
  forall m n, SuperieurOuEgal m n -> SuperieurOuEgal (S m) (S n).
Proof.
Admitted.

Print le.
(*
Inductive le (n : nat) : nat -> Prop :=
    le_n : n <= n | le_S : forall m : nat, n <= m -> n <= S m.
n
^        m = n
| m <= n /
|   x   /
|   x  /
|   x / 
|   x/
|   / 
|  /  
| /   
|-----------------------> m


                          m <= n 
------ [diagonale]        -------- [montéeVerticale]
m <= m                    m <= S n

*)

Definition superieurOuEgal_adequation : forall m n, (SuperieurOuEgal m n) -> (n <= m).
Proof.
  fix REC 3.
Admitted.
  
Definition superieurOuEgal_completude : forall m n, m <= n -> (SuperieurOuEgal n m).
Proof.
  fix REC 3.
Admitted.

(** * B.2 Inférieur strict *)
Print lt.
(*
S n <= m
--------
  n <  m


lt = fun n m : nat => S n <= m
     : nat -> nat -> Prop
*)

Lemma lt_inferieurStrict :
  forall m n, m < n -> (m <= n) /\ (m <> n).
Proof.
Admitted.

Lemma inferieurStrict_lt :
  forall m n, ((m <= n) /\ (m <> n)) -> (m < n).
Proof.
Admitted.

(** * Division euclidienne *)

Fixpoint divisionEuclidienne(n d : nat) : nat * nat.
Proof.
  case n as [ | pn].
Admitted.

Print divisionEuclidienne.

Example divisionEuclidienne_13_5 : divisionEuclidienne 13 5 = (2, 3).
Admitted.

Example divisionEuclidienne_14_5 : divisionEuclidienne 14 5 = (2, 4).
Admitted.

Example divisionEuclidienne_15_5 : divisionEuclidienne 15 5 = (3, 0).
Admitted.

Example divisionEuclidienne_13_0 : divisionEuclidienne 13 0 = (0, 13).
Admitted.

Definition quotient(n d : nat) : nat.
  case (divisionEuclidienne n d) as [q _].
  exact q.
Defined.

Print quotient.

Definition reste(n d : nat) : nat.
Admitted.

Print reste.

Proposition divEuclidienne_decomposition :
  forall n d, n = (quotient n d) * d + (reste n d).
Proof.
  (* unfold quotient, reste.*)
  fix HR 1.
  (* Indication : utiiser ring.*)
Admitted.

Proposition divEuclidienne_resteDivParZero : forall n, (reste n 0 = n).
Proof.
Admitted.

Proposition divEuclidienne_quotientDivParZero : forall n, (quotient n 0 = 0).
Proof.
Admitted.

Proposition divEuclidienne_majorationReste :
  forall n d, (0 < d) -> (reste n d) < d.
Proof.
Admitted.

Proposition divEuclidienne_caracterisation :
  forall d, (0 < d) ->
       forall n q r, (n = q * d + r) -> (r < d)
                -> ((quotient n d = q) /\ (reste n d = r)).
Proof.
  (* compliqué ! *)
Admitted.

Proposition divEuclidienne_caracterisationReste :
  forall d, (0 < d) ->
       forall n q r, (n = q * d + r) -> (r < d)
                -> (reste n d = r).
Proof.
Admitted.

Proposition reste_idempotence :
  forall d n, reste (reste n d) d = reste n d.
Proof.
Admitted.
 
Proposition reste_preMorphismeAdditif :
  forall d m n, reste (m + n) d = reste ((reste m d) + (reste n d)) d.
Proof.
Admitted.

Definition modulo_egalite(d m n: nat) : Prop.
  exact (reste m d = reste n d).
Defined.  

Proposition modulo_egalite_reflexivite : forall d n, modulo_egalite d n n.
Proof.
Admitted.

Proposition modulo_egalite_symetrie : forall d m n, modulo_egalite d m n -> modulo_egalite d n m.
Proof.
Admitted.

Proposition modulo_egalite_transitivite :
  forall d n1 n2 m, modulo_egalite d n1 m -> modulo_egalite d m n2 -> modulo_egalite d n1 n2.
Proof.
Admitted.

Proposition modulo_egalite_compatibiliteAddition :
  forall d, forall m1 n1 m2 n2,
    modulo_egalite d m1 m2
    -> modulo_egalite d n1 n2
    -> modulo_egalite d (m1 + n1) (m2 + n2).
Proof.
Admitted.

(** * Vers une représentation canonique ? question difficile.
 
Modulo d (pour représenter les classes de la relation modulo (S d)) : 
{(h : d, v : 0), ..., (h : 0, v : d)} formé de couples (h, v), avec  
v la valeur et h le nombre de valeurs au-dessus. Invariant : h + v = d.

Construction en deux temps.

1. ModuloBrut(d : nat) : nat -> Type - paramétrisation par 'd' et indexation par 'h'

                          (ModuloBrut d (S h))
-------------- [zeroMod]  -------------------- [succMod]
ModuloBrut d d              (ModuloBrut d h)

Interprétation :
- ModuloBrut d h est le type singleton {h, v}, avec h + v = d.

2. Modulo (d : nat) : somme des singletons (ModuloBrut d h)

Modulo(d : nat) : Type.

(h : nat) (ModuloBrut d h)
-------------------------- [modulo]
       Modulo d

- Interprétation : Modulo d = {(d, 0), ..., (0, d)} - Nat modulo (S d)
*)

Inductive ModuloBrut(d : nat) : nat -> Type :=
| mb_zero : ModuloBrut d d
| mb_succ : forall h, ModuloBrut d (S h) -> ModuloBrut d h.

Fixpoint moduloBrut_valeur(d h : nat)(mb : ModuloBrut d h) : nat.
Proof.
  case mb as [ | h pmb].
  - exact 0.
  - exact (S (moduloBrut_valeur _ _ pmb)).
Defined.

Proposition moduloBrut_majoration :
  forall (d h : nat)(mb : ModuloBrut d h), SuperieurOuEgal d h.
Proof.
  fix HR 3.
Admitted.

Proposition moduloBrut_invariant :
  forall d h, forall (mb : ModuloBrut d h),
    (moduloBrut_valeur d h mb) + h = d. 
Proof.
Admitted.

Inductive Modulo(d : nat) : Type :=
| modulo : forall h, ModuloBrut d h -> Modulo d.

Definition modulo_valeur(d : nat)(m : Modulo d) : nat.
Proof.
  case m as [h mb].
  exact (moduloBrut_valeur _ _ mb).
Defined.

Definition modulo_hauteur(d : nat)(m : Modulo d) : nat.
Proof.
  case m as [h mb].
  exact h.
Defined.

Proposition modulo_invariant :
  forall d, forall (m : Modulo d),
    (modulo_valeur d m) + (modulo_hauteur d m) = d. 
Proof.
Admitted.

(* Modulo d : algèbre sur la signature (0, S). *)

Definition modulo_zero(d : nat) : Modulo d := modulo _ _ (mb_zero d).

Definition modulo_succ(d : nat)(m : Modulo d) : Modulo d.
Proof.
  case m as [h mb].
  case h as [ | ph].
  + exact (modulo_zero d).
  + exact (modulo _ _ (mb_succ _ _ mb)).
Defined.

Fixpoint modulo_morphismeNat(d n : nat) : Modulo d.
Proof.
  case n as [ | pn].
  - exact (modulo_zero d).
  - exact (modulo_succ d (modulo_morphismeNat d pn)).
Defined.

Lemma modulo_morphismeNat_valeur :
  forall d, forall n,
    modulo_valeur d (modulo_morphismeNat d n) = reste n (S d).
Proof.
  fix HR 2.
  (* compliqué ! *)
Admitted.

(* compatibilité *)
Lemma modulo_morphismeNat_calculParReste :
  forall d, forall n,
    modulo_morphismeNat d n = modulo_morphismeNat d (reste n (S d)).
Proof.
  fix HR 2.
  (* compliqué ! *)
Admitted.

Proposition modulo_egalite_compatibiliteMorphismeNat :
  forall d, forall m n,
    modulo_egalite (S d) m n
    -> modulo_morphismeNat d m = modulo_morphismeNat d n.
Proof.
  intros d m n equiv_m_n.
  unfold modulo_egalite.
  rewrite (modulo_morphismeNat_calculParReste d m).
  rewrite (modulo_morphismeNat_calculParReste d n).
  rewrite equiv_m_n.
  reflexivity.
Qed.  

Definition zeroMod3 := modulo_morphismeNat 2 3.
Print zeroMod3.
Compute zeroMod3.

Definition unMod3 := modulo_morphismeNat 2 1.
Print unMod3.
Compute unMod3.

Definition deuxMod3 := modulo_morphismeNat 2 2.
Print deuxMod3.
Compute deuxMod3.

Example identite_valeur_2_mod3 :
  modulo_morphismeNat 2 (modulo_valeur _ deuxMod3) = deuxMod3.
Admitted.

(* L'inversibilité antérieure entraîne la surjectivité. *)
Proposition moduloBrut_morphismeNat_inversibiliteAnterieure :
  forall d h (mb : ModuloBrut d h),
    modulo_morphismeNat d (moduloBrut_valeur _ _ mb) = modulo _ _ mb.
Proof.
Admitted.

Proposition modulo_morphismeNat_inversibiliteAnterieure :
  forall d (m : Modulo d),
    modulo_morphismeNat d (modulo_valeur _ m) = m.
Proof.
Admitted.

(* L'inversibilité postérieure entraîne l'injectivité (modulo (S d)). *)

Proposition modulo_morphismeNat_inversibilitePosterieure :
  forall d n,
    modulo_egalite (S d) (modulo_valeur d (modulo_morphismeNat d n))
                                  n.
Proof.
Admitted.

(* Monoïde additif *)

Fixpoint sommeBrute(d h : nat)(mb : ModuloBrut d h)(n : Modulo d){struct mb} : Modulo d.
Proof.
Admitted.

Definition somme{d : nat}(m n : Modulo d) : Modulo d.
Proof.
Admitted.

Example somme_12_13_mod25 :
  somme (modulo_morphismeNat 24 12) (modulo_morphismeNat 24 13) = modulo_morphismeNat 24 0.
Admitted.

(*
Fixpoint sommeBrute(d h k : nat)(m : ModuloBrut h d)(n : ModuloBrut k d){struct m} : Modulo d.
Proof.
  case m as [ | d m].
  - exact (modulo (S h) k n).
  - case (sommeBrute _ _ _ m n) as [hr mbr].
    case hr as [ | phr].
    * exact (modulo _ d (zeroMod _)).
    * exact (modulo _ phr (succMod _ _ mbr)).
Defined.

Definition somme{d : nat}(m n : Modulo d) : Modulo d.
Proof.
  case m as [h mb].
  case n as [k nb].
  exact (sommeBrute _ _ _ mb nb).
Defined.  *)


Example somme_1_2_mod3 : somme unMod3 deuxMod3 = zeroMod3.
Admitted.

Example somme_2_2_mod3 : somme deuxMod3 deuxMod3 = unMod3.
Admitted.

(* Complément : sur l'unicité de la représentation. *)

(* Conversion : foncteur catégorique - voir egalite_preuves_singletonSiDecidable. *)
Definition conversion(d h1 h2 : nat)(eg : h1 = h2) : ModuloBrut d h1 -> ModuloBrut d h2. 
  case eg.
  exact (fun mb => mb).
Defined.

(* Utilisation de l'unicité des preuves d'égalité sur nat :
- apply UIP_nat. *)
Lemma moduloBrut_singleton_casZeroModuloConversion :
  forall d h (mb : ModuloBrut d h)(eg : h = d), 
    conversion d h d eg mb = mb_zero d.   
Proof.
Admitted.

Lemma moduloBrut_singleton_casZero :  forall d (mb : ModuloBrut d d),
    mb = mb_zero d.
Proof.
Admitted.

(* Les types 'ModuloBrut'sont des types singletons. *)
Proposition moduloBrut_typesSingletons :
  forall (d h : nat)(mb1 mb2 : ModuloBrut d h),
    mb1 = mb2.
Proof.
  fix HR 3.
Admitted.  

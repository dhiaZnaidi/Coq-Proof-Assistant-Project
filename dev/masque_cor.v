Require Import List Arith Bool Decidable PeanoNat Coq.Arith.Peano_dec.
Import ListNotations.
Require Extraction.

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


(* Croissance de S : ∀ m n, m >= n -> (S m) >= (S n).

Idée
n      m = n
^       /
|      /
|     x HR
|    /x/?  
|   / x/   
|  /  x    m >= n
| /   
|-----------------------> m

Induction sur (m >= n).
- cas (m >= m). Par [diagonale], (S m) >= (S m)
- cas (m >= n), déduit de (m >= (S n)). HR donne (S m) >= (S (S n)),
  puis [descenteVerticale] donne ((S m) >= (S n)). *)
Proposition superieurOuEgal_Scroissante :
  forall m n, SuperieurOuEgal m n -> SuperieurOuEgal (S m) (S n).
Proof.
  fix HR 3.
  intros m n sup_m_n.
  case sup_m_n as [ | n sup_m_Sn].
  - apply diagonale.
  - apply descenteVerticale.
    apply HR.
    assumption.
Qed.

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

(* Adéquation : ∀ m n, m >= n -> n <= m. (<= := le)

Idée
n      m = n
^       /
|      /
|     x 
|    /x  
|   /xx    HR          (S n) <= m   
|  /xxx?   m >= n       n    <= m ?
| /   
|-----------------------> m

Induction sur (m >= n).
- cas (m >= m). Par [diagonale], m <= m.
- cas (m >= n), déduit de (m >= (S n)). HR donne ((S n) <= m),
  puis par transitivité (n <= m), car (n <= (S n)). *)
Definition superieurOuEgal_adequation : forall m n, (SuperieurOuEgal m n) -> (n <= m).
Proof.
  fix REC 3.
  intros m n sup_m_n.
  case sup_m_n as [ | n sup].
  - apply le_n.
  - transitivity (S n).
    Search(_ <= S _).
    apply Nat.le_succ_diag_r.
    apply REC.
    assumption.
Qed.

(* Complétude : ∀ m n, n <= m -> m >= n. (<= := le)

Idée
n
^        m = n
| m <= n /
|   xxxx/  ?   n >= (S m) -> n >= m
|   xxx/   HR  n - 1 >= m 
|   x / 
|   x/
|   / 
|  /  
| /   
|-----------------------> m

Induction sur (n <= m).
- cas (m <= m). Par [diagonale], m <= m.
- cas (m <= (S n)), déduit de (m <= n). HR donne (n >= m), 
  puis par croissance ((S n) >= (S m)), enfin par [descenteVerticale],
  ((S n) >= m). *)
Definition superieurOuEgal_completude : forall m n, m <= n -> (SuperieurOuEgal n m).
Proof.
  fix REC 3.
  intros m n inf_m_n.
  case inf_m_n as [ | pn inf].
  - apply (diagonale m).
  - apply descenteVerticale.
    apply superieurOuEgal_Scroissante.
    apply (REC m pn inf).
Qed.

(** * B.2 Inférieur strict *)
Print lt.
(*
S n <= m
--------
  n <  m


lt = fun n m : nat => S n <= m
     : nat -> nat -> Prop
*)

(*
 - m < n -> m <= S m <= n
 - m < n -> m = n -> (S n) <= n, absurde  
*)
Lemma lt_inferieurStrict :
  forall m n, m < n -> (m <= n) /\ (m <> n).
Proof.
  unfold lt.
  intros m n lt_m_n.
  split.
  - transitivity (S m).
    apply Nat.le_succ_diag_r.
    assumption.
  - intro eg_m_n.
    rewrite eg_m_n in lt_m_n.
    Search(S _ <= _).
    apply (Nat.nle_succ_diag_l n).
    assumption.
Qed.

(* ∀ m n, ((m <= n) ∧ (m ≠ n)) -> (m < n).

Décomposition par cas / (m <= n)
- cas (m <= m). Absurde.
- cas (m <= (S n)), déduit de (m <= n). Par croissance de S, (S m) <= (S n),
  soit m < (S n).
*)
Lemma inferieurStrict_lt :
  forall m n, ((m <= n) /\ (m <> n)) -> (m < n).
Proof.
  unfold lt.
  intros m n h.
  case h as [le_m_n diff_m_n].
  case le_m_n as [ | pn le_m_pn].
  - exfalso.
    apply diff_m_n.
    reflexivity.
  - Search(S _ <= S _).
    apply le_n_S.
    assumption.
Qed.


(** * Division euclidienne *)

(* division euclidienne
                  
 -------------    
 0 = 0 * d + 0

 n = q * d + r     d = r + 1    n = q * d + r     d ≠ r + 1
 ---------------------------    ---------------------------
    S n = (q + 1) * d + 0          S n = q * d + (r + 1)            
*)
Fixpoint divisionEuclidienne(n d : nat) : nat * nat.
Proof.
  case n as [ | pn].
  - exact (0, 0).
  - case (divisionEuclidienne pn d) as [q r].
    case (d =? (S r)) as [ | ].
    -- exact (S q, 0).
    -- exact (q, S r).
Defined.

Print divisionEuclidienne.

Example divisionEuclidienne_13_5 : divisionEuclidienne 13 5 = (2, 3).
cbn.
reflexivity.
Qed.

Example divisionEuclidienne_14_5 : divisionEuclidienne 14 5 = (2, 4).
cbn.
reflexivity.
Qed.

Example divisionEuclidienne_15_5 : divisionEuclidienne 15 5 = (3, 0).
cbn.
reflexivity.
Qed.

Example divisionEuclidienne_13_0 : divisionEuclidienne 13 0 = (0, 13).
cbn.
reflexivity.
Qed.


Definition quotient(n d : nat) : nat.
  case (divisionEuclidienne n d) as [q _].
  exact q.
Defined.

Print quotient.

Definition reste(n d : nat) : nat.
  case (divisionEuclidienne n d) as [_ r].
  exact r.
Defined.

Print reste.

Proposition divEuclidienne_decomposition :
  forall n d, n = (quotient n d) * d + (reste n d).
Proof.
  unfold quotient, reste.
  fix HR 1.
  intros n d.
  case n as [ | pn].
  - cbn.
    reflexivity.
  - cbn.
    case (divisionEuclidienne pn d) as [q r] eqn:divE.
    case (d =? (S r)) as [ | ] eqn:egReste.
    -- rewrite (HR pn d).
       rewrite divE.
       rewrite (beq_nat_true _ _ egReste).
       ring.
    -- rewrite (HR pn d).
       rewrite divE.
       ring.
Qed.
(* Un cas particulier : d = 0. Reste. *)
Proposition divEuclidienne_resteDivParZero : forall n, (reste n 0 = n).
Proof.
  intro n.
  rewrite (divEuclidienne_decomposition n 0) at 2.
  ring.
Qed.
(* Un cas particulier : d = 0. Quotient. *)
Proposition divEuclidienne_quotientDivParZero : forall n, (quotient n 0 = 0).
Proof.
  unfold quotient.
  fix HR 1.
  intro n.
  case n as [ | pn].
  - cbn.
    reflexivity.
  - cbn.
    case (divisionEuclidienne pn 0) as [q r] eqn:eqDiv.
    pose (hr := HR pn).
    rewrite eqDiv in hr.
    assumption.
Qed.

(* Cas général : d > 0.
   Majoration du reste : strictement par d.
                  
----------------------    
0 = 0 * d + 0 => 0 < d

n = q * d + r     d = r + 1    
------------------------------    
S n = (q + 1) * d + 0 => 0 < d 

n = q * d + r     d ≠ r + 1  HR : r < d
----------------------------------------------------------- 
S n = q * d + (r + 1) => r + 1 <= d, d ≠ r + 1 => r + 1 < d           
*)
Proposition divEuclidienne_majorationReste :
  forall n d, (0 < d) -> (reste n d) < d.
Proof.
  unfold reste.
  fix HR 1.
  intros n d dPos.
  case n as [ | pn].
  - cbn.
    assumption.
  - cbn.
    case (divisionEuclidienne pn d) as [q r] eqn:eqDiv.
    case (d =? S r) as [ | ] eqn:eqD.
    -- assumption.
    -- apply inferieurStrict_lt.
       split.
       --- pose (hr := HR pn d).
           rewrite eqDiv in hr.
           apply hr.
           assumption.
       --- intro abs.
           Search((_ =? _ = false) -> ~(_ = _)).
           apply (beq_nat_false _ _ eqD).
           symmetry.
           assumption.
Qed.

(* Cas général : d > 0. Unicité de la décomposition euclidienne.

(q1 * d + r1) = (q2 * d + r2)  (r1 < d)  (r2 < d)
------------------------------------------------
      (q1 = q2) ∧ (r1 = r2)

Induction sur q1, décomposition de q2
- q1 = 0, q2 = 0 : trivial
- q1 = 0, q2 = S p2 : r1 = d + ..., r1 < d, absurde.
- q1 = S p1, q2 = 0 : absurde aussi.
- q1 = S p1, q2 = S p2 : HR / p1, p2 r1, r2 *)
Lemma decompositionEuclidienne_unicite :
  forall d, (0 < d) -> forall q1 r1 q2 r2,
      ((q1 * d + r1) = (q2 * d + r2))
      -> (r1 < d) -> (r2 < d)
      -> (q1 = q2) /\ (r1 = r2). 
Proof.
  intros d dPos.
  fix HR 1.
  intros q1 r1 q2 r2 egDec maj1 maj2.
  case q1 as [ | p1].
  - case q2 as [ | p2].
    + split.
      * reflexivity.
      * cbn in egDec.
        assumption.
    + exfalso.
      cbn in egDec.
      Search(_ <= _ + _). (* Nat.le_add_r *)
      Search(_ <= _ -> _ <= _ -> _ = _). (* Nat.le_antisymm *)
      assert (d <= r1) as oppMaj1.
      {
        rewrite egDec.
        Search(_ + (_ + _)).
        rewrite plus_assoc_reverse.
        apply Nat.le_add_r.
      }
      Search (S _ <= _).
      apply (Nat.nle_succ_diag_l r1).
      transitivity d; assumption.
  - case q2 as [ | p2].
    + exfalso.
      cbn in egDec.
      assert (d <= r2) as oppMaj2.
      {
        rewrite <- egDec.
        Search(_ + (_ + _)).
        rewrite plus_assoc_reverse.
        apply Nat.le_add_r.
      }
      apply (Nat.nle_succ_diag_l r2).
      transitivity d; assumption.      
    + cbn in egDec.
      assert(p1 * d + r1 = p2 * d + r2) as egDec'.
      {
        Search(_ + _ = _ + _).
        rewrite plus_assoc_reverse in egDec.
        rewrite plus_assoc_reverse in egDec.
        apply (plus_reg_l _ _ d) in egDec.
        assumption.
      }
      pose (hr := HR p1 r1 p2 r2 egDec' maj1 maj2).
      case hr as [egQ egR].
      split.
      * rewrite egQ.
        reflexivity.
      * assumption.
Qed.

(* Cas général : d > 0. Caractérisation du quotient et du reste
   par décomposition euclidienne. *)
Proposition divEuclidienne_caracterisation :
  forall d, (0 < d) ->
       forall n q r, (n = q * d + r) -> (r < d)
                -> ((quotient n d = q) /\ (reste n d = r)).
Proof.
  intros d dPos n q r egN majR.
  rewrite (divEuclidienne_decomposition n d) in egN.
  apply decompositionEuclidienne_unicite with d.
  - assumption.
  - assumption.
  - apply divEuclidienne_majorationReste.
    assumption.
  - assumption.
Qed.


Proposition divEuclidienne_caracterisationReste :
  forall d, (0 < d) ->
       forall n q r, (n = q * d + r) -> (r < d)
                -> (reste n d = r).
Proof.
  intros d dPos n q r eqN majR.
  case (divEuclidienne_caracterisation d dPos n q r eqN majR) as [_ eqR].
  assumption.
Qed.


(* Premières applications de la caractérisation par décomposition du reste :
   le caractère cyclique et l'idempotence. *)
Proposition reste_cycle :
  forall d, reste d d = 0.
Proof.
  intro d.
  case d as [ | pd].
  - reflexivity.
  - apply divEuclidienne_caracterisationReste with 1.
    -- Search(0 < S _).
       apply Nat.lt_0_succ.
    -- ring.
    -- apply Nat.lt_0_succ.
Qed.
 

Proposition reste_idempotence :
  forall d n, reste (reste n d) d = reste n d.
Proof.
  intros d n.
  case d as [ | pd].
  - rewrite divEuclidienne_resteDivParZero.
    reflexivity.
  - apply divEuclidienne_caracterisationReste with 0.
    -- Search(0 < S _).
       apply Nat.lt_0_succ.
    -- reflexivity.
    -- apply divEuclidienne_majorationReste.
       apply Nat.lt_0_succ.
Qed.

(* Une seconde application de la caractérisation par décomposition :
   le calcul du reste d'une somme. *)
Proposition reste_preMorphismeAdditif :
  forall d m n, reste (m + n) d = reste ((reste m d) + (reste n d)) d.
Proof.
  intros d m n.
  case d as [ | pd].
  - (* cas 'd = 0' *)
    repeat (rewrite divEuclidienne_resteDivParZero).
    reflexivity.
  - (* cas 'd = S pd' *)
    pose (qm := quotient m (S pd)).
    pose (qn := quotient n (S pd)).
    pose (rm := reste m (S pd)).
    pose (rn := reste n (S pd)).
    pose (q_rmrn := quotient (rm + rn) (S pd)).
    pose (r_rmrn := reste (rm + rn) (S pd)).
    (* m + n = (qm + qn + q_rmrn) * d + r_rmrn *)
    fold rm.
    fold rn.
    fold r_rmrn.
    apply divEuclidienne_caracterisationReste with (qm + qn + q_rmrn).
    -- Search(0 < S _).
       apply Nat.lt_0_succ.
    -- rewrite (divEuclidienne_decomposition m (S pd)).
       rewrite (divEuclidienne_decomposition n (S pd)).
       fold qm qn rm rn.    
       transitivity (qm * S pd + qn * S pd + (rm + rn)).
       ring.
       rewrite (divEuclidienne_decomposition (rm + rn) (S pd)).
       fold q_rmrn r_rmrn.    
       ring.
    -- apply divEuclidienne_majorationReste.
       Search(0 < S _).
       apply Nat.lt_0_succ.
Qed.

(* Définition de l'équivalence modulo d. *)
Definition modulo_egalite(d m n: nat) : Prop.
  exact (reste m d = reste n d).
Defined.  

Proposition modulo_egalite_reflexivite : forall d n, modulo_egalite d n n.
Proof.
  intros d n.
  unfold modulo_egalite.
  reflexivity.
Qed.

Proposition modulo_egalite_symetrie : forall d m n, modulo_egalite d m n -> modulo_egalite d n m.
Proof.
  intros d m n.
  unfold modulo_egalite.
  intro h.
  symmetry.
  assumption.
Qed.

Proposition modulo_egalite_transitivite :
  forall d n1 n2 m, modulo_egalite d n1 m -> modulo_egalite d m n2 -> modulo_egalite d n1 n2.
Proof.
  unfold modulo_egalite.
  intros d n1 n2 m eg1 eg2.
  transitivity (reste m d); assumption.
Qed.
(* Compatibilité avec l'addition de l'équivalence modulo. *)
Proposition modulo_egalite_compatibiliteAddition :
  forall d, forall m1 n1 m2 n2,
    modulo_egalite d m1 m2
    -> modulo_egalite d n1 n2
    -> modulo_egalite d (m1 + n1) (m2 + n2).
Proof.
  intros d m1 n1 m2 n2 egM egN.
  unfold modulo_egalite.
  rewrite (reste_preMorphismeAdditif d m1 n1).
  rewrite (reste_preMorphismeAdditif d m2 n2).
  rewrite egM.
  rewrite egN.
  reflexivity.
Qed.  

Print Nat.sub.

(* Définition d'un opposé modulo. *)
Definition modulo_oppose(n d : nat) : nat.
  exact (reste (Nat.sub d (reste n d)) d).
Defined.

(* Correction de l'opposé : (n modulo d) + (opposé modulo d de n) = 0 modulo d.
- (n%d + (d - n%d)%d)%d = 0 ?
- (n%d + (d - n%d)%d)%d
  = ((n%d)%d + (d - n%d)%d)%d  idempotence
  = (n%d + (d - n%d))%d        pré-morphisme additif
  = d%d                        (0 < d) -> (n%d < d)              
  = 0
*)
Proposition modulo_oppose_correction :
  forall n d, (0 < d) -> modulo_egalite d ((reste n d) + (modulo_oppose n d)) 0.
Proof.
  intros n d dPos.
  unfold modulo_egalite.
  unfold modulo_oppose.
  rewrite <- (reste_idempotence d n) at 1.
  rewrite <- (reste_preMorphismeAdditif d).
  Search(_ + (_ - _)). (* le_plus_minus_r *)
  assert(reste n d <= d) as majR.
  {
    Search(_ < _ -> _ <= _).
    apply Nat.lt_le_incl.
    apply divEuclidienne_majorationReste.
    assumption.
  }
  erewrite (le_plus_minus_r _ _ majR).
  apply  divEuclidienne_caracterisationReste with (S 0).
  assumption.
  cbn.
  ring.
  cbn.
  assumption.
Qed.

(** * Vers une représentation canonique ?

Avertissement : ci-dessous '(S d)' correspond à 'd' utilisé au dessus.
On exclut ainsi le cas particulier de la relation modulo zéro.

Il est possible de représenter le quotient de nat par l'égalité modulo
(S d) par restriction de nat : on considère l'ensemble '{v : nat & v
<= d}' ou encore '{v : nat & ∃h, v + h = d}'.  Un inconvénient de
cette définition est de recourir à une proposition, autrement dit une
partie non calculatoire.

Il est cependant possible de transformer cette définition en utilisant
une double définition inductive :
- la première vise à décrire les couples '(h, v)' tels que 'v + h = d',
- la seconde vise à décrire leur réunion.

Cette approche présente des difficultés : certaines démonstrations sont difficiles
pour des questions techniques liées aux définitions inductives.

En résumé : 'Modulo d' (pour représenter les classes de la relation modulo '(S d)') :
'{(d, 0), ..., (0, d)}' formé de couples '(h, v)',
avec 'v' la valeur et 'h' le complémentaire. Invariant : 'h + v = d'.

Construction en deux temps.

1. 'ModuloBrut(d : nat) : nat -> Type' - paramétrisation par 'd' et
indexation par 'h'

                                (ModuloBrut d (S h))
---------------- [mb_zero]      -------------------- [mb_succ]
(ModuloBrut d d)                   (ModuloBrut d h)

Interprétation :
- 'ModuloBrut d h' est le type singleton '{(h, v)}', avec 'h + v = d',
la valeur 'v' étant donnée par '(mb_succ^v mb_zero)'.
- La structure des termes est identique à celle des preuves de 'd >= h' (cf. supra).

2. 'Modulo (d : nat)' : somme des singletons '(ModuloBrut d h)'

Modulo(d : nat) : Type.

(h : nat) (ModuloBrut d h)
-------------------------- [modulo]
       Modulo d

Interprétation :
- 'Modulo d = {(d, 0), ..., (0, d)}' - 'nat' modulo '(S d)'
*)

Inductive ModuloBrut(d : nat) : nat -> Type :=
| mb_zero : ModuloBrut d d
| mb_succ : forall h, ModuloBrut d (S h) -> ModuloBrut d h.

Fixpoint moduloBrut_valeur(d h : nat)(mb : ModuloBrut d h) : nat.
Proof.
  case mb as [ | h pmb].
  - exact 0. (* mb_zero évalué en 0 *)
  - exact (S (moduloBrut_valeur _ _ pmb)). (* mb_succ évalué en S *)
Defined.

(* La structure des termes de 'ModuloBrut d h'
correspond exactement à celle des preuves de 'SuperieurOuEgal d h'. *)
Proposition moduloBrut_majoration :
  forall (d h : nat)(mb : ModuloBrut d h), SuperieurOuEgal d h.
Proof.
  fix HR 3.
  intros d h mb.
  case mb as [ | h pmb].
  - apply diagonale.
  - apply descenteVerticale.
    exact (HR _ _ pmb).
Defined.

(* L'invariant est bien vérifié. *)
Proposition moduloBrut_invariant :
  forall d h, forall (mb : ModuloBrut d h),
    (moduloBrut_valeur d h mb) + h = d. 
Proof.
  fix HR 3.
  intros d h mb.
  case mb as [ | h pmb].
  - cbn.
    reflexivity.
  - cbn.
    pose (hr := HR d (S h) pmb).
    Search(_ + S _).
    rewrite <- plus_n_Sm in hr.
    assumption.
Qed.

(* Somme (réuniondisjointe) des singletons 'ModuloBrut d h'

  h : nat   m : ModuloBrut d h
  ----------------------------
      modulo m  : Modulo d
*)
Inductive Modulo(d : nat) : Type :=
| modulo : forall h, ModuloBrut d h -> Modulo d.

(* Valeur et complémentaire :
   - V (v, h) = v
   - C (v, h) = h
   - invariant : V (v, h) + C (v, h) = d *)
Definition modulo_valeur{d : nat}(m : Modulo d) : nat.
Proof.
  case m as [h mb].
  exact (moduloBrut_valeur _ _ mb).
Defined.

Definition modulo_complementaire{d : nat}(m : Modulo d) : nat.
Proof.
  case m as [h mb].
  exact h.
Defined.

Proposition modulo_invariant :
  forall d, forall (m : Modulo d),
    (modulo_valeur m) + (modulo_complementaire m) = d. 
Proof.
  intros d m.
  case m as [h mb].
  cbn.
  apply moduloBrut_invariant.
Qed.

Proposition modulo_valeur_majoration :
  forall d, forall (m : Modulo d),
    (modulo_valeur m) < S d.
Proof.
  intros d m.
  Search(_ <= _ -> _ < S _).
  apply le_lt_n_Sm.
  transitivity ((modulo_valeur m) + (modulo_complementaire m)).
  Search(_ <= _ + _).
  apply Nat.le_add_r.
  rewrite (modulo_invariant d m).
  constructor.
Qed.  
  
(* Structure algébrique de 'Modulo d'
- algèbre sur la signature (0, S) :
  - une constante correspondant à '0',
  - une fonction correspondant au successeur 'S'. 
- groupe additif commutatif :
  - loi additive associative et commutative,
  - élément neutre '0',
  - opposé (de valeur égale au reste du successeur du complémentaire).
- anneau commutatif (non traité, mais pourrait l'être) :
  - loi multiplicative associative et commutative,
  - élément neutre '1',
  - pas d'inverse en général, l'inversibilité étant équivalente au fait
    d'être premier avec 'S d' (par application du théorème de Bézout
    https://fr.wikipedia.org/wiki/Th%C3%A9or%C3%A8me_de_Bachet-B%C3%A9zout). *)

(* Modulo d : algèbre sur la signature (0, S). *)

Definition modulo_zero(d : nat) : Modulo d := modulo _ _ (mb_zero d).

Definition moduloBrut_succ{d h : nat}(mb : ModuloBrut d h) : Modulo d.
Proof.
  case h as [ | ph].
  + exact (modulo_zero d).
  + exact (modulo _ _ (mb_succ _ _ mb)).
Defined.

Definition modulo_succ{d : nat}(m : Modulo d) : Modulo d.
Proof.
  case m as [h mb].
  exact (moduloBrut_succ mb).
Defined.

(* Morphisme d'algèbre sur la signature '(0, S)', de 'nat' vers 'Modulo d' (noté M).
   - M 0 = 0
   - M(S n) = S (M n)
   (0 et S étant interprétés de deux manières différentes dans l'algèbre du domaine,
   'nat', et dans l'algèbre image, 'Modulo d') *) 
Fixpoint modulo_morphismeNat(d : nat)(n : nat) : Modulo d.
Proof.
  case n as [ | pn].
  - exact (modulo_zero d).
  - exact (modulo_succ (modulo_morphismeNat d pn)).
Defined.

(* Valeur : pré_inverse du morphisme

'V (M n) = R n', où 'R' calcule le reste modulo '(S d)'.
Induction sur 'n'
- n = 0 : V (M 0) = 0 = R 0 
- n = S pn : analyse suivant 'M pn'
  - M pn = (0, v) : par l'invariant, v = d.
    - V (M (S pn)) = V (S (0, d)) = V (d, 0) = 0
    - R (S pn) = 0 car HR : V (M pn) = d = R pn
  - M pn = (S h, v) : par l'invariant, v + (S h) = d
    - V (M (S pn)) = V (S (S h, v)) = V (h, S v) = S v
    - R (S pn) = S (R pn) car (HR : v = R pn) et (R pn) < d. *) 
Lemma modulo_morphismeNat_valeur :
  forall d, forall n,
    modulo_valeur (modulo_morphismeNat d n) = reste n (S d).
Proof.
  fix HR 2.
  intros d n.
  case n as [ | pn].
  - cbn.
    reflexivity.
  - cbn.
    case (modulo_morphismeNat d pn) as [h mb] eqn:egMorphPn.
    cbn.
    case h as [ | ph].
    + cbn.
      pose (hr := HR d pn).
      rewrite egMorphPn in hr.
      assert(reste pn (S d) = d) as egRestPn.
      {
        rewrite <- hr.
        rewrite <- (modulo_invariant d (modulo d 0 mb)) at 3.
        cbn.
        ring.
      }
      symmetry.
      apply divEuclidienne_caracterisationReste with (S (quotient pn (S d))).
      Search(0 < S _).
      apply Nat.lt_0_succ.
      assert(pn = quotient pn (S d) * S d + d) as egPn.
      {
        rewrite <- egRestPn at 3.
        apply divEuclidienne_decomposition.
      }
      rewrite egPn at 1.
      ring.
      apply Nat.lt_0_succ.
    + cbn.
      pose (hr := HR d pn).
      rewrite egMorphPn in hr.
      cbn in hr.
      rewrite hr.
      symmetry.
      apply divEuclidienne_caracterisationReste with (quotient pn (S d)).
      Search(0 < S _).
      apply Nat.lt_0_succ.
      assert(pn = quotient pn (S d) * S d + (reste pn (S d))) as egPn.
      {
        apply divEuclidienne_decomposition.
      }
      rewrite egPn at 1.
      ring.
      Search(S _ < S _).
      apply lt_n_S.
      assert (S(reste pn (S d)) + ph = d) as invRpn.
      {
        transitivity ((reste pn (S d)) + (S ph)).
        ring.
        rewrite <- hr.
        apply moduloBrut_invariant.
      }
      Search (_ <= _). (* Nat.le_add_r: forall n m : nat, n <= n + m *)
      rewrite <- invRpn at 2.
      apply Nat.le_add_r.
Qed.      

(* Vers la compatibilité avec le morphisme de l'égalité modulo
- M n = M (R n)

Induction sur n
- n = 0 : M 0 = M (R 0) 
- n = S pn : analyse suivant (M pn)
  - M pn = (0, v) : par l'invariant, v = d.
    - M (S pn) = S (M pn) = (d, 0)
    - R (S pn) = V (M (S pn)) (en utilisant la proposition préc.)
               = V (d, O) = 0 
      - M (R (S pn)) = M 0 =  (d, 0)
  - M pn = (S h, v) : par l'invariant, v + (S h) = d
    - HR : M pn = M (R pn), avec (R pn) = V (M pn) = v
    - M (S pn) = S (M pn) = (h, S v) 
    - R (S pn) = V (M (S pn)) = V (h, S v) = S v = S (R pn)
      - M (R (S pn)) = M (S (R pn)) = S (M (R pn)) = S (M pn) par HR *)
Lemma modulo_morphismeNat_calculParReste :
  forall d, forall n,
    modulo_morphismeNat d n = modulo_morphismeNat d (reste n (S d)).
Proof.
  fix HR 2.
  intros d n.
  case n as [ | pn].
  - cbn.
    reflexivity.
  - cbn.
    case (modulo_morphismeNat d pn) as [h mb] eqn:egMorphPn.
    cbn.
    case h as [ | ph].
    + rewrite <- modulo_morphismeNat_valeur.
      cbn.
      rewrite egMorphPn.
      cbn.
      reflexivity.
    + assert(reste (S pn) (S d) = S (reste pn (S d))) as egR.
      {
        rewrite <- modulo_morphismeNat_valeur.
        cbn.
        rewrite egMorphPn.
        cbn.
        f_equal.
        rewrite <- modulo_morphismeNat_valeur.
        rewrite egMorphPn.
        cbn.
        reflexivity.
      }
      rewrite egR.
      cbn.
      rewrite <- (HR d pn).
      rewrite egMorphPn.
      cbn.
      reflexivity.
Qed.

(* Compatibilité de l'égalité modulo avec le morphisme *)
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
  modulo_morphismeNat 2 (modulo_valeur deuxMod3) = deuxMod3.
reflexivity.
Qed.

(* L'inversibilité antérieure entraîne la surjectivité. *)
Proposition moduloBrut_morphismeNat_inversibiliteAnterieure :
  forall d h (mb : ModuloBrut d h),
    modulo_morphismeNat d (moduloBrut_valeur _ _ mb) = modulo _ _ mb.
Proof.
  fix HR 3.
  intros d h mb.
  case mb as [ | h pmb].
  - cbn.
    reflexivity.
  - cbn.
    pose (hr := HR _ _ pmb).
    cbn in hr.
    rewrite hr.
    reflexivity.
Qed.

Proposition modulo_morphismeNat_inversibiliteAnterieure :
  forall d (m : Modulo d),
    modulo_morphismeNat d (modulo_valeur m) = m.
Proof.
  intros d m.
  case m as [h mb].
  apply moduloBrut_morphismeNat_inversibiliteAnterieure.
Qed.

(* Surjectivité du morphisme *)
Proposition modulo_morphismeNat_surjectivite :
  forall d (m : Modulo d), exists n, modulo_morphismeNat d n = m.
Proof.
  intros d m.
  exists (modulo_valeur m).
  apply modulo_morphismeNat_inversibiliteAnterieure.
Qed.

(* L'inversibilité postérieure entraîne l'injectivité (modulo (S d)). *)
Proposition modulo_morphismeNat_inversibilitePosterieure :
  forall d n,
    modulo_egalite (S d)
      (modulo_valeur (modulo_morphismeNat d n)) 
      n.
Proof.
  intros d n.
  unfold modulo_egalite.
  rewrite (modulo_morphismeNat_valeur d).
  rewrite (reste_idempotence (S d)).
  reflexivity.    
Qed.

(* Injectivité du morphisme modulo *)
Proposition modulo_morphismeNat_injectivite :
  forall d n1 n2,
    (modulo_morphismeNat d n1) = (modulo_morphismeNat d n2)
    -> modulo_egalite (S d) n1 n2.
Proof.
  intros d n1 n2 egIm.
  apply modulo_egalite_transitivite with (modulo_valeur (modulo_morphismeNat d n1)).
  apply modulo_egalite_symetrie.
  apply modulo_morphismeNat_inversibilitePosterieure.
  rewrite egIm.
  apply modulo_morphismeNat_inversibilitePosterieure.
Qed.


(* Groupe additif commutatif *)

Fixpoint moduloBrut_somme{d h : nat}(mb : ModuloBrut d h)(n : Modulo d){struct mb} : Modulo d.
Proof.
  case mb as [ | h pmb].
  - exact n.
  - exact (modulo_succ (moduloBrut_somme _ _ pmb n)).
Defined.

Definition modulo_somme{d : nat}(m n : Modulo d) : Modulo d.
Proof.
  case m as [h mb].
  exact (moduloBrut_somme mb n).
Defined.  

Example somme_12_13_mod25 :
  modulo_somme (modulo_morphismeNat 24 12) (modulo_morphismeNat 24 13) = modulo_morphismeNat 24 0.
reflexivity.
Qed.

Example somme_1_2_mod3 : modulo_somme unMod3 deuxMod3 = zeroMod3.
reflexivity.
Qed.

Example somme_2_2_mod3 : modulo_somme deuxMod3 deuxMod3 = unMod3.
reflexivity.
Qed.

Proposition modulo_somme_neutraliteGauche :
  forall d (n : Modulo d),
    modulo_somme (modulo_zero d) n = n.
Proof.
  intros d n.
  cbn.
  reflexivity.
Qed.

Lemma moduloBrut_somme_neutraliteDroite :
  forall d h (nb : ModuloBrut d h),
    moduloBrut_somme nb (modulo_zero d) = modulo _ _ nb.
Proof.
  fix HR 3.
  intros d h nb.
  case nb as [ | h pnb].
  - cbn.
    reflexivity.
  - cbn.
    rewrite (HR _ _ pnb).
    cbn.
    reflexivity.
Qed.

(* n + 0 = n *)
Proposition modulo_somme_neutraliteDroite :
  forall d (n : Modulo d),
    modulo_somme n (modulo_zero d) = n.
Proof.
  intros d n.
  case n as [h nb].    
  cbn.
  apply moduloBrut_somme_neutraliteDroite.
Qed.

Lemma moduloBrut_somme_successionDroite :
  forall d h (mb : ModuloBrut d h) (n : Modulo d),
    moduloBrut_somme mb (modulo_succ n) =
      modulo_succ (moduloBrut_somme mb n).
Proof.
  fix HR 3.
  intros d h mb n.
  case mb as [ | h pmb].
  - cbn.
    reflexivity.
  - cbn.
    rewrite (HR _ _ pmb _).
    reflexivity.
Qed.

Proposition modulo_somme_successionDroite :
  forall d (m n : Modulo d),
    modulo_somme m (modulo_succ n)
    = modulo_succ (modulo_somme m n).
Proof.
  intros d m n.
  case m as [h mb].    
  cbn.
  apply moduloBrut_somme_successionDroite.
Qed.


Lemma moduloBrut_somme_commutativite :
  forall d h (mb : ModuloBrut d h) k (nb : ModuloBrut d k),
    moduloBrut_somme mb (modulo _ _ nb)
    = moduloBrut_somme nb (modulo _ _ mb).
Proof.
  intro d.
  fix HR 2.
  intros h mb k nb.
  case mb as [ | h pmb].
  - cbn.
    rewrite moduloBrut_somme_neutraliteDroite.
    reflexivity.
  - cbn.
    fold (moduloBrut_succ pmb).
    fold (modulo_succ (modulo _ _ pmb)).
    rewrite moduloBrut_somme_successionDroite.
    rewrite (HR (S h) pmb k nb).
    reflexivity.
Qed.

(* m + n = n + m *)
Proposition modulo_somme_commutativite :
  forall d (m n : Modulo d),
    modulo_somme m n = modulo_somme n m.
Proof.
  intro d.
  intros m n.
  case m as [h mb].
  case n as [k nb].
  apply moduloBrut_somme_commutativite.
Qed.

(* démonstration directe pénible ! *)
(* Lemma moduloBrut_somme_successionGauche :
  forall d h (mb : ModuloBrut d h) (n : Modulo d),
    modulo_somme (moduloBrut_succ mb) n =
      modulo_succ (moduloBrut_somme mb n).
Proof.
  fix HR 3.
  intros d h mb n.
  case mb as [ | h pmb].
  - cbn.
    Print moduloBrut_succ.
    Check (mb_zero d).
    (* oblige à décomposer d ! *)
Abort. *)

(* Démonstration utilisant la commutativité *)
Proposition modulo_somme_successionGauche :
  forall d (m n : Modulo d),
    modulo_somme (modulo_succ m) n
    = modulo_succ (modulo_somme m n).
Proof.
  intros d m n.
  rewrite modulo_somme_commutativite.
  rewrite modulo_somme_successionDroite.
  rewrite modulo_somme_commutativite.
  reflexivity.
Qed.

(* Compatibilité du morphisme avec l'addition
- M (m + n) = (M m) + (M n)

Induction sur m
- m = 0
  - M (0 + n) = M n
  - (M 0) + (M n) = (d, 0) + (M n) = M n
- m = S pm
  - M ((S pm) + n) = M (S (pm + n)) = S (M (pm + n)) =[HR] S ((M pm) + (M n))
  - (M (S pm)) + (M n) = (S (M pm)) + (M n) =[succ gauche] S ((M pm) + (M n))
 *)
Proposition modulo_morphismeNat_compatibiliteAddition :
  forall d m n,  
    modulo_morphismeNat d (m + n)
    = modulo_somme (modulo_morphismeNat d m) (modulo_morphismeNat d n).
Proof.
  fix HR 2.
  intros d m n.
  case m as [ | pm].
  - cbn.
    reflexivity.
  - cbn.
    rewrite (HR d pm n).
    rewrite modulo_somme_successionGauche.
    reflexivity.
Qed.

(* Associativité de la somme *)
Lemma moduloBrut_somme_associativite_droiteAGauche :
  forall d h (mb : ModuloBrut d h) (n1 n2 : Modulo d),
    moduloBrut_somme mb (modulo_somme n1 n2)
    = modulo_somme (moduloBrut_somme mb n1) n2.
Proof.
  intro d.
  fix HR 2.
  intros h mb n1 n2.
  case mb as [ | h pmb].
  - cbn.
    reflexivity.
  - cbn.
    rewrite modulo_somme_successionGauche.
    rewrite (HR _ pmb n1 n2).
    reflexivity.
Qed.

(* m + (n1 + n2) = (m + n1) + n2 *)
Proposition modulo_somme_associativite_droiteAGauche :
  forall d (m n1 n2 : Modulo d),
    modulo_somme m (modulo_somme n1 n2)
    = modulo_somme (modulo_somme m n1) n2.
Proof.
  intros d m n1 n2.
  case m as [h mb].
  apply moduloBrut_somme_associativite_droiteAGauche.
Qed.

(* (m + n1) + n2 = m + (n1 + n2) *)
Proposition modulo_somme_associativite_gaucheADroite :
  forall d (m n1 n2 : Modulo d),
    modulo_somme (modulo_somme m n1) n2
    = modulo_somme m (modulo_somme n1 n2).
Proof.
  intros d m n1 n2.
  symmetry.
  apply modulo_somme_associativite_droiteAGauche.
Qed.

Definition moduloBrut_opposeSomme{d h : nat}(mb : ModuloBrut d h) : Modulo d.
Proof.
  exact (modulo_morphismeNat d (S h)).
Defined.

Definition modulo_opposeSomme{d : nat}(m : Modulo d) : Modulo d.
Proof.
  case m as [h mb].
  exact (moduloBrut_opposeSomme mb).
Defined.  

(* m + (- m) = 0 *)
Proposition modulo_opposeSomme_correction :
  forall d (m : Modulo d),
    modulo_somme m (modulo_opposeSomme m) = modulo_zero d.
Proof.
  intros d m.
  rewrite <- (modulo_morphismeNat_inversibiliteAnterieure d m) at 1.
  case m as [h mb].
  cbn.
  rewrite modulo_somme_successionDroite.
  rewrite <- modulo_morphismeNat_compatibiliteAddition.
  assert(moduloBrut_valeur d h mb + h = d) as inv.
  {
    replace h with (modulo_complementaire (modulo _ _ mb)) at 2.
    apply (modulo_invariant d (modulo _ _ mb)).
    reflexivity.
  }
  rewrite inv.
  transitivity (modulo_morphismeNat d (S d)).
  - reflexivity.
  - rewrite (modulo_morphismeNat_calculParReste).
    rewrite reste_cycle.
    reflexivity.
Qed.

(* Complément : sur l'unicité de la représentation. Démonstrations difficiles. *)

(* Objectif : démontrer que chaque type 'ModuloBrut d h' est un singleton.
 Première tentative. *)
(* Proposition moduloBrut_typesSingletons :
  forall (d h : nat)(mb1 mb2 : ModuloBrut d h),
    mb1 = mb2.
Proof.
  fix HR 3.
  intros d h mb1 mb2.
  case mb1 as [ | h pmb1].
  - admit. (* On aurait besoin d'un lemme. *)
  - case mb2 as [ | h pmb2].
    * exfalso.
      apply moduloBrut_majoration in pmb1 as majAbs.
      apply superieurOuEgal_adequation in majAbs.
      Search(S _ <= _).
      apply (Nat.nle_succ_diag_l d).
      assumption.
    * f_equal.
      apply HR.
Abort. *)

(* Essayons de démontrer ce lemme. *)
(* Lemma moduloBrut_singleton_casZero :  forall d (mb : ModuloBrut d d),
    mb = mb_zero d.
Proof.
  intros d mb.
  (* case mb as [ | h pmb].
     Error: Cannot instantiate metavariable P of type
     "forall n : nat, ModuloBrut d n -> Prop"
     with abstraction "fun (d : nat) (mb : ModuloBrut d d) => mb = mb_zero d"
     of incompatible type "forall d : nat, ModuloBrut d d -> Prop".

   Explication :

   - Système d'inférence
                                   (ModuloBrut d (S h))
   ---------------- [mb_zero]      -------------------- [mb_succ]
   (ModuloBrut d d)                   (ModuloBrut d h)

   - Règle d'inférence pour la tactique 'case' (en première approximation)
   (d : nat) ⊢ mb_zero d = mb_zero d
         (d : nat), (h : nat), (pmb : ModuloBrut d (S h)) ⊢
            (mb = mb_zero d)[mb := mb_succ d h pmb] // Mal typé !
   -------------------------------------------------------------- [case mb]
   (d : nat), (mb :  ModuloBrut d d) ⊢ mb = mb_zero d 
  *)
Abort.*)


(* Pour permettre une décomposition par 'case', il devient nécessaire de modifier
   la formulation de la proposition, en distinguant 'd' du complémentaire 'h'.
   Pour typer, on utilise un foncteur qui transforme :
   - / objets : un 'h : nat' en un type 'ModuloBrut d h',
   - / flèches : une égalité 'eg : h1 = h2' en une fonction
     'conversion eg : ModuloBrut d h1 -> ModuloBrut d h2'. *)

(* Conversion : foncteur catégorique - voir egalite_preuves_singletonSiDecidable. *)
Definition conversion{d h1 h2 : nat}(eg : h1 = h2) : ModuloBrut d h1 -> ModuloBrut d h2. 
  case eg. (* 'eg' serait remplacé par 'eq_refl h1', et 'h2' est récrit en 'h1'. *)
  exact (fun mb => mb). (* La conversion devient l'identité. *)
Defined.

(* On reformule le lemme en utilisant la conversion.  *)
(*
Lemma moduloBrut_singleton_casZeroModuloConversion :
  forall d h (mb : ModuloBrut d h)(eg : h = d), 
    conversion eg mb = mb_zero d.   
Proof.
  intros d h mb.
  intro eg.
  case mb as [ | h pmb].  
  - Print eq. (* Définition de l'égalité. *)
    Print conversion.
    (* Pour simplifier la conversion, il est nécessaire de transformer 'eg' en 'eq_refl'. *)
    (* case eg. Erreur ! *)
    (* Error: Cannot instantiate metavariable P of type
       "forall a : nat, d = a -> Prop" with abstraction
       "fun (d : nat) (eg : d = d) => conversion eg (mb_zero d) = mb_zero d"
       of incompatible type "forall d : nat, d = d -> Prop".

       Explication
       - Système d'inférence pour l'égalité 'eq' (notée '=')

       eq(T : Type)(x : T) : T -> Prop // Paramétrisation par 'T' et 'x',
                                          indexation par un 'T'

       ----- [eq_refl]
       x = x           // L'index 'x' doit être égal, c'est-à-dire identique,
                       // au paramètre 'x'.

       - Règle d'inférence pour la tactique 'case'

       La règle pour la tactique 'case' pourrait être la suivante :

       (d : nat) ⊢ (conversion eg (mb_zero d) = mb_zero d)[eg := @eq_refl nat d]
       ------------------------------------------------------------------------- [case eg]
       (d : nat), (eg : d = d) ⊢ conversion eg (mb_zero d) = mb_zero d

       Dans ce cas, on aurait bien le sous-but souhaité :
       - (d : nat) ⊢ mb_zero d = mb_zero d

       Cependant, la règle pour la tactique 'case' réalise aussi
       une abstraction de l'index, car il n'est pas possible de résoudre
       en général les contraintes induites par les index qui peuvent varier librement
       dans les conclusions des règles du type inductif, contrairement aux paramètres.

       (d : nat) ⊢ ...[y := d, egX := @eq_refl nat d]
       -------------------------------------------------------------------------- [case eg]
       (d : nat), (eg : d = d)
          ⊢ (conversion egX (mb_zero d) = mb_zero d)[y := d, egX : (d = y) := eg]
            // égalité mal typée : '(ModuloBrut d y) / (ModuloBrut d d)'

       Ainsi Coq interdit l'usage de la tactique 'case'. La solution ici est de
       démontrer que 'eg' est égal à '@eq_refl nat d' (abrégé en 'eq_refl'). C'est le cas
       pour tous les types pour lesquels l'égalité est décidable, comme 'nat'. 
     *)
Abort.*)
 
(* Nouvel essai : au lieu de la tactique 'case', on utilise le fait
que toute égalité sur 'nat' est le constructeur 'eq_refl'. *)
Lemma moduloBrut_singleton_casZeroModuloConversion :
  forall d h (mb : ModuloBrut d h)(eg : h = d), 
    conversion eg mb = mb_zero d.   
Proof.
  intros d h mb.
  intro eg.
  case mb as [ | h pmb].
  - (* Pour simplifier la conversion, il est nécessaire de transformer 'eg' en 'eq_refl'.
       On peut montrer que 'eg' est égal à 'eq_refl', grâce à la décidabilité
       de l'égalité sur 'nat'. C'est un résultat dans la bibliothèqe standard. *)
    assert(eg = eq_refl) as eqPreuves.
    {
      Check UIP_nat.
      apply UIP_nat. 
    }
    rewrite eqPreuves.
    cbn.
    reflexivity.
  - (* cas absurde : 'S h <= d' et 'h = d' impossibles. *)
    exfalso.
    apply moduloBrut_majoration in pmb as majAbs.
    apply superieurOuEgal_adequation in majAbs.
    Search(S _ <= _).
    apply (Nat.nle_succ_diag_l d).
    rewrite eg in majAbs.
    assumption.
Qed.
(* On déduit le lemme en instantiant l'égalité par 'eq_refl' :
la conversion est alors l'identité. *)
Lemma moduloBrut_singleton_casZero :  forall d (mb : ModuloBrut d d),
    mb = mb_zero d.
Proof.
  intros d mb.
  transitivity (conversion eq_refl mb).
  - reflexivity.
  - apply moduloBrut_singleton_casZeroModuloConversion.
Qed.


(* On peut conclure en reprenant la démonstration interrompue.
Les types 'ModuloBrut'sont des types singletons. *)
Proposition moduloBrut_typesSingletons :
  forall (d h : nat)(mb1 mb2 : ModuloBrut d h),
    mb1 = mb2.
Proof.
  fix HR 3.
  intros d h mb1 mb2.
  case mb1 as [ | h pmb1].
  - symmetry.
    apply moduloBrut_singleton_casZero.
  - case mb2 as [ | h pmb2].
    * exfalso.
      apply moduloBrut_majoration in pmb1 as majAbs.
      apply superieurOuEgal_adequation in majAbs.
      Search(S _ <= _).
      apply (Nat.nle_succ_diag_l d).
      assumption.
    * f_equal.
      apply HR.
Qed.
  
Print Some.

Locate "++".

Print map.

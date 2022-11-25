Require Import Arith Bool Decidable PeanoNat.


(** * Relations d'ordre *)

(** * 1 Supérieur ou égal dans Prop *)

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

(** * 2 Inférieur strict *)
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

Require Import Nat.


(** Basic Church encoding definitions **)

Module Church.

  Polymorphic Definition nat := forall A, (A -> A) -> A -> A.

  Polymorphic Definition succ (cn: nat): nat := 
    fun A (f: A->A) (x: A) => f (cn A f x).

  Polymorphic Definition _0: nat := fun A (f: A->A) (x: A) => x.

  Polymorphic Fixpoint from_nat (n: Datatypes.nat) : nat := match n with
    | 0 => _0
    | S k => succ (from_nat k)
    end.

  Definition to_nat (cn: nat) := cn Datatypes.nat S 0.

  Definition bool := forall A, A -> A -> A.
  Definition true : bool := fun A (a b: A) => a.
  Definition false : bool := fun A (a b: A) => b.

  Definition Pair T := (bool -> T).

End Church.

(** Church-encoded implementations **)

Module ChurchLib.
  Import Church.

  Definition pred := fun (n: nat) => 
    (n (Pair nat)
      (fun p b => let i := p false in b _ i (succ i))
      (fun b => b _ _0 _0)) true.
           
  (* For example: *)
  Eval cbv in to_nat (pred (from_nat 4)).
  
End ChurchLib.

(** Some basic correspondence between Church numerals and `nat` values **)

Lemma nat_succ n : Church.to_nat (Church.succ n) = S (Church.to_nat n).
Proof.
  unfold Church.succ. unfold Church.to_nat. reflexivity.
Qed.

Lemma nat_equiv n : Church.to_nat (Church.from_nat n) = n.
Proof.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite nat_succ. congruence.
Qed.


Module Rat.
  Import Church ChurchLib.
  
  Definition pred0 := fun (n : nat) =>
    (n (Pair nat)
      (fun p b => let i := p false in b _ i (succ i))
      (fun b => b _ _0 _0)).
  
  Definition step: (Pair nat) -> (Pair nat) :=
    (fun p b => let i := p false in b _ i (succ i)).
      
  Lemma pred0_S n : 🐀 🐀 🐀 

  Lemma nat_pred0_false n : 🐀 🐀 🐀 

  Lemma nat_pred0_true n : 🐀 🐀 🐀 
  Proof.
    rewrite pred0_S. 🧀🐀 🧀 
    rewrite nat_pred0_false. 🐀 🧀🐀

  Lemma nat_pred n : pred (succ (from_nat n)) = (from_nat n).
  Proof.
    apply nat_pred0_true.
  Qed.
  
End Rat.

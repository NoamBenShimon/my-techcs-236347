Set Implicit Arguments.

Require Import Arith.Arith.
Import Nat.

(* ----------------------------------------------------------------- *)
(* Let's start by proving some basic facts about natural numbers.    *)

(* this one is going to come in handy *)
Theorem f_equal : forall A B (f : A -> B) x y, x = y -> f x = f y.
Proof.
  intros. rewrite H. reflexivity.  (* First one's free. *)
Qed.                               (* Try to understand it though! *)

(* notice that "+" is not defined symmetrically! *)
Print Nat.add.
Eval simpl in fun x => 1 + x.
Eval simpl in fun x => x + 1.

Lemma plus_one : forall x, x + 1 = S x.
Proof.
  intro x.
  induction x.
  - simpl.
    reflexivity.
  - simpl.
    apply f_equal. 
    apply IHx.
Qed.

Lemma plus_one' : forall x y, x + S y = S x + y.
Proof.
  intros x y.
  rewrite Nat.add_succ_r. (* Simplify left side *)
  rewrite Nat.add_succ_l. (* Simplify right side *)
  reflexivity.
Qed.

(* Definition of divisibility + some syntactic sugar *)
Definition divides a b := exists k, a * k = b.
Notation "( a | b )" := (divides a b).

(* commutativity lemmas. we're about to need them. *)
Check Nat.add_comm.
Check Nat.mul_comm.
Check Nat.mul.

  
Lemma divides_refl : forall n, (n | n).
Proof.
  intro n.
  unfold divides.
  exists 1.
  rewrite Nat.mul_comm.
  rewrite Nat.mul_1_l.
  reflexivity.
Qed.



(* ----------------------------------------------------------------- *)
(* Armed with these lemmas, let's try to define the Greatest Common  *)
(* Denominator and Euclid's algorithm.                               *)

Section Gcd.

  Definition is_gcd (a b z : nat) :=
    (z | a) /\ (z | b) /\ forall z', (z' | a) -> (z' | b) -> (z' | z).  

  (* First some basic properties of gcd *)
  Theorem is_gcd_refl : forall z, is_gcd z z z.
  Proof.
    intro z.
    unfold is_gcd.
    split.
    - apply divides_refl.
    - split. 
      apply divides_refl.
      tauto.
  Qed.
  

  Theorem is_gcd_comm : forall a b z, is_gcd a b z -> is_gcd b a z.
  Proof.
    intros a b z.
    unfold is_gcd.
    intro H.
    destruct H as [HA [HB HP]].
    split. apply HB.
    split. apply HA.
    firstorder.
  Qed.
  
  
  (* -- this is a simplified version of Euclid -- *)
  Inductive gcd : nat -> nat -> nat -> Prop :=
    base : (forall z, gcd z z z)
  | step_a : forall a b z, gcd a b z -> gcd (a + b) b z
  | step_b : forall a b z, gcd a b z -> gcd a (a + b) z.

  
  (* distributivity lemmas. you will need them too! *)
  Check Nat.mul_add_distr_l.
  Check Nat.mul_sub_distr_l.

  Search (_ * (_ + _)).       (* this is how you could find them yourself *)
  Search (_ * (_ - _)).       (* if I hadn't told you *)

  Lemma gcd_step_aux : forall a b z, is_gcd a b z -> is_gcd (a + b) b z.
  Proof.
    intros a b z.
    unfold is_gcd.
    
    intro H.
    destruct H as [HA [HB HP]].
    
    remember HB as HBC.
    unfold divides in HA, HB.
    destruct HA as [k_a HKA].
    destruct HB as [k_b HKB].
    
    split. 
      unfold divides.
      exists (k_a + k_b).
      rewrite Nat.mul_add_distr_l.
      rewrite HKA, HKB.
      reflexivity.
    
    
    split. apply HBC.
      intros z' HAB' HB'.
      remember HB' as HBC'.
      unfold divides in HAB', HB'.
      destruct HAB' as [kab' HAB''].
      destruct HB' as [kb' HB''].
    
    apply HP.
      unfold divides.
      exists (kab' - kb').
      rewrite Nat.mul_sub_distr_l.
      rewrite HAB'', HB''.
      rewrite Nat.add_sub.
      reflexivity.
    
    apply HBC'.
  Qed.
    
 
  Theorem gcd_pcorrect : forall a b z, gcd a b z -> is_gcd a b z.
  Proof.
    intros a b z H.
    induction H.
    - apply is_gcd_refl.
    - apply gcd_step_aux.
      apply IHgcd.
    - apply is_gcd_comm. 
      rewrite Nat.add_comm.
      apply gcd_step_aux.
      apply is_gcd_comm.
      apply IHgcd.
    Qed.
    
    


End Gcd.

Require Import Arith.Arith.
Import Nat.

(* -- this is the simplified version of Euclid we saw in class -- *)
Inductive gcd : nat -> nat -> nat -> Prop :=
  base   : forall z, gcd z z z
| step_a : forall a b z, gcd a b z -> gcd (a + b) b z
| step_b : forall a b z, gcd a b z -> gcd a (a + b) z.

(* -- This is a more accurate description of Euclid's algorithm -- *)
Inductive euclid : nat -> nat -> nat -> Prop :=
  stop    : forall z, euclid z z z
| step_a' : forall a b z, a > b -> euclid (a - b) b z -> euclid a b z
| step_b' : forall a b z, a < b -> euclid a (b - a) z -> euclid a b z.

Theorem euclid_gcd : forall a b z, euclid a b z -> gcd a b z.
Proof.
  intros a b z H.
  induction H as [z | a b z H_gt H_euclid IH | a b z H_lt H_euclid IH].

  (* Case: stop z *)
  - apply base.

  (* Case: step_a' *)
  - (* We have a > b and euclid (a - b) b z, and IH: gcd (a - b) b z *)
    (* We need to show gcd a b z *)
    (* Since a > b, we have a = (a - b) + b *)
    assert (H_eq: a = (a - b) + b).
    { symmetry.
      rewrite Nat.sub_add with b a.
      reflexivity.
      apply lt_le_incl.
      exact H_gt. }
    rewrite H_eq.
    apply step_a.
    exact IH.

  (* Case: step_b' *)
  - (* We have a < b and euclid a (b - a) z, and IH: gcd a (b - a) z *)
    (* We need to show gcd a b z *)
    (* Since a < b, we have b = a + (b - a) *)
    assert (H_eq: b = a + (b - a)).
    { symmetry.
      rewrite <- Nat.add_comm.
      rewrite Nat.sub_add with a b.
      reflexivity.
      apply lt_le_incl.
      exact H_lt. }
    rewrite H_eq.
    apply step_b.
    exact IH.
Qed.
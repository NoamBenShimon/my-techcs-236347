Set Implicit Arguments.

Require Import Arith.
Require Import Lia.
Import Nat.

(*
 * M:
 * 1	c = 1 
 * 2  while c > 0 
 * 3    if n > 100 
 * 4      n := n – 10 
 * 5      c := c – 1 
 * 6    else
 * 7      n := n + 11 
 * 8      c := c + 1 
 * 9  return n
 *)

Definition state : Set := nat * nat.  (* n, c *)

Inductive step : state -> state -> Prop :=
  step_hi : forall n c, c > 0 -> n > 100 -> step (n, c) (n - 10, c - 1)
| step_lo : forall n c, c > 0 -> n <= 100 -> step (n, c) (n + 11, c + 1).

(* = Loop Invariant = *)
Definition inv s :=
  match s with
    (n, c) => n <= c * 10 + 91
  end.

(* Useful arithmetic lemmas from the standard library *)
Check le_add_r.
Check sub_le_mono_r.
Check add_sub_swap.
Check add_comm.
Check mul_succ_l.
Check mul_sub_distr_r.


Lemma preserves s1 s2 : inv s1 -> step s1 s2 -> inv s2.
Proof.
  intros Before Step.
  destruct Step.
  
  - unfold inv.
    unfold inv in Before.
    lia.
    
  - unfold inv.
    unfold inv in Before.
    lia.
  (* ... *)
Qed.

(*
 * Now we prove that the invariant holds for all reachable 
 * states.
 *)
Section ReflexiveTransitiveClosureDef.

  Variable D : Set.
  Variable R : D -> D -> Prop.

  Inductive tc : D -> D -> Prop :=
    tc_refl : forall s, tc s s
  | tc_step : forall s u t, tc s u -> R u t -> tc s t.

End ReflexiveTransitiveClosureDef.


Lemma inv_tc s1 s2 : inv s1 -> tc step s1 s2 -> inv s2.
Proof.
  intros Before Step.
  induction Step.
  - apply Before.
  - apply IHStep in Before.
    apply (preserves Before H).
Qed.
  

Theorem mccarthy91 n n' : n <= 101 ->
                          tc step (n, 1) (n', 0) ->
                          n' <= 91.
Proof.
  intros Before Step.
  
  assert (inv_init : inv (n, 1)).
  {
    unfold inv.
    lia.
  }
  
  apply (inv_tc inv_init Step).
Qed.


(*
 * Bonus: prove that n' >= 91 as well.
 *)
Theorem mccarthy91' n n' : n <= 101 ->
                          tc step (n, 1) (n', 0) ->
                          n' >= 91.
Proof.
  intros Before Step.
  
  inversion Step. subst.
  
  - remember (n', 0) as f0 eqn:eq_f0.
    destruct H0.
    + assert (ThePairEquality : (n', 0) = (n0 - 10, c - 1)).
      {
        rewrite eq_f0.
        reflexivity.
      }

      injection ThePairEquality. intros.
      lia.
    
    + assert (c_succ_0 : 0 = S(c)).
      {
        injection eq_f0 as eq_n eq_c.
        lia.
      }
      discriminate c_succ_0.
  
Qed.


(*
 * Extra bonus: do the same proof with the other variant of tc.
 * Which one is easier?
 *)
Section ReflexiveTransitiveClosureAltDef.

  Variable D : Set.
  Variable R : D -> D -> Prop.

  Inductive tc' : D -> D -> Prop :=
    tc'_refl : forall s, tc' s s
  | tc'_step : forall s u t, R s u -> tc' u t -> tc' s t.

End ReflexiveTransitiveClosureAltDef.


Theorem mccarthy'91 n n' : n <= 101 ->
                           tc' step (n, 1) (n', 0) ->
                           n' <= 91.

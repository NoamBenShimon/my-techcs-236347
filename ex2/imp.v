Set Implicit Arguments.

Inductive var := a | b | n | x | y.

Definition op := nat -> nat -> nat.
  
Inductive expr :=
  expr_var : var -> expr
| expr_num : nat -> expr
| expr_op : expr -> op -> expr -> expr.

Inductive cmd :=
  assign : var -> expr -> cmd
| seq : cmd -> cmd -> cmd
| skip : cmd
| if_then_else : expr -> cmd -> cmd -> cmd
| while : expr -> cmd -> cmd
| assume : expr -> cmd.

Definition state := var -> nat.

Fixpoint sem (e : expr) (s : state) :=
  match e with
  | expr_var v => s v
  | expr_num m => m
  | expr_op e1 op e2 => op (sem e1 s) (sem e2 s)
  end.


(* -- Defining the program `euclid` in IMP -- *)
Require Import Arith.
Import Nat.

(* some operators *)
Definition gt01 n m := if gt_dec n m then 1 else 0.
Definition ne01 n m := if eq_dec n m then 0 else 1.

(* This notation will shorten things a bit *)
Notation "$ v" := (expr_var v) (at level 7, format "$ v").

Definition euclid_body :=
    seq (assume (expr_op $a ne01 $b))
        (if_then_else (expr_op $a gt01 $b)
                      (assign a (expr_op $a sub $b))
                      (assign b (expr_op $b sub $a))).
                      
                      
(* ====== Q4 ====== *)

Inductive gcd : nat -> nat -> nat -> Prop :=
| base   : forall z, gcd z z z
| step_a : forall a b z, gcd a b z -> gcd (a + b) b z
| step_b : forall a b z, gcd a b z -> gcd a (a + b) z.

Section ReflexiveTransitiveClosureDef.

  Variable D : Set.
  Variable R : D -> D -> Prop.

  Inductive tc : D -> D -> Prop :=
    tc_refl : forall s, tc s s
  | tc_step : forall s u t, R s u -> tc u t -> tc s t.
    
End ReflexiveTransitiveClosureDef.

(*Definition var_eq_dec (v1 v2 : var) : {v1 = v2} + {v1 <> v2}.
Proof.
  decide equality.
Defined.*)

Definition eq_var (v1 v2 : var) : bool :=
  match v1, v2 with
  | a, a => true
  | b, b => true
  | n, n => true
  | x, x => true
  | y, y => true
  | _, _ => false
  end.

Inductive sos : (state * cmd) -> (state * cmd) -> Prop :=
| sos_asn : forall s v e,
    sos (s, assign v e) 
    ((fun v' : var => if eq_var v v' then sem e s else s v'), skip)
    
| sos_seq : forall s s' c1 c1' c2,
    sos (s, c1) (s', c1') ->
    sos (s, (seq c1 c2)) (s', (seq c1' c2))
    
| sos_skp : forall s c2,
    sos (s, seq skip c2) (s, c2)

| sos_if_true: forall s e c1 c2,
    sem e s <> 0 ->
    sos (s, if_then_else e c1 c2) (s, c1)

| sos_if_false: forall s e c1 c2,
    sem e s = 0 ->
    sos (s, if_then_else e c1 c2) (s, c2)

| sos_while_true: forall s e c,
    sem e s <> 0 ->
    sos (s, while e c) (s, seq c (while e c))

| sos_while_false: forall s e c,
    sem e s = 0 ->
    sos (s, while e c) (s, skip)

| sos_assume_true: forall s e,
    sem e s <> 0 ->
    sos (s, assume e) (s, skip)
.
      
Definition step : state -> state -> Prop := 
  fun s s' => tc sos (s, euclid_body) (s', skip).

Lemma tc_trans : forall (D : Set) (R : D -> D -> Prop) (x y z : D),
                 tc R x y -> tc R y z -> tc R x z.
Proof.
  intros D R x y z Hxy Hyz.
  induction Hxy.
  - apply Hyz.
  - apply tc_step with u. 
    + apply H.
    + apply IHHxy.
      apply Hyz.
Qed.

Lemma tc_inv : forall (D : Set) (R : D -> D -> Prop) (x z : D),
               tc R x z -> x = z \/ exists y, R x y /\ tc R y z.
Proof.
  intros D R x z Hxz.
  induction Hxz.
  - left; reflexivity.
  - right.
    exists u.
    split.
    + apply H.
    + apply Hxz.
Qed.

(* Case a => a > b *)
(* Case a-a => Show that a becomes a-b *)
Lemma case_a_a : forall s s', (s a) > (s b) -> step s s' -> (s' a) = (s a) - (s b).
Proof.
  intros s s' a_gr_b H.
  inversion H; clear H.
  
  inversion H0; subst.
  
  inversion H7; subst. inversion H1; subst. inversion H.
  - inversion H9; subst.
  - subst. inversion H3; subst. inversion H4; subst.
    + inversion H5; subst. inversion H6; subst. inversion H5; subst.
      inversion H8; subst.
      * firstorder.
      * inversion H11.
    + subst.
      simpl in H12. unfold gt01, gt_dec in H12.
      destruct lt_dec in H12.
      * discriminate H12.
      * firstorder.
Qed.

(* Case a-b => Show that b stay b *)
Lemma case_a_b : forall s s', (s a) > (s b) -> step s s' -> (s' b) = (s b).
Proof.
  intros s s' a_gr_b H.
  
  inversion H; clear H; subst.
  
  inversion H0; subst.
  inversion H5; subst.
  inversion H1; subst.
  inversion H; subst.
  - inversion H9; subst.
  - inversion H; subst.
    inversion H3; subst.
    inversion H4; subst.
    + inversion H6; subst.
      inversion H7; subst.
      inversion H8; subst.
      * reflexivity.
      * inversion H9; subst.
    + subst.
      simpl in H12. unfold gt01, gt_dec in H12.
      destruct lt_dec in H12.
      * discriminate H12.
      * firstorder.
Qed.

(* Case a => a <= b *)
(* Case b-b => Show that b becomes b-a *)
Lemma case_b_b : forall s s', (s a) <= (s b) -> step s s' -> (s' b) = (s b) - (s a).
Proof.
  intros s s' b_ge_a H.
  assert (a_le_b : (s b) >= (s a)). { firstorder. }
  inversion H; clear H.
  
  inversion H0; subst.
  
  inversion H7; subst. inversion H1; subst. inversion H.
  - inversion H9; subst.
  - subst. inversion H3; subst. inversion H4; subst.
    + inversion H5; subst. inversion H6; subst. inversion H5; subst.
      inversion H8; subst.
      * simpl in H2, H12.
        unfold gt01 in H12. unfold ne01 in H2.
        destruct gt_dec in H12.
        -- apply (le_ngt (s'0 a) (s'0 b)) in g.
           contradiction.
           firstorder.
        -- contradiction.
      * inversion H11.
    + subst.
      simpl in H12. unfold gt01, gt_dec in H12.
      destruct lt_dec in H12.
      * discriminate H12.
      * inversion H5; subst. inversion H6; subst.
        inversion H8; subst.
        -- reflexivity.
        -- inversion H9.
Qed.

(* Case b-a => Show that a stays a *)
Lemma case_b_a : forall s s', (s a) <= (s b) -> step s s' -> (s' a) = (s a).
Proof.
  intros s s' b_ge_a H.
  assert (a_le_b : (s b) >= (s a)). { firstorder. }
  inversion H; clear H; subst.
  
  inversion H0; subst.
  inversion H5; subst.
  inversion H1; subst.
  inversion H; subst.
  - inversion H9; subst.
  - inversion H; subst.
    inversion H3; subst.
    inversion H4; subst.
    + inversion H6; subst.
      inversion H7; subst.
      simpl in H12. unfold gt01, gt_dec in H12.
      destruct lt_dec in H12.
      * apply (le_ngt (s'0 a) (s'0 b)) in l.
        contradiction.
        firstorder.
      * contradiction.
    + simpl in H12. unfold gt01, gt_dec in H12.
      destruct lt_dec in H12.
      * discriminate H12.
      * subst. inversion H6; subst.
        inversion H7; subst.
        inversion H8; subst.
        -- reflexivity.
        -- inversion H9.
Qed.

Lemma step_modification_symmetry : forall s s', step s s' -> 
                                   (s' b = s b) /\ (s a = s' a + s' b) 
                                   \/
                                   (s' a = s a) /\ (s b = s' a + s' b).
Proof.
  intros.
  destruct (le_dec (s a) (s b)) as [Hle | Hgt].
  - right.
    assert (case_ba : s' a = s a). { apply case_b_a; assumption; assumption. }
    assert (case_b : (s' a = s a) /\ (s b = s' a + s' b)).
    {
      split.
      - assumption.
      - rewrite case_ba. apply case_b_b in H. rewrite H. 
        rewrite add_comm. symmetry. apply (Nat.sub_add (s a) (s b)). 
        assumption. assumption.
    }
    assumption.
  - left.
    apply not_le in Hgt.
    assert (case_ab : s' b = s b). { apply case_a_b; assumption; assumption. }
    assert (case_a : (s' b = s b) /\ (s a = s' a + s' b)).
    {
      split.
      - assumption.
      - rewrite case_ab. apply case_a_a in H. rewrite H. 
        symmetry. apply (Nat.sub_add (s b) (s a)). 
        apply lt_le_incl in Hgt. assumption. assumption.
    }
    assumption.
Qed.

Lemma euclid_inv : forall s s' z,
                   tc step s s' -> gcd (s' a) (s' b) z -> gcd (s a) (s b) z.
Proof.
  intros s s' z Step gcd'__s.
  induction Step.
  - assumption. 
  - apply step_modification_symmetry in H.
    destruct H.  
    + destruct H. rewrite <- H in *. rewrite H0. apply step_a. 
      apply IHStep. assumption.
    + destruct H. rewrite <- H in *. rewrite H0. apply step_b.
      apply IHStep. assumption.
Qed.

Theorem Correctness : forall (a0 b0 : nat) (s s' : state), 
                      s a = a0 
                      -> s b = b0 
                      -> tc step s s' -> s' a = s' b
                      -> gcd a0 b0 (s' a).
Proof.
  intros.
  subst. 
  assert (gcd (s' a) (s' b) (s' a)).
    rewrite H2 in *. constructor.
  rewrite H2 in *.
  eapply euclid_inv.
  apply H1.
  rewrite H2 in *.
  assumption.
Qed.
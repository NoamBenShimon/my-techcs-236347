Set Implicit Arguments.
Require Import Lists.List.
Require Import Arith.
Import ListNotations.
Print list.
Print rev.

(* Q1. Define `is_sorted`.  (should return a Prop.)  *)

(* We define is_sorted recursively by always deconstructing one element at a time:
   - An empty list is sorted
   - A single element list is sorted
   - For a non-empty list, check if head relates properly to all elements in tail *)
Fixpoint is_sorted {A : Type} (l : list A) (R : A -> A -> Prop) : Prop :=
  match l with
  | [] => True
  | x :: xs =>
      match xs with
      | [] => True
      | y :: _ => R x y /\ is_sorted xs R
      end
  end.

(* Show that this list is sorted. *)
Lemma warm_up : is_sorted [3;5;9] le.
Proof.
  (* Unfold the definition *)
  simpl.
  split.
  - (* 3 <= 5 *)
    apply le_S. apply le_S. apply le_n.
  - split.
    + (* 5 <= 9 *)
      apply le_S. apply le_S. apply le_S. apply le_S. apply le_n.
    + (* is_sorted [9] le, which is True *)
      exact I.
Qed.

(* Q2. Prove that an ascending list of nat, when reversed,
 *     becomes a descending list. *)

(* First, let's prove that In y (rev l) <-> In y l *)
Lemma in_rev_iff : forall {A : Type} (y : A) (l : list A),
  In y (rev l) <-> In y l.
Proof.
  intros A y l.
  induction l as [|h t IH].
  - (* Base case: empty list *)
    simpl. split; intro H; exact H.
  - (* Inductive case *)
    simpl. split.
    + (* -> direction *)
      intro H_in_rev.
      rewrite in_app_iff in H_in_rev.
      destruct H_in_rev as [H_in_rev_t | H_in_h].
      * right. rewrite <- IH. exact H_in_rev_t.
      * simpl in H_in_h. destruct H_in_h as [H_eq | H_false].
        -- left. exact H_eq.
        -- contradiction.
    + (* <- direction *)
      intro H_in_orig.
      rewrite in_app_iff.
      destruct H_in_orig as [H_eq | H_in_t].
      * right. simpl. left. exact H_eq.
      * left. rewrite IH. exact H_in_t.
Qed.

(* Helper lemma: if a list is sorted ascending, then the head is <= all elements *)
Lemma sorted_head_le_all : forall l : list nat, forall h : nat,
  is_sorted (h :: l) le -> forall y, In y l -> h <= y.
Proof.
  induction l as [|h' t IH]; intros h H_sorted y H_in.
  - (* Base case: empty tail *)
    simpl in H_in. contradiction.
  - (* Inductive case *)
    simpl in H_sorted. destruct H_sorted as [H_le H_tail_sorted].
    simpl in H_in. destruct H_in as [H_eq | H_in_t].
    + (* y = h' *)
      subst y. exact H_le.
    + (* y ∈ t *)
      (* We need to show h <= y where y ∈ t *)
      (* We know h <= h' and the tail starting from h' is sorted *)
      (* So we need to use transitivity: h <= h' <= y *)

      (* First, let's get h' <= y from the sorted tail *)
      assert (H_h'_le_y: h' <= y).
      {
        destruct t as [|h'' t'].
        - simpl in H_in_t. contradiction.
        - apply IH with (h := h').
          + exact H_tail_sorted.
          + exact H_in_t.
      }

      (* Now use transitivity *)
      apply Nat.le_trans with h'.
      * exact H_le.
      * exact H_h'_le_y.
Qed.

(* Helper lemma: a sorted list appended with an element smaller than all elements
   in the list results in a sorted list (in reverse order) *)
Lemma sorted_app_smaller : forall l : list nat, forall x : nat,
  is_sorted l ge ->
  (forall y, In y l -> x <= y) ->
  is_sorted (l ++ [x]) ge.
Proof.
  induction l as [|h t IH]; intros x H_sorted H_smaller.
  - (* Base case: empty list *)
    simpl. exact I.
  - (* Inductive case *)
    destruct t as [|h' t'].
    + (* Single element case: [h] ++ [x] = [h; x] *)
      simpl. split.
      * (* Need to show h >= x *)
        apply H_smaller. simpl. left. reflexivity.
      * exact I.
    + (* Multiple elements case *)
      simpl. split.
      * (* First two elements of h :: t' ++ [x] satisfy ge *)
        simpl in H_sorted. destruct H_sorted as [H_ge H_tail_sorted].
        exact H_ge.
      * (* Tail is sorted *)
        apply IH.
        -- simpl in H_sorted. destruct H_sorted as [_ H_tail_sorted].
           exact H_tail_sorted.
        -- intros y H_in. apply H_smaller. simpl. right. exact H_in.
Qed.

(* Main theorem *)
Theorem rev_asc_desc : forall l : list nat,
  is_sorted l le -> is_sorted (rev l) ge.
Proof.
  induction l as [|h t IH]; intro H.
  - (* Base case: empty list *)
    simpl. exact I.
  - (* Inductive case *)
    simpl. (* rev (h :: t) = rev t ++ [h] *)

    destruct t as [|h' t'].
    + (* Single element case *)
      simpl. exact I.
    + (* Multiple elements case *)
      (* We have: is_sorted (h :: h' :: t') le *)
      (* Need to show: is_sorted (rev (h' :: t') ++ [h]) ge *)

      (* Apply inductive hypothesis to get sorted tail *)
      assert (H_rev_sorted: is_sorted (rev (h' :: t')) ge).
      {
        apply IH.
        simpl in H. destruct H as [H_le H_tail_sorted].
        exact H_tail_sorted.
      }

      (* Now use helper lemma *)
      apply sorted_app_smaller.
      * exact H_rev_sorted.
      * (* Show h <= all elements in rev (h' :: t') *)
        intros y H_in.

        (* Use our lemma to convert In y (rev (h' :: t')) to In y (h' :: t') *)
        assert (H_in_orig: In y (h' :: t')).
        { rewrite <- in_rev_iff. exact H_in. }

        (* Now use sorted_head_le_all to show h <= y *)
        apply sorted_head_le_all with (l := h' :: t').
        -- exact H.
        -- exact H_in_orig.
Qed.
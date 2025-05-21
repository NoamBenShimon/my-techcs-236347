Set Implicit Arguments. (* Allows us to use inference for dependent arguments *)

Require Import Reals.   (* Imports real arithmetic. *)
Notation Real := R.        (* Notice: due to the absence of overloading, all       *)
Delimit Scope R_scope   (* numerical constants and operators are nat-typed,     *)
  with Real.               (* unless stated otherwise via the scope delimiter '%'. *)

Check 3 + 4.            (* : ℕ  (nat)  *)
Check (3 + 4) % Real.      (* : ℝ  (Real) *)


Inductive Vec : nat -> Set :=
  VNil : Vec 0
| VCons : forall n, Real -> Vec n -> Vec (S n).

(* Some syntactic sugar *)
Notation "<< x , .. , y >>" := (VCons x .. (VCons y VNil) .. ).

Check << 5, 9, 6 >> .

Fixpoint Concat {n m : nat} (v1: Vec n) (v2: Vec m) : (Vec (n+m)) :=
  match v1 with
  | VNil        => v2
  | VCons h t => VCons h (Concat t v2)
  end.

Check Concat .
(*
Concat
     :  Vec ?n ->
        Vec ?m ->
        Vec (?n + ?m)
where
?n : [ |- nat]
?m : [ |- nat]
*)
Check Concat << 1, 2, 3 >> << 4, 5, 6 >> .
Eval cbn in (Concat << 1, 2, 3 >> << 4, 5, 6 >>).

Definition head := fun {n : nat} (v : Vec (S n)) => 
  match v with
  | VCons h _ => h : Real
  end.

Check head .
(*
head
     : Vec (S ?n) -> Real
where
?n : [ |- nat]
*)
Check head << 5, 9, 6 >> .
Eval cbn in (head << 5, 9, 6 >>).

(* For Q3 + Q4 *)

Fixpoint Vec' n : Set :=
  match n with
    0 => unit
  | S k => Real * Vec' k
  end.

Definition vec_to_vec' : forall n, Vec n -> Vec' n :=
  fix recur (n : nat) (v : Vec n) : (Vec' n) :=
    match v in Vec m return Vec' m with
      VNil => tt
    | @VCons n' h t => (h, recur n' t)
    end.

Check vec_to_vec' .
(*
vec_to_vec'
     : forall n : nat, Vec n -> Vec' n
*)
Eval cbn in (vec_to_vec' VNil) .
Eval cbn in (vec_to_vec' VNil : unit) .
Eval cbn in (vec_to_vec' << 5, 9, 6 >>) .
Eval cbn in Vec' 0 .

Fixpoint inner_product' (n : nat) (v1 v2 : Vec' n) : Real :=
  match n return Vec' n -> Vec' n -> Real with
    0 => fun _ _ => 0%Real
  | S n' => fun v1 v2 =>
    match v1, v2 with
      (x1, v1'), (x2, v2') =>
        Rplus (Rmult x1 x2) (inner_product' n' v1' v2')
    end
  end v1 v2.

Definition inner_product {n : nat} (v1 v2 : Vec n) : Real := 
  inner_product' n (vec_to_vec' v1) (vec_to_vec' v2).

Check inner_product'.
(*
inner_product'
     : forall n : nat, Vec' n -> Vec' n -> Real
*)
Check inner_product .
(*
inner_product
     : Vec ?n -> Vec ?n -> Real
where
?n : [ |- nat]
*)
Eval cbn in (inner_product << 1, 2, 3 >> << 1, 2, 3 >>) .
Compute (inner_product << 1, 2, 3 >> << 1, 2, 3 >>) .
Check inner_product << 1, 2, 3 >> << 1, 2, 3 >>.

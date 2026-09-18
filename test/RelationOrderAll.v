(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Relation.Order.All.

Definition relation_order_all_delivers
  : forall (A : Type) (R : A -> A -> Prop),
      StrictOrder R -> PartialOrder R -> TotalOrder R -> ~ Falsum -> Verum
  := fun (A : Type) (R : A -> A -> Prop)
         (_ : StrictOrder R) (_ : PartialOrder R) (_ : TotalOrder R)
         (_ : ~ Falsum) => I.

Definition relation_order_all_delivers_projections
  : forall (A : Type) (R : A -> A -> Prop) (t : TotalOrder R) (x : A) (y : A),
      R x y \/ R y x
  := fun (A : Type) (R : A -> A -> Prop) (t : TotalOrder R) (x : A) (y : A) =>
       Total.totality x y.

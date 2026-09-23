(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.

Module Induced. (* Induced *)

(* [y] is below [x] under [Induced R f] exactly when [f y] is below [f x]
 * under [R].
 *)
(* [forall {A : Type} {B : Type} . (B -> B -> Prop) -> (A -> B) -> A -> A -> Prop] *)
Definition T :=
  fun {A : Type} {B : Type}
    (R : B -> B -> Prop) (f : A -> B) (y : A) (x : A) .
    (R (f y) (f x)).

Abbreviation Induced := T.

(* Induced.introduction *)
Theorem introduction
  : forall {A : Type} {B : Type} {R : B -> B -> Prop} {f : A -> B} {y : A} {x : A} .
      R (f y) (f x) -> Induced R f y x.
Proof.
  intros A B R f y x h.
  ipso h.
Qed.

(* Induced.elimination *)
Theorem elimination
  : forall {A : Type} {B : Type} {R : B -> B -> Prop} {f : A -> B} {y : A} {x : A} .
      Induced R f y x -> R (f y) (f x).
Proof.
  intros A B R f y x h.
  ipso h.
Qed.

End Induced. (* Induced *)

(* The module holds the definition, this gives back the short spelling, as
 * every type in the tree is written.
 *)
Abbreviation Induced := Induced.T.

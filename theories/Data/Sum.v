(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Core.All] carries [->] and [=]: with [-noinit] a file has only what it
   requires. *)
From jwa Require Import Core.All.

(* A sum holds one [A] or one [B], tagged by which. Both are parameters: the
   type behind each tag is fixed for the whole sum. The ctors are named as
   the [Disjunction] ctors are, since a sum is to types what [\/] is to
   propositions. *)
Inductive Sum (A : Type) (B : Type) : Type :=
  | Sum_left  : A -> Sum A B
  | Sum_right : B -> Sum A B.

(* One type is inferred from the value, the other from the expected type; a
   use that has neither needs [@Sum_left A B a]. *)
Arguments Sum_left  {A} {B} a.
Arguments Sum_right {A} {B} b.

(* The eliminator behind [induction], written out. Nothing recurses: a sum
   holds no smaller sum, so one [match] is the whole content. *)
Definition Sum_induction
  : forall (A : Type) (B : Type) (P : Sum A B -> Prop),
      (forall (a : A), P (Sum_left a)) ->
      (forall (b : B), P (Sum_right b)) ->
      forall (s : Sum A B), P s
  := fun (A : Type) (B : Type) (P : Sum A B -> Prop)
         (left  : forall (a : A), P (Sum_left a))
         (right : forall (b : B), P (Sum_right b))
         (s : Sum A B) =>
       match s with
       | Sum_left a  => left a
       | Sum_right b => right b
       end.

(* A module may carry the type's name; its members read [Sum.copair]. *)
Module Sum.

(* [forall {A : Type} {B : Type} {C : Type}, (A -> C) -> (B -> C) -> Sum A B -> C]
   The copairing of [f] and [g]: whichever side the sum holds is handed to
   the function for that side. *)
Definition copair := fun {A : Type} {B : Type} {C : Type}
                         (f : A -> C) (g : B -> C) (s : Sum A B) =>
  match s return C with
  | Sum_left a  => f a
  | Sum_right b => g b
  end.

End Sum.

(* The level is reserved in [Core.Notations]; only the meaning belongs here.
   Declared at file level, it reaches a client through [Require Export]. A
   type former sits in [jwa_type_scope] beside [->], so [A + B -> C] needs
   no delimiter. *)
Notation "A + B" := (Sum A B) : jwa_type_scope.

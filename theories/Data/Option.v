(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Data.Functor.

Inductive Option (A : Type) : Type :=
  | None : Option A
  | Some : A -> Option A.

Arguments None {A}.
Arguments Some {A} a.

(* A module may carry the type's name; its members read [Option.map]. *)
Module Option.

(* [forall {A : Type} {B : Type} . (A -> B) -> Option A -> Option B] *)
Definition map := fun {A : Type} {B : Type} (f : A -> B) (o : Option A) .
  match o return Option B with
  | None   => None
  | Some a => Some (f a)
  end.

Theorem map_identity
  : forall (A : Type) (o : Option A) . map (fun (a : A) . a) o = o.
Proof.
  intros A o.
  destruct o as [| a]; unfold map in |- *; simpl in |- *; reflexivity.
Qed.

Theorem map_composition
  : forall (A : Type) (B : Type) (C : Type) (f : A -> B) (g : B -> C) (o : Option A) .
      map g (map f o) = map (fun (a : A) . g (f a)) o.
Proof.
  intros A B C f g o.
  destruct o as [| a]; simpl in |- *; reflexivity.
Qed.

Theorem some_injectivity
  : forall (A : Type) (a : A) (b : A) . Some a = Some b -> a = b.
Proof.
  intros A a b e.
  pose (f := fun (o : Option A) . match o with | Some x => x | None => a end).
  pose proof (Identity.congruence f e) as e'.
  simpl in e'.
  exact e'.
Qed.

End Option.

Instance Option_functor
  : Functor Option :=
  {| Functor.map             := fun (A : Type) (B : Type) . Option.map
   ; Functor.map_identity    := Option.map_identity
   ; Functor.map_composition := Option.map_composition |}.

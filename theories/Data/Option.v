(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Data.Functor.

(* A module may carry the type's name; its members read [Option.map]. The
 * type and its ctors are declared inside it: a ctor at the top level is
 * rebound by any later file declaring the same name, silently and with no
 * warning.
 *)
Module Option. (* Option *)

Inductive T (A : Type) : Type :=
  | None : T A
  | Some : A -> T A.

Arguments None {A}.
Arguments Some {A} a.

(* The carrier is named [T] so that the type itself reads [Option] on both
 * sides of the module: here through this abbreviation, outside through the
 * one that follows [End Option].
 *)
Abbreviation Option := T.

(* [forall {A : Type} {B : Type} . (A -> B) -> Option A -> Option B] *)
Definition map := fun {A : Type} {B : Type} (f : A -> B) (o : Option A) .
  match o return Option B with
  | None   => None
  | Some a => Some (f a)
  end.

Module some. (* some *)

(* some.injectivity *)
Theorem injectivity
  : forall {A : Type} {a : A} {b : A} . Some a = Some b -> a = b.
Proof.
  intros A a b e.
  let f := fun (o : Option A) . match o with | Some x => x | None => a end.
  let proof e' := Identity.congruence f e.
  simpl in e'.
  ipso e'.
Qed.

End some. (* some *)

Module mapping. (* mapping *)

(* mapping.identity *)
Theorem identity
  : forall {A : Type} (o : Option A) . map (fun (a : A) . a) o = o.
Proof.
  intros A o.
  match o with | | a end;
      simpl map in |- *;
      simpl in |- *;
      quod idem est.
Qed.

(* mapping.composition *)
Theorem composition
  : forall {A : Type} {B : Type} {C : Type} (f : A -> B) (g : B -> C) (o : Option A) .
      map g (map f o) = map (fun (a : A) . g (f a)) o.
Proof.
  intros A B C f g o.
  match o with | | a end;
      simpl in |- *;
      quod idem est.
Qed.

End mapping. (* mapping *)

End Option. (* Option *)

(* The counterpart of the abbreviation inside the module: a client writes
 * [Option A], not [Option.T A].
 *)
Abbreviation Option := Option.T.

(* [Some] and [None] stay reachable unprefixed. An abbreviation is the ctor
 * itself, so [Some a] still serves as a [match] pattern, the implicit [A]
 * survives, and both still print bare. It does not reserve the name: a
 * later file declaring its own [Some] rebinds this one, silently and with
 * no warning.
 *)
Abbreviation None := Option.None.
Abbreviation Some := Option.Some.

Instance Option_functor
  : Functor Option :=
  {| Functor.map             := fun (A : Type) (B : Type) . Option.map
   ; Functor.map_identity    := @Option.mapping.identity
   ; Functor.map_composition := @Option.mapping.composition |}.

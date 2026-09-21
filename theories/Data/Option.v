(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Data.Functor.

(* A module may carry the type's name; its members read [Option.map]. The
 * type and its ctors are declared inside it: across files a duplicate ctor
 * name rebinds the bare one silently and with no warning, so a name's
 * meaning would otherwise depend on import order.
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
  pose (f := fun (o : Option A) . match o with | Some x => x | None => a end).
  pose proof (Identity.congruence f e) as e'.
  simpl in e'.
  exact e'.
Qed.

End some. (* some *)

Module mapping. (* mapping *)

(* mapping.identity *)
Theorem identity
  : forall {A : Type} (o : Option A) . map (fun (a : A) . a) o = o.
Proof.
  intros A o.
  destruct o as [| a];
      unfold map in |- *;
      simpl in |- *;
      reflexivity.
Qed.

(* mapping.composition *)
Theorem composition
  : forall {A : Type} {B : Type} {C : Type} (f : A -> B) (g : B -> C) (o : Option A) .
      map g (map f o) = map (fun (a : A) . g (f a)) o.
Proof.
  intros A B C f g o.
  destruct o as [| a];
      simpl in |- *;
      reflexivity.
Qed.

End mapping. (* mapping *)

End Option. (* Option *)

(* The counterpart of the abbreviation inside the module: a client writes
 * [Option A], not [Option.T A].
 *)
Abbreviation Option := Option.T.

(* The two ctors get their bare spelling back, as [Bool]'s do and for the
 * same reason: they are this type's literals, common enough that the prefix
 * would cost more than it explains. An abbreviation is the ctor itself, so
 * [Some a] still serves as a [match] pattern and the implicit [A] survives.
 * It buys the spelling, not the safety -- a later file declaring its own
 * [Some] rebinds this one silently -- so the exposure is a decision taken
 * here rather than a consequence of where the [Inductive] happened to sit.
 *)
Abbreviation None := Option.None.
Abbreviation Some := Option.Some.

Instance Option_functor
  : Functor Option :=
  {| Functor.map             := fun (A : Type) (B : Type) . Option.map
   ; Functor.map_identity    := @Option.mapping.identity
   ; Functor.map_composition := @Option.mapping.composition |}.

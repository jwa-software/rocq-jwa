(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Data.Collection.List.
From jwa Require Import Data.Number.Nat.

(* A module may carry the type's name; its members read
 * [NonEmptyList.head]. The type and its ctors are declared inside it: a
 * ctor at the top level is rebound by any later file declaring the same
 * name, silently and with no warning.
 *)
Module NonEmptyList. (* NonEmptyList *)

(* A non-empty list is one element, or one element in front of a non-empty
 * list. It differs from [List] in one ctor: where a list ends with [Nil],
 * this ends with an element, so every value has a first element and the
 * operations that read one are total.
 *)
Inductive T (A : Type) : Type :=
  | One  : A -> T A
  | Cons : A -> T A -> T A.

(* [A] is inferred from the element in both ctors, so neither ever needs
 * writing out.
 *)
Arguments One  {A} a.
Arguments Cons {A} a x.

(* The carrier is named [T] so that the type itself reads [NonEmptyList] on
 * both sides of the module: here through this abbreviation, outside
 * through the one that follows [End NonEmptyList].
 *)
Abbreviation NonEmptyList := T.

(* [List]'s scope is opened for the [::] and [[]] of [to_list]. *)
Local Open Scope jwa_list_scope.

(* The eliminator behind the [induction] tactic, written out. Its content
 * is the [fix]: the proof for [Cons a x] is built from the proof for [x],
 * and following [x] down to [One] is what terminates.
 *)
Definition induction
  : forall (A : Type) (P : NonEmptyList A -> Prop) .
      (forall (a : A) . P (One a)) ->
      (forall (a : A) (x : NonEmptyList A) . P x -> P (Cons a x)) ->
      (forall (x : NonEmptyList A) . P x)
  := fun (A : Type) (P : NonEmptyList A -> Prop)
       (base : forall (a : A) . P (One a))
       (step : forall (a : A) (x : NonEmptyList A) . P x -> P (Cons a x)) .
       fix go (x : NonEmptyList A) : P x :=
         match x with
         | One a     => base a
         | Cons a x' => step a x' (go x')
         end.

(* [forall {A : Type} . NonEmptyList A -> A] *)
Definition head := fun {A : Type} (x : NonEmptyList A) .
  match x with
  | One  a   => a
  | Cons a _ => a
  end.

(* [forall {A : Type} . NonEmptyList A -> A] *)
Fixpoint last {A : Type} (x : NonEmptyList A) : A :=
  match x with
  | One  a    => a
  | Cons _ x' => last x'
  end.

(* The count is a [Nat] rather than a [NatWithZero]: no value of this type
 * holds nothing, so the zero would name a case that cannot arise.
 *)
(* [forall {A : Type} . NonEmptyList A -> Nat] *)
Fixpoint length {A : Type} (x : NonEmptyList A) : Nat :=
  match x with
  | One  _    => Nat.One
  | Cons _ x' => Nat.Successor (length x')
  end.

(* The forgetful map into [List]: every operation of [List] is reachable
 * through it, and a law proved there transports along it.
 *)
(* [forall {A : Type} . NonEmptyList A -> List A] *)
Fixpoint to_list {A : Type} (x : NonEmptyList A) : List A :=
  match x with
  | One  a    => a :: []
  | Cons a x' => a :: to_list x'
  end.

End NonEmptyList. (* NonEmptyList *)

(* The counterpart of the abbreviation inside the module: a client writes
 * [NonEmptyList A], not [NonEmptyList.T A].
 *)
Abbreviation NonEmptyList := NonEmptyList.T.

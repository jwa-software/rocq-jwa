(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Core.All] carries [->] and [=]; [Structures.Semigroup] and
   [Structures.Monoid] are the classes the instance at the bottom fills;
   [Data.NatWithZero] is what [length] counts in. *)
From jwa Require Import Core.All.
From jwa Require Import Structures.Semigroup.
From jwa Require Import Structures.Monoid.
From jwa Require Import Data.NatWithZero.

(* A list is empty, or one element in front of a list. [A] is a parameter:
   every element has the one type. *)
Inductive List (A : Type) : Type :=
  | Nil  : List A
  | Cons : A -> List A -> List A.

(* [A] is inferred from the element or, for [Nil], from the expected type; a
   use that has neither needs [@Nil A]. *)
Arguments Nil  {A}.
Arguments Cons {A} a l.

(* The eliminator behind [induction], written out. Its content is the [fix]:
   the proof for [Cons a l] is built from the proof for [l], and following
   [l] down to [Nil] is what terminates. *)
Definition List_induction
  : forall (A : Type) (P : List A -> Prop),
      P Nil ->
      (forall (a : A) (l : List A), P l -> P (Cons a l)) ->
      forall (l : List A), P l
  := fun (A : Type) (P : List A -> Prop)
         (base : P Nil)
         (step : forall (a : A) (l : List A), P l -> P (Cons a l)) =>
       fix go (l : List A) : P l :=
         match l with
         | Nil       => base
         | Cons a l' => step a l' (go l')
         end.

(* A module may carry the type's name; its members read [List.append]. *)
Module List.

(* Recursion is on the first list: [append Nil l2] is [l2], and each [Cons]
   of [l1] is put back in front of the result. *)
Fixpoint append {A : Type} (l1 : List A) (l2 : List A) : List A :=
  match l1 with
  | Nil        => l2
  | Cons a l1' => Cons a (append l1' l2)
  end.

Theorem append_associativity
  : forall {A : Type} (l1 : List A) (l2 : List A) (l3 : List A),
      append (append l1 l2) l3 = append l1 (append l2 l3).
Proof.
  (* The context gains [A], [l1], [l2] and [l3]:
     [|- append (append l1 l2) l3 = append l1 (append l2 l3)] *)
  intros A l1 l2 l3.
  (* [l1] is either [Nil] or [Cons a l1']: one goal per ctor, and the second
     has [a], [l1'] and
     [IH : append (append l1' l2) l3 = append l1' (append l2 l3)] in its
     context. *)
  induction l1 as [| a l1' IH] using List_induction.
  - (* [|- append (append Nil l2) l3 = append Nil (append l2 l3)] *)
    (* Both [append Nil]s compute: [|- append l2 l3 = append l2 l3] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
  - (* [|- append (append (Cons a l1') l2) l3
         = append (Cons a l1') (append l2 l3)] *)
    (* One [append] step on each side:
       [|- Cons a (append (append l1' l2) l3)
           = Cons a (append l1' (append l2 l3))] *)
    simpl in |- *.
    (* [IH] replaces the left side:
       [|- Cons a (append l1' (append l2 l3))
           = Cons a (append l1' (append l2 l3))] *)
    rewrite IH in |- *.
    (* Both sides are the same term. *)
    reflexivity.
Qed.

(* [append] recurses on its first argument, so [append Nil l] reduces while
   [append l Nil] does not; the second identity takes an induction. *)

Lemma append_nil_left : forall {A : Type} (l : List A), append Nil l = l.
Proof.
  (* The context gains [A] and [l]: [|- append Nil l = l] *)
  intros A l.
  (* [append] matches its first argument, and [Nil] returns the second:
     [|- l = l] *)
  simpl in |- *.
  (* Both sides are the same term. *)
  reflexivity.
Qed.

Lemma append_nil_right : forall {A : Type} (l : List A), append l Nil = l.
Proof.
  (* The context gains [A] and [l]: [|- append l Nil = l] *)
  intros A l.
  (* [l] is either [Nil] or [Cons a l']: one goal per ctor, and the second
     has [a], [l'] and [IH : append l' Nil = l'] in its context. *)
  induction l as [| a l' IH] using List_induction.
  - (* [|- append Nil Nil = Nil] *)
    (* [append Nil] computes: [|- Nil = Nil] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
  - (* [|- append (Cons a l') Nil = Cons a l'] *)
    (* One [append] step: [|- Cons a (append l' Nil) = Cons a l'] *)
    simpl in |- *.
    (* [IH] replaces the inner [append]: [|- Cons a l' = Cons a l'] *)
    rewrite IH in |- *.
    (* Both sides are the same term. *)
    reflexivity.
Qed.

(* The empty list has length zero, which is why the count is a
   [NatWithZero] and not a [Nat]. Each [Cons] adds one on the right:
   [add] matches its first argument, so with the recursive call there
   [simpl] leaves [add (length l') (Positive One)] folded instead of
   opening a [match] on a term it cannot reduce. *)
Fixpoint length {A : Type} (l : List A) : NatWithZero :=
  match l with
  | Nil       => Zero
  | Cons _ l' => NatWithZero.add (length l') (Positive One)
  end.

Theorem length_additivity_over_append
  : forall {A : Type} (l1 : List A) (l2 : List A),
      length (append l1 l2) = NatWithZero.add (length l1) (length l2).
Proof.
  (* The context gains [A], [l1] and [l2]:
     [|- length (append l1 l2) = NatWithZero.add (length l1) (length l2)] *)
  intros A l1 l2.
  (* [l1] is either [Nil] or [Cons a l1']: one goal per ctor, and the second
     has [a], [l1'] and
     [IH : length (append l1' l2) = NatWithZero.add (length l1') (length l2)]
     in its context. *)
  induction l1 as [| a l1' IH] using List_induction.
  - (* [|- length (append Nil l2) = NatWithZero.add (length Nil) (length l2)] *)
    (* [append Nil] and [length Nil] compute, and [add Zero] returns its
       second argument: [|- length l2 = length l2] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
  - (* [|- length (append (Cons a l1') l2)
         = NatWithZero.add (length (Cons a l1')) (length l2)] *)
    (* One step of [append] and one of [length] on each side; the [add]s
       stay, since their first arguments are not ctors:
       [|- NatWithZero.add (length (append l1' l2)) (Positive One)
           = NatWithZero.add (NatWithZero.add (length l1') (Positive One))
                             (length l2)] *)
    simpl in |- *.
    (* [IH] replaces the inner [length]:
       [|- NatWithZero.add (NatWithZero.add (length l1') (length l2))
                           (Positive One)
           = NatWithZero.add (NatWithZero.add (length l1') (Positive One))
                             (length l2)] *)
    rewrite IH in |- *.
    (* Associativity regroups the left side:
       [|- NatWithZero.add (length l1')
                           (NatWithZero.add (length l2) (Positive One))
           = NatWithZero.add (NatWithZero.add (length l1') (Positive One))
                             (length l2)] *)
    rewrite NatWithZero.add_associativity in |- *.
    (* And the right side:
       [|- NatWithZero.add (length l1')
                           (NatWithZero.add (length l2) (Positive One))
           = NatWithZero.add (length l1')
                             (NatWithZero.add (Positive One) (length l2))] *)
    rewrite NatWithZero.add_associativity in |- *.
    (* Commutativity of the inner sum on the left, with its arguments named
       so that [rewrite] does not pick the outer sum:
       [|- NatWithZero.add (length l1')
                           (NatWithZero.add (Positive One) (length l2))
           = NatWithZero.add (length l1')
                             (NatWithZero.add (Positive One) (length l2))] *)
    rewrite (NatWithZero.add_commutativity (length l2) (Positive One)) in |- *.
    (* Both sides are the same term. *)
    reflexivity.
Qed.

End List.

(* The level is reserved in [Core.Notations]; only the meaning belongs here.
   Declared at file level, it reaches a client through [Require Export]. *)
Notation "l1 ++ l2" := (List.append l1 l2) : jwa_type_scope.

(* [[]] lives in [jwa_list_scope], which [Core.Notations] declares without
   opening: a client writes [[]%list] or opens the scope. The token is
   [[]] as one piece; [[ ]] with a space is not it. *)
Notation "[]" := Nil : jwa_list_scope.

(* [append] with [Nil] is the monoid on lists. [A] is a parameter of the
   instance, so every element type gets one; [@] makes it explicit where
   the operation and the laws are handed over unapplied. *)
Instance List_append_monoid
  : forall (A : Type), Monoid.T (List A) (@List.append A) Nil :=
  fun (A : Type) =>
    {| Monoid.semigroup :=
         {| Semigroup.associativity := @List.append_associativity A |}
     ; Monoid.identity_left  := @List.append_nil_left A
     ; Monoid.identity_right := @List.append_nil_right A |}.

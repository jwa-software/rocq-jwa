(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Core.All] carries [->] and [=]; [Structures.Semigroup],
   [Structures.Monoid] and [Structures.Functor] are the classes the
   instances at the bottom fill; [Data.NatWithZero] is what [length] counts
   in. *)
From jwa Require Import Core.All.
From jwa Require Import Structures.Semigroup.
From jwa Require Import Structures.Monoid.
From jwa Require Import Structures.Functor.
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

(* [map] applies [f] to every element and keeps the shape. *)
Fixpoint map {A : Type} {B : Type} (f : A -> B) (l : List A) : List B :=
  match l with
  | Nil       => Nil
  | Cons a l' => Cons (f a) (map f l')
  end.

(* The two functor laws, stated for every [l] as in [Data.Option]: nothing
   here assumes functional extensionality. *)

Theorem map_identity
  : forall (A : Type) (l : List A), map (fun a => a) l = l.
Proof.
  (* The context gains [A] and [l]: [|- map (fun a => a) l = l] *)
  intros A l.
  (* [l] is either [Nil] or [Cons a l']: one goal per ctor, and the second
     has [a], [l'] and [IH : map (fun a => a) l' = l'] in its context. *)
  induction l as [| a l' IH] using List_induction.
  - (* [|- map (fun a => a) Nil = Nil] *)
    (* [map] on [Nil] computes: [|- Nil = Nil] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
  - (* [|- map (fun a => a) (Cons a l') = Cons a l'] *)
    (* One [map] step, and [(fun a => a) a] reduces to [a]:
       [|- Cons a (map (fun a => a) l') = Cons a l'] *)
    simpl in |- *.
    (* [IH] replaces the inner [map]: [|- Cons a l' = Cons a l'] *)
    rewrite IH in |- *.
    (* Both sides are the same term. *)
    reflexivity.
Qed.

Theorem map_composition
  : forall (A : Type) (B : Type) (C : Type) (f : A -> B) (g : B -> C)
      (l : List A),
    map g (map f l) = map (fun a => g (f a)) l.
Proof.
  (* The context gains [A], [B], [C], [f], [g] and [l]:
     [|- map g (map f l) = map (fun a => g (f a)) l] *)
  intros A B C f g l.
  (* [l] is either [Nil] or [Cons a l']: one goal per ctor, and the second
     has [a], [l'] and [IH : map g (map f l') = map (fun a => g (f a)) l']
     in its context. *)
  induction l as [| a l' IH] using List_induction.
  - (* [|- map g (map f Nil) = map (fun a => g (f a)) Nil] *)
    (* Every [map] on [Nil] computes: [|- Nil = Nil] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
  - (* [|- map g (map f (Cons a l')) = map (fun a => g (f a)) (Cons a l')] *)
    (* Two [map] steps on the left, one on the right, and the composed
       function applied to [a] reduces to [g (f a)]:
       [|- Cons (g (f a)) (map g (map f l'))
           = Cons (g (f a)) (map (fun a => g (f a)) l')] *)
    simpl in |- *.
    (* [IH] replaces the inner [map]s:
       [|- Cons (g (f a)) (map (fun a => g (f a)) l')
           = Cons (g (f a)) (map (fun a => g (f a)) l')] *)
    rewrite IH in |- *.
    (* Both sides are the same term. *)
    reflexivity.
Qed.

(* [map] distributes over [append]: mapping a concatenation is
   concatenating the mapped halves. *)
Theorem map_distributivity_over_append
  : forall (A : Type) (B : Type) (f : A -> B) (l1 : List A) (l2 : List A),
      map f (append l1 l2) = append (map f l1) (map f l2).
Proof.
  (* The context gains [A], [B], [f], [l1] and [l2]:
     [|- map f (append l1 l2) = append (map f l1) (map f l2)] *)
  intros A B f l1 l2.
  (* [l1] is either [Nil] or [Cons a l1']: one goal per ctor, and the second
     has [a], [l1'] and
     [IH : map f (append l1' l2) = append (map f l1') (map f l2)] in its
     context. *)
  induction l1 as [| a l1' IH] using List_induction.
  - (* [|- map f (append Nil l2) = append (map f Nil) (map f l2)] *)
    (* [append Nil], [map f Nil] and then [append Nil] again compute:
       [|- map f l2 = map f l2] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
  - (* [|- map f (append (Cons a l1') l2)
         = append (map f (Cons a l1')) (map f l2)] *)
    (* One step of [append] and of [map] on each side:
       [|- Cons (f a) (map f (append l1' l2))
           = Cons (f a) (append (map f l1') (map f l2))] *)
    simpl in |- *.
    (* [IH] replaces the inner [map]:
       [|- Cons (f a) (append (map f l1') (map f l2))
           = Cons (f a) (append (map f l1') (map f l2))] *)
    rewrite IH in |- *.
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

(* The two functor laws were already proved above, so the instance only
   hands them over. [map]'s type arguments are maximally inserted, so the
   bare name collapses to one fixed pair of them; binding [A] and [B] first
   is what keeps it general enough for the field, as in [Data.Option]. *)
Instance List_functor : Functor.T List :=
  {| Functor.map             := fun (A : Type) (B : Type) => List.map
   ; Functor.map_identity    := List.map_identity
   ; Functor.map_composition := List.map_composition |}.

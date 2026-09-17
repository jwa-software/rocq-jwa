(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Core.All] carries [->] and [=]; [Structures.Semigroup],
   [Structures.Monoid] and [Structures.Functor] are the classes the
   instances at the bottom fill; [Data.NatWithZero] is what [length] counts
   in, [Data.Nat] carries the [One] inside [Positive One], and [Data.Bool]
   is what a [filter] predicate answers in. *)
From jwa Require Import Core.All.
From jwa Require Import Structures.Semigroup.
From jwa Require Import Structures.Monoid.
From jwa Require Import Structures.Functor.
From jwa Require Import Data.Bool.
From jwa Require Import Data.Nat.
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

(* [reverse] moves each element to the end of the reversed rest. Quadratic,
   and the simplest shape for the proofs below; an accumulator version can
   come with a proof that it agrees. *)
Fixpoint reverse {A : Type} (l : List A) : List A :=
  match l with
  | Nil       => Nil
  | Cons a l' => append (reverse l') (Cons a Nil)
  end.

(* [reverse] turns a concatenation around: the reversed halves come back in
   the opposite order. *)
Theorem reverse_antidistributivity_over_append
  : forall (A : Type) (l1 : List A) (l2 : List A),
      reverse (append l1 l2) = append (reverse l2) (reverse l1).
Proof.
  (* The context gains [A], [l1] and [l2]:
     [|- reverse (append l1 l2) = append (reverse l2) (reverse l1)] *)
  intros A l1 l2.
  (* [l1] is either [Nil] or [Cons a l1']: one goal per ctor, and the second
     has [a], [l1'] and
     [IH : reverse (append l1' l2) = append (reverse l2) (reverse l1')] in
     its context. *)
  induction l1 as [| a l1' IH] using List_induction.
  - (* [|- reverse (append Nil l2) = append (reverse l2) (reverse Nil)] *)
    (* [append Nil] and [reverse Nil] compute; [append (reverse l2) Nil]
       does not, since its first argument is not a ctor:
       [|- reverse l2 = append (reverse l2) Nil] *)
    simpl in |- *.
    (* [append_nil_right] removes the trailing [Nil]:
       [|- reverse l2 = reverse l2] *)
    rewrite append_nil_right in |- *.
    (* Both sides are the same term. *)
    reflexivity.
  - (* [|- reverse (append (Cons a l1') l2)
         = append (reverse l2) (reverse (Cons a l1'))] *)
    (* One [append] step and one [reverse] step on the left, one [reverse]
       step on the right:
       [|- append (reverse (append l1' l2)) (Cons a Nil)
           = append (reverse l2) (append (reverse l1') (Cons a Nil))] *)
    simpl in |- *.
    (* [IH] replaces the inner [reverse]:
       [|- append (append (reverse l2) (reverse l1')) (Cons a Nil)
           = append (reverse l2) (append (reverse l1') (Cons a Nil))] *)
    rewrite IH in |- *.
    (* Associativity regroups the left side:
       [|- append (reverse l2) (append (reverse l1') (Cons a Nil))
           = append (reverse l2) (append (reverse l1') (Cons a Nil))] *)
    rewrite append_associativity in |- *.
    (* Both sides are the same term. *)
    reflexivity.
Qed.

Theorem reverse_involution
  : forall (A : Type) (l : List A), reverse (reverse l) = l.
Proof.
  (* The context gains [A] and [l]: [|- reverse (reverse l) = l] *)
  intros A l.
  (* [l] is either [Nil] or [Cons a l']: one goal per ctor, and the second
     has [a], [l'] and [IH : reverse (reverse l') = l'] in its context. *)
  induction l as [| a l' IH] using List_induction.
  - (* [|- reverse (reverse Nil) = Nil] *)
    (* Both [reverse]s compute: [|- Nil = Nil] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
  - (* [|- reverse (reverse (Cons a l')) = Cons a l'] *)
    (* The inner [reverse] steps once; the outer one is stuck on the
       [append] that results:
       [|- reverse (append (reverse l') (Cons a Nil)) = Cons a l'] *)
    simpl in |- *.
    (* [reverse_antidistributivity_over_append] turns the [append] around:
       [|- append (reverse (Cons a Nil)) (reverse (reverse l')) = Cons a l'] *)
    rewrite reverse_antidistributivity_over_append in |- *.
    (* [reverse (Cons a Nil)] computes to [Cons a Nil], and [append] of a
       one-element list steps: [|- Cons a (reverse (reverse l')) = Cons a l'] *)
    simpl in |- *.
    (* [IH] replaces the double [reverse]: [|- Cons a l' = Cons a l'] *)
    rewrite IH in |- *.
    (* Both sides are the same term. *)
    reflexivity.
Qed.

(* [fold_right f z] replaces every [Cons] by [f] and the final [Nil] by [z],
   working from the right: [Cons a (Cons b Nil)] becomes [f a (f b z)]. *)
Fixpoint fold_right {A : Type} {B : Type} (f : A -> B -> B) (z : B)
                    (l : List A) : B :=
  match l with
  | Nil       => z
  | Cons a l' => f a (fold_right f z l')
  end.

(* Read [fold_right f _ l] as a function of its seed; then the fold of a
   concatenation is the composition of the two folds, the second list's
   applied first. *)
Theorem fold_right_composition_over_append
  : forall (A : Type) (B : Type) (f : A -> B -> B) (z : B)
      (l1 : List A) (l2 : List A),
    fold_right f z (append l1 l2) = fold_right f (fold_right f z l2) l1.
Proof.
  (* The context gains [A], [B], [f], [z], [l1] and [l2]:
     [|- fold_right f z (append l1 l2)
         = fold_right f (fold_right f z l2) l1] *)
  intros A B f z l1 l2.
  (* [l1] is either [Nil] or [Cons a l1']: one goal per ctor, and the second
     has [a], [l1'] and
     [IH : fold_right f z (append l1' l2)
           = fold_right f (fold_right f z l2) l1']
     in its context. *)
  induction l1 as [| a l1' IH] using List_induction.
  - (* [|- fold_right f z (append Nil l2)
         = fold_right f (fold_right f z l2) Nil] *)
    (* [append Nil] and the outer fold on [Nil] compute:
       [|- fold_right f z l2 = fold_right f z l2] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
  - (* [|- fold_right f z (append (Cons a l1') l2)
         = fold_right f (fold_right f z l2) (Cons a l1')] *)
    (* One [append] step and one fold step on each side:
       [|- f a (fold_right f z (append l1' l2))
           = f a (fold_right f (fold_right f z l2) l1')] *)
    simpl in |- *.
    (* [IH] replaces the inner fold:
       [|- f a (fold_right f (fold_right f z l2) l1')
           = f a (fold_right f (fold_right f z l2) l1')] *)
    rewrite IH in |- *.
    (* Both sides are the same term. *)
    reflexivity.
Qed.

(* A catamorphism is a function on lists that is some [fold_right]: it only
   fixes what replaces [Cons] and what replaces [Nil]. [append], [length]
   and [map] are three of them. *)

Theorem append_catamorphism
  : forall (A : Type) (l1 : List A) (l2 : List A),
      append l1 l2 = fold_right Cons l2 l1.
Proof.
  (* The context gains [A], [l1] and [l2]:
     [|- append l1 l2 = fold_right Cons l2 l1] *)
  intros A l1 l2.
  (* [l1] is either [Nil] or [Cons a l1']: one goal per ctor, and the second
     has [a], [l1'] and [IH : append l1' l2 = fold_right Cons l2 l1'] in its
     context. *)
  induction l1 as [| a l1' IH] using List_induction.
  - (* [|- append Nil l2 = fold_right Cons l2 Nil] *)
    (* Both sides compute to [l2]: [|- l2 = l2] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
  - (* [|- append (Cons a l1') l2 = fold_right Cons l2 (Cons a l1')] *)
    (* One step on each side:
       [|- Cons a (append l1' l2) = Cons a (fold_right Cons l2 l1')] *)
    simpl in |- *.
    (* [IH] replaces the inner [append]:
       [|- Cons a (fold_right Cons l2 l1') = Cons a (fold_right Cons l2 l1')] *)
    rewrite IH in |- *.
    (* Both sides are the same term. *)
    reflexivity.
Qed.

Theorem length_catamorphism
  : forall (A : Type) (l : List A),
      length l
      = fold_right (fun (_ : A) (n : NatWithZero) => NatWithZero.add n (Positive One))
                   Zero
                   l.
Proof.
  (* The context gains [A] and [l]:
     [|- length l = fold_right (fun _ n => add n (Positive One)) Zero l] *)
  intros A l.
  (* [l] is either [Nil] or [Cons a l']: one goal per ctor, and the second
     has [a], [l'] and [IH], the statement for [l'], in its context. *)
  induction l as [| a l' IH] using List_induction.
  - (* Both sides compute to [Zero]: [|- Zero = Zero] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
  - (* One step on each side, and the function applied to [a] reduces:
       [|- NatWithZero.add (length l') (Positive One)
           = NatWithZero.add (fold_right (fun _ n => add n (Positive One))
                                          Zero
                                          l')
                             (Positive One)] *)
    simpl in |- *.
    (* [IH] replaces [length l']; both sides are then the same term. *)
    rewrite IH in |- *.
    (* Both sides are the same term. *)
    reflexivity.
Qed.

Theorem map_catamorphism
  : forall (A : Type) (B : Type) (f : A -> B) (l : List A),
      map f l
      = fold_right (fun (a : A) (mapped : List B) => Cons (f a) mapped)
                   Nil
                   l.
Proof.
  (* The context gains [A], [B], [f] and [l]:
     [|- map f l = fold_right (fun a mapped => Cons (f a) mapped) Nil l] *)
  intros A B f l.
  (* [l] is either [Nil] or [Cons a l']: one goal per ctor, and the second
     has [a], [l'] and [IH], the statement for [l'], in its context. *)
  induction l as [| a l' IH] using List_induction.
  - (* Both sides compute to [Nil]: [|- Nil = Nil] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
  - (* One step on each side, and the function applied to [a] reduces:
       [|- Cons (f a) (map f l')
           = Cons (f a) (fold_right (fun a mapped => Cons (f a) mapped)
                                    Nil l')] *)
    simpl in |- *.
    (* [IH] replaces [map f l']; both sides are then the same term. *)
    rewrite IH in |- *.
    (* Both sides are the same term. *)
    reflexivity.
Qed.

(* Membership, defined by recursion into [Prop]: [Contains a Nil] computes
   to [Falsum] and [Contains a (Cons b l)] to [a = b \/ Contains a l], so
   [simpl] exposes the cases and every proof below is a case analysis. *)
Fixpoint Contains {A : Type} (a : A) (l : List A) : Prop :=
  match l with
  | Nil       => Falsum
  | Cons b l' => a = b \/ Contains a l'
  end.

Theorem nil_contains_nothing
  : forall (A : Type) (a : A), ~ Contains a Nil.
Proof.
  (* The context gains [A] and [a]: [|- ~ Contains a Nil] *)
  intros A a.
  (* [|- Contains a Nil -> Falsum] *)
  unfold Unjunction in |- *.
  (* [Contains a Nil] computes: [|- Falsum -> Falsum] *)
  simpl in |- *.
  (* The context gains [f : Falsum]: [|- Falsum] *)
  intro f.
  (* [f] is a proof of the goal as it stands. *)
  exact f.
Qed.

(* Membership in a concatenation is membership in either half. The two
   halves are lemmas, the [<->] the theorem. *)

Lemma contains_distributivity_over_append_forward
  : forall (A : Type) (a : A) (l1 : List A) (l2 : List A),
      Contains a (append l1 l2) -> Contains a l1 \/ Contains a l2.
Proof.
  (* The context gains [A], [a], [l1] and [l2]:
     [|- Contains a (append l1 l2) -> Contains a l1 \/ Contains a l2] *)
  intros A a l1 l2.
  (* [l1] is either [Nil] or [Cons b l1']: one goal per ctor, and the second
     has [b], [l1'] and
     [IH : Contains a (append l1' l2) -> Contains a l1' \/ Contains a l2]
     in its context. *)
  induction l1 as [| b l1' IH] using List_induction.
  - (* [|- Contains a (append Nil l2) -> Contains a Nil \/ Contains a l2] *)
    (* [append Nil] and [Contains a Nil] compute:
       [|- Contains a l2 -> Falsum \/ Contains a l2] *)
    simpl in |- *.
    (* The context gains [h : Contains a l2]: [|- Falsum \/ Contains a l2] *)
    intro h.
    (* [h] is the right side. *)
    exact (Disjunction_right h).
  - (* [|- Contains a (append (Cons b l1') l2)
         -> Contains a (Cons b l1') \/ Contains a l2] *)
    (* One [append] step and both [Contains] on a [Cons] compute:
       [|- a = b \/ Contains a (append l1' l2)
           -> (a = b \/ Contains a l1') \/ Contains a l2] *)
    simpl in |- *.
    (* The context gains [h : a = b \/ Contains a (append l1' l2)]:
       [|- (a = b \/ Contains a l1') \/ Contains a l2] *)
    intro h.
    (* [h] gives two goals: one with [e : a = b], one with
       [h' : Contains a (append l1' l2)]. *)
    destruct h as [e | h'].
    + (* [e] is the left side of the left side. *)
      exact (Disjunction_left (Disjunction_left e)).
    + (* [IH] turns [h'] into [Contains a l1' \/ Contains a l2], which
         gives two goals: one with [h1 : Contains a l1'], one with
         [h2 : Contains a l2]. *)
      destruct (IH h') as [h1 | h2].
      * (* [h1] is the right side of the left side. *)
        exact (Disjunction_left (Disjunction_right h1)).
      * (* [h2] is the right side. *)
        exact (Disjunction_right h2).
Qed.

Lemma contains_distributivity_over_append_backward
  : forall (A : Type) (a : A) (l1 : List A) (l2 : List A),
      Contains a l1 \/ Contains a l2 -> Contains a (append l1 l2).
Proof.
  (* The context gains [A], [a], [l1] and [l2]:
     [|- Contains a l1 \/ Contains a l2 -> Contains a (append l1 l2)] *)
  intros A a l1 l2.
  (* [l1] is either [Nil] or [Cons b l1']: one goal per ctor, and the second
     has [b], [l1'] and
     [IH : Contains a l1' \/ Contains a l2 -> Contains a (append l1' l2)]
     in its context. *)
  induction l1 as [| b l1' IH] using List_induction.
  - (* [|- Contains a Nil \/ Contains a l2 -> Contains a (append Nil l2)] *)
    (* [Contains a Nil] and [append Nil] compute:
       [|- Falsum \/ Contains a l2 -> Contains a l2] *)
    simpl in |- *.
    (* The context gains [h : Falsum \/ Contains a l2]: [|- Contains a l2] *)
    intro h.
    (* [h] gives two goals: one with [f : Falsum], one with
       [h2 : Contains a l2]. *)
    destruct h as [f | h2].
    + (* [f : Falsum], which is what [contradiction] looks for. *)
      contradiction.
    + (* [h2] is a proof of the goal as it stands. *)
      exact h2.
  - (* [|- Contains a (Cons b l1') \/ Contains a l2
         -> Contains a (append (Cons b l1') l2)] *)
    (* Both [Contains] on a [Cons] and the [append] step compute:
       [|- (a = b \/ Contains a l1') \/ Contains a l2
           -> a = b \/ Contains a (append l1' l2)] *)
    simpl in |- *.
    (* The context gains [h : (a = b \/ Contains a l1') \/ Contains a l2]:
       [|- a = b \/ Contains a (append l1' l2)] *)
    intro h.
    (* [h] gives two goals: one with [h1 : a = b \/ Contains a l1'], one
       with [h2 : Contains a l2]. *)
    destruct h as [h1 | h2].
    + (* [h1] gives two goals: one with [e : a = b], one with
         [h1' : Contains a l1']. *)
      destruct h1 as [e | h1'].
      * (* [e] is the left side. *)
        exact (Disjunction_left e).
      * (* [Disjunction_right] turns the goal into its right side:
           [|- Contains a (append l1' l2)] *)
        apply Disjunction_right.
        (* [IH] turns a proof of [Contains a l1' \/ Contains a l2] into
           one of the goal: [|- Contains a l1' \/ Contains a l2] *)
        apply IH.
        (* [h1'] is the left side. *)
        exact (Disjunction_left h1').
    + (* [Disjunction_right] turns the goal into its right side:
         [|- Contains a (append l1' l2)] *)
      apply Disjunction_right.
      (* [IH] turns a proof of [Contains a l1' \/ Contains a l2] into one
         of the goal: [|- Contains a l1' \/ Contains a l2] *)
      apply IH.
      (* [h2] is the right side. *)
      exact (Disjunction_right h2).
Qed.

Theorem contains_distributivity_over_append
  : forall (A : Type) (a : A) (l1 : List A) (l2 : List A),
      Contains a (append l1 l2) <-> Contains a l1 \/ Contains a l2.
Proof.
  (* The context gains [A], [a], [l1] and [l2]:
     [|- Contains a (append l1 l2) <-> Contains a l1 \/ Contains a l2] *)
  intros A a l1 l2.
  (* [Bijunction] has one ctor with two fields, so the goal splits into two
     goals, the forward and the backward half. *)
  split.
  - (* [contains_distributivity_over_append_forward A a l1 l2] is a proof
       of the goal as it stands. *)
    exact (contains_distributivity_over_append_forward A a l1 l2).
  - (* [contains_distributivity_over_append_backward A a l1 l2] is a proof
       of the goal as it stands. *)
    exact (contains_distributivity_over_append_backward A a l1 l2).
Qed.

(* [map] carries membership along: an element of [l] has its image in
   [map f l]. *)
Theorem map_containment_preservation
  : forall (A : Type) (B : Type) (f : A -> B) (a : A) (l : List A),
      Contains a l -> Contains (f a) (map f l).
Proof.
  (* The context gains [A], [B], [f], [a] and [l]:
     [|- Contains a l -> Contains (f a) (map f l)] *)
  intros A B f a l.
  (* [l] is either [Nil] or [Cons b l']: one goal per ctor, and the second
     has [b], [l'] and [IH : Contains a l' -> Contains (f a) (map f l')] in
     its context. *)
  induction l as [| b l' IH] using List_induction.
  - (* [|- Contains a Nil -> Contains (f a) (map f Nil)] *)
    (* [map f Nil] and both [Contains] compute: [|- Falsum -> Falsum] *)
    simpl in |- *.
    (* The context gains [g : Falsum]: [|- Falsum] *)
    intro g.
    (* [g] is a proof of the goal as it stands. *)
    exact g.
  - (* [|- Contains a (Cons b l') -> Contains (f a) (map f (Cons b l'))] *)
    (* The [map] step and both [Contains] compute:
       [|- a = b \/ Contains a l' -> f a = f b \/ Contains (f a) (map f l')] *)
    simpl in |- *.
    (* The context gains [h : a = b \/ Contains a l']:
       [|- f a = f b \/ Contains (f a) (map f l')] *)
    intro h.
    (* [h] gives two goals: one with [e : a = b], one with
       [h' : Contains a l']. *)
    destruct h as [e | h'].
    + (* [Disjunction_left] turns the goal into its left side:
         [|- f a = f b] *)
      apply Disjunction_left.
      (* [e] replaces [a] by [b]: [|- f b = f b] *)
      rewrite e in |- *.
      (* Both sides are the same term. *)
      reflexivity.
    + (* [Disjunction_right] turns the goal into its right side:
         [|- Contains (f a) (map f l')] *)
      apply Disjunction_right.
      (* [IH] turns a proof of [Contains a l'] into one of the goal:
         [|- Contains a l'] *)
      apply IH.
      (* [h'] is a proof of the goal as it stands. *)
      exact h'.
Qed.

(* [reverse] keeps membership, in both directions; each direction goes
   through the distributivity over [append], since [reverse] is built from
   it. *)

Lemma reverse_containment_preservation_forward
  : forall (A : Type) (a : A) (l : List A),
      Contains a (reverse l) -> Contains a l.
Proof.
  (* The context gains [A], [a] and [l]:
     [|- Contains a (reverse l) -> Contains a l] *)
  intros A a l.
  (* [l] is either [Nil] or [Cons b l']: one goal per ctor, and the second
     has [b], [l'] and [IH : Contains a (reverse l') -> Contains a l'] in
     its context. *)
  induction l as [| b l' IH] using List_induction.
  - (* [|- Contains a (reverse Nil) -> Contains a Nil] *)
    (* [reverse Nil] and [Contains a Nil] compute: [|- Falsum -> Falsum] *)
    simpl in |- *.
    (* The context gains [f : Falsum]: [|- Falsum] *)
    intro f.
    (* [f] is a proof of the goal as it stands. *)
    exact f.
  - (* [|- Contains a (reverse (Cons b l')) -> Contains a (Cons b l')] *)
    (* The [reverse] step and the [Contains] on the right compute:
       [|- Contains a (append (reverse l') (Cons b Nil))
           -> a = b \/ Contains a l'] *)
    simpl in |- *.
    (* The context gains [h : Contains a (append (reverse l') (Cons b Nil))]:
       [|- a = b \/ Contains a l'] *)
    intro h.
    (* The forward distributivity splits [h] into two goals: one with
       [h1 : Contains a (reverse l')], one with
       [h2 : Contains a (Cons b Nil)]. *)
    destruct (contains_distributivity_over_append_forward
                A a (reverse l') (Cons b Nil) h) as [h1 | h2].
    + (* [Disjunction_right] turns the goal into its right side:
         [|- Contains a l'] *)
      apply Disjunction_right.
      (* [IH] turns a proof of [Contains a (reverse l')] into one of the
         goal: [|- Contains a (reverse l')] *)
      apply IH.
      (* [h1] is a proof of the goal as it stands. *)
      exact h1.
    + (* [h2] computes to [a = b \/ Falsum]. *)
      simpl in h2.
      (* [h2] gives two goals: one with [e : a = b], one with
         [f : Falsum]. *)
      destruct h2 as [e | f].
      * (* [e] is the left side. *)
        exact (Disjunction_left e).
      * (* [f : Falsum], which is what [contradiction] looks for. *)
        contradiction.
Qed.

Lemma reverse_containment_preservation_backward
  : forall (A : Type) (a : A) (l : List A),
      Contains a l -> Contains a (reverse l).
Proof.
  (* The context gains [A], [a] and [l]:
     [|- Contains a l -> Contains a (reverse l)] *)
  intros A a l.
  (* [l] is either [Nil] or [Cons b l']: one goal per ctor, and the second
     has [b], [l'] and [IH : Contains a l' -> Contains a (reverse l')] in
     its context. *)
  induction l as [| b l' IH] using List_induction.
  - (* [|- Contains a Nil -> Contains a (reverse Nil)] *)
    (* [Contains a Nil] and [reverse Nil] compute: [|- Falsum -> Falsum] *)
    simpl in |- *.
    (* The context gains [f : Falsum]: [|- Falsum] *)
    intro f.
    (* [f] is a proof of the goal as it stands. *)
    exact f.
  - (* [|- Contains a (Cons b l') -> Contains a (reverse (Cons b l'))] *)
    (* The [Contains] on the left and the [reverse] step compute:
       [|- a = b \/ Contains a l'
           -> Contains a (append (reverse l') (Cons b Nil))] *)
    simpl in |- *.
    (* The context gains [h : a = b \/ Contains a l']:
       [|- Contains a (append (reverse l') (Cons b Nil))] *)
    intro h.
    (* The backward distributivity turns a proof of
       [Contains a (reverse l') \/ Contains a (Cons b Nil)] into one of the
       goal: [|- Contains a (reverse l') \/ Contains a (Cons b Nil)] *)
    apply contains_distributivity_over_append_backward.
    (* [h] gives two goals: one with [e : a = b], one with
       [h' : Contains a l']. *)
    destruct h as [e | h'].
    + (* [Disjunction_right] turns the goal into its right side:
         [|- Contains a (Cons b Nil)] *)
      apply Disjunction_right.
      (* [Contains a (Cons b Nil)] computes: [|- a = b \/ Falsum] *)
      simpl in |- *.
      (* [e] is the left side. *)
      exact (Disjunction_left e).
    + (* [Disjunction_left] turns the goal into its left side:
         [|- Contains a (reverse l')] *)
      apply Disjunction_left.
      (* [IH] turns a proof of [Contains a l'] into one of the goal:
         [|- Contains a l'] *)
      apply IH.
      (* [h'] is a proof of the goal as it stands. *)
      exact h'.
Qed.

Theorem reverse_containment_preservation
  : forall (A : Type) (a : A) (l : List A),
      Contains a (reverse l) <-> Contains a l.
Proof.
  (* The context gains [A], [a] and [l]:
     [|- Contains a (reverse l) <-> Contains a l] *)
  intros A a l.
  (* [Bijunction] has one ctor with two fields, so the goal splits into two
     goals, the forward and the backward half. *)
  split.
  - (* [reverse_containment_preservation_forward A a l] is a proof of the
       goal as it stands. *)
    exact (reverse_containment_preservation_forward A a l).
  - (* [reverse_containment_preservation_backward A a l] is a proof of the
       goal as it stands. *)
    exact (reverse_containment_preservation_backward A a l).
Qed.

(* [filter p] keeps the elements [p] answers [true] on, in their order. *)
Fixpoint filter {A : Type} (p : A -> Bool) (l : List A) : List A :=
  match l with
  | Nil       => Nil
  | Cons a l' =>
      match p a with
      | true  => Cons a (filter p l')
      | false => filter p l'
      end
  end.
End List.

(* The level is reserved in [Core.Notations]; only the meaning belongs here.
   Declared at file level, it reaches a client through [Require Export].
   Every list notation lives in [jwa_list_scope], which [Core.Notations]
   declares without opening: a client writes [(l1 ++ l2)%list] or opens the
   scope. *)
Notation "l1 ++ l2" := (List.append l1 l2) : jwa_list_scope.

(* The token is [[]] as one piece; [[ ]] with a space is not it. *)
Notation "[]" := Nil : jwa_list_scope.

(* Membership reads as a sentence, [l contains a], with the list first; the
   arguments of [Contains] are the other way round, element first, so that
   [Contains a] is a predicate on lists. *)
Notation "l 'contains' a" := (List.Contains a l)
  : jwa_list_scope.

(* The same relation read from the element's side. [only parsing] keeps one
   spelling for printing, so a goal always shows [l contains a]. *)
Notation "a 'belongs_to' l" := (List.Contains a l) (only parsing)
  : jwa_list_scope.

(* The negations, so that [~ Contains a l] reads and prints as a sentence
   too; the element-first form is again [only parsing]. *)
Notation "l 'does_not_contain' a" := (~ (List.Contains a l))
  : jwa_list_scope.
Notation "a 'does_not_belong_to' l" := (~ (List.Contains a l)) (only parsing)
  : jwa_list_scope.

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

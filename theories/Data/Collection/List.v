(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Core.All] carries [->] and [=]; [Algebra.Semigroup],
   [Algebra.Monoid] and [Data.Functor] are the classes the
   instances at the bottom fill; [Data.Number.NatWithZero] is what [length] counts
   in, [Data.Number.Nat] carries the [One] inside [Positive One], [Data.Bool] is
   what a [filter] predicate answers in, [Data.Option] is what [head] and
   [tail] answer in, and [Data.Pair] is what [pop], [zip] and [partition]
   answer in. *)
From jwa Require Import Algebra.Monoid.
From jwa Require Import Algebra.Semigroup.
From jwa Require Import Core.All.
From jwa Require Import Data.Bool.
From jwa Require Import Data.Functor.
From jwa Require Import Data.Number.Nat.
From jwa Require Import Data.Number.NatWithZero.
From jwa Require Import Data.Option.
From jwa Require Import Data.Pair.

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

Lemma append_left_identity : forall {A : Type} (l : List A), append Nil l = l.
Proof.
  (* The context gains [A] and [l]: [|- append Nil l = l] *)
  intros A l.
  (* [append] matches its first argument, and [Nil] returns the second:
     [|- l = l] *)
  simpl in |- *.
  (* Both sides are the same term. *)
  reflexivity.
Qed.

Lemma append_right_identity : forall {A : Type} (l : List A), append l Nil = l.
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
    (* [append_right_identity] removes the trailing [Nil]:
       [|- reverse l2 = reverse l2] *)
    rewrite append_right_identity in |- *.
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
  unfold Negation in |- *.
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
    exact (Disjunction.right h).
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
      exact (Disjunction.left (Disjunction.left e)).
    + (* [IH] turns [h'] into [Contains a l1' \/ Contains a l2], which
         gives two goals: one with [h1 : Contains a l1'], one with
         [h2 : Contains a l2]. *)
      destruct (IH h') as [h1 | h2].
      * (* [h1] is the right side of the left side. *)
        exact (Disjunction.left (Disjunction.right h1)).
      * (* [h2] is the right side. *)
        exact (Disjunction.right h2).
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
        exact (Disjunction.left e).
      * (* [Disjunction.right] turns the goal into its right side:
           [|- Contains a (append l1' l2)] *)
        apply Disjunction.right.
        (* [IH] turns a proof of [Contains a l1' \/ Contains a l2] into
           one of the goal: [|- Contains a l1' \/ Contains a l2] *)
        apply IH.
        (* [h1'] is the left side. *)
        exact (Disjunction.left h1').
    + (* [Disjunction.right] turns the goal into its right side:
         [|- Contains a (append l1' l2)] *)
      apply Disjunction.right.
      (* [IH] turns a proof of [Contains a l1' \/ Contains a l2] into one
         of the goal: [|- Contains a l1' \/ Contains a l2] *)
      apply IH.
      (* [h2] is the right side. *)
      exact (Disjunction.right h2).
Qed.

Theorem contains_distributivity_over_append
  : forall (A : Type) (a : A) (l1 : List A) (l2 : List A),
      Contains a (append l1 l2) <-> Contains a l1 \/ Contains a l2.
Proof.
  (* The context gains [A], [a], [l1] and [l2]:
     [|- Contains a (append l1 l2) <-> Contains a l1 \/ Contains a l2] *)
  intros A a l1 l2.
  (* [Biimplication] has one ctor with two fields, so the goal splits into two
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
    + (* [Disjunction.left] turns the goal into its left side:
         [|- f a = f b] *)
      apply Disjunction.left.
      (* [e] replaces [a] by [b]: [|- f b = f b] *)
      rewrite e in |- *.
      (* Both sides are the same term. *)
      reflexivity.
    + (* [Disjunction.right] turns the goal into its right side:
         [|- Contains (f a) (map f l')] *)
      apply Disjunction.right.
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
    + (* [Disjunction.right] turns the goal into its right side:
         [|- Contains a l'] *)
      apply Disjunction.right.
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
        exact (Disjunction.left e).
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
    + (* [Disjunction.right] turns the goal into its right side:
         [|- Contains a (Cons b Nil)] *)
      apply Disjunction.right.
      (* [Contains a (Cons b Nil)] computes: [|- a = b \/ Falsum] *)
      simpl in |- *.
      (* [e] is the left side. *)
      exact (Disjunction.left e).
    + (* [Disjunction.left] turns the goal into its left side:
         [|- Contains a (reverse l')] *)
      apply Disjunction.left.
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
  (* [Biimplication] has one ctor with two fields, so the goal splits into two
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

(* Filtering a concatenation filters each half. The head's answer decides
   the shape, so each step is a case analysis on [p b]. *)
Theorem filter_distributivity_over_append
  : forall (A : Type) (p : A -> Bool) (l1 : List A) (l2 : List A),
      filter p (append l1 l2) = append (filter p l1) (filter p l2).
Proof.
  (* The context gains [A], [p], [l1] and [l2]:
     [|- filter p (append l1 l2) = append (filter p l1) (filter p l2)] *)
  intros A p l1 l2.
  (* [l1] is either [Nil] or [Cons b l1']: one goal per ctor, and the second
     has [b], [l1'] and
     [IH : filter p (append l1' l2) = append (filter p l1') (filter p l2)]
     in its context. *)
  induction l1 as [| b l1' IH] using List_induction.
  - (* [|- filter p (append Nil l2) = append (filter p Nil) (filter p l2)] *)
    (* [append Nil], [filter p Nil] and [append Nil] again compute:
       [|- filter p l2 = filter p l2] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
  - (* [|- filter p (append (Cons b l1') l2)
         = append (filter p (Cons b l1')) (filter p l2)] *)
    (* One [append] step and one [filter] step on each side leave a
       [match p b] on both:
       [|- match p b with
           | true => Cons b (filter p (append l1' l2))
           | false => filter p (append l1' l2)
           end
           = append (match p b with
                     | true => Cons b (filter p l1')
                     | false => filter p l1'
                     end)
                    (filter p l2)] *)
    simpl in |- *.
    (* [p b] is either [true] or [false]: one goal per ctor. *)
    destruct (p b) as [|].
    + (* Both [match]es take their [true] branch, and [append] steps:
         [|- Cons b (filter p (append l1' l2))
             = Cons b (append (filter p l1') (filter p l2))] *)
      simpl in |- *.
      (* [IH] replaces the inner [filter]; both sides are then the same
         term. *)
      rewrite IH in |- *.
      (* Both sides are the same term. *)
      reflexivity.
    + (* Both [match]es take their [false] branch:
         [|- filter p (append l1' l2) = append (filter p l1') (filter p l2)] *)
      simpl in |- *.
      (* [IH] is a proof of the goal as it stands. *)
      exact IH.
Qed.

(* [filter] is a catamorphism too: [Cons] becomes a conditional [Cons]. *)
Theorem filter_catamorphism
  : forall (A : Type) (p : A -> Bool) (l : List A),
      filter p l
      = fold_right (fun (a : A) (kept : List A) =>
                      match p a with
                      | true  => Cons a kept
                      | false => kept
                      end)
                    Nil
                    l.
Proof.
  (* The context gains [A], [p] and [l]:
     [|- filter p l = fold_right (fun a kept => match p a with ...) Nil l] *)
  intros A p l.
  (* [l] is either [Nil] or [Cons b l']: one goal per ctor, and the second
     has [b], [l'] and [IH], the statement for [l'], in its context. *)
  induction l as [| b l' IH] using List_induction.
  - (* Both sides compute to [Nil]: [|- Nil = Nil] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
  - (* One step on each side, and the function applied to [b] reduces to
       the same [match p b] as [filter] leaves:
       [|- match p b with
           | true => Cons b (filter p l')
           | false => filter p l'
           end
           = match p b with
             | true => Cons b (fold_right ... Nil l')
             | false => fold_right ... Nil l'
             end] *)
    simpl in |- *.
    (* [IH] replaces [filter p l'] in both branches; both sides are then the
       same term. *)
    rewrite IH in |- *.
    (* Both sides are the same term. *)
    reflexivity.
Qed.

(* The specification of [filter]: an element is in the result exactly when
   it was in the input and [p] answers [true] on it. The two halves are
   lemmas, the [<->] the theorem. Where the head's answer matters later,
   [destruct ... eqn:] keeps it as an equation in the context. *)

Lemma filter_specification_forward
  : forall (A : Type) (p : A -> Bool) (a : A) (l : List A),
      Contains a (filter p l) -> Contains a l /\ p a = true.
Proof.
  (* The context gains [A], [p], [a] and [l]:
     [|- Contains a (filter p l) -> Contains a l /\ p a = true] *)
  intros A p a l.
  (* [l] is either [Nil] or [Cons b l']: one goal per ctor, and the second
     has [b], [l'] and
     [IH : Contains a (filter p l') -> Contains a l' /\ p a = true] in its
     context. *)
  induction l as [| b l' IH] using List_induction.
  - (* [|- Contains a (filter p Nil) -> Contains a Nil /\ p a = true] *)
    (* [filter p Nil] and both [Contains] compute:
       [|- Falsum -> Falsum /\ p a = true] *)
    simpl in |- *.
    (* The context gains [f : Falsum]: [|- Falsum /\ p a = true] *)
    intro f.
    (* [f : Falsum], which is what [contradiction] looks for. *)
    contradiction.
  - (* [|- Contains a (filter p (Cons b l'))
         -> Contains a (Cons b l') /\ p a = true] *)
    (* The [filter] step leaves a [match p b] under [Contains], and the
       [Contains] on the right computes:
       [|- Contains a (match p b with
                       | true => Cons b (filter p l')
                       | false => filter p l'
                       end)
           -> (a = b \/ Contains a l') /\ p a = true] *)
    simpl in |- *.
    (* [p b] is either [true] or [false]: one goal per ctor, each keeping
       the answer as [pb]. *)
    destruct (p b) as [|] eqn:pb.
    + (* The [match] takes its [true] branch and [Contains] computes:
         [|- a = b \/ Contains a (filter p l')
             -> (a = b \/ Contains a l') /\ p a = true] *)
      simpl in |- *.
      (* The context gains [h : a = b \/ Contains a (filter p l')]:
         [|- (a = b \/ Contains a l') /\ p a = true] *)
      intro h.
      (* [h] gives two goals: one with [e : a = b], one with
         [h' : Contains a (filter p l')]. *)
      destruct h as [e | h'].
      * (* The goal splits into two goals: [|- a = b \/ Contains a l'] and
           [|- p a = true]. *)
        split.
        -- (* [e] is the left side. *)
           exact (Disjunction.left e).
        -- (* [e] replaces [a] by [b]: [|- p b = true] *)
           rewrite e in |- *.
           (* [pb] is a proof of the goal as it stands. *)
           exact pb.
      * (* [IH] turns [h'] into [Contains a l' /\ p a = true], which splits
           into [hl : Contains a l'] and [pa : p a = true]. *)
        destruct (IH h') as [hl pa].
        (* The goal splits into two goals: [|- a = b \/ Contains a l'] and
           [|- p a = true]. *)
        split.
        -- (* [hl] is the right side. *)
           exact (Disjunction.right hl).
        -- (* [pa] is a proof of the goal as it stands. *)
           exact pa.
    + (* The [match] takes its [false] branch:
         [|- Contains a (filter p l')
             -> (a = b \/ Contains a l') /\ p a = true] *)
      simpl in |- *.
      (* The context gains [h' : Contains a (filter p l')]:
         [|- (a = b \/ Contains a l') /\ p a = true] *)
      intro h'.
      (* [IH] turns [h'] into [Contains a l' /\ p a = true], which splits
         into [hl : Contains a l'] and [pa : p a = true]. *)
      destruct (IH h') as [hl pa].
      (* The goal splits into two goals: [|- a = b \/ Contains a l'] and
         [|- p a = true]. *)
      split.
      * (* [hl] is the right side. *)
        exact (Disjunction.right hl).
      * (* [pa] is a proof of the goal as it stands. *)
        exact pa.
Qed.

Lemma filter_specification_backward
  : forall (A : Type) (p : A -> Bool) (a : A) (l : List A),
      Contains a l /\ p a = true -> Contains a (filter p l).
Proof.
  (* The context gains [A], [p], [a] and [l]:
     [|- Contains a l /\ p a = true -> Contains a (filter p l)] *)
  intros A p a l.
  (* [l] is either [Nil] or [Cons b l']: one goal per ctor, and the second
     has [b], [l'] and
     [IH : Contains a l' /\ p a = true -> Contains a (filter p l')] in its
     context. *)
  induction l as [| b l' IH] using List_induction.
  - (* [|- Contains a Nil /\ p a = true -> Contains a (filter p Nil)] *)
    (* Both [Contains] and [filter p Nil] compute:
       [|- Falsum /\ p a = true -> Falsum] *)
    simpl in |- *.
    (* The context gains [h : Falsum /\ p a = true]: [|- Falsum] *)
    intro h.
    (* Only the left half of [h] is needed: [f : Falsum]. *)
    destruct h as [f _].
    (* [f : Falsum], which is what [contradiction] looks for. *)
    contradiction.
  - (* [|- Contains a (Cons b l') /\ p a = true
         -> Contains a (filter p (Cons b l'))] *)
    (* The [Contains] on the left computes and the [filter] step leaves a
       [match p b]:
       [|- (a = b \/ Contains a l') /\ p a = true
           -> Contains a (match p b with
                          | true => Cons b (filter p l')
                          | false => filter p l'
                          end)] *)
    simpl in |- *.
    (* The context gains [h : (a = b \/ Contains a l') /\ p a = true]:
       the goal is the [Contains] of the [match]. *)
    intro h.
    (* [h] splits into [h1 : a = b \/ Contains a l'] and [pa : p a = true]. *)
    destruct h as [h1 pa].
    (* [h1] gives two goals: one with [e : a = b], one with
       [h' : Contains a l']. *)
    destruct h1 as [e | h'].
    + (* [e] replaces [a] by [b] in [pa]: [pa : p b = true]. *)
      rewrite e in pa.
      (* [pa] replaces [p b] by [true], and the [match] takes that branch:
         [|- Contains a (Cons b (filter p l'))] *)
      rewrite pa in |- *.
      (* [Contains] on a [Cons] computes:
         [|- a = b \/ Contains a (filter p l')] *)
      simpl in |- *.
      (* [e] is the left side. *)
      exact (Disjunction.left e).
    + (* [p b] is either [true] or [false]: one goal per ctor. *)
      destruct (p b) as [|].
      * (* The [match] takes its [true] branch and [Contains] computes:
           [|- a = b \/ Contains a (filter p l')] *)
        simpl in |- *.
        (* [Disjunction.right] turns the goal into its right side:
           [|- Contains a (filter p l')] *)
        apply Disjunction.right.
        (* [IH] turns a proof of [Contains a l' /\ p a = true] into one of
           the goal: [|- Contains a l' /\ p a = true] *)
        apply IH.
        (* The goal splits into two goals: [|- Contains a l'] and
           [|- p a = true]. *)
        split.
        -- (* [h'] is a proof of the goal as it stands. *)
           exact h'.
        -- (* [pa] is a proof of the goal as it stands. *)
           exact pa.
      * (* The [match] takes its [false] branch:
           [|- Contains a (filter p l')] *)
        simpl in |- *.
        (* [IH] turns a proof of [Contains a l' /\ p a = true] into one of
           the goal: [|- Contains a l' /\ p a = true] *)
        apply IH.
        (* The goal splits into two goals: [|- Contains a l'] and
           [|- p a = true]. *)
        split.
        -- (* [h'] is a proof of the goal as it stands. *)
           exact h'.
        -- (* [pa] is a proof of the goal as it stands. *)
           exact pa.
Qed.

Theorem filter_specification
  : forall (A : Type) (p : A -> Bool) (a : A) (l : List A),
      Contains a (filter p l) <-> Contains a l /\ p a = true.
Proof.
  (* The context gains [A], [p], [a] and [l]:
     [|- Contains a (filter p l) <-> Contains a l /\ p a = true] *)
  intros A p a l.
  (* [Biimplication] has one ctor with two fields, so the goal splits into two
     goals, the forward and the backward half. *)
  split.
  - (* [filter_specification_forward A p a l] is a proof of the goal
       as it stands. *)
    exact (filter_specification_forward A p a l).
  - (* [filter_specification_backward A p a l] is a proof of the
       goal as it stands. *)
    exact (filter_specification_backward A p a l).
Qed.

(* [All P] holds when every element satisfies [P], [Any P] when some
   element does. Both recurse into [Prop] as [Contains] does: [Nil] gives
   the neutral proposition, [Cons] a conjunction or a disjunction. *)

Fixpoint All {A : Type} (P : A -> Prop) (l : List A) : Prop :=
  match l with
  | Nil       => Verum
  | Cons a l' => P a /\ All P l'
  end.

Fixpoint Any {A : Type} (P : A -> Prop) (l : List A) : Prop :=
  match l with
  | Nil       => Falsum
  | Cons a l' => P a \/ Any P l'
  end.

(* [All] over a concatenation is [All] over each half. *)

Lemma all_distributivity_over_append_forward
  : forall (A : Type) (P : A -> Prop) (l1 : List A) (l2 : List A),
      All P (append l1 l2) -> All P l1 /\ All P l2.
Proof.
  (* The context gains [A], [P], [l1] and [l2]:
     [|- All P (append l1 l2) -> All P l1 /\ All P l2] *)
  intros A P l1 l2.
  (* [l1] is either [Nil] or [Cons b l1']: one goal per ctor, and the second
     has [b], [l1'] and
     [IH : All P (append l1' l2) -> All P l1' /\ All P l2] in its context. *)
  induction l1 as [| b l1' IH] using List_induction.
  - (* [|- All P (append Nil l2) -> All P Nil /\ All P l2] *)
    (* [append Nil] and [All P Nil] compute:
       [|- All P l2 -> Verum /\ All P l2] *)
    simpl in |- *.
    (* The context gains [h : All P l2]: [|- Verum /\ All P l2] *)
    intro h.
    (* The goal splits into two goals: [|- Verum] and [|- All P l2]. *)
    split.
    + (* [I] is the proof of [Verum]. *)
      exact I.
    + (* [h] is a proof of the goal as it stands. *)
      exact h.
  - (* [|- All P (append (Cons b l1') l2) -> All P (Cons b l1') /\ All P l2] *)
    (* One [append] step and both [All] on a [Cons] compute:
       [|- P b /\ All P (append l1' l2) -> (P b /\ All P l1') /\ All P l2] *)
    simpl in |- *.
    (* The context gains [h : P b /\ All P (append l1' l2)]:
       [|- (P b /\ All P l1') /\ All P l2] *)
    intro h.
    (* [h] splits into [pb : P b] and [h' : All P (append l1' l2)]. *)
    destruct h as [pb h'].
    (* [IH] turns [h'] into [All P l1' /\ All P l2], which splits into
       [h1 : All P l1'] and [h2 : All P l2]. *)
    destruct (IH h') as [h1 h2].
    (* The goal splits into two goals: [|- P b /\ All P l1'] and
       [|- All P l2]. *)
    split.
    + (* The goal splits into two goals: [|- P b] and [|- All P l1']. *)
      split.
      * (* [pb] is a proof of the goal as it stands. *)
        exact pb.
      * (* [h1] is a proof of the goal as it stands. *)
        exact h1.
    + (* [h2] is a proof of the goal as it stands. *)
      exact h2.
Qed.

Lemma all_distributivity_over_append_backward
  : forall (A : Type) (P : A -> Prop) (l1 : List A) (l2 : List A),
      All P l1 /\ All P l2 -> All P (append l1 l2).
Proof.
  (* The context gains [A], [P], [l1] and [l2]:
     [|- All P l1 /\ All P l2 -> All P (append l1 l2)] *)
  intros A P l1 l2.
  (* [l1] is either [Nil] or [Cons b l1']: one goal per ctor, and the second
     has [b], [l1'] and
     [IH : All P l1' /\ All P l2 -> All P (append l1' l2)] in its context. *)
  induction l1 as [| b l1' IH] using List_induction.
  - (* [|- All P Nil /\ All P l2 -> All P (append Nil l2)] *)
    (* [All P Nil] and [append Nil] compute:
       [|- Verum /\ All P l2 -> All P l2] *)
    simpl in |- *.
    (* The context gains [h : Verum /\ All P l2]: [|- All P l2] *)
    intro h.
    (* Only the right half of [h] is needed: [h2 : All P l2]. *)
    destruct h as [_ h2].
    (* [h2] is a proof of the goal as it stands. *)
    exact h2.
  - (* [|- All P (Cons b l1') /\ All P l2 -> All P (append (Cons b l1') l2)] *)
    (* Both [All] on a [Cons] and the [append] step compute:
       [|- (P b /\ All P l1') /\ All P l2 -> P b /\ All P (append l1' l2)] *)
    simpl in |- *.
    (* The context gains [h : (P b /\ All P l1') /\ All P l2]:
       [|- P b /\ All P (append l1' l2)] *)
    intro h.
    (* [h] splits into [h1 : P b /\ All P l1'] and [h2 : All P l2]. *)
    destruct h as [h1 h2].
    (* [h1] splits into [pb : P b] and [h1' : All P l1']. *)
    destruct h1 as [pb h1'].
    (* The goal splits into two goals: [|- P b] and
       [|- All P (append l1' l2)]. *)
    split.
    + (* [pb] is a proof of the goal as it stands. *)
      exact pb.
    + (* [IH] turns a proof of [All P l1' /\ All P l2] into one of the goal:
         [|- All P l1' /\ All P l2] *)
      apply IH.
      (* The goal splits into two goals: [|- All P l1'] and [|- All P l2]. *)
      split.
      * (* [h1'] is a proof of the goal as it stands. *)
        exact h1'.
      * (* [h2] is a proof of the goal as it stands. *)
        exact h2.
Qed.

Theorem all_distributivity_over_append
  : forall (A : Type) (P : A -> Prop) (l1 : List A) (l2 : List A),
      All P (append l1 l2) <-> All P l1 /\ All P l2.
Proof.
  (* The context gains [A], [P], [l1] and [l2]:
     [|- All P (append l1 l2) <-> All P l1 /\ All P l2] *)
  intros A P l1 l2.
  (* [Biimplication] has one ctor with two fields, so the goal splits into two
     goals, the forward and the backward half. *)
  split.
  - (* [all_distributivity_over_append_forward A P l1 l2] is a proof of the
       goal as it stands. *)
    exact (all_distributivity_over_append_forward A P l1 l2).
  - (* [all_distributivity_over_append_backward A P l1 l2] is a proof of the
       goal as it stands. *)
    exact (all_distributivity_over_append_backward A P l1 l2).
Qed.

(* [Any] over a concatenation is [Any] over either half. *)

Lemma any_distributivity_over_append_forward
  : forall (A : Type) (P : A -> Prop) (l1 : List A) (l2 : List A),
      Any P (append l1 l2) -> Any P l1 \/ Any P l2.
Proof.
  (* The context gains [A], [P], [l1] and [l2]:
     [|- Any P (append l1 l2) -> Any P l1 \/ Any P l2] *)
  intros A P l1 l2.
  (* [l1] is either [Nil] or [Cons b l1']: one goal per ctor, and the second
     has [b], [l1'] and
     [IH : Any P (append l1' l2) -> Any P l1' \/ Any P l2] in its context. *)
  induction l1 as [| b l1' IH] using List_induction.
  - (* [|- Any P (append Nil l2) -> Any P Nil \/ Any P l2] *)
    (* [append Nil] and [Any P Nil] compute:
       [|- Any P l2 -> Falsum \/ Any P l2] *)
    simpl in |- *.
    (* The context gains [h : Any P l2]: [|- Falsum \/ Any P l2] *)
    intro h.
    (* [h] is the right side. *)
    exact (Disjunction.right h).
  - (* [|- Any P (append (Cons b l1') l2) -> Any P (Cons b l1') \/ Any P l2] *)
    (* One [append] step and both [Any] on a [Cons] compute:
       [|- P b \/ Any P (append l1' l2) -> (P b \/ Any P l1') \/ Any P l2] *)
    simpl in |- *.
    (* The context gains [h : P b \/ Any P (append l1' l2)]:
       [|- (P b \/ Any P l1') \/ Any P l2] *)
    intro h.
    (* [h] gives two goals: one with [pb : P b], one with
       [h' : Any P (append l1' l2)]. *)
    destruct h as [pb | h'].
    + (* [pb] is the left side of the left side. *)
      exact (Disjunction.left (Disjunction.left pb)).
    + (* [IH] turns [h'] into [Any P l1' \/ Any P l2], which gives two
         goals: one with [h1 : Any P l1'], one with [h2 : Any P l2]. *)
      destruct (IH h') as [h1 | h2].
      * (* [h1] is the right side of the left side. *)
        exact (Disjunction.left (Disjunction.right h1)).
      * (* [h2] is the right side. *)
        exact (Disjunction.right h2).
Qed.

Lemma any_distributivity_over_append_backward
  : forall (A : Type) (P : A -> Prop) (l1 : List A) (l2 : List A),
      Any P l1 \/ Any P l2 -> Any P (append l1 l2).
Proof.
  (* The context gains [A], [P], [l1] and [l2]:
     [|- Any P l1 \/ Any P l2 -> Any P (append l1 l2)] *)
  intros A P l1 l2.
  (* [l1] is either [Nil] or [Cons b l1']: one goal per ctor, and the second
     has [b], [l1'] and
     [IH : Any P l1' \/ Any P l2 -> Any P (append l1' l2)] in its context. *)
  induction l1 as [| b l1' IH] using List_induction.
  - (* [|- Any P Nil \/ Any P l2 -> Any P (append Nil l2)] *)
    (* [Any P Nil] and [append Nil] compute:
       [|- Falsum \/ Any P l2 -> Any P l2] *)
    simpl in |- *.
    (* The context gains [h : Falsum \/ Any P l2]: [|- Any P l2] *)
    intro h.
    (* [h] gives two goals: one with [f : Falsum], one with
       [h2 : Any P l2]. *)
    destruct h as [f | h2].
    + (* [f : Falsum], which is what [contradiction] looks for. *)
      contradiction.
    + (* [h2] is a proof of the goal as it stands. *)
      exact h2.
  - (* [|- Any P (Cons b l1') \/ Any P l2 -> Any P (append (Cons b l1') l2)] *)
    (* Both [Any] on a [Cons] and the [append] step compute:
       [|- (P b \/ Any P l1') \/ Any P l2 -> P b \/ Any P (append l1' l2)] *)
    simpl in |- *.
    (* The context gains [h : (P b \/ Any P l1') \/ Any P l2]:
       [|- P b \/ Any P (append l1' l2)] *)
    intro h.
    (* [h] gives two goals: one with [h1 : P b \/ Any P l1'], one with
       [h2 : Any P l2]. *)
    destruct h as [h1 | h2].
    + (* [h1] gives two goals: one with [pb : P b], one with
         [h1' : Any P l1']. *)
      destruct h1 as [pb | h1'].
      * (* [pb] is the left side. *)
        exact (Disjunction.left pb).
      * (* [Disjunction.right] turns the goal into its right side:
           [|- Any P (append l1' l2)] *)
        apply Disjunction.right.
        (* [IH] turns a proof of [Any P l1' \/ Any P l2] into one of the
           goal: [|- Any P l1' \/ Any P l2] *)
        apply IH.
        (* [h1'] is the left side. *)
        exact (Disjunction.left h1').
    + (* [Disjunction.right] turns the goal into its right side:
         [|- Any P (append l1' l2)] *)
      apply Disjunction.right.
      (* [IH] turns a proof of [Any P l1' \/ Any P l2] into one of the goal:
         [|- Any P l1' \/ Any P l2] *)
      apply IH.
      (* [h2] is the right side. *)
      exact (Disjunction.right h2).
Qed.

Theorem any_distributivity_over_append
  : forall (A : Type) (P : A -> Prop) (l1 : List A) (l2 : List A),
      Any P (append l1 l2) <-> Any P l1 \/ Any P l2.
Proof.
  (* The context gains [A], [P], [l1] and [l2]:
     [|- Any P (append l1 l2) <-> Any P l1 \/ Any P l2] *)
  intros A P l1 l2.
  (* [Biimplication] has one ctor with two fields, so the goal splits into two
     goals, the forward and the backward half. *)
  split.
  - (* [any_distributivity_over_append_forward A P l1 l2] is a proof of the
       goal as it stands. *)
    exact (any_distributivity_over_append_forward A P l1 l2).
  - (* [any_distributivity_over_append_backward A P l1 l2] is a proof of the
       goal as it stands. *)
    exact (any_distributivity_over_append_backward A P l1 l2).
Qed.

(* The specifications of [All] and [Any] through membership: [All P l] says
   [P] of every member, [Any P l] that some member satisfies [P]. The
   second is the first use of [exists] in the library. *)

Lemma all_specification_forward
  : forall (A : Type) (P : A -> Prop) (l : List A),
      All P l -> forall (a : A), Contains a l -> P a.
Proof.
  (* The context gains [A], [P] and [l]:
     [|- All P l -> forall (a : A), Contains a l -> P a] *)
  intros A P l.
  (* [l] is either [Nil] or [Cons b l']: one goal per ctor, and the second
     has [b], [l'] and
     [IH : All P l' -> forall (a : A), Contains a l' -> P a] in its
     context. *)
  induction l as [| b l' IH] using List_induction.
  - (* [|- All P Nil -> forall (a : A), Contains a Nil -> P a] *)
    (* [All P Nil] and [Contains a Nil] compute:
       [|- Verum -> forall (a : A), Falsum -> P a] *)
    simpl in |- *.
    (* The context gains [v : Verum], [a] and [f : Falsum]: [|- P a] *)
    intros v a f.
    (* [f : Falsum], which is what [contradiction] looks for. *)
    contradiction.
  - (* [|- All P (Cons b l')
         -> forall (a : A), Contains a (Cons b l') -> P a] *)
    (* Both [All] and [Contains] on a [Cons] compute:
       [|- P b /\ All P l' -> forall (a : A), a = b \/ Contains a l' -> P a] *)
    simpl in |- *.
    (* The context gains [h : P b /\ All P l']:
       [|- forall (a : A), a = b \/ Contains a l' -> P a] *)
    intro h.
    (* [h] splits into [pb : P b] and [h' : All P l']. *)
    destruct h as [pb h'].
    (* The context gains [a] and [ha : a = b \/ Contains a l']: [|- P a] *)
    intros a ha.
    (* [ha] gives two goals: one with [e : a = b], one with
       [ha' : Contains a l']. *)
    destruct ha as [e | ha'].
    + (* [e] replaces [a] by [b]: [|- P b] *)
      rewrite e in |- *.
      (* [pb] is a proof of the goal as it stands. *)
      exact pb.
    + (* [IH h'] turns membership in [l'] into [P]: [|- Contains a l'] *)
      apply (IH h').
      (* [ha'] is a proof of the goal as it stands. *)
      exact ha'.
Qed.

Lemma all_specification_backward
  : forall (A : Type) (P : A -> Prop) (l : List A),
      (forall (a : A), Contains a l -> P a) -> All P l.
Proof.
  (* The context gains [A], [P] and [l]:
     [|- (forall (a : A), Contains a l -> P a) -> All P l] *)
  intros A P l.
  (* [l] is either [Nil] or [Cons b l']: one goal per ctor, and the second
     has [b], [l'] and
     [IH : (forall (a : A), Contains a l' -> P a) -> All P l'] in its
     context. *)
  induction l as [| b l' IH] using List_induction.
  - (* [|- (forall (a : A), Contains a Nil -> P a) -> All P Nil] *)
    (* [Contains a Nil] and [All P Nil] compute:
       [|- (forall (a : A), Falsum -> P a) -> Verum] *)
    simpl in |- *.
    (* The context gains [h], which is never used: [|- Verum] *)
    intro h.
    (* [I] is the proof of [Verum]. *)
    exact I.
  - (* [|- (forall (a : A), Contains a (Cons b l') -> P a)
         -> All P (Cons b l')] *)
    (* Both [Contains] and [All] on a [Cons] compute:
       [|- (forall (a : A), a = b \/ Contains a l' -> P a)
           -> P b /\ All P l'] *)
    simpl in |- *.
    (* The context gains [h : forall (a : A), a = b \/ Contains a l' -> P a]:
       [|- P b /\ All P l'] *)
    intro h.
    (* The goal splits into two goals: [|- P b] and [|- All P l']. *)
    split.
    + (* [h b] turns a proof of [b = b \/ Contains b l'] into one of [P b]:
         [|- b = b \/ Contains b l'] *)
      apply (h b).
      (* [b = b] is the left side, proved by reflexivity of [=]. *)
      exact (Disjunction.left (Identity.reflexivity b)).
    + (* [IH] turns a proof of the membership hypothesis for [l'] into one
         of the goal: [|- forall (a : A), Contains a l' -> P a] *)
      apply IH.
      (* The context gains [a] and [ha : Contains a l']: [|- P a] *)
      intros a ha.
      (* [h a] turns a proof of [a = b \/ Contains a l'] into one of [P a]:
         [|- a = b \/ Contains a l'] *)
      apply (h a).
      (* [ha] is the right side. *)
      exact (Disjunction.right ha).
Qed.

Theorem all_specification
  : forall (A : Type) (P : A -> Prop) (l : List A),
      All P l <-> (forall (a : A), Contains a l -> P a).
Proof.
  (* The context gains [A], [P] and [l]:
     [|- All P l <-> (forall (a : A), Contains a l -> P a)] *)
  intros A P l.
  (* [Biimplication] has one ctor with two fields, so the goal splits into two
     goals, the forward and the backward half. *)
  split.
  - (* [all_specification_forward A P l] is a proof of the goal as it
       stands. *)
    exact (all_specification_forward A P l).
  - (* [all_specification_backward A P l] is a proof of the goal as it
       stands. *)
    exact (all_specification_backward A P l).
Qed.

Lemma any_specification_forward
  : forall (A : Type) (P : A -> Prop) (l : List A),
      Any P l -> exists (a : A), Contains a l /\ P a.
Proof.
  (* The context gains [A], [P] and [l]:
     [|- Any P l -> exists (a : A), Contains a l /\ P a] *)
  intros A P l.
  (* [l] is either [Nil] or [Cons b l']: one goal per ctor, and the second
     has [b], [l'] and
     [IH : Any P l' -> exists (a : A), Contains a l' /\ P a] in its
     context. *)
  induction l as [| b l' IH] using List_induction.
  - (* [|- Any P Nil -> exists (a : A), Contains a Nil /\ P a] *)
    (* [Any P Nil] computes: [|- Falsum -> exists (a : A), ...] *)
    simpl in |- *.
    (* The context gains [f : Falsum]: the goal is the [exists]. *)
    intro f.
    (* [f : Falsum], which is what [contradiction] looks for. *)
    contradiction.
  - (* [|- Any P (Cons b l')
         -> exists (a : A), Contains a (Cons b l') /\ P a] *)
    (* Both [Any] and [Contains] on a [Cons] compute:
       [|- P b \/ Any P l'
           -> exists (a : A), (a = b \/ Contains a l') /\ P a] *)
    simpl in |- *.
    (* The context gains [h : P b \/ Any P l']: the goal is the [exists]. *)
    intro h.
    (* [h] gives two goals: one with [pb : P b], one with
       [h' : Any P l']. *)
    destruct h as [pb | h'].
    + (* [b] is the witness: [Exists_introduction b] asks for
         [(b = b \/ Contains b l') /\ P b]. *)
      apply (Exists_introduction b).
      (* The goal splits into two goals: [|- b = b \/ Contains b l'] and
         [|- P b]. *)
      split.
      * (* [b = b] is the left side, proved by reflexivity of [=]. *)
        exact (Disjunction.left (Identity.reflexivity b)).
      * (* [pb] is a proof of the goal as it stands. *)
        exact pb.
    + (* [IH] turns [h'] into an [exists], which [destruct] opens into a
         witness [a] and [ha : Contains a l' /\ P a]. *)
      destruct (IH h') as [a ha].
      (* [ha] splits into [ha' : Contains a l'] and [pa : P a]. *)
      destruct ha as [ha' pa].
      (* [a] is the witness: [Exists_introduction a] asks for
         [(a = b \/ Contains a l') /\ P a]. *)
      apply (Exists_introduction a).
      (* The goal splits into two goals: [|- a = b \/ Contains a l'] and
         [|- P a]. *)
      split.
      * (* [ha'] is the right side. *)
        exact (Disjunction.right ha').
      * (* [pa] is a proof of the goal as it stands. *)
        exact pa.
Qed.

Lemma any_specification_backward
  : forall (A : Type) (P : A -> Prop) (l : List A),
      (exists (a : A), Contains a l /\ P a) -> Any P l.
Proof.
  (* The context gains [A], [P] and [l]:
     [|- (exists (a : A), Contains a l /\ P a) -> Any P l] *)
  intros A P l.
  (* [l] is either [Nil] or [Cons b l']: one goal per ctor, and the second
     has [b], [l'] and
     [IH : (exists (a : A), Contains a l' /\ P a) -> Any P l'] in its
     context. *)
  induction l as [| b l' IH] using List_induction.
  - (* [|- (exists (a : A), Contains a Nil /\ P a) -> Any P Nil] *)
    (* [Contains a Nil] and [Any P Nil] compute:
       [|- (exists (a : A), Falsum /\ P a) -> Falsum] *)
    simpl in |- *.
    (* The context gains [h], the [exists]: [|- Falsum] *)
    intro h.
    (* [h] opens into a witness [a] and [ha : Falsum /\ P a]. *)
    destruct h as [a ha].
    (* Only the left half of [ha] is needed: [f : Falsum]. *)
    destruct ha as [f _].
    (* [f : Falsum], which is what [contradiction] looks for. *)
    contradiction.
  - (* [|- (exists (a : A), Contains a (Cons b l') /\ P a)
         -> Any P (Cons b l')] *)
    (* Both [Contains] and [Any] on a [Cons] compute:
       [|- (exists (a : A), (a = b \/ Contains a l') /\ P a)
           -> P b \/ Any P l'] *)
    simpl in |- *.
    (* The context gains [h], the [exists]: [|- P b \/ Any P l'] *)
    intro h.
    (* [h] opens into a witness [a] and
       [ha : (a = b \/ Contains a l') /\ P a]. *)
    destruct h as [a ha].
    (* [ha] splits into [ha' : a = b \/ Contains a l'] and [pa : P a]. *)
    destruct ha as [ha' pa].
    (* [ha'] gives two goals: one with [e : a = b], one with
       [ha'' : Contains a l']. *)
    destruct ha' as [e | ha''].
    + (* [e] replaces [a] by [b] in [pa]: [pa : P b]. *)
      rewrite e in pa.
      (* [pa] is the left side. *)
      exact (Disjunction.left pa).
    + (* [Disjunction.right] turns the goal into its right side:
         [|- Any P l'] *)
      apply Disjunction.right.
      (* [IH] turns a proof of the [exists] for [l'] into one of the goal:
         [|- exists (a : A), Contains a l' /\ P a] *)
      apply IH.
      (* [a] is the witness: [Exists_introduction a] asks for
         [Contains a l' /\ P a]. *)
      apply (Exists_introduction a).
      (* The goal splits into two goals: [|- Contains a l'] and [|- P a]. *)
      split.
      * (* [ha''] is a proof of the goal as it stands. *)
        exact ha''.
      * (* [pa] is a proof of the goal as it stands. *)
        exact pa.
Qed.

Theorem any_specification
  : forall (A : Type) (P : A -> Prop) (l : List A),
      Any P l <-> (exists (a : A), Contains a l /\ P a).
Proof.
  (* The context gains [A], [P] and [l]:
     [|- Any P l <-> (exists (a : A), Contains a l /\ P a)] *)
  intros A P l.
  (* [Biimplication] has one ctor with two fields, so the goal splits into two
     goals, the forward and the backward half. *)
  split.
  - (* [any_specification_forward A P l] is a proof of the goal as it
       stands. *)
    exact (any_specification_forward A P l).
  - (* [any_specification_backward A P l] is a proof of the goal as it
       stands. *)
    exact (any_specification_backward A P l).
Qed.

(* [Contains], [All] and [Any] are catamorphisms into [Prop]: [Cons]
   becomes a connective and [Nil] its neutral proposition. *)

Theorem contains_catamorphism
  : forall (A : Type) (a : A) (l : List A),
      Contains a l
      = fold_right (fun (b : A) (rest : Prop) => a = b \/ rest) Falsum l.
Proof.
  (* The context gains [A], [a] and [l]:
     [|- Contains a l = fold_right (fun b rest => a = b \/ rest) Falsum l] *)
  intros A a l.
  (* [l] is either [Nil] or [Cons b l']: one goal per ctor, and the second
     has [b], [l'] and [IH], the statement for [l'], in its context. *)
  induction l as [| b l' IH] using List_induction.
  - (* Both sides compute to [Falsum]: [|- Falsum = Falsum] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
  - (* One step on each side, and the function applied to [b] reduces:
       [|- a = b \/ Contains a l'
           = a = b \/ fold_right (fun b rest => a = b \/ rest) Falsum l'] *)
    simpl in |- *.
    (* [IH] replaces [Contains a l']; both sides are then the same term. *)
    rewrite IH in |- *.
    (* Both sides are the same term. *)
    reflexivity.
Qed.

Theorem all_catamorphism
  : forall (A : Type) (P : A -> Prop) (l : List A),
      All P l = fold_right (fun (a : A) (rest : Prop) => P a /\ rest) Verum l.
Proof.
  (* The context gains [A], [P] and [l]:
     [|- All P l = fold_right (fun a rest => P a /\ rest) Verum l] *)
  intros A P l.
  (* [l] is either [Nil] or [Cons a l']: one goal per ctor, and the second
     has [a], [l'] and [IH], the statement for [l'], in its context. *)
  induction l as [| a l' IH] using List_induction.
  - (* Both sides compute to [Verum]: [|- Verum = Verum] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
  - (* One step on each side, and the function applied to [a] reduces:
       [|- P a /\ All P l'
           = P a /\ fold_right (fun a rest => P a /\ rest) Verum l'] *)
    simpl in |- *.
    (* [IH] replaces [All P l']; both sides are then the same term. *)
    rewrite IH in |- *.
    (* Both sides are the same term. *)
    reflexivity.
Qed.

Theorem any_catamorphism
  : forall (A : Type) (P : A -> Prop) (l : List A),
      Any P l = fold_right (fun (a : A) (rest : Prop) => P a \/ rest) Falsum l.
Proof.
  (* The context gains [A], [P] and [l]:
     [|- Any P l = fold_right (fun a rest => P a \/ rest) Falsum l] *)
  intros A P l.
  (* [l] is either [Nil] or [Cons a l']: one goal per ctor, and the second
     has [a], [l'] and [IH], the statement for [l'], in its context. *)
  induction l as [| a l' IH] using List_induction.
  - (* Both sides compute to [Falsum]: [|- Falsum = Falsum] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
  - (* One step on each side, and the function applied to [a] reduces:
       [|- P a \/ Any P l'
           = P a \/ fold_right (fun a rest => P a \/ rest) Falsum l'] *)
    simpl in |- *.
    (* [IH] replaces [Any P l']; both sides are then the same term. *)
    rewrite IH in |- *.
    (* Both sides are the same term. *)
    reflexivity.
Qed.

(* Taking a list apart at the front: [head] looks at the first element and
   [tail] drops it. Both answer in [Option], since the empty list has
   neither. *)

(* [forall {A : Type}, List A -> Option A] *)
Definition head := fun {A : Type} (l : List A) =>
  match l with
  | Nil      => None
  | Cons a _ => Some a
  end.

(* [forall {A : Type}, List A -> Option (List A)] *)
Definition tail := fun {A : Type} (l : List A) =>
  match l with
  | Nil       => None
  | Cons _ l' => Some l'
  end.

(* The specifications: [head l] is [Some a] exactly when [l] starts with
   [a], and [tail l] is [Some l'] exactly when [l] is [l'] behind one
   element. Each is a [<->] with its halves as lemmas. *)

Lemma head_specification_forward
  : forall (A : Type) (a : A) (l : List A),
      head l = Some a -> exists (l' : List A), l = Cons a l'.
Proof.
  (* The context gains [A], [a] and [l]:
     [|- head l = Some a -> exists (l' : List A), l = Cons a l'] *)
  intros A a l.
  (* [l] is either [Nil] or [Cons b rest]: one goal per ctor. *)
  destruct l as [| b rest].
  - (* [|- head Nil = Some a -> exists (l' : List A), Nil = Cons a l'] *)
    (* [head Nil] computes: [|- None = Some a -> ...] *)
    simpl in |- *.
    (* The context gains [e : None = Some a]: the goal is the [exists]. *)
    intro e.
    (* [e] claims [None = Some a], and the two are different ctors. *)
    discriminate.
  - (* [|- head (Cons b rest) = Some a
         -> exists (l' : List A), Cons b rest = Cons a l'] *)
    (* [head (Cons b rest)] computes: [|- Some b = Some a -> ...] *)
    simpl in |- *.
    (* The context gains [e : Some b = Some a]: the goal is the [exists]. *)
    intro e.
    (* [Option.some_injectivity] turns [e] into [e' : b = a]. *)
    pose proof (Option.some_injectivity A b a e) as e'.
    (* [rest] is the witness: [|- Cons b rest = Cons a rest] *)
    apply (Exists_introduction rest).
    (* [e'] replaces [b] by [a]: [|- Cons a rest = Cons a rest] *)
    rewrite e' in |- *.
    (* Both sides are the same term. *)
    reflexivity.
Qed.

Lemma head_specification_backward
  : forall (A : Type) (a : A) (l : List A),
      (exists (l' : List A), l = Cons a l') -> head l = Some a.
Proof.
  (* The context gains [A], [a] and [l]:
     [|- (exists (l' : List A), l = Cons a l') -> head l = Some a] *)
  intros A a l.
  (* The context gains [h], the [exists]: [|- head l = Some a] *)
  intro h.
  (* [h] opens into a witness [l'] and [e : l = Cons a l']. *)
  destruct h as [l' e].
  (* [e] replaces [l]: [|- head (Cons a l') = Some a] *)
  rewrite e in |- *.
  (* [head (Cons a l')] computes: [|- Some a = Some a] *)
  simpl in |- *.
  (* Both sides are the same term. *)
  reflexivity.
Qed.

Theorem head_specification
  : forall (A : Type) (a : A) (l : List A),
      head l = Some a <-> (exists (l' : List A), l = Cons a l').
Proof.
  (* The context gains [A], [a] and [l]:
     [|- head l = Some a <-> (exists (l' : List A), l = Cons a l')] *)
  intros A a l.
  (* [Biimplication] has one ctor with two fields, so the goal splits into two
     goals, the forward and the backward half. *)
  split.
  - (* [head_specification_forward A a l] is a proof of the goal as it
       stands. *)
    exact (head_specification_forward A a l).
  - (* [head_specification_backward A a l] is a proof of the goal as it
       stands. *)
    exact (head_specification_backward A a l).
Qed.

Lemma tail_specification_forward
  : forall (A : Type) (l : List A) (l' : List A),
      tail l = Some l' -> exists (a : A), l = Cons a l'.
Proof.
  (* The context gains [A], [l] and [l']:
     [|- tail l = Some l' -> exists (a : A), l = Cons a l'] *)
  intros A l l'.
  (* [l] is either [Nil] or [Cons b rest]: one goal per ctor. *)
  destruct l as [| b rest].
  - (* [|- tail Nil = Some l' -> exists (a : A), Nil = Cons a l'] *)
    (* [tail Nil] computes: [|- None = Some l' -> ...] *)
    simpl in |- *.
    (* The context gains [e : None = Some l']: the goal is the [exists]. *)
    intro e.
    (* [e] claims [None = Some l'], and the two are different ctors. *)
    discriminate.
  - (* [|- tail (Cons b rest) = Some l'
         -> exists (a : A), Cons b rest = Cons a l'] *)
    (* [tail (Cons b rest)] computes: [|- Some rest = Some l' -> ...] *)
    simpl in |- *.
    (* The context gains [e : Some rest = Some l']: the goal is the
       [exists]. *)
    intro e.
    (* [Option.some_injectivity] turns [e] into [e' : rest = l']. *)
    pose proof (Option.some_injectivity (List A) rest l' e) as e'.
    (* [b] is the witness: [|- Cons b rest = Cons b l'] *)
    apply (Exists_introduction b).
    (* [e'] replaces [rest] by [l']: [|- Cons b l' = Cons b l'] *)
    rewrite e' in |- *.
    (* Both sides are the same term. *)
    reflexivity.
Qed.

Lemma tail_specification_backward
  : forall (A : Type) (l : List A) (l' : List A),
      (exists (a : A), l = Cons a l') -> tail l = Some l'.
Proof.
  (* The context gains [A], [l] and [l']:
     [|- (exists (a : A), l = Cons a l') -> tail l = Some l'] *)
  intros A l l'.
  (* The context gains [h], the [exists]: [|- tail l = Some l'] *)
  intro h.
  (* [h] opens into a witness [a] and [e : l = Cons a l']. *)
  destruct h as [a e].
  (* [e] replaces [l]: [|- tail (Cons a l') = Some l'] *)
  rewrite e in |- *.
  (* [tail (Cons a l')] computes: [|- Some l' = Some l'] *)
  simpl in |- *.
  (* Both sides are the same term. *)
  reflexivity.
Qed.

Theorem tail_specification
  : forall (A : Type) (l : List A) (l' : List A),
      tail l = Some l' <-> (exists (a : A), l = Cons a l').
Proof.
  (* The context gains [A], [l] and [l']:
     [|- tail l = Some l' <-> (exists (a : A), l = Cons a l')] *)
  intros A l l'.
  (* [Biimplication] has one ctor with two fields, so the goal splits into two
     goals, the forward and the backward half. *)
  split.
  - (* [tail_specification_forward A l l'] is a proof of the goal as it
       stands. *)
    exact (tail_specification_forward A l l').
  - (* [tail_specification_backward A l l'] is a proof of the goal as it
       stands. *)
    exact (tail_specification_backward A l l').
Qed.

(* Taking a list apart at the back, through [reverse]: the last element is
   the head of the reversal, and what precedes it is the tail of the
   reversal turned back around. *)

(* [forall {A : Type}, List A -> Option A] *)
Definition last := fun {A : Type} (l : List A) => head (reverse l).

(* [forall {A : Type}, List A -> Option (List A)] *)
Definition initial := fun {A : Type} (l : List A) => Option.map reverse (tail (reverse l)).

(* The specifications mirror those of [head] and [tail]: [last l] is
   [Some a] exactly when [l] ends with [a], and [initial l] is [Some l']
   exactly when [l] is [l'] followed by one element. *)

Lemma last_specification_forward
  : forall (A : Type) (a : A) (l : List A),
      last l = Some a -> exists (l' : List A), l = append l' (Cons a Nil).
Proof.
  (* The context gains [A], [a] and [l]:
     [|- last l = Some a -> exists (l' : List A), l = append l' (Cons a Nil)] *)
  intros A a l.
  (* [|- head (reverse l) = Some a -> ...] *)
  unfold last in |- *.
  (* The context gains [h : head (reverse l) = Some a]: the goal is the
     [exists]. *)
  intro h.
  (* The specification of [head] turns [h] into an [exists], which opens
     into a witness [r] and [e : reverse l = Cons a r]. *)
  destruct (head_specification_forward A a (reverse l) h) as [r e].
  (* [reverse r] is the witness: [|- l = append (reverse r) (Cons a Nil)] *)
  apply (Exists_introduction (reverse r)).
  (* [reverse] applied to both sides of [e]; the context gains
     [e' : reverse (reverse l) = reverse (Cons a r)]. *)
  pose proof (Identity.congruence reverse e) as e'.
  (* [reverse_involution] undoes the double reversal:
     [e' : l = reverse (Cons a r)] *)
  rewrite reverse_involution in e'.
  (* The [reverse] step computes: [e' : l = append (reverse r) (Cons a Nil)] *)
  simpl in e'.
  (* [e'] is a proof of the goal as it stands. *)
  exact e'.
Qed.

Lemma last_specification_backward
  : forall (A : Type) (a : A) (l : List A),
      (exists (l' : List A), l = append l' (Cons a Nil)) -> last l = Some a.
Proof.
  (* The context gains [A], [a] and [l]:
     [|- (exists (l' : List A), l = append l' (Cons a Nil))
         -> last l = Some a] *)
  intros A a l.
  (* The context gains [h], the [exists]: [|- last l = Some a] *)
  intro h.
  (* [h] opens into a witness [l'] and [e : l = append l' (Cons a Nil)]. *)
  destruct h as [l' e].
  (* [|- head (reverse l) = Some a] *)
  unfold last in |- *.
  (* [e] replaces [l]: [|- head (reverse (append l' (Cons a Nil))) = Some a] *)
  rewrite e in |- *.
  (* [reverse_antidistributivity_over_append] turns the [append] around:
     [|- head (append (reverse (Cons a Nil)) (reverse l')) = Some a] *)
  rewrite reverse_antidistributivity_over_append in |- *.
  (* [reverse (Cons a Nil)] computes to [Cons a Nil], the [append] steps
     once and [head] reads the front: [|- Some a = Some a] *)
  simpl in |- *.
  (* Both sides are the same term. *)
  reflexivity.
Qed.

Theorem last_specification
  : forall (A : Type) (a : A) (l : List A),
      last l = Some a <-> (exists (l' : List A), l = append l' (Cons a Nil)).
Proof.
  (* The context gains [A], [a] and [l]:
     [|- last l = Some a
         <-> (exists (l' : List A), l = append l' (Cons a Nil))] *)
  intros A a l.
  (* [Biimplication] has one ctor with two fields, so the goal splits into two
     goals, the forward and the backward half. *)
  split.
  - (* [last_specification_forward A a l] is a proof of the goal as it
       stands. *)
    exact (last_specification_forward A a l).
  - (* [last_specification_backward A a l] is a proof of the goal as it
       stands. *)
    exact (last_specification_backward A a l).
Qed.

Lemma initial_specification_forward
  : forall (A : Type) (l : List A) (l' : List A),
      initial l = Some l' -> exists (a : A), l = append l' (Cons a Nil).
Proof.
  (* The context gains [A], [l] and [l']:
     [|- initial l = Some l' -> exists (a : A), l = append l' (Cons a Nil)] *)
  intros A l l'.
  (* [|- Option.map reverse (tail (reverse l)) = Some l' -> ...] *)
  unfold initial in |- *.
  (* [reverse l] is either [Nil] or [Cons b r]: one goal per ctor, each
     keeping the equation as [er]. *)
  destruct (reverse l) as [| b r] eqn:er.
  - (* [tail Nil] and then [Option.map] compute:
       [|- None = Some l' -> ...] *)
    simpl in |- *.
    (* The context gains [h : None = Some l']: the goal is the [exists]. *)
    intro h.
    (* [h] claims [None = Some l'], and the two are different ctors. *)
    discriminate.
  - (* [tail (Cons b r)] and then [Option.map] compute:
       [|- Some (reverse r) = Some l' -> ...] *)
    simpl in |- *.
    (* The context gains [h : Some (reverse r) = Some l']: the goal is the
       [exists]. *)
    intro h.
    (* [Option.some_injectivity] turns [h] into [e' : reverse r = l']. *)
    pose proof (Option.some_injectivity (List A) (reverse r) l' h) as e'.
    (* [b] is the witness: [|- l = append l' (Cons b Nil)] *)
    apply (Exists_introduction b).
    (* [reverse] applied to both sides of [er]; the context gains
       [er' : reverse (reverse l) = reverse (Cons b r)]. *)
    pose proof (Identity.congruence reverse er) as er'.
    (* [reverse_involution] undoes the double reversal:
       [er' : l = reverse (Cons b r)] *)
    rewrite reverse_involution in er'.
    (* The [reverse] step computes:
       [er' : l = append (reverse r) (Cons b Nil)] *)
    simpl in er'.
    (* [e'] replaces [reverse r] by [l']: [er' : l = append l' (Cons b Nil)] *)
    rewrite e' in er'.
    (* [er'] is a proof of the goal as it stands. *)
    exact er'.
Qed.

Lemma initial_specification_backward
  : forall (A : Type) (l : List A) (l' : List A),
      (exists (a : A), l = append l' (Cons a Nil)) -> initial l = Some l'.
Proof.
  (* The context gains [A], [l] and [l']:
     [|- (exists (a : A), l = append l' (Cons a Nil)) -> initial l = Some l'] *)
  intros A l l'.
  (* The context gains [h], the [exists]: [|- initial l = Some l'] *)
  intro h.
  (* [h] opens into a witness [a] and [e : l = append l' (Cons a Nil)]. *)
  destruct h as [a e].
  (* [|- Option.map reverse (tail (reverse l)) = Some l'] *)
  unfold initial in |- *.
  (* [e] replaces [l]:
     [|- Option.map reverse (tail (reverse (append l' (Cons a Nil))))
         = Some l'] *)
  rewrite e in |- *.
  (* [reverse_antidistributivity_over_append] turns the [append] around:
     [|- Option.map reverse (tail (append (reverse (Cons a Nil)) (reverse l')))
         = Some l'] *)
  rewrite reverse_antidistributivity_over_append in |- *.
  (* [reverse (Cons a Nil)] computes to [Cons a Nil], the [append] steps
     once, [tail] drops [a] and [Option.map] reaches the payload:
     [|- Some (reverse (reverse l')) = Some l'] *)
  simpl in |- *.
  (* [reverse_involution] undoes the double reversal: [|- Some l' = Some l'] *)
  rewrite reverse_involution in |- *.
  (* Both sides are the same term. *)
  reflexivity.
Qed.

Theorem initial_specification
  : forall (A : Type) (l : List A) (l' : List A),
      initial l = Some l' <-> (exists (a : A), l = append l' (Cons a Nil)).
Proof.
  (* The context gains [A], [l] and [l']:
     [|- initial l = Some l'
         <-> (exists (a : A), l = append l' (Cons a Nil))] *)
  intros A l l'.
  (* [Biimplication] has one ctor with two fields, so the goal splits into two
     goals, the forward and the backward half. *)
  split.
  - (* [initial_specification_forward A l l'] is a proof of the goal as it
       stands. *)
    exact (initial_specification_forward A l l').
  - (* [initial_specification_backward A l l'] is a proof of the goal as it
       stands. *)
    exact (initial_specification_backward A l l').
Qed.

(* [forall {A : Type}, List A -> Option (A * List A)]
   [head] and [tail] in one answer: [None] on the empty list, else the
   first element paired with the rest. *)
Definition pop := fun {A : Type} (l : List A) =>
  match l return Option (A * List A) with
  | Nil       => None
  | Cons a l' => Some (Pair_introduction a l')
  end.

Lemma pop_specification_forward
  : forall (A : Type) (a : A) (l' : List A) (l : List A),
      pop l = Some (Pair_introduction a l') -> l = Cons a l'.
Proof.
  (* The context gains [A], [a], [l'] and [l]:
     [|- pop l = Some (Pair_introduction a l') -> l = Cons a l'] *)
  intros A a l' l.
  (* [l] is either [Nil] or [Cons b rest]: one goal per ctor. *)
  destruct l as [| b rest].
  - (* [pop Nil] computes:
       [|- None = Some (Pair_introduction a l') -> Nil = Cons a l'] *)
    simpl in |- *.
    (* The context gains [e : None = Some (Pair_introduction a l')]:
       [|- Nil = Cons a l'] *)
    intro e.
    (* [e] equates two distinct ctors, which closes any goal. *)
    discriminate.
  - (* [pop (Cons b rest)] computes:
       [|- Some (Pair_introduction b rest) = Some (Pair_introduction a l')
           -> Cons b rest = Cons a l'] *)
    simpl in |- *.
    (* The context gains
       [e : Some (Pair_introduction b rest) = Some (Pair_introduction a l')]:
       [|- Cons b rest = Cons a l'] *)
    intro e.
    (* [Option.some_injectivity] strips the [Some]:
       [e' : Pair_introduction b rest = Pair_introduction a l'] *)
    pose proof (Option.some_injectivity (A * List A)
                  (Pair_introduction b rest) (Pair_introduction a l') e) as e'.
    (* [Pair.introduction_injectivity] splits the pair:
       [e'' : b = a /\ rest = l'] *)
    pose proof (Pair.introduction_injectivity A (List A) b rest a l' e') as e''.
    (* The conjunction opens into [eb : b = a] and [erest : rest = l']. *)
    destruct e'' as [eb erest].
    (* [eb] replaces [b]: [|- Cons a rest = Cons a l'] *)
    rewrite eb in |- *.
    (* [erest] replaces [rest]: [|- Cons a l' = Cons a l'] *)
    rewrite erest in |- *.
    (* Both sides are the same term. *)
    reflexivity.
Qed.

Lemma pop_specification_backward
  : forall (A : Type) (a : A) (l' : List A) (l : List A),
      l = Cons a l' -> pop l = Some (Pair_introduction a l').
Proof.
  (* The context gains [A], [a], [l'], [l] and [e : l = Cons a l']:
     [|- pop l = Some (Pair_introduction a l')] *)
  intros A a l' l e.
  (* [e] replaces [l]: [|- pop (Cons a l') = Some (Pair_introduction a l')] *)
  rewrite e in |- *.
  (* [pop (Cons a l')] computes:
     [|- Some (Pair_introduction a l') = Some (Pair_introduction a l')] *)
  simpl in |- *.
  (* Both sides are the same term. *)
  reflexivity.
Qed.

(* [pop] answers [Some (a , l')] exactly on [Cons a l']. *)
Theorem pop_specification
  : forall (A : Type) (a : A) (l' : List A) (l : List A),
      pop l = Some (Pair_introduction a l') <-> l = Cons a l'.
Proof.
  (* The context gains [A], [a], [l'] and [l]:
     [|- pop l = Some (Pair_introduction a l') <-> l = Cons a l'] *)
  intros A a l' l.
  (* [Biimplication] has one ctor with two fields, so the goal splits into two
     goals, the forward and the backward half. *)
  split.
  - (* [pop_specification_forward A a l' l] is a proof of the goal as it
       stands. *)
    exact (pop_specification_forward A a l' l).
  - (* [pop_specification_backward A a l' l] is a proof of the goal as it
       stands. *)
    exact (pop_specification_backward A a l' l).
Qed.

(* Projecting a [pop] gives back [head] and [tail]. *)

Theorem pop_head_projection
  : forall (A : Type) (l : List A), Option.map Pair.first (pop l) = head l.
Proof.
  (* The context gains [A] and [l]: [|- Option.map Pair.first (pop l) = head l] *)
  intros A l.
  (* [l] is either [Nil] or [Cons a l']: one goal per ctor. *)
  destruct l as [| a l'].
  - (* [pop], [Option.map] and [head] compute on [Nil]: [|- None = None] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
  - (* [pop] gives [Some (Pair_introduction a l')], [Option.map] applies
       [Pair.first] inside, [head] gives [Some a]: [|- Some a = Some a] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
Qed.

Theorem pop_tail_projection
  : forall (A : Type) (l : List A), Option.map Pair.second (pop l) = tail l.
Proof.
  (* The context gains [A] and [l]:
     [|- Option.map Pair.second (pop l) = tail l] *)
  intros A l.
  (* [l] is either [Nil] or [Cons a l']: one goal per ctor. *)
  destruct l as [| a l'].
  - (* [pop], [Option.map] and [tail] compute on [Nil]: [|- None = None] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
  - (* [pop] gives [Some (Pair_introduction a l')], [Option.map] applies
       [Pair.second] inside, [tail] gives [Some l']: [|- Some l' = Some l'] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
Qed.

Fixpoint zip {A : Type} {B : Type} (l1 : List A) (l2 : List B)
  : List (A * B) :=
  match l1, l2 with
  | Cons a l1', Cons b l2' => Cons (Pair_introduction a b) (zip l1' l2')
  | Nil, Nil               => Nil
  | Nil, Cons _ _          => Nil
  | Cons _ _, Nil          => Nil
  end.

(* [forall {A : Type} {B : Type}, List (A * B) -> List A * List B]
   The two projections mapped over the list, so the laws of [map] carry
   over. *)
Definition unzip := fun {A : Type} {B : Type} (l : List (A * B)) =>
  Pair_introduction (map Pair.first l) (map Pair.second l).

(* Zipping the two halves of an [unzip] rebuilds the list. The other order,
   [unzip (zip l1 l2)], needs the two lists to be of one length. *)
Theorem zip_unzip_identity
  : forall (A : Type) (B : Type) (l : List (A * B)),
      zip (Pair.first (unzip l)) (Pair.second (unzip l)) = l.
Proof.
  (* The context gains [A], [B] and [l]:
     [|- zip (Pair.first (unzip l)) (Pair.second (unzip l)) = l] *)
  intros A B l.
  (* [l] is either [Nil] or [Cons p l']: one goal per ctor, and the second
     has [p], [l'] and
     [IH : zip (Pair.first (unzip l')) (Pair.second (unzip l')) = l'] in its
     context. *)
  induction l as [| p l' IH] using List_induction.
  - (* [unzip Nil] is [Pair_introduction Nil Nil], the projections and [zip]
       compute: [|- Nil = Nil] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
  - (* [unzip (Cons p l')] unfolds to a pair of two [map]s, each stepping
       once, the projections compute and [zip] steps once:
       [|- Cons (Pair_introduction (Pair.first p) (Pair.second p))
                (zip (map Pair.first l') (map Pair.second l'))
           = Cons p l'] *)
    simpl in |- *.
    (* [IH] unfolds to the same shape:
       [IH : zip (Pair.first (Pair_introduction (map Pair.first l')
                                                (map Pair.second l')))
                 (Pair.second (Pair_introduction (map Pair.first l')
                                                 (map Pair.second l')))
             = l'] *)
    unfold unzip in IH.
    (* The projections compute:
       [IH : zip (map Pair.first l') (map Pair.second l') = l'] *)
    simpl in IH.
    (* [IH] replaces the inner [zip]:
       [|- Cons (Pair_introduction (Pair.first p) (Pair.second p)) l'
           = Cons p l'] *)
    rewrite IH in |- *.
    (* [Pair.introduction_surjectivity] read right to left folds the pair
       of projections back into [p]: [|- Cons p l' = Cons p l'] *)
    rewrite <- (Pair.introduction_surjectivity A B p) in |- *.
    (* Both sides are the same term. *)
    reflexivity.
Qed.

(* Unzipping a [zip] gives the two lists back when they are of one length;
   [zip] stops with the shorter list, so a longer one is not recovered.
   Induction on [l1] with [l2] kept in the motive, since [zip] and
   [length] step on both lists at once; the two mismatched cases contradict
   [NatWithZero.add_positive_refutes_zero] and the matched case feeds the
   hypothesis through [NatWithZero.add_right_cancellation]. *)
Theorem unzip_zip_identity
  : forall (A : Type) (B : Type) (l1 : List A) (l2 : List B),
      length l1 = length l2 -> unzip (zip l1 l2) = Pair_introduction l1 l2.
Proof.
  (* The context gains [A], [B] and [l1]:
     [|- forall (l2 : List B), length l1 = length l2
         -> unzip (zip l1 l2) = Pair_introduction l1 l2] *)
  intros A B l1.
  (* [l1] is either [Nil] or [Cons a l1']: one goal per ctor, and the
     second has [a], [l1'] and
     [IH : forall (l2 : List B), length l1' = length l2
           -> unzip (zip l1' l2) = Pair_introduction l1' l2]
     in its context. *)
  induction l1 as [| a l1' IH] using List_induction.
  - (* The context gains [l2] and [e : length Nil = length l2]:
       [|- unzip (zip Nil l2) = Pair_introduction Nil l2] *)
    intros l2 e.
    (* [l2] is either [Nil] or [Cons b l2']: one goal per ctor. *)
    destruct l2 as [| b l2'].
    + (* [|- Pair_introduction (map Pair.first (zip Nil Nil))
                               (map Pair.second (zip Nil Nil))
           = Pair_introduction Nil Nil] *)
      unfold unzip in |- *.
      (* [zip] and both [map]s compute on [Nil]:
         [|- Pair_introduction Nil Nil = Pair_introduction Nil Nil] *)
      simpl in |- *.
      (* Both sides are the same term. *)
      reflexivity.
    + (* Both [length]s step:
         [e : Zero = NatWithZero.add (length l2') (Positive One)] *)
      simpl in e.
      (* Turned round:
         [e' : NatWithZero.add (length l2') (Positive One) = Zero] *)
      pose proof (Identity.symmetry e) as e'.
      (* [h : ~ (NatWithZero.add (length l2') (Positive One) = Zero)] *)
      pose proof (NatWithZero.add_positive_refutes_zero (length l2') One) as h.
      (* [h : NatWithZero.add (length l2') (Positive One) = Zero -> Falsum] *)
      unfold Negation in h.
      (* [f : Falsum] *)
      pose proof (h e') as f.
      (* [f : Falsum], which is what [contradiction] looks for. *)
      contradiction.
  - (* The context gains [l2] and [e : length (Cons a l1') = length l2]:
       [|- unzip (zip (Cons a l1') l2) = Pair_introduction (Cons a l1') l2] *)
    intros l2 e.
    (* [l2] is either [Nil] or [Cons b l2']: one goal per ctor. *)
    destruct l2 as [| b l2'].
    + (* Both [length]s step:
         [e : NatWithZero.add (length l1') (Positive One) = Zero] *)
      simpl in e.
      (* [h : ~ (NatWithZero.add (length l1') (Positive One) = Zero)] *)
      pose proof (NatWithZero.add_positive_refutes_zero (length l1') One) as h.
      (* [h : NatWithZero.add (length l1') (Positive One) = Zero -> Falsum] *)
      unfold Negation in h.
      (* [f : Falsum] *)
      pose proof (h e) as f.
      (* [f : Falsum], which is what [contradiction] looks for. *)
      contradiction.
    + (* Both [length]s step:
         [e : NatWithZero.add (length l1') (Positive One)
              = NatWithZero.add (length l2') (Positive One)] *)
      simpl in e.
      (* The [Positive One] cancels: [e' : length l1' = length l2'] *)
      pose proof (NatWithZero.add_right_cancellation
                    (length l1') (length l2') (Positive One) e) as e'.
      (* [IH] on [l2'] and [e']:
         [IH' : unzip (zip l1' l2') = Pair_introduction l1' l2'] *)
      pose proof (IH l2' e') as IH'.
      (* [IH' : Pair_introduction (map Pair.first (zip l1' l2'))
                                  (map Pair.second (zip l1' l2'))
                = Pair_introduction l1' l2'] *)
      unfold unzip in IH'.
      (* [Pair.introduction_injectivity] splits the pair:
         [e'' : map Pair.first (zip l1' l2') = l1'
                /\ map Pair.second (zip l1' l2') = l2'] *)
      pose proof (Pair.introduction_injectivity (List A) (List B)
                    (map Pair.first (zip l1' l2'))
                    (map Pair.second (zip l1' l2'))
                    l1' l2' IH') as e''.
      (* The conjunction opens into [e1] and [e2], one per component. *)
      destruct e'' as [e1 e2].
      (* [|- Pair_introduction
               (map Pair.first (zip (Cons a l1') (Cons b l2')))
               (map Pair.second (zip (Cons a l1') (Cons b l2')))
           = Pair_introduction (Cons a l1') (Cons b l2')] *)
      unfold unzip in |- *.
      (* [zip] steps once and each [map] steps once:
         [|- Pair_introduction (Cons a (map Pair.first (zip l1' l2')))
                               (Cons b (map Pair.second (zip l1' l2')))
             = Pair_introduction (Cons a l1') (Cons b l2')] *)
      simpl in |- *.
      (* [e1] replaces the first [map]:
         [|- Pair_introduction (Cons a l1')
                               (Cons b (map Pair.second (zip l1' l2')))
             = Pair_introduction (Cons a l1') (Cons b l2')] *)
      rewrite e1 in |- *.
      (* [e2] replaces the second:
         [|- Pair_introduction (Cons a l1') (Cons b l2')
             = Pair_introduction (Cons a l1') (Cons b l2')] *)
      rewrite e2 in |- *.
      (* Both sides are the same term. *)
      reflexivity.
Qed.

(* Splits a list into the elements [p] accepts and the ones it rejects, in
   one pass; the recursive result is opened by a [match] so both halves
   are extended in place. *)
Fixpoint partition {A : Type} (p : A -> Bool) (l : List A)
  : List A * List A :=
  match l with
  | Nil       => Pair_introduction Nil Nil
  | Cons a l' =>
      match partition p l' with
      | Pair_introduction yes no =>
          match p a with
          | true  => Pair_introduction (Cons a yes) no
          | false => Pair_introduction yes (Cons a no)
          end
      end
  end.

(* The two halves of a [partition] are the two [filter]s, by [p] and by its
   negation. *)
Theorem partition_specification
  : forall (A : Type) (p : A -> Bool) (l : List A),
      partition p l
      = Pair_introduction (filter p l)
                          (filter (fun (a : A) => Bool.negate (p a)) l).
Proof.
  (* The context gains [A], [p] and [l]:
     [|- partition p l
         = Pair_introduction (filter p l)
                             (filter (fun a => Bool.negate (p a)) l)] *)
  intros A p l.
  (* [l] is either [Nil] or [Cons a l']: one goal per ctor, and the second
     has [a], [l'] and
     [IH : partition p l'
           = Pair_introduction (filter p l')
                               (filter (fun a => Bool.negate (p a)) l')]
     in its context. *)
  induction l as [| a l' IH] using List_induction.
  - (* [partition] and both [filter]s compute on [Nil]:
       [|- Pair_introduction Nil Nil = Pair_introduction Nil Nil] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
  - (* Each side steps once; the left side is a [match] on [partition p l'],
       the right side a pair of two [match]es on [p a] and on
       [Bool.negate (p a)]. *)
    simpl in |- *.
    (* [IH] replaces [partition p l'] by a [Pair_introduction], on which the
       outer [match] reduces:
       [|- match p a with
           | true  => Pair_introduction (Cons a (filter p l'))
                        (filter (fun a => Bool.negate (p a)) l')
           | false => Pair_introduction (filter p l')
                        (Cons a (filter (fun a => Bool.negate (p a)) l'))
           end
           = Pair_introduction
               (match p a with
                | true  => Cons a (filter p l')
                | false => filter p l'
                end)
               (match Bool.negate (p a) with
                | true  => Cons a (filter (fun a => Bool.negate (p a)) l')
                | false => filter (fun a => Bool.negate (p a)) l'
                end)] *)
    rewrite IH in |- *.
    (* [p a] is either [true] or [false]: one goal per ctor, with
       [pa : p a = true] or [pa : p a = false] in its context, every [p a]
       in the goal replaced and the two [match]es on it reduced; only the
       [match] on [Bool.negate true] (or [false]) is left. *)
    destruct (p a) as [|] eqn:pa.
    + (* [Bool.negate true] computes to [false] and its [match] reduces:
         [|- Pair_introduction (Cons a (filter p l'))
               (filter (fun a => Bool.negate (p a)) l')
             = Pair_introduction (Cons a (filter p l'))
                 (filter (fun a => Bool.negate (p a)) l')] *)
      simpl in |- *.
      (* Both sides are the same term. *)
      reflexivity.
    + (* [Bool.negate false] computes to [true] and its [match] reduces:
         [|- Pair_introduction (filter p l')
               (Cons a (filter (fun a => Bool.negate (p a)) l'))
             = Pair_introduction (filter p l')
                 (Cons a (filter (fun a => Bool.negate (p a)) l'))] *)
      simpl in |- *.
      (* Both sides are the same term. *)
      reflexivity.
Qed.

(* Indexing from [Zero]: [nth l i] is the element [i] places from the front,
   [None] past the end. Recursion is on the list; the index is peeled by
   one alongside, [Positive One] being the last step before [Zero]. *)
Fixpoint nth {A : Type} (l : List A) (i : NatWithZero) : Option A :=
  match l with
  | Nil       => None
  | Cons a l' =>
      match i with
      | Zero                    => Some a
      | Positive One            => nth l' Zero
      | Positive (Successor i') => nth l' (Positive i')
      end
  end.

(* [nth] answers exactly for the indices below the length. Each step of the
   index is one step of the list, so the halves lift [IH] through
   [Positive One] added on both sides of the order. *)

Lemma nth_specification_forward
  : forall (A : Type) (l : List A) (i : NatWithZero),
      (exists (a : A), nth l i = Some a) -> NatWithZero.LessThan i (length l).
Proof.
  (* The context gains [A] and [l]. *)
  intros A l.
  (* [l] is either [Nil] or [Cons b l']: one goal per ctor, and the second
     has [b], [l'] and [IH] for every index in its context. *)
  induction l as [| b l' IH] using List_induction.
  - (* [nth Nil i] computes to [None], so the witness equates two distinct
       ctors, which closes any goal. *)
    intros i h.
    destruct h as [a e].
    simpl in e.
    discriminate.
  - (* One goal per shape of the index. *)
    intros i h.
    destruct i as [| i'].
    + (* [Zero] is below the length of a [Cons], the length of [l'] plus one:
         [|- NatWithZero.LessThan Zero
               (NatWithZero.add (length l') (Positive One))] *)
      simpl in |- *.
      exact (NatWithZero.add_positive_positivity (length l') One).
    + destruct i' as [| i''].
      * (* [nth (Cons b l') (Positive One)] computes to [nth l' Zero], so
           [IH] puts [Zero] below [length l']. *)
        simpl in h.
        pose proof (IH Zero h) as lt.
        (* The step [Positive One] is added on both sides of [lt]; the left
           sum computes to [Positive One], the right one is turned round:
           [|- NatWithZero.LessThan (Positive One)
                 (NatWithZero.add (length l') (Positive One))] *)
        simpl in |- *.
        rewrite (NatWithZero.add_commutativity (length l') (Positive One)) in |- *.
        exact (NatWithZero.add_strict_monotonicity (Positive One) Zero (length l') lt).
      * (* [nth (Cons b l') (Positive (Successor i''))] computes to
           [nth l' (Positive i'')], so [IH] puts [Positive i''] below
           [length l']. *)
        simpl in h.
        pose proof (IH (Positive i'') h) as lt.
        (* The step is added on both sides of [lt]; the left sum computes to
           [Positive (Successor i'')]. *)
        simpl in |- *.
        rewrite (NatWithZero.add_commutativity (length l') (Positive One)) in |- *.
        exact (NatWithZero.add_strict_monotonicity
                 (Positive One) (Positive i'') (length l') lt).
Qed.

Lemma nth_specification_backward
  : forall (A : Type) (l : List A) (i : NatWithZero),
      NatWithZero.LessThan i (length l) -> exists (a : A), nth l i = Some a.
Proof.
  (* The context gains [A] and [l]. *)
  intros A l.
  induction l as [| b l' IH] using List_induction.
  - (* Nothing is below [length Nil], which computes to [Zero]: [h] opens
       into [k] and [e : add i (Positive k) = Zero], which
       [add_positive_refutes_zero] refutes. *)
    intros i h.
    simpl in h.
    unfold NatWithZero.LessThan in h.
    destruct h as [k e].
    pose proof (NatWithZero.add_positive_refutes_zero i k) as r.
    unfold Negation in r.
    pose proof (r e) as f.
    contradiction.
  - (* One goal per shape of the index. *)
    intros i h.
    destruct i as [| i'].
    + (* [nth (Cons b l') Zero] computes to [Some b], the witness. *)
      simpl in |- *.
      apply (Exists_introduction b).
      reflexivity.
    + destruct i' as [| i''].
      * (* [length (Cons b l')] computes; commutativity turns the sum round
           and the shared step cancels, the left side being
           [add (Positive One) Zero]: [lt : LessThan Zero (length l')] *)
        simpl in h.
        rewrite (NatWithZero.add_commutativity (length l') (Positive One)) in h.
        pose proof (NatWithZero.add_strict_cancellation (Positive One) Zero (length l') h)
          as lt.
        (* [nth (Cons b l') (Positive One)] computes to [nth l' Zero], which
           [IH] settles. *)
        simpl in |- *.
        exact (IH Zero lt).
      * (* The same one step further: the left side of [h] is
           [add (Positive One) (Positive i'')] once computed. *)
        simpl in h.
        rewrite (NatWithZero.add_commutativity (length l') (Positive One)) in h.
        pose proof (NatWithZero.add_strict_cancellation
                      (Positive One) (Positive i'') (length l') h) as lt.
        simpl in |- *.
        exact (IH (Positive i'') lt).
Qed.

Theorem nth_specification
  : forall (A : Type) (l : List A) (i : NatWithZero),
      (exists (a : A), nth l i = Some a) <-> NatWithZero.LessThan i (length l).
Proof.
  (* The context gains [A], [l] and [i]. *)
  intros A l i.
  (* [Biimplication] has one ctor with two fields, so the goal splits into two
     goals, the forward and the backward half. *)
  split.
  - exact (nth_specification_forward  A l i).
  - exact (nth_specification_backward A l i).
Qed.

(* [take n l] is the first [n] elements, all of [l] when there are fewer;
   [drop n l] is what is left. Both recurse on the list, peeling the count
   alongside as [nth] does. *)
Fixpoint take {A : Type} (n : NatWithZero) (l : List A) : List A :=
  match l with
  | Nil       => Nil
  | Cons a l' =>
      match n with
      | Zero                    => Nil
      | Positive One            => Cons a Nil
      | Positive (Successor n') => Cons a (take (Positive n') l')
      end
  end.

Fixpoint drop {A : Type} (n : NatWithZero) (l : List A) : List A :=
  match l with
  | Nil       => Nil
  | Cons a l' =>
      match n with
      | Zero                    => Cons a l'
      | Positive One            => l'
      | Positive (Successor n') => drop (Positive n') l'
      end
  end.

(* [forall {A : Type}, NatWithZero -> List A -> List A * List A] *)
Definition split_at := fun {A : Type} (n : NatWithZero) (l : List A) =>
  Pair_introduction (take n l) (drop n l).

(* The two parts put back together give the list. *)
Theorem take_drop_decomposition
  : forall (A : Type) (l : List A) (n : NatWithZero),
      append (take n l) (drop n l) = l.
Proof.
  (* The context gains [A] and [l]. *)
  intros A l.
  (* [l] is either [Nil] or [Cons a l']: one goal per ctor, and the second
     has [a], [l'] and [IH] for every count in its context. *)
  induction l as [| a l' IH] using List_induction.
  - (* Both parts of [Nil] compute to [Nil], and so does their
       concatenation. *)
    intros n.
    simpl in |- *.
    reflexivity.
  - (* One goal per shape of the count. *)
    intros n.
    destruct n as [| n'].
    + (* [take Zero] is [Nil] and [drop Zero] is the list:
         [|- Cons a l' = Cons a l'] after computing *)
      simpl in |- *.
      reflexivity.
    + destruct n' as [| n''].
      * (* [take (Positive One)] keeps the head and [drop (Positive One)]
           the tail: [|- Cons a l' = Cons a l'] after computing *)
        simpl in |- *.
        reflexivity.
      * (* One step of each:
           [|- Cons a (append (take (Positive n'') l') (drop (Positive n'') l'))
               = Cons a l'] *)
        simpl in |- *.
        (* [IH] at the smaller count closes the tail. *)
        rewrite (IH (Positive n'')) in |- *.
        reflexivity.
Qed.

(* The length of a [take] is the smaller of the count and the length; each
   step adds one to both candidates, and addition distributes over [min]. *)
Theorem length_take
  : forall (A : Type) (l : List A) (n : NatWithZero),
      length (take n l) = NatWithZero.min n (length l).
Proof.
  (* The context gains [A] and [l]. *)
  intros A l.
  induction l as [| a l' IH] using List_induction.
  - (* [take n Nil] and [length Nil] compute to [Nil] and [Zero], and [Zero]
       absorbs under [min]: [|- Zero = NatWithZero.min n Zero] *)
    intros n.
    simpl in |- *.
    rewrite (NatWithZero.min_right_absorption n) in |- *.
    reflexivity.
  - (* One goal per shape of the count. *)
    intros n.
    destruct n as [| n'].
    + (* [take Zero] is [Nil], and [Zero] absorbs under [min]:
         [|- Zero = NatWithZero.min Zero (NatWithZero.add (length l') (Positive One))] *)
      simpl in |- *.
      rewrite (NatWithZero.min_left_absorption
                 (NatWithZero.add (length l') (Positive One))) in |- *.
      reflexivity.
    + destruct n' as [| n''].
      * (* [take (Positive One)] keeps one element, whose length computes to
           [Positive One]; that is the smaller candidate, the length of [l']
           plus one being at least one:
           [|- Positive One
               = NatWithZero.min (Positive One)
                   (NatWithZero.add (length l') (Positive One))] *)
        simpl in |- *.
        rewrite (Biimplication.elimination_backward
                   (NatWithZero.min (Positive One)
                      (NatWithZero.add (length l') (Positive One)) = Positive One)
                   (NatWithZero.LessOrEqual (Positive One)
                      (NatWithZero.add (length l') (Positive One)))
                   (NatWithZero.min_specification (Positive One)
                      (NatWithZero.add (length l') (Positive One)))
                   (NatWithZero.add_right_inflation (length l') (Positive One))) in |- *.
        reflexivity.
      * (* One step of [take] and one of [length]:
           [|- NatWithZero.add (length (take (Positive n'') l')) (Positive One)
               = NatWithZero.min (Positive (Successor n''))
                   (NatWithZero.add (length l') (Positive One))] *)
        simpl in |- *.
        (* [IH] at the smaller count replaces the inner length. *)
        rewrite (IH (Positive n'')) in |- *.
        (* Commutativity puts the step in front, and addition distributes
           over [min]:
           [|- NatWithZero.min (NatWithZero.add (Positive One) (Positive n''))
                 (NatWithZero.add (Positive One) (length l'))
               = ...] *)
        rewrite (NatWithZero.add_commutativity
                   (NatWithZero.min (Positive n'') (length l')) (Positive One)) in |- *.
        rewrite (NatWithZero.add_left_distributivity_over_min
                   (Positive One) (Positive n'') (length l')) in |- *.
        (* The first candidate is [Positive (Successor n'')] by computation;
           [simpl] would also open the second, whose first argument is a
           ctor, into a [match] on [length l']. *)
        change (NatWithZero.add (Positive One) (Positive n''))
          with (Positive (Successor n'')) in |- *.
        (* Commutativity turns the second candidate round: both sides are
           the same term. *)
        rewrite (NatWithZero.add_commutativity (Positive One) (length l')) in |- *.
        reflexivity.
Qed.

(* The length of a [drop] is the length less the count; each step takes one
   from both, which truncated subtraction ignores. *)
Theorem length_drop
  : forall (A : Type) (l : List A) (n : NatWithZero),
      length (drop n l) = NatWithZero.subtract (length l) n.
Proof.
  (* The context gains [A] and [l]. *)
  intros A l.
  induction l as [| a l' IH] using List_induction.
  - (* [drop n Nil] and [length Nil] compute, and [subtract Zero n] computes
       to [Zero]: [|- Zero = Zero] *)
    intros n.
    simpl in |- *.
    reflexivity.
  - (* One goal per shape of the count. *)
    intros n.
    destruct n as [| n'].
    + (* [drop Zero] is the list, and [Zero] is a right identity of
         subtraction. *)
      simpl in |- *.
      rewrite (NatWithZero.subtract_right_identity
                 (NatWithZero.add (length l') (Positive One))) in |- *.
      reflexivity.
    + destruct n' as [| n''].
      * (* [drop (Positive One)] is the tail, and taking the step away from
           the length plus the step gives the length back:
           [|- length l'
               = NatWithZero.subtract (NatWithZero.add (length l') (Positive One))
                   (Positive One)] *)
        simpl in |- *.
        rewrite (NatWithZero.subtract_inversion_of_add (length l') (Positive One)) in |- *.
        reflexivity.
      * (* One step of [drop] and one of [length]:
           [|- length (drop (Positive n'') l')
               = NatWithZero.subtract (NatWithZero.add (length l') (Positive One))
                   (Positive (Successor n''))] *)
        simpl in |- *.
        rewrite (IH (Positive n'')) in |- *.
        (* Commutativity puts the step in front on the left; the count is the
           step plus [Positive n''] by computation; the shared step cancels. *)
        rewrite (NatWithZero.add_commutativity (length l') (Positive One)) in |- *.
        change (Positive (Successor n''))
          with (NatWithZero.add (Positive One) (Positive n'')) in |- *.
        rewrite (NatWithZero.subtract_translation_invariance
                   (Positive One) (length l') (Positive n'')) in |- *.
        reflexivity.
Qed.

(* [replicate n a] is [a] repeated [n] times. A count of [Zero] gives [Nil];
   a positive count recurses on its [Nat], one element per step, since a
   [NatWithZero] has no step of its own to recurse on. *)
Fixpoint replicate_positive {A : Type} (k : Nat) (a : A) : List A :=
  match k with
  | One          => Cons a Nil
  | Successor k' => Cons a (replicate_positive k' a)
  end.

(* [forall {A : Type}, NatWithZero -> A -> List A] *)
Definition replicate := fun {A : Type} (n : NatWithZero) (a : A) =>
  match n with
  | Zero       => Nil
  | Positive k => replicate_positive k a
  end.

Lemma length_replicate_positive
  : forall (A : Type) (k : Nat) (a : A), length (replicate_positive k a) = Positive k.
Proof.
  (* The context gains [A], [k] and [a]. *)
  intros A k a.
  (* [k] is either [One] or [Successor k']: one goal per ctor, and the
     second has [k'] and [IH : length (replicate_positive k' a) = Positive k']
     in its context. *)
  induction k as [| k' IH] using Nat_induction.
  - (* One element, whose length computes: [|- Positive One = Positive One] *)
    simpl in |- *.
    reflexivity.
  - (* One step: [|- NatWithZero.add (length (replicate_positive k' a)) (Positive One)
                     = Positive (Successor k')] *)
    simpl in |- *.
    rewrite IH in |- *.
    (* The sum computes to [Positive (Nat.add k' One)]; commutativity turns
       the inner sum round and it computes to [Successor k']. *)
    simpl in |- *.
    rewrite (Nat.add_commutativity k' One) in |- *.
    simpl in |- *.
    reflexivity.
Qed.

Theorem length_replicate
  : forall (A : Type) (n : NatWithZero) (a : A), length (replicate n a) = n.
Proof.
  (* The context gains [A], [n] and [a]; one goal per ctor of [n]. *)
  intros A n a.
  destruct n as [| k].
  - simpl in |- *.
    reflexivity.
  - (* [replicate (Positive k)] computes to [replicate_positive k]. *)
    simpl in |- *.
    exact (length_replicate_positive A k a).
Qed.

(* [zip] stops with the shorter list, so its length is the smaller of the
   two; each step adds one to both, and addition distributes over [min]. *)
Theorem length_zip
  : forall (A : Type) (B : Type) (l1 : List A) (l2 : List B),
      length (zip l1 l2) = NatWithZero.min (length l1) (length l2).
Proof.
  (* The context gains [A], [B] and [l1]. *)
  intros A B l1.
  induction l1 as [| a l1' IH] using List_induction.
  - (* [zip Nil l2] computes to [Nil] whichever ctor [l2] is, and [Zero]
       absorbs under [min]. *)
    intros l2.
    destruct l2 as [| b l2'].
    + simpl in |- *.
      reflexivity.
    + simpl in |- *.
      rewrite (NatWithZero.min_left_absorption
                 (NatWithZero.add (length l2') (Positive One))) in |- *.
      reflexivity.
  - intros l2.
    destruct l2 as [| b l2'].
    + (* [zip (Cons a l1') Nil] computes to [Nil], and [Zero] absorbs on the
         right. *)
      simpl in |- *.
      rewrite (NatWithZero.min_right_absorption
                 (NatWithZero.add (length l1') (Positive One))) in |- *.
      reflexivity.
    + (* One step of [zip] and of each [length]:
         [|- NatWithZero.add (length (zip l1' l2')) (Positive One)
             = NatWithZero.min (NatWithZero.add (length l1') (Positive One))
                 (NatWithZero.add (length l2') (Positive One))] *)
      simpl in |- *.
      rewrite (IH l2') in |- *.
      (* Commutativity puts the step in front, addition distributes over
         [min], and commutativity turns both candidates back. *)
      rewrite (NatWithZero.add_commutativity
                 (NatWithZero.min (length l1') (length l2')) (Positive One)) in |- *.
      rewrite (NatWithZero.add_left_distributivity_over_min
                 (Positive One) (length l1') (length l2')) in |- *.
      rewrite (NatWithZero.add_commutativity (Positive One) (length l1')) in |- *.
      rewrite (NatWithZero.add_commutativity (Positive One) (length l2')) in |- *.
      reflexivity.
Qed.

(* The sum and the product of a list of numbers: [fold_right] over the two
   monoids of [NatWithZero], the empty list giving the identity. *)

(* [List NatWithZero -> NatWithZero] *)
Definition sum := fun (l : List NatWithZero) => fold_right NatWithZero.add Zero l.

(* [List NatWithZero -> NatWithZero] *)
Definition product := fun (l : List NatWithZero) =>
  fold_right NatWithZero.mul (Positive One) l.

Theorem sum_additivity_over_append
  : forall (l1 : List NatWithZero) (l2 : List NatWithZero),
      sum (append l1 l2) = NatWithZero.add (sum l1) (sum l2).
Proof.
  (* The context gains [l1] and [l2]; [sum] opens into its fold. *)
  intros l1 l2.
  unfold sum in |- *.
  induction l1 as [| a l1' IH] using List_induction.
  - (* [append Nil] and the fold of [Nil] compute, and [add Zero] returns
       its second argument: both sides are the same term. *)
    simpl in |- *.
    reflexivity.
  - (* One step of [append] and of each fold:
       [|- NatWithZero.add a (fold_right NatWithZero.add Zero (append l1' l2))
           = NatWithZero.add (NatWithZero.add a (fold_right NatWithZero.add Zero l1'))
               (fold_right NatWithZero.add Zero l2)] *)
    simpl in |- *.
    rewrite IH in |- *.
    (* Associativity regroups the right side: both sides are the same
       term. *)
    rewrite (NatWithZero.add_associativity
               a (fold_right NatWithZero.add Zero l1') (fold_right NatWithZero.add Zero l2))
      in |- *.
    reflexivity.
Qed.

Theorem product_multiplicativity_over_append
  : forall (l1 : List NatWithZero) (l2 : List NatWithZero),
      product (append l1 l2) = NatWithZero.mul (product l1) (product l2).
Proof.
  (* The context gains [l1] and [l2]; [product] opens into its fold. *)
  intros l1 l2.
  unfold product in |- *.
  induction l1 as [| a l1' IH] using List_induction.
  - (* [append Nil] is the identity, the fold of [Nil] is the seed, and
       [Positive One] is the left identity of [mul]. [simpl] is avoided: it
       would open [mul (Positive One) _] into a [match] on the fold. *)
    rewrite (append_left_identity l2) in |- *.
    change (fold_right NatWithZero.mul (Positive One) Nil) with (Positive One) in |- *.
    rewrite (NatWithZero.mul_left_identity (fold_right NatWithZero.mul (Positive One) l2))
      in |- *.
    reflexivity.
  - (* One step of [append] and of each fold; [IH] replaces the inner fold
       and associativity regroups the right side. *)
    simpl in |- *.
    rewrite IH in |- *.
    rewrite (NatWithZero.mul_associativity
               a (fold_right NatWithZero.mul (Positive One) l1')
               (fold_right NatWithZero.mul (Positive One) l2)) in |- *.
    reflexivity.
Qed.

(* [count p l] is how many elements [p] answers [true] on. *)
Fixpoint count {A : Type} (p : A -> Bool) (l : List A) : NatWithZero :=
  match l with
  | Nil       => Zero
  | Cons a l' =>
      match p a with
      | true  => NatWithZero.add (count p l') (Positive One)
      | false => count p l'
      end
  end.

(* [count] is the length of the [filter]: the same case analysis on each
   answer. *)
Theorem count_specification
  : forall (A : Type) (p : A -> Bool) (l : List A), count p l = length (filter p l).
Proof.
  (* The context gains [A], [p] and [l]. *)
  intros A p l.
  induction l as [| a l' IH] using List_induction.
  - (* Both sides compute to [Zero]. *)
    simpl in |- *.
    reflexivity.
  - (* Both sides open on [p a]: one goal per answer. *)
    simpl in |- *.
    destruct (p a) as [|].
    + (* [length (Cons a _)] computes:
         [|- NatWithZero.add (count p l') (Positive One)
             = NatWithZero.add (length (filter p l')) (Positive One)] *)
      simpl in |- *.
      rewrite IH in |- *.
      reflexivity.
    + (* [IH] is a proof of the goal as it stands. *)
      exact IH.
Qed.

(* [All] is monotone in its predicate: whatever holds of every element under
   [P] holds under any [Q] that [P] implies. *)
Lemma all_monotonicity
  : forall (A : Type) (P : A -> Prop) (Q : A -> Prop) (l : List A),
      (forall (a : A), P a -> Q a) -> All P l -> All Q l.
Proof.
  (* The context gains [A], [P], [Q], [l] and [h]. *)
  intros A P Q l h.
  induction l as [| b l' IH] using List_induction.
  - (* [All _ Nil] computes to [Verum] on both sides. *)
    simpl in |- *.
    intro v.
    exact v.
  - (* Both [All]s on a [Cons] compute: [|- P b /\ All P l' -> Q b /\ All Q l'] *)
    simpl in |- *.
    intro c.
    destruct c as [pb all'].
    exact (Conjunction_introduction (h b pb) (IH all')).
Qed.

(* Insertion sort, relative to a comparison [le] that answers [true] when
   its first argument may come first. [insert] walks past every element
   that may precede [a] and puts [a] in front of the first that may not. *)
Fixpoint insert {A : Type} (le : A -> A -> Bool) (a : A) (l : List A) : List A :=
  match l with
  | Nil       => Cons a Nil
  | Cons b l' =>
      match le a b with
      | true  => Cons a (Cons b l')
      | false => Cons b (insert le a l')
      end
  end.

Fixpoint insertion_sort {A : Type} (le : A -> A -> Bool) (l : List A) : List A :=
  match l with
  | Nil       => Nil
  | Cons a l' => insert le a (insertion_sort le l')
  end.

(* Sortedness: every element may precede all that follow it. Stated with
   [All] rather than on neighbours, so that [insert] is checked one element
   at a time. *)
Fixpoint Sorted {A : Type} (le : A -> A -> Bool) (l : List A) : Prop :=
  match l with
  | Nil       => Verum
  | Cons a l' => All (fun (b : A) => le a b = true) l' /\ Sorted le l'
  end.

(* Inserting an element every member of which satisfies [P] keeps [All P]. *)
Lemma insert_all_preservation
  : forall (A : Type) (le : A -> A -> Bool) (P : A -> Prop) (a : A) (l : List A),
      P a -> All P l -> All P (insert le a l).
Proof.
  (* The context gains [A], [le], [P], [a], [l] and [pa]. *)
  intros A le P a l pa.
  induction l as [| b l' IH] using List_induction.
  - (* [insert] into [Nil] is the one element: [|- Verum -> P a /\ Verum] *)
    simpl in |- *.
    intro v.
    exact (Conjunction_introduction pa v).
  - (* [|- P b /\ All P l' -> All P (match le a b with ... end)] *)
    simpl in |- *.
    intro c.
    destruct c as [pb all'].
    (* One goal per answer of [le a b]. *)
    destruct (le a b) as [|].
    + (* [a] goes in front: [|- P a /\ P b /\ All P l'] after computing *)
      simpl in |- *.
      exact (Conjunction_introduction pa (Conjunction_introduction pb all')).
    + (* [a] goes into the tail: [|- P b /\ All P (insert le a l')] *)
      simpl in |- *.
      exact (Conjunction_introduction pb (IH all')).
Qed.

(* Inserting into a sorted list keeps it sorted, given that the comparison
   is total (either of two may come first) and transitive. Where [a] stops,
   it precedes the head by the answer and the rest by transitivity; where it
   walks on, the head precedes it by totality. *)
Lemma insert_sortedness
  : forall (A : Type) (le : A -> A -> Bool),
      (forall (a : A) (b : A), le a b = true \/ le b a = true) ->
      (forall (a : A) (b : A) (c : A),
         le a b = true -> le b c = true -> le a c = true) ->
      forall (a : A) (l : List A), Sorted le l -> Sorted le (insert le a l).
Proof.
  (* The context gains [A], [le], [total], [transitive], [a] and [l]. *)
  intros A le total transitive a l.
  induction l as [| b l' IH] using List_induction.
  - (* One element is sorted: [|- Verum -> Verum /\ Verum] after computing *)
    simpl in |- *.
    intro v.
    exact (Conjunction_introduction v v).
  - (* [|- All (fun x => le b x = true) l' /\ Sorted le l'
         -> Sorted le (match le a b with ... end)] *)
    simpl in |- *.
    intro s.
    destruct s as [below sorted'].
    (* One goal per answer of [le a b], the answer kept as [c]. *)
    destruct (le a b) as [|] eqn:c.
    + (* [a] goes in front of [b]: it precedes [b] by [c] and everything
         after [b] by transitivity through [b]. *)
      simpl in |- *.
      pose proof (all_monotonicity A
                    (fun (x : A) => le b x = true) (fun (x : A) => le a x = true) l'
                    (fun (x : A) (h : le b x = true) => transitive a b x c h) below)
        as below_a.
      exact (Conjunction_introduction
               (Conjunction_introduction c below_a)
               (Conjunction_introduction below sorted')).
    + (* [a] goes into the tail: [b] precedes [a] by totality, since [c]
         refutes the other side, and precedes the rest as before; the tail
         is sorted by [IH]. *)
      simpl in |- *.
      pose proof (total a b) as t.
      destruct t as [ab | ba].
      * (* [ab] and [c] equate [false] with [true]. *)
        rewrite c in ab.
        discriminate.
      * exact (Conjunction_introduction
                 (insert_all_preservation A le (fun (x : A) => le b x = true) a l' ba below)
                 (IH sorted')).
Qed.

Theorem insertion_sort_sortedness
  : forall (A : Type) (le : A -> A -> Bool),
      (forall (a : A) (b : A), le a b = true \/ le b a = true) ->
      (forall (a : A) (b : A) (c : A),
         le a b = true -> le b c = true -> le a c = true) ->
      forall (l : List A), Sorted le (insertion_sort le l).
Proof.
  (* The context gains [A], [le], [total], [transitive] and [l]. *)
  intros A le total transitive l.
  induction l as [| a l' IH] using List_induction.
  - (* [insertion_sort Nil] computes to [Nil], which is sorted: [|- Verum] *)
    simpl in |- *.
    exact I.
  - (* One step: [|- Sorted le (insert le a (insertion_sort le l'))] *)
    simpl in |- *.
    exact (insert_sortedness A le total transitive a (insertion_sort le l') IH).
Qed.

(* [insert] adds exactly its element to the members. *)

Lemma insert_containment_forward
  : forall (A : Type) (le : A -> A -> Bool) (a : A) (b : A) (l : List A),
      Contains b (insert le a l) -> b = a \/ Contains b l.
Proof.
  (* The context gains [A], [le], [a], [b] and [l]. *)
  intros A le a b l.
  induction l as [| c l' IH] using List_induction.
  - (* [insert] into [Nil] is the one element: both sides compute to
       [b = a \/ Falsum]. *)
    simpl in |- *.
    intro h.
    exact h.
  - (* One goal per answer of [le a c]. *)
    simpl in |- *.
    destruct (le a c) as [|].
    + (* [a] in front: both sides compute to [b = a \/ b = c \/ Contains b l']. *)
      simpl in |- *.
      intro h.
      exact h.
    + (* [a] in the tail:
         [|- b = c \/ Contains b (insert le a l') -> b = a \/ b = c \/ Contains b l'] *)
      simpl in |- *.
      intro h.
      destruct h as [e | h'].
      * exact (Disjunction.right (Disjunction.left e)).
      * (* [IH] sorts the tail's membership into the two sides. *)
        pose proof (IH h') as h''.
        destruct h'' as [e | h'''].
        { exact (Disjunction.left e). }
        { exact (Disjunction.right (Disjunction.right h''')). }
Qed.

Lemma insert_containment_backward
  : forall (A : Type) (le : A -> A -> Bool) (a : A) (b : A) (l : List A),
      b = a \/ Contains b l -> Contains b (insert le a l).
Proof.
  (* The context gains [A], [le], [a], [b] and [l]. *)
  intros A le a b l.
  induction l as [| c l' IH] using List_induction.
  - (* Both sides compute to [b = a \/ Falsum]. *)
    simpl in |- *.
    intro h.
    exact h.
  - (* One goal per answer of [le a c]. *)
    simpl in |- *.
    destruct (le a c) as [|].
    + (* Both sides compute to [b = a \/ b = c \/ Contains b l']. *)
      simpl in |- *.
      intro h.
      exact h.
    + (* [|- b = a \/ b = c \/ Contains b l' -> b = c \/ Contains b (insert le a l')] *)
      simpl in |- *.
      intro h.
      destruct h as [e | h'].
      * (* [b] is [a], which [IH] places in the tail. *)
        exact (Disjunction.right (IH (Disjunction.left e))).
      * destruct h' as [e | h''].
        { exact (Disjunction.left e). }
        { exact (Disjunction.right (IH (Disjunction.right h''))). }
Qed.

Theorem insert_containment
  : forall (A : Type) (le : A -> A -> Bool) (a : A) (b : A) (l : List A),
      Contains b (insert le a l) <-> b = a \/ Contains b l.
Proof.
  (* The context gains [A], [le], [a], [b] and [l]. *)
  intros A le a b l.
  (* [Biimplication] has one ctor with two fields, so the goal splits into two
     goals, the forward and the backward half. *)
  split.
  - exact (insert_containment_forward  A le a b l).
  - exact (insert_containment_backward A le a b l).
Qed.

(* Sorting keeps the members: each insertion adds exactly the element the
   step took off. *)

Lemma insertion_sort_containment_preservation_forward
  : forall (A : Type) (le : A -> A -> Bool) (a : A) (l : List A),
      Contains a (insertion_sort le l) -> Contains a l.
Proof.
  (* The context gains [A], [le], [a] and [l]. *)
  intros A le a l.
  induction l as [| b l' IH] using List_induction.
  - (* [insertion_sort Nil] computes to [Nil]. *)
    simpl in |- *.
    intro h.
    exact h.
  - (* [|- Contains a (insert le b (insertion_sort le l')) -> a = b \/ Contains a l'] *)
    simpl in |- *.
    intro h.
    pose proof (insert_containment_forward A le b a (insertion_sort le l') h) as h'.
    destruct h' as [e | h''].
    + exact (Disjunction.left e).
    + exact (Disjunction.right (IH h'')).
Qed.

Lemma insertion_sort_containment_preservation_backward
  : forall (A : Type) (le : A -> A -> Bool) (a : A) (l : List A),
      Contains a l -> Contains a (insertion_sort le l).
Proof.
  (* The context gains [A], [le], [a] and [l]. *)
  intros A le a l.
  induction l as [| b l' IH] using List_induction.
  - (* [insertion_sort Nil] computes to [Nil]. *)
    simpl in |- *.
    intro h.
    exact h.
  - (* [|- a = b \/ Contains a l' -> Contains a (insert le b (insertion_sort le l'))] *)
    simpl in |- *.
    intro h.
    apply (insert_containment_backward A le b a (insertion_sort le l')).
    destruct h as [e | h'].
    + exact (Disjunction.left e).
    + exact (Disjunction.right (IH h')).
Qed.

Theorem insertion_sort_containment_preservation
  : forall (A : Type) (le : A -> A -> Bool) (a : A) (l : List A),
      Contains a (insertion_sort le l) <-> Contains a l.
Proof.
  (* The context gains [A], [le], [a] and [l]. *)
  intros A le a l.
  (* [Biimplication] has one ctor with two fields, so the goal splits into two
     goals, the forward and the backward half. *)
  split.
  - exact (insertion_sort_containment_preservation_forward  A le a l).
  - exact (insertion_sort_containment_preservation_backward A le a l).
Qed.

Lemma insert_length
  : forall (A : Type) (le : A -> A -> Bool) (a : A) (l : List A),
      length (insert le a l) = NatWithZero.add (length l) (Positive One).
Proof.
  (* The context gains [A], [le], [a] and [l]. *)
  intros A le a l.
  induction l as [| b l' IH] using List_induction.
  - (* One element on each side: both compute to [Positive One]. *)
    simpl in |- *.
    reflexivity.
  - (* One goal per answer of [le a b]. *)
    simpl in |- *.
    destruct (le a b) as [|].
    + (* [a] in front: both sides count two steps over [length l']. *)
      simpl in |- *.
      reflexivity.
    + (* [a] in the tail: [IH] counts it there:
         [|- NatWithZero.add (length (insert le a l')) (Positive One)
             = NatWithZero.add (NatWithZero.add (length l') (Positive One)) (Positive One)] *)
      simpl in |- *.
      rewrite IH in |- *.
      reflexivity.
Qed.

Theorem insertion_sort_length_preservation
  : forall (A : Type) (le : A -> A -> Bool) (l : List A),
      length (insertion_sort le l) = length l.
Proof.
  (* The context gains [A], [le] and [l]. *)
  intros A le l.
  induction l as [| a l' IH] using List_induction.
  - simpl in |- *.
    reflexivity.
  - (* One step: the insertion counts one over the sorted tail, which [IH]
       counts as [l']. *)
    simpl in |- *.
    rewrite (insert_length A le a (insertion_sort le l')) in |- *.
    rewrite IH in |- *.
    reflexivity.
Qed.

(* [Cons] and [Nil] are distinct ctors, as a statement. *)
Theorem cons_nil_distinctness
  : forall (A : Type) (a : A) (l : List A), ~ (Cons a l = Nil).
Proof.
  (* The context gains [A], [a], [l] and, once unfolded, [e], which equates
   * two distinct ctors.
   *)
  intros A a l.
  unfold Negation in |- *.
  intro e.
  discriminate.
Qed.

(* [range n] is [Zero] up to but excluding [n], in that order: a positive
 * count recurses on its [Nat], each step putting the new last element
 * behind the ones before it.
 *)
(* [Nat -> List NatWithZero] *)
Fixpoint range_positive (p : Nat) : List NatWithZero :=
  match p with
  | One          => Cons Zero Nil
  | Successor p' => append (range_positive p') (Cons (Positive p') Nil)
  end.

(* [NatWithZero -> List NatWithZero] *)
Definition range := fun (n : NatWithZero) =>
  match n with
  | Zero       => Nil
  | Positive p => range_positive p
  end.

Lemma length_range_positive
  : forall (p : Nat), length (range_positive p) = Positive p.
Proof.
  (* [p] is either [One] or [Successor p']: one goal per ctor, and the
   * second has [IH : length (range_positive p') = Positive p'] in its
   * context.
   *)
  intros p.
  induction p as [| p' IH] using Nat_induction.
  - (* One element: [|- Positive One = Positive One] after computing *)
    simpl in |- *.
    reflexivity.
  - (* One step of [range_positive]; the length of the concatenation is the
     * sum of the lengths, [IH] replaces the first, the second computes to
     * [Positive One], and the sum computes up to the inner sum turned
     * round.
     *)
    simpl in |- *.
    rewrite (length_additivity_over_append
               (range_positive p') (Cons (Positive p') Nil)) in |- *.
    rewrite IH in |- *.
    simpl in |- *.
    rewrite (Nat.add_commutativity p' One) in |- *.
    simpl in |- *.
    reflexivity.
Qed.

Theorem length_range : forall (n : NatWithZero), length (range n) = n.
Proof.
  (* The context gains [n]; one goal per ctor. *)
  intros n.
  destruct n as [| p].
  - simpl in |- *.
    reflexivity.
  - (* [range (Positive p)] computes to [range_positive p]. *)
    simpl in |- *.
    exact (length_range_positive p).
Qed.

(* The members of [range n] are exactly the numbers below [n]. Each step
 * adds one element at the end, and strictly below one more than
 * [Positive p'] is at most [Positive p']: the old members by [IH], the new
 * one by equality.
 *)

Lemma range_positive_containment_forward
  : forall (p : Nat) (i : NatWithZero),
      Contains i (range_positive p) -> NatWithZero.LessThan i (Positive p).
Proof.
  (* The context gains [p]; one goal per ctor, the second with [IH] for
   * every [i].
   *)
  intros p.
  induction p as [| p' IH] using Nat_induction.
  - (* [Contains i (Cons Zero Nil)] computes to [i = Zero \/ Falsum]: [i] is
     * [Zero], which is below [Positive One] with [One] as the witness.
     *)
    intros i h.
    simpl in h.
    destruct h as [e | f].
    + rewrite e in |- *.
      unfold NatWithZero.LessThan in |- *.
      apply (Exists_introduction One).
      simpl in |- *.
      reflexivity.
    + contradiction.
  - (* Membership in the concatenation is membership in either part. The
     * bound [Positive (Successor p')] is [add (Positive One) (Positive p')]
     * by computation, turned round, so that the successor law reduces the
     * goal to [i] at most [Positive p'].
     *)
    intros i h.
    simpl in h.
    pose proof (Biimplication.elimination_forward
                  (Contains i (append (range_positive p') (Cons (Positive p') Nil)))
                  (Contains i (range_positive p') \/ Contains i (Cons (Positive p') Nil))
                  (contains_distributivity_over_append
                     NatWithZero i (range_positive p') (Cons (Positive p') Nil))
                  h) as h'.
    change (Positive (Successor p'))
      with (NatWithZero.add (Positive One) (Positive p')) in |- *.
    rewrite (NatWithZero.add_commutativity (Positive One) (Positive p')) in |- *.
    apply (Biimplication.elimination_backward
             (NatWithZero.LessThan i (NatWithZero.add (Positive p') (Positive One)))
             (NatWithZero.LessOrEqual i (Positive p'))
             (NatWithZero.less_than_successor_specification i (Positive p'))).
    unfold NatWithZero.LessOrEqual in |- *.
    destruct h' as [h1 | h2].
    + (* In the first part: below [Positive p'] by [IH]. *)
      exact (Disjunction.right (IH i h1)).
    + (* In the second part, which computes to [i = Positive p' \/ Falsum]. *)
      simpl in h2.
      destruct h2 as [e | f].
      * exact (Disjunction.left e).
      * contradiction.
Qed.

Lemma range_positive_containment_backward
  : forall (p : Nat) (i : NatWithZero),
      NatWithZero.LessThan i (Positive p) -> Contains i (range_positive p).
Proof.
  (* The context gains [p]; one goal per ctor, the second with [IH] for
   * every [i].
   *)
  intros p.
  induction p as [| p' IH] using Nat_induction.
  - (* Below [Positive One] is [Zero] alone: a positive [i] would put a
     * [Successor] against [One] in the witness equation.
     *)
    intros i h.
    unfold NatWithZero.LessThan in h.
    destruct h as [k e].
    destruct i as [| q].
    + simpl in |- *.
      exact (Disjunction.left (Identity.reflexivity Zero)).
    + (* [e] computes to [Positive (Nat.add q k) = Positive One]; the sum is
       * a [Successor] whichever ctor [q] is.
       *)
      simpl in e.
      pose proof (NatWithZero.positive_injectivity (Nat.add q k) One e) as e'.
      destruct q as [| q'].
      * simpl in e'.
        discriminate.
      * simpl in e'.
        discriminate.
  - (* The bound is [add (Positive One) (Positive p')] by computation,
     * turned round, so that the successor law reads [h] as [i] at most
     * [Positive p']: equality puts [i] in the second part, a strict step
     * in the first by [IH].
     *)
    intros i h.
    change (Positive (Successor p'))
      with (NatWithZero.add (Positive One) (Positive p')) in h.
    rewrite (NatWithZero.add_commutativity (Positive One) (Positive p')) in h.
    pose proof (Biimplication.elimination_forward
                  (NatWithZero.LessThan i (NatWithZero.add (Positive p') (Positive One)))
                  (NatWithZero.LessOrEqual i (Positive p'))
                  (NatWithZero.less_than_successor_specification i (Positive p')) h)
      as h'.
    simpl in |- *.
    apply (Biimplication.elimination_backward
             (Contains i (append (range_positive p') (Cons (Positive p') Nil)))
             (Contains i (range_positive p') \/ Contains i (Cons (Positive p') Nil))
             (contains_distributivity_over_append
                NatWithZero i (range_positive p') (Cons (Positive p') Nil))).
    unfold NatWithZero.LessOrEqual in h'.
    destruct h' as [e | lt].
    + apply Disjunction.right.
      simpl in |- *.
      exact (Disjunction.left e).
    + exact (Disjunction.left (IH i lt)).
Qed.

Theorem range_containment_specification
  : forall (n : NatWithZero) (i : NatWithZero),
      Contains i (range n) <-> NatWithZero.LessThan i n.
Proof.
  (* The context gains [n] and [i]; one goal per ctor of [n]. *)
  intros n i.
  destruct n as [| p].
  - (* [range Zero] is [Nil], which contains nothing, and nothing is below
     * [Zero]: [|- Falsum <-> NatWithZero.LessThan i Zero] after computing
     *)
    simpl in |- *.
    split.
    + intro f.
      contradiction.
    + intro h.
      unfold NatWithZero.LessThan in h.
      destruct h as [k e].
      pose proof (NatWithZero.add_positive_refutes_zero i k) as r.
      unfold Negation in r.
      pose proof (r e) as f.
      contradiction.
  - (* [range (Positive p)] computes to [range_positive p]. *)
    simpl in |- *.
    split.
    + exact (range_positive_containment_forward  p i).
    + exact (range_positive_containment_backward p i).
Qed.

(* The largest member of a list, [Zero] for [Nil]: [fold_right] over the
 * [max] monoid.
 *)
(* [List NatWithZero -> NatWithZero] *)
Definition maximum_of := fun (l : List NatWithZero) => fold_right NatWithZero.max Zero l.

(* Every member is at most the maximum: the head by the left injection,
 * the rest through the right injection and transitivity.
 *)
Theorem maximum_of_upper_bound
  : forall (l : List NatWithZero),
      All (fun (a : NatWithZero) => NatWithZero.LessOrEqual a (maximum_of l)) l.
Proof.
  (* The context gains [l]; [maximum_of] opens into its fold. *)
  intros l.
  unfold maximum_of in |- *.
  induction l as [| a l' IH] using List_induction.
  - simpl in |- *.
    exact I.
  - (* One step of the fold and of [All]:
     * [|- NatWithZero.LessOrEqual a (NatWithZero.max a M)
     *     /\ All (fun x => NatWithZero.LessOrEqual x (NatWithZero.max a M)) l']
     * with [M] the fold of [l'].
     *)
    simpl in |- *.
    split.
    + exact (NatWithZero.max_left_injection a (fold_right NatWithZero.max Zero l')).
    + exact (all_monotonicity NatWithZero
               (fun (x : NatWithZero) =>
                  NatWithZero.LessOrEqual x (fold_right NatWithZero.max Zero l'))
               (fun (x : NatWithZero) =>
                  NatWithZero.LessOrEqual x
                    (NatWithZero.max a (fold_right NatWithZero.max Zero l')))
               l'
               (fun (x : NatWithZero)
                    (h : NatWithZero.LessOrEqual x (fold_right NatWithZero.max Zero l')) =>
                  NatWithZero.less_or_equal_transitivity
                    x (fold_right NatWithZero.max Zero l')
                    (NatWithZero.max a (fold_right NatWithZero.max Zero l'))
                    h
                    (NatWithZero.max_right_injection
                       a (fold_right NatWithZero.max Zero l')))
               IH).
Qed.

(* A non-empty list contains its maximum: the head when the maximum of the
 * tail is at most it, and otherwise that maximum, a member of the tail by
 * [IH].
 *)
Theorem maximum_of_containment
  : forall (l : List NatWithZero), ~ (l = Nil) -> Contains (maximum_of l) l.
Proof.
  (* The context gains [l]; [maximum_of] opens into its fold. *)
  intros l.
  unfold maximum_of in |- *.
  induction l as [| a l' IH] using List_induction.
  - (* [Nil] is [Nil]: the premise refutes itself. *)
    intro h.
    unfold Negation in h.
    pose proof (h (Identity.reflexivity Nil)) as f.
    contradiction.
  - (* One goal per ctor of the tail. *)
    intro h.
    destruct l' as [| b l''].
    + (* One element: the fold is [max a Zero], which is [a]. *)
      simpl in |- *.
      rewrite (NatWithZero.max_right_identity a) in |- *.
      exact (Disjunction.left (Identity.reflexivity a)).
    + (* One step of the fold and of [Contains], written out so that the
       * fold of the tail stays as [IH] and [c] state it:
       * [|- max a M = a \/ Contains (max a M) (Cons b l'')] with [M] the
       * fold of [Cons b l'']; one goal per side of totality between [M]
       * and [a].
       *)
      pose proof (IH (cons_nil_distinctness NatWithZero b l'')) as c.
      change (NatWithZero.max a (fold_right NatWithZero.max Zero (Cons b l'')) = a
              \/ Contains (NatWithZero.max a (fold_right NatWithZero.max Zero (Cons b l'')))
                          (Cons b l'')) in |- *.
      pose proof (NatWithZero.less_or_equal_totality
                    (fold_right NatWithZero.max Zero (Cons b l'')) a) as t.
      destruct t as [le | ge].
      * (* [M] is at most [a]: the maximum is [a], the head. *)
        apply Disjunction.left.
        exact (Biimplication.elimination_backward
                 (NatWithZero.max a (fold_right NatWithZero.max Zero (Cons b l'')) = a)
                 (NatWithZero.LessOrEqual (fold_right NatWithZero.max Zero (Cons b l'')) a)
                 (NatWithZero.max_specification
                    a (fold_right NatWithZero.max Zero (Cons b l''))) le).
      * (* [a] is at most [M]: the maximum is [M], turned round by
         * commutativity, which [c] places in the tail.
         *)
        apply Disjunction.right.
        rewrite (NatWithZero.max_commutativity
                   a (fold_right NatWithZero.max Zero (Cons b l''))) in |- *.
        rewrite (Biimplication.elimination_backward
                   (NatWithZero.max (fold_right NatWithZero.max Zero (Cons b l'')) a
                    = fold_right NatWithZero.max Zero (Cons b l''))
                   (NatWithZero.LessOrEqual a (fold_right NatWithZero.max Zero (Cons b l'')))
                   (NatWithZero.max_specification
                      (fold_right NatWithZero.max Zero (Cons b l'')) a) ge) in |- *.
        exact c.
Qed.

(* The smallest member, [None] for [Nil]: the head alone, or the [min] of
 * the head and the smallest of the tail. No identity is available for
 * [min], so the empty case is an [Option].
 *)
(* [List NatWithZero -> Option NatWithZero] *)
Fixpoint minimum_of (l : List NatWithZero) : Option NatWithZero :=
  match l with
  | Nil       => None
  | Cons a l' =>
      match minimum_of l' with
      | None   => Some a
      | Some m => Some (NatWithZero.min a m)
      end
  end.

Lemma minimum_of_none_specification
  : forall (l : List NatWithZero), minimum_of l = None <-> l = Nil.
Proof.
  (* The context gains [l]. *)
  intros l.
  split.
  - (* A [Cons] answers [Some] whichever way its tail answers. *)
    intro e.
    destruct l as [| a l'].
    + reflexivity.
    + simpl in e.
      destruct (minimum_of l') as [| m].
      * discriminate.
      * discriminate.
  - (* [e : l = Nil] replaces [l], and [minimum_of Nil] computes. *)
    intro e.
    rewrite e in |- *.
    simpl in |- *.
    reflexivity.
Qed.

(* The minimum is at most every member: [IH] bounds the tail by its own
 * minimum, and [min] is at most both its arguments.
 *)
Theorem minimum_of_lower_bound
  : forall (l : List NatWithZero) (m : NatWithZero),
      minimum_of l = Some m
      -> All (fun (a : NatWithZero) => NatWithZero.LessOrEqual m a) l.
Proof.
  (* The context gains [l]; one goal per ctor, the second with [IH] for
   * every [m].
   *)
  intros l.
  induction l as [| a l' IH] using List_induction.
  - (* [minimum_of Nil] computes to [None]: [e] equates two distinct ctors. *)
    intros m e.
    simpl in e.
    discriminate.
  - (* [e] opens on the answer for [l']; one goal per ctor of it. *)
    intros m e.
    simpl in e.
    destruct (minimum_of l') as [| m'] eqn:r.
    + (* [l'] is [Nil] by the specification, and [e] computes to
       * [Some a = Some m]: [m] is [a], at most itself and nothing else.
       *)
      simpl in e.
      pose proof (Biimplication.elimination_forward
                    (minimum_of l' = None) (l' = Nil)
                    (minimum_of_none_specification l') r) as en.
      pose proof (Option.some_injectivity NatWithZero a m e) as e'.
      rewrite en in |- *.
      rewrite e' in |- *.
      simpl in |- *.
      exact (Conjunction_introduction (NatWithZero.less_or_equal_reflexivity m) I).
    + (* [e] computes to [Some (min a m') = Some m]; [m] turned round
       * replaces it: [min a m'] is at most [a] by the left projection, and
       * at most the members of [l'] through the right projection and
       * [IH] at [m'], whose premise the case analysis has turned into
       * [Some m' = Some m'].
       *)
      simpl in e.
      pose proof (Option.some_injectivity NatWithZero (NatWithZero.min a m') m e) as e'.
      pose proof (Identity.symmetry e') as e''.
      rewrite e'' in |- *.
      simpl in |- *.
      split.
      * exact (NatWithZero.min_left_projection a m').
      * exact (all_monotonicity NatWithZero
                 (fun (x : NatWithZero) => NatWithZero.LessOrEqual m' x)
                 (fun (x : NatWithZero) => NatWithZero.LessOrEqual (NatWithZero.min a m') x)
                 l'
                 (fun (x : NatWithZero) (h : NatWithZero.LessOrEqual m' x) =>
                    NatWithZero.less_or_equal_transitivity
                      (NatWithZero.min a m') m' x
                      (NatWithZero.min_right_projection a m') h)
                 (IH m' (Identity.reflexivity (Some m')))).
Qed.

(* A list contains its minimum: the head when the tail is empty or its
 * minimum is not below the head, and otherwise that minimum, a member of
 * the tail by [IH].
 *)
Theorem minimum_of_containment
  : forall (l : List NatWithZero) (m : NatWithZero),
      minimum_of l = Some m -> Contains m l.
Proof.
  (* The context gains [l]; one goal per ctor, the second with [IH] for
   * every [m].
   *)
  intros l.
  induction l as [| a l' IH] using List_induction.
  - intros m e.
    simpl in e.
    discriminate.
  - (* [e] opens on the answer for [l']; one goal per ctor of it. *)
    intros m e.
    simpl in e.
    destruct (minimum_of l') as [| m'] eqn:r.
    + (* [e] computes to [Some a = Some m]: [m] is the head. *)
      simpl in e.
      pose proof (Option.some_injectivity NatWithZero a m e) as e'.
      simpl in |- *.
      exact (Disjunction.left (Identity.symmetry e')).
    + (* [e] computes to [Some (min a m') = Some m]; whichever of [a] and
       * [m'] is below, [min] is it: the head, or a member of [l'] by [IH]
       * at [m'], whose premise the case analysis has turned into
       * [Some m' = Some m'].
       *)
      simpl in e.
      pose proof (Option.some_injectivity NatWithZero (NatWithZero.min a m') m e) as e'.
      pose proof (Identity.symmetry e') as e''.
      rewrite e'' in |- *.
      simpl in |- *.
      pose proof (NatWithZero.less_or_equal_totality a m') as t.
      destruct t as [le | ge].
      * apply Disjunction.left.
        exact (Biimplication.elimination_backward
                 (NatWithZero.min a m' = a) (NatWithZero.LessOrEqual a m')
                 (NatWithZero.min_specification a m') le).
      * apply Disjunction.right.
        rewrite (NatWithZero.min_commutativity a m') in |- *.
        rewrite (Biimplication.elimination_backward
                   (NatWithZero.min m' a = m') (NatWithZero.LessOrEqual m' a)
                   (NatWithZero.min_specification m' a) ge) in |- *.
        exact (IH m' (Identity.reflexivity (Some m'))).
Qed.

(* The closed form of the sum of [Zero] up to [p]: twice it is [p] times
 * one more. Each step adds the new last element at the end of the range,
 * distributivity splits the doubled sum, and the two products join into
 * the next one. The sum of the one added element is written out by
 * [change], since [simpl] would also open [range_positive] one level too
 * far for [IH].
 *)
Theorem sum_range_closed_form
  : forall (p : Nat),
      NatWithZero.mul (Positive (Successor One)) (sum (range (Positive (Successor p))))
      = NatWithZero.mul (Positive p) (Positive (Successor p)).
Proof.
  (* [p] is either [One] or [Successor p']: one goal per ctor, and the
   * second has [IH] for [p'] in its context.
   *)
  intros p.
  induction p as [| p' IH] using Nat_induction.
  - (* [range (Positive (Successor One))] is [Zero] then [Positive One],
     * whose sum is [Positive One]; both sides compute to
     * [Positive (Successor One)].
     *)
    unfold sum in |- *.
    simpl in |- *.
    reflexivity.
  - (* The range gains [Positive (Successor p')] at the end; the sum is
     * additive over the concatenation, and the sum of the one element is
     * itself.
     *)
    change (range (Positive (Successor (Successor p'))))
      with (append (range (Positive (Successor p'))) (Cons (Positive (Successor p')) Nil))
      in |- *.
    rewrite (sum_additivity_over_append
               (range (Positive (Successor p'))) (Cons (Positive (Successor p')) Nil))
      in |- *.
    change (sum (Cons (Positive (Successor p')) Nil)) with (Positive (Successor p')) in |- *.
    (* Distributivity splits the doubled sum, and [IH] replaces its first
     * half; distributivity read right to left joins the two products.
     *)
    rewrite (NatWithZero.mul_left_distributivity_over_add
               (Positive (Successor One))
               (sum (range (Positive (Successor p')))) (Positive (Successor p'))) in |- *.
    rewrite IH in |- *.
    pose proof (Identity.symmetry
                  (NatWithZero.mul_right_distributivity_over_add
                     (Positive (Successor p')) (Positive p') (Positive (Successor One))))
      as d.
    rewrite d in |- *.
    (* The joined factor computes to [Positive (Nat.add p' (Successor One))],
     * which turned round computes to [Positive (Successor (Successor p'))];
     * commutativity on the right makes both sides the same term.
     *)
    change (NatWithZero.add (Positive p') (Positive (Successor One)))
      with (Positive (Nat.add p' (Successor One))) in |- *.
    rewrite (Nat.add_commutativity p' (Successor One)) in |- *.
    change (Nat.add (Successor One) p') with (Successor (Successor p')) in |- *.
    rewrite (NatWithZero.mul_commutativity
               (Positive (Successor p')) (Positive (Successor (Successor p')))) in |- *.
    reflexivity.
Qed.

(* [count] answers [Zero] exactly when [p] answers [false] on every
 * member.
 *)
Theorem count_all_specification
  : forall (A : Type) (p : A -> Bool) (l : List A),
      count p l = Zero <-> All (fun (a : A) => p a = false) l.
Proof.
  (* The context gains [A], [p] and [l]. *)
  intros A p l.
  induction l as [| a l' IH] using List_induction.
  - (* Both sides compute: [|- Zero = Zero <-> Verum] *)
    simpl in |- *.
    split.
    + intro e.
      exact I.
    + intro v.
      reflexivity.
  - (* Both sides open on [p a]: one goal per answer. *)
    simpl in |- *.
    destruct (p a) as [|].
    + (* A [true] answer counts one, which no [Zero] is, and refutes
       * [true = false]: both halves close by contradiction.
       *)
      simpl in |- *.
      split.
      * intro e.
        pose proof (NatWithZero.add_positive_refutes_zero (count p l') One) as r.
        unfold Negation in r.
        pose proof (r e) as f.
        contradiction.
      * intro c.
        destruct c as [e f].
        discriminate.
    + (* A [false] answer counts nothing and holds: [IH] on the rest. *)
      simpl in |- *.
      split.
      * intro e.
        exact (Conjunction_introduction
                 (Identity.reflexivity false)
                 (Biimplication.elimination_forward
                    (count p l' = Zero) (All (fun (a : A) => p a = false) l') IH e)).
      * intro c.
        destruct c as [e all'].
        exact (Biimplication.elimination_backward
                 (count p l' = Zero) (All (fun (a : A) => p a = false) l') IH all').
Qed.

End List.

(* The level is reserved in [Core.Notations]; only the meaning belongs here.
   Declared at file level, it reaches a client through [Require Export].
   Every list notation lives in [jwa_list_scope], which [Core.Notations]
   declares without opening: a client writes [(l1 ++ l2)%list] or opens the
   scope. *)
Notation "l1 ++ l2" := (List.append l1 l2)
  : jwa_list_scope.

(* The token is [[]] as one piece; [[ ]] with a space is not it. *)
Notation "[]" := Nil
  : jwa_list_scope.

(* [a :: l] puts one element in front; with [[]] it spells a list out:
   [a :: b :: []]. *)
Notation "a :: l" := (Cons a l)
  : jwa_list_scope.

(* Membership reads as a sentence, [l contains_member a], with the list
   first; the arguments of [Contains] are the other way round, element
   first, so that [Contains a] is a predicate on lists. *)
Notation "l 'contains_member' a" := (List.Contains a l)
  : jwa_list_scope.

(* The same relation read from the element's side. [only parsing] keeps one
   spelling for printing, so a goal always shows [l contains_member a]. *)
Notation "a 'belongs_to' l" := (List.Contains a l) (only parsing)
  : jwa_list_scope.

(* The negations, so that [~ Contains a l] reads and prints as a sentence
   too; the element-first form is again [only parsing]. *)
Notation "l 'does_not_contain_member' a" := (~ (List.Contains a l))
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
     ; Monoid.left_identity  := @List.append_left_identity A
     ; Monoid.right_identity := @List.append_right_identity A |}.

(* The two functor laws were already proved above, so the instance only
   hands them over. [map]'s type arguments are maximally inserted, so the
   bare name collapses to one fixed pair of them; binding [A] and [B] first
   is what keeps it general enough for the field, as in [Data.Option]. *)
Instance List_functor
  : Functor.T List :=
  {| Functor.map             := fun (A : Type) (B : Type) => List.map
   ; Functor.map_identity    := List.map_identity
   ; Functor.map_composition := List.map_composition |}.

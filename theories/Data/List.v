(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Core.All] carries [->] and [=]; [Structures.Semigroup],
   [Structures.Monoid] and [Structures.Functor] are the classes the
   instances at the bottom fill; [Data.NatWithZero] is what [length] counts
   in, [Data.Nat] carries the [One] inside [Positive One], [Data.Bool] is
   what a [filter] predicate answers in, [Data.Option] is what [head] and
   [tail] answer in, and [Data.Pair] is what [pop], [zip] and [partition]
   answer in. *)
From jwa Require Import Core.All.
From jwa Require Import Structures.Semigroup.
From jwa Require Import Structures.Monoid.
From jwa Require Import Structures.Functor.
From jwa Require Import Data.Bool.
From jwa Require Import Data.Option.
From jwa Require Import Data.Pair.
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
           exact (Disjunction_left e).
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
           exact (Disjunction_right hl).
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
        exact (Disjunction_right hl).
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
      exact (Disjunction_left e).
    + (* [p b] is either [true] or [false]: one goal per ctor. *)
      destruct (p b) as [|].
      * (* The [match] takes its [true] branch and [Contains] computes:
           [|- a = b \/ Contains a (filter p l')] *)
        simpl in |- *.
        (* [Disjunction_right] turns the goal into its right side:
           [|- Contains a (filter p l')] *)
        apply Disjunction_right.
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
  (* [Bijunction] has one ctor with two fields, so the goal splits into two
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
  (* [Bijunction] has one ctor with two fields, so the goal splits into two
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
    exact (Disjunction_right h).
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
      exact (Disjunction_left (Disjunction_left pb)).
    + (* [IH] turns [h'] into [Any P l1' \/ Any P l2], which gives two
         goals: one with [h1 : Any P l1'], one with [h2 : Any P l2]. *)
      destruct (IH h') as [h1 | h2].
      * (* [h1] is the right side of the left side. *)
        exact (Disjunction_left (Disjunction_right h1)).
      * (* [h2] is the right side. *)
        exact (Disjunction_right h2).
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
        exact (Disjunction_left pb).
      * (* [Disjunction_right] turns the goal into its right side:
           [|- Any P (append l1' l2)] *)
        apply Disjunction_right.
        (* [IH] turns a proof of [Any P l1' \/ Any P l2] into one of the
           goal: [|- Any P l1' \/ Any P l2] *)
        apply IH.
        (* [h1'] is the left side. *)
        exact (Disjunction_left h1').
    + (* [Disjunction_right] turns the goal into its right side:
         [|- Any P (append l1' l2)] *)
      apply Disjunction_right.
      (* [IH] turns a proof of [Any P l1' \/ Any P l2] into one of the goal:
         [|- Any P l1' \/ Any P l2] *)
      apply IH.
      (* [h2] is the right side. *)
      exact (Disjunction_right h2).
Qed.

Theorem any_distributivity_over_append
  : forall (A : Type) (P : A -> Prop) (l1 : List A) (l2 : List A),
      Any P (append l1 l2) <-> Any P l1 \/ Any P l2.
Proof.
  (* The context gains [A], [P], [l1] and [l2]:
     [|- Any P (append l1 l2) <-> Any P l1 \/ Any P l2] *)
  intros A P l1 l2.
  (* [Bijunction] has one ctor with two fields, so the goal splits into two
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
      exact (Disjunction_left (Equijunction_reflexivity b)).
    + (* [IH] turns a proof of the membership hypothesis for [l'] into one
         of the goal: [|- forall (a : A), Contains a l' -> P a] *)
      apply IH.
      (* The context gains [a] and [ha : Contains a l']: [|- P a] *)
      intros a ha.
      (* [h a] turns a proof of [a = b \/ Contains a l'] into one of [P a]:
         [|- a = b \/ Contains a l'] *)
      apply (h a).
      (* [ha] is the right side. *)
      exact (Disjunction_right ha).
Qed.

Theorem all_specification
  : forall (A : Type) (P : A -> Prop) (l : List A),
      All P l <-> (forall (a : A), Contains a l -> P a).
Proof.
  (* The context gains [A], [P] and [l]:
     [|- All P l <-> (forall (a : A), Contains a l -> P a)] *)
  intros A P l.
  (* [Bijunction] has one ctor with two fields, so the goal splits into two
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
        exact (Disjunction_left (Equijunction_reflexivity b)).
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
        exact (Disjunction_right ha').
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
      exact (Disjunction_left pa).
    + (* [Disjunction_right] turns the goal into its right side:
         [|- Any P l'] *)
      apply Disjunction_right.
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
  (* [Bijunction] has one ctor with two fields, so the goal splits into two
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
  (* [Bijunction] has one ctor with two fields, so the goal splits into two
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
  (* [Bijunction] has one ctor with two fields, so the goal splits into two
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
  pose proof (Equijunction_congruence reverse e) as e'.
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
  (* [Bijunction] has one ctor with two fields, so the goal splits into two
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
    pose proof (Equijunction_congruence reverse er) as er'.
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
  (* [Bijunction] has one ctor with two fields, so the goal splits into two
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
  (* [Bijunction] has one ctor with two fields, so the goal splits into two
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
   hypothesis through [NatWithZero.add_cancellation_right]. *)
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
      pose proof (Equijunction_symmetry e) as e'.
      (* [h : ~ (NatWithZero.add (length l2') (Positive One) = Zero)] *)
      pose proof (NatWithZero.add_positive_refutes_zero (length l2') One) as h.
      (* [h : NatWithZero.add (length l2') (Positive One) = Zero -> Falsum] *)
      unfold Unjunction in h.
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
      unfold Unjunction in h.
      (* [f : Falsum] *)
      pose proof (h e) as f.
      (* [f : Falsum], which is what [contradiction] looks for. *)
      contradiction.
    + (* Both [length]s step:
         [e : NatWithZero.add (length l1') (Positive One)
              = NatWithZero.add (length l2') (Positive One)] *)
      simpl in e.
      (* The [Positive One] cancels: [e' : length l1' = length l2'] *)
      pose proof (NatWithZero.add_cancellation_right
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

End List.

(* The level is reserved in [Core.Notations]; only the meaning belongs here.
   Declared at file level, it reaches a client through [Require Export].
   Every list notation lives in [jwa_list_scope], which [Core.Notations]
   declares without opening: a client writes [(l1 ++ l2)%list] or opens the
   scope. *)
Notation "l1 ++ l2" := (List.append l1 l2) : jwa_list_scope.

(* The token is [[]] as one piece; [[ ]] with a space is not it. *)
Notation "[]" := Nil : jwa_list_scope.

(* [a :: l] puts one element in front; with [[]] it spells a list out:
   [a :: b :: []]. *)
Notation "a :: l" := (Cons a l) : jwa_list_scope.

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

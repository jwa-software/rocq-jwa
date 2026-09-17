(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Core.All] carries [->] and [=]: with [-noinit] a file has only what it
   requires. *)
From jwa Require Import Core.All.

(* A pair holds one [A] and one [B], in that order. Both are parameters: the
   type of each component is fixed for the whole pair. The ctor is named as
   the [-junction] ctors are, since a pair is to types what [/\] is to
   propositions. *)
Inductive Pair (A : Type) (B : Type) : Type :=
  | Pair_introduction : A -> B -> Pair A B.

(* Both types are inferred from the components. *)
Arguments Pair_introduction {A} {B} a b.

(* The eliminator behind [induction], written out. Nothing recurses: a pair
   holds no smaller pair, so one [match] is the whole content. *)
Definition Pair_induction
  : forall (A : Type) (B : Type) (P : Pair A B -> Prop),
      (forall (a : A) (b : B), P (Pair_introduction a b)) ->
      forall (p : Pair A B), P p
  := fun (A : Type) (B : Type) (P : Pair A B -> Prop)
         (step : forall (a : A) (b : B), P (Pair_introduction a b))
         (p : Pair A B) =>
       match p with
       | Pair_introduction a b => step a b
       end.

(* A module may carry the type's name; its members read [Pair.first]. *)
Module Pair.

(* [forall {A : Type} {B : Type}, Pair A B -> A] *)
Definition first := fun {A : Type} {B : Type} (p : Pair A B) =>
  match p return A with
  | Pair_introduction a _ => a
  end.

(* [forall {A : Type} {B : Type}, Pair A B -> B] *)
Definition second := fun {A : Type} {B : Type} (p : Pair A B) =>
  match p return B with
  | Pair_introduction _ b => b
  end.

Theorem introduction_injectivity
  : forall (A : Type) (B : Type) (a1 : A) (b1 : B) (a2 : A) (b2 : B),
      Pair_introduction a1 b1 = Pair_introduction a2 b2 -> a1 = a2 /\ b1 = b2.
Proof.
  (* The context gains [A], [B], [a1], [b1], [a2], [b2] and
     [e : Pair_introduction a1 b1 = Pair_introduction a2 b2]:
     [|- a1 = a2 /\ b1 = b2] *)
  intros A B a1 b1 a2 b2 e.
  (* The context gains
     [ea : first (Pair_introduction a1 b1) = first (Pair_introduction a2 b2)]. *)
  pose proof (Equijunction_congruence first e) as ea.
  (* Both [first]s compute: [ea : a1 = a2] *)
  simpl in ea.
  (* The context gains
     [eb : second (Pair_introduction a1 b1) = second (Pair_introduction a2 b2)]. *)
  pose proof (Equijunction_congruence second e) as eb.
  (* Both [second]s compute: [eb : b1 = b2] *)
  simpl in eb.
  (* [/\] is built from a proof of each side. *)
  exact (Conjunction_introduction ea eb).
Qed.

(* [Pair_introduction] is surjective: every pair is the pairing of its own
   projections. This is the eta rule for pairs, which an [Inductive] does not
   compute, so it is proved. *)
Theorem introduction_surjectivity
  : forall (A : Type) (B : Type) (p : Pair A B),
      p = Pair_introduction (first p) (second p).
Proof.
  (* The context gains [A], [B] and [p]:
     [|- p = Pair_introduction (first p) (second p)] *)
  intros A B p.
  (* [p] is [Pair_introduction a b], with [a] and [b] in the context:
     [|- Pair_introduction a b
         = Pair_introduction (first (Pair_introduction a b))
                             (second (Pair_introduction a b))] *)
  destruct p as [a b].
  (* Both projections compute:
     [|- Pair_introduction a b = Pair_introduction a b] *)
  simpl in |- *.
  (* Both sides are the same term. *)
  reflexivity.
Qed.

(* [forall {A : Type} {B : Type}, Pair A B -> Pair B A] *)
Definition swap := fun {A : Type} {B : Type} (p : Pair A B) =>
  match p return Pair B A with
  | Pair_introduction a b => Pair_introduction b a
  end.

Theorem swap_involution
  : forall (A : Type) (B : Type) (p : Pair A B), swap (swap p) = p.
Proof.
  (* The context gains [A], [B] and [p]: [|- swap (swap p) = p] *)
  intros A B p.
  (* [p] is [Pair_introduction a b], with [a] and [b] in the context:
     [|- swap (swap (Pair_introduction a b)) = Pair_introduction a b] *)
  destruct p as [a b].
  (* Both [swap]s compute:
     [|- Pair_introduction a b = Pair_introduction a b] *)
  simpl in |- *.
  (* Both sides are the same term. *)
  reflexivity.
Qed.

(* [forall {A : Type} {B : Type} {C : Type}, (A -> C) -> Pair A B -> Pair C B] *)
Definition map_first := fun {A : Type} {B : Type} {C : Type}
                            (f : A -> C) (p : Pair A B) =>
  match p return Pair C B with
  | Pair_introduction a b => Pair_introduction (f a) b
  end.

(* [forall {A : Type} {B : Type} {C : Type}, (B -> C) -> Pair A B -> Pair A C] *)
Definition map_second := fun {A : Type} {B : Type} {C : Type}
                             (f : B -> C) (p : Pair A B) =>
  match p return Pair A C with
  | Pair_introduction a b => Pair_introduction a (f b)
  end.

(* [forall {A : Type} {B : Type} {C : Type} {D : Type},
     (A -> C) -> (B -> D) -> Pair A B -> Pair C D] *)
Definition bimap := fun {A : Type} {B : Type} {C : Type} {D : Type}
                           (f : A -> C) (g : B -> D)
                           (p : Pair A B) =>
  match p return Pair C D with
  | Pair_introduction a b => Pair_introduction (f a) (g b)
  end.
End Pair.

(* The level is reserved in [Core.Notations]; only the meaning belongs here.
   Declared at file level, it reaches a client through [Require Export]. A
   type former sits in [jwa_type_scope] beside [->], so [A * B -> C] needs
   no delimiter. *)
Notation "A * B" := (Pair A B) : jwa_type_scope.

(* The value-level notations live in [jwa_pair_scope], which [Core.Notations]
   declares without opening: a client writes [(a , b)%pair] or opens the
   scope. *)
Notation "( a , b )" := (Pair_introduction a b) : jwa_pair_scope.

(* The projections under their textbook names. Each is a keyword standing
   for the function itself, so [pi_1 p] is ordinary application and
   [pi_1 (a , b)] computes as [Pair.first (a , b)] does. *)
Notation "'pi_1'" := Pair.first : jwa_pair_scope.
Notation "'pi_2'" := Pair.second : jwa_pair_scope.

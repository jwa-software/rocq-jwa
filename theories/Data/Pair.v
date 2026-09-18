(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Core.All] carries [->] and [=]: with [-noinit] a file has only what it
   requires. [Algebra.Semigroup], [Algebra.Monoid] and
   [Data.Functor] are the classes the instances at the bottom fill. *)
From jwa Require Import Algebra.Commutative.
From jwa Require Import Algebra.Monoid.
From jwa Require Import Algebra.Semigroup.
From jwa Require Import Core.All.
From jwa Require Import Data.Functor.

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
     [ea : first (Pair_introduction a1 b1)
         = first (Pair_introduction a2 b2)]. *)
  pose proof (Identity.congruence first e) as ea.
  (* Both [first]s compute: [ea : a1 = a2] *)
  simpl in ea.
  (* The context gains
     [eb : second (Pair_introduction a1 b1)
         = second (Pair_introduction a2 b2)]. *)
  pose proof (Identity.congruence second e) as eb.
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
      = Pair_introduction (first (Pair_introduction a b)) (second (Pair_introduction a b))] *)
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

(* [forall {A : Type} {B : Type} {C : Type},
     (A -> C) -> Pair A B -> Pair C B] *)
Definition map_first := fun {A : Type} {B : Type} {C : Type}
                            (f : A -> C) (p : Pair A B) =>
  match p return Pair C B with
  | Pair_introduction a b => Pair_introduction (f a) b
  end.

(* [forall {A : Type} {B : Type} {C : Type},
     (B -> C) -> Pair A B -> Pair A C] *)
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

(* The functor laws for each component and for both at once: the map
   preserves the identity function and preserves composition. Stated for
   every [p] rather than as an equality between functions, since nothing
   here assumes functional extensionality. *)

Theorem map_first_identity
  : forall (A : Type) (B : Type) (p : Pair A B),
      map_first (fun (a : A) => a) p = p.
Proof.
  (* The context gains [A], [B] and [p]: [|- map_first (fun a => a) p = p] *)
  intros A B p.
  (* [p] is [Pair_introduction a b], with [a] and [b] in the context:
     [|- map_first (fun a => a) (Pair_introduction a b)
      = Pair_introduction a b] *)
  destruct p as [a b].
  (* [map_first] computes and [(fun a => a) a] reduces to [a]:
     [|- Pair_introduction a b = Pair_introduction a b] *)
  simpl in |- *.
  (* Both sides are the same term. *)
  reflexivity.
Qed.

Theorem map_first_composition
  : forall (A : Type) (B : Type) (C : Type) (D : Type) (f : A -> C) (g : C -> D)
      (p : Pair A B),
      map_first g (map_first f p) = map_first (fun (a : A) => g (f a)) p.
Proof.
  (* The context gains [A], [B], [C], [D], [f], [g] and [p]:
     [|- map_first g (map_first f p) = map_first (fun a => g (f a)) p] *)
  intros A B C D f g p.
  (* [p] is [Pair_introduction a b], with [a] and [b] in the context:
     [|- map_first g (map_first f (Pair_introduction a b))
      = map_first (fun a => g (f a)) (Pair_introduction a b)] *)
  destruct p as [a b].
  (* The left side computes in two [map_first] steps to
     [Pair_introduction (g (f a)) b], the right side in one step to the
     same: [|- Pair_introduction (g (f a)) b = Pair_introduction (g (f a)) b] *)
  simpl in |- *.
  (* Both sides are the same term. *)
  reflexivity.
Qed.

Theorem map_second_identity
  : forall (A : Type) (B : Type) (p : Pair A B),
      map_second (fun (b : B) => b) p = p.
Proof.
  (* The context gains [A], [B] and [p]: [|- map_second (fun b => b) p = p] *)
  intros A B p.
  (* [p] is [Pair_introduction a b], with [a] and [b] in the context:
     [|- map_second (fun b => b) (Pair_introduction a b)
      = Pair_introduction a b] *)
  destruct p as [a b].
  (* [map_second] computes and [(fun b => b) b] reduces to [b]:
     [|- Pair_introduction a b = Pair_introduction a b] *)
  simpl in |- *.
  (* Both sides are the same term. *)
  reflexivity.
Qed.

Theorem map_second_composition
  : forall (A : Type) (B : Type) (C : Type) (D : Type) (f : B -> C) (g : C -> D)
      (p : Pair A B),
      map_second g (map_second f p) = map_second (fun (b : B) => g (f b)) p.
Proof.
  (* The context gains [A], [B], [C], [D], [f], [g] and [p]:
     [|- map_second g (map_second f p) = map_second (fun b => g (f b)) p] *)
  intros A B C D f g p.
  (* [p] is [Pair_introduction a b], with [a] and [b] in the context:
     [|- map_second g (map_second f (Pair_introduction a b))
      = map_second (fun b => g (f b)) (Pair_introduction a b)] *)
  destruct p as [a b].
  (* The left side computes in two [map_second] steps to
     [Pair_introduction a (g (f b))], the right side in one step to the
     same: [|- Pair_introduction a (g (f b)) = Pair_introduction a (g (f b))] *)
  simpl in |- *.
  (* Both sides are the same term. *)
  reflexivity.
Qed.

(* The two maps touch different components, so their order does not
   matter. *)
Theorem map_first_map_second_commutativity
  : forall (A : Type) (B : Type) (C : Type) (D : Type) (f : A -> C) (g : B -> D)
      (p : Pair A B),
      map_first f (map_second g p) = map_second g (map_first f p).
Proof.
  (* The context gains [A], [B], [C], [D], [f], [g] and [p]:
     [|- map_first f (map_second g p) = map_second g (map_first f p)] *)
  intros A B C D f g p.
  (* [p] is [Pair_introduction a b], with [a] and [b] in the context:
     [|- map_first f (map_second g (Pair_introduction a b))
         = map_second g (map_first f (Pair_introduction a b))] *)
  destruct p as [a b].
  (* Both sides compute in two steps to the same pair:
     [|- Pair_introduction (f a) (g b) = Pair_introduction (f a) (g b)] *)
  simpl in |- *.
  (* Both sides are the same term. *)
  reflexivity.
Qed.

Theorem bimap_identity
  : forall (A : Type) (B : Type) (p : Pair A B),
      bimap (fun (a : A) => a) (fun (b : B) => b) p = p.
Proof.
  intros A B p.
  destruct p as [a b].
  simpl in |- *.
  reflexivity.
Qed.

Theorem bimap_composition
  : forall (A : Type) (B : Type) (C : Type) (D : Type) (E : Type) (F : Type)
      (f1 : A -> C) (f2 : B -> D) (g1 : C -> E) (g2 : D -> F) (p : Pair A B),
      bimap g1 g2 (bimap f1 f2 p)
      = bimap (fun (a : A) => g1 (f1 a)) (fun (b : B) => g2 (f2 b)) p.
Proof.
  (* The context gains the six types, [f1], [f2], [g1], [g2] and [p]:
     [|- bimap g1 g2 (bimap f1 f2 p)
         = bimap (fun a => g1 (f1 a)) (fun b => g2 (f2 b)) p] *)
  intros A B C D E F f1 f2 g1 g2 p.
  (* [p] is [Pair_introduction a b], with [a] and [b] in the context:
     [|- bimap g1 g2 (bimap f1 f2 (Pair_introduction a b))
      = bimap (fun a => g1 (f1 a)) (fun b => g2 (f2 b)) (Pair_introduction a b)] *)
  destruct p as [a b].
  (* The left side computes in two [bimap] steps to
     [Pair_introduction (g1 (f1 a)) (g2 (f2 b))], the right side in one
     step to the same:
     [|- Pair_introduction (g1 (f1 a)) (g2 (f2 b))
      = Pair_introduction (g1 (f1 a)) (g2 (f2 b))] *)
  simpl in |- *.
  (* Both sides are the same term. *)
  reflexivity.
Qed.

Theorem bimap_decomposition
  : forall (A : Type) (B : Type) (C : Type) (D : Type)
      (f : A -> C) (g : B -> D)
      (p : Pair A B),
      bimap f g p = map_first f (map_second g p).
Proof.
  (* The context gains [A], [B], [C], [D], [f], [g] and [p]:
     [|- bimap f g p = map_first f (map_second g p)] *)
  intros A B C D f g p.
  (* [p] is [Pair_introduction a b], with [a] and [b] in the context:
     [|- bimap f g (Pair_introduction a b)
      = map_first f (map_second g (Pair_introduction a b))] *)
  destruct p as [a b].
  (* The left side computes in one step, the right side in two, to the
     same pair:
     [|- Pair_introduction (f a) (g b)
      = Pair_introduction (f a) (g b)] *)
  simpl in |- *.
  (* Both sides are the same term. *)
  reflexivity.
Qed.

(* [forall {A : Type} {B : Type} {C : Type}, (Pair A B -> C) -> A -> B -> C] *)
Definition curry := fun {A : Type} {B : Type} {C : Type}
                        (f : Pair A B -> C) (a : A) (b : B) =>
  f (Pair_introduction a b).

(* [forall {A : Type} {B : Type} {C : Type}, (A -> B -> C) -> Pair A B -> C]
   The [match] is what makes [uncurry f] applied to a [Pair_introduction]
   compute to [f a b] outright, which both round trips below rest on. *)
Definition uncurry := fun {A : Type} {B : Type} {C : Type}
                          (f : A -> B -> C) (p : Pair A B) =>
  match p return C with
  | Pair_introduction a b => f a b
  end.

(* The two round trips, each stated for every argument rather than as an
   equality between functions, since nothing here assumes functional
   extensionality. *)

Theorem uncurry_curry_identity
  : forall (A : Type) (B : Type) (C : Type) (f : Pair A B -> C) (p : Pair A B),
      uncurry (curry f) p = f p.
Proof.
  (* The context gains [A], [B], [C], [f] and [p]:
     [|- uncurry (curry f) p = f p] *)
  intros A B C f p.
  (* [p] is [Pair_introduction a b], with [a] and [b] in the context:
     [|- uncurry (curry f) (Pair_introduction a b) = f (Pair_introduction a b)] *)
  destruct p as [a b].
  (* [uncurry] computes on the ctor; [curry] has no [match] to step, so
     [simpl] leaves it folded:
     [|- curry f a b = f (Pair_introduction a b)] *)
  simpl in |- *.
  (* [|- f (Pair_introduction a b) = f (Pair_introduction a b)] *)
  unfold curry in |- *.
  (* Both sides are the same term. *)
  reflexivity.
Qed.

Theorem curry_uncurry_identity
  : forall (A : Type) (B : Type) (C : Type) (f : A -> B -> C) (a : A) (b : B),
      curry (uncurry f) a b = f a b.
Proof.
  (* The context gains [A], [B], [C], [f], [a] and [b]:
     [|- curry (uncurry f) a b = f a b] *)
  intros A B C f a b.
  (* [|- uncurry f (Pair_introduction a b) = f a b] *)
  unfold curry in |- *.
  (* [uncurry] computes on the ctor: [|- f a b = f a b] *)
  simpl in |- *.
  (* Both sides are the same term. *)
  reflexivity.
Qed.

(* [forall {A : Type} {B : Type},
      (A -> A -> A) -> (B -> B -> B) -> Pair A B -> Pair A B -> Pair A B]
   The operation of the direct product: each component is combined by its
   own operation. *)
Definition product := fun {A : Type} {B : Type}
                          (opA : A -> A -> A) (opB : B -> B -> B)
                          (p1 : Pair A B) (p2 : Pair A B) =>
  match p1, p2 return Pair A B with
  | Pair_introduction a1 b1, Pair_introduction a2 b2 => Pair_introduction (opA a1 a2) (opB b1 b2)
  end.

(* The laws of the direct product follow from the laws of the components,
   which the class premises supply; [rewrite] finds each one by resolution
   from the premise in the context. *)

Theorem product_associativity
  : forall (A : Type) (opA : A -> A -> A) (B : Type) (opB : B -> B -> B),
      Semigroup opA -> Semigroup opB ->
      forall (p1 : Pair A B) (p2 : Pair A B) (p3 : Pair A B),
        product opA opB (product opA opB p1 p2) p3
        = product opA opB p1 (product opA opB p2 p3).
Proof.
  (* The context gains [A], [opA], [B], [opB], [SA : Semigroup opA],
     [SB : Semigroup opB], [p1], [p2] and [p3]:
     [|- product opA opB (product opA opB p1 p2) p3
      = product opA opB p1 (product opA opB p2 p3)] *)
  intros A opA B opB SA SB p1 p2 p3.
  (* Each pair is a [Pair_introduction] of two components, which enter the
     context. *)
  destruct p1 as [a1 b1].
  destruct p2 as [a2 b2].
  destruct p3 as [a3 b3].
  (* Both sides compute in two steps:
     [|- Pair_introduction (opA (opA a1 a2) a3) (opB (opB b1 b2) b3)
      = Pair_introduction (opA a1 (opA a2 a3)) (opB b1 (opB b2 b3))] *)
  simpl in |- *.
  (* The first components agree:
     [|- Pair_introduction (opA a1 (opA a2 a3)) (opB (opB b1 b2) b3)
      = Pair_introduction (opA a1 (opA a2 a3)) (opB b1 (opB b2 b3))] *)
  rewrite (Semigroup.associativity a1 a2 a3) in |- *.
  (* The second components agree:
     [|- Pair_introduction (opA a1 (opA a2 a3)) (opB b1 (opB b2 b3))
      = Pair_introduction (opA a1 (opA a2 a3)) (opB b1 (opB b2 b3))] *)
  rewrite (Semigroup.associativity b1 b2 b3) in |- *.
  (* Both sides are the same term. *)
  reflexivity.
Qed.

Theorem product_left_identity
  : forall (A : Type) (opA : A -> A -> A) (eA : A)
      (B : Type) (opB : B -> B -> B) (eB : B),
      Monoid opA eA ->
      Monoid opB eB ->
      forall (p : Pair A B),
        product opA opB (Pair_introduction eA eB) p = p.
Proof.
  (* The context gains [A], [opA], [eA], [B], [opB], [eB],
     [MA : Monoid opA eA], [MB : Monoid opB eB] and [p]:
     [|- product opA opB (Pair_introduction eA eB) p = p] *)
  intros A opA eA B opB eB MA MB p.
  (* [p] is [Pair_introduction a b], with [a] and [b] in the context:
     [|- product opA opB (Pair_introduction eA eB) (Pair_introduction a b)
      = Pair_introduction a b] *)
  destruct p as [a b].
  (* The left side computes:
     [|- Pair_introduction (opA eA a) (opB eB b) = Pair_introduction a b] *)
  simpl in |- *.
  (* The context gains [la : opA eA a = a]. *)
  destruct (Monoid.identity a) as [la _].
  (* [|- Pair_introduction a (opB eB b) = Pair_introduction a b] *)
  rewrite la in |- *.
  (* The context gains [lb : opB eB b = b]. *)
  destruct (Monoid.identity b) as [lb _].
  (* [|- Pair_introduction a b = Pair_introduction a b] *)
  rewrite lb in |- *.
  (* Both sides are the same term. *)
  reflexivity.
Qed.

Theorem product_right_identity
  : forall (A : Type) (opA : A -> A -> A) (eA : A)
      (B : Type) (opB : B -> B -> B) (eB : B),
      Monoid opA eA ->
      Monoid opB eB ->
      forall (p : Pair A B),
      product opA opB p (Pair_introduction eA eB) = p.
Proof.
  (* The context gains [A], [opA], [eA], [B], [opB], [eB],
     [MA : Monoid opA eA], [MB : Monoid opB eB] and [p]:
     [|- product opA opB p (Pair_introduction eA eB) = p] *)
  intros A opA eA B opB eB MA MB p.
  (* [p] is [Pair_introduction a b], with [a] and [b] in the context:
     [|- product opA opB (Pair_introduction a b) (Pair_introduction eA eB)
      = Pair_introduction a b] *)
  destruct p as [a b].
  (* The left side computes:
     [|- Pair_introduction (opA a eA) (opB b eB)
      = Pair_introduction a          b] *)
  simpl in |- *.
  (* The context gains [ra : opA a eA = a]. *)
  destruct (Monoid.identity a) as [_ ra].
  (* [|- Pair_introduction a (opB b eB) = Pair_introduction a b] *)
  rewrite ra in |- *.
  (* The context gains [rb : opB b eB = b]. *)
  destruct (Monoid.identity b) as [_ rb].
  (* [|- Pair_introduction a b = Pair_introduction a b] *)
  rewrite rb in |- *.
  (* Both sides are the same term. *)
  reflexivity.
Qed.

Theorem product_commutativity
  : forall (A : Type) (opA : A -> A -> A) (B : Type) (opB : B -> B -> B),
      Commutative.T A opA ->
      Commutative.T B opB ->
      forall (p1 : Pair A B) (p2 : Pair A B),
        product opA opB p1 p2 = product opA opB p2 p1.
Proof.
  (* The context gains [A], [opA], [B], [opB], [CA : Commutative.T A opA],
     [CB : Commutative.T B opB], [p1] and [p2]:
     [|- product opA opB p1 p2 = product opA opB p2 p1] *)
  intros A opA B opB CA CB p1 p2.
  (* Each pair is a [Pair_introduction] of two components, which enter the
     context. *)
  destruct p1 as [a1 b1].
  destruct p2 as [a2 b2].
  (* Both sides compute:
     [|- Pair_introduction (opA a1 a2) (opB b1 b2)
      = Pair_introduction (opA a2 a1) (opB b2 b1)] *)
  simpl in |- *.
  (* The first components agree:
     [|- Pair_introduction (opA a2 a1) (opB b1 b2)
      = Pair_introduction (opA a2 a1) (opB b2 b1)] *)
  rewrite (Commutative.commutativity a1 a2) in |- *.
  (* The second components agree:
     [|- Pair_introduction (opA a2 a1) (opB b2 b1)
      = Pair_introduction (opA a2 a1) (opB b2 b1)] *)
  rewrite (Commutative.commutativity b1 b2) in |- *.
  (* Both sides are the same term. *)
  reflexivity.
Qed.

End Pair.

(* The level is reserved in [Core.Notations]; only the meaning belongs here.
   Declared at file level, it reaches a client through [Require Export]. A
   type former sits in [jwa_type_scope] beside [->], so [A * B -> C] needs
   no delimiter. *)
Notation "A * B" := (Pair A B)
  : jwa_type_scope.

(* The value-level notations live in [jwa_pair_scope], which [Core.Notations]
   declares without opening: a client writes [(a , b)%pair] or opens the
   scope. [only parsing] keeps them out of printing, so a goal shows
   [Pair_introduction a b] as the code names it rather than
   [(a, b)%pair]. *)
Notation "( a , b )" := (Pair_introduction a b) (only parsing)
  : jwa_pair_scope.

(* The projections under their textbook names. Each is a keyword standing
   for the function itself, so [pi_1 p] is ordinary application and
   [pi_1 (a , b)] computes as [Pair.first (a , b)] does. *)
Notation "'pi_1'" := Pair.first (only parsing)
  : jwa_pair_scope.
Notation "'pi_2'" := Pair.second (only parsing)
  : jwa_pair_scope.

(* [Pair A] is a functor in its second component; [A] is a parameter of the
   instance, so every first component gets one. The two laws were already
   proved above, so the instance only hands them over, applied to [A].
   [map_second]'s type arguments are maximally inserted, so the bare name
   collapses to one fixed triple of them; binding [B] and [C] first is what
   keeps it general enough for the field, as in [Data.Option]. *)
Instance Pair_functor
  : forall (A : Type), Functor (Pair A) :=
  fun (A : Type) =>
    {| Functor.map             := fun (B : Type) (C : Type) => Pair.map_second
     ; Functor.map_identity    := Pair.map_second_identity A
     ; Functor.map_composition := Pair.map_second_composition A |}.

Instance Pair_semigroup
  : forall (A : Type) (opA : A -> A -> A)
      (B : Type) (opB : B -> B -> B),
      Semigroup opA ->
      Semigroup opB ->
      Semigroup (Pair.product opA opB) :=
  fun (A : Type) (opA : A -> A -> A)
      (B : Type) (opB : B -> B -> B)
      (SA : Semigroup opA)
      (SB : Semigroup opB) =>
    {| Semigroup.associativity :=
        Pair.product_associativity A opA B opB SA SB |}.

Instance Pair_monoid
  : forall (A : Type) (opA : A -> A -> A) (eA : A)
      (B : Type) (opB : B -> B -> B) (eB : B),
      Monoid opA eA ->
      Monoid opB eB ->
      Monoid (Pair.product opA opB) (Pair_introduction eA eB) :=
  fun (A : Type) (opA : A -> A -> A) (eA : A)
      (B : Type) (opB : B -> B -> B) (eB : B)
      (MA : Monoid opA eA)
      (MB : Monoid opB eB) =>
    {| Monoid.semigroup := Pair_semigroup A opA B opB _ _
     ; Monoid.identity :=
         fun (p : Pair A B) =>
           Conjunction_introduction
             (Pair.product_left_identity A opA eA B opB eB MA MB p)
             (Pair.product_right_identity A opA eA B opB eB MA MB p) |}.

Instance Pair_commutative
  : forall (A : Type) (opA : A -> A -> A) (B : Type) (opB : B -> B -> B),
      Commutative.T A opA -> Commutative.T B opB ->
      Commutative.T (Pair A B) (Pair.product opA opB) :=
  fun (A : Type) (opA : A -> A -> A) (B : Type) (opB : B -> B -> B)
      (CA : Commutative.T A opA) (CB : Commutative.T B opB) =>
    {| Commutative.commutativity :=
        Pair.product_commutativity A opA B opB CA CB |}.

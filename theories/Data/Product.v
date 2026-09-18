(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Core.All] carries [->] and [=]: with [-noinit] a file has only what it
 * requires. [Algebra.Semigroup], [Algebra.Monoid] and
 * [Data.Functor] are the classes the instances at the bottom fill.
 *)
From jwa Require Import Algebra.Commutative.
From jwa Require Import Algebra.Monoid.
From jwa Require Import Algebra.Semigroup.
From jwa Require Import Core.All.
From jwa Require Import Data.Functor.

(* A product holds one [A] and one [B], in that order. Both are parameters:
 * the type of each component is fixed for the whole product. The ctor is
 * named as [Conjunction_introduction] is, since a product is to types what
 * [/\] is to propositions.
 *)
Inductive Product (A : Type) (B : Type) : Type :=
  | Product_introduction : A -> B -> Product A B.

(* Both types are inferred from the components. *)
Arguments Product_introduction {A} {B} a b.

(* The eliminator behind [induction], written out. Nothing recurses: a
 * product holds no smaller product, so one [match] is the whole content.
 *)
(* [forall (A : Type) (B : Type) (P : Product A B -> Prop),
 *    (forall (a : A) (b : B), P (Product_introduction a b)) ->
 *    forall (p : Product A B), P p]
 *)
Definition Product_induction
  : forall (A : Type) (B : Type) (P : Product A B -> Prop),
      (forall (a : A) (b : B), P (Product_introduction a b)) ->
      forall (p : Product A B), P p
  := fun (A : Type) (B : Type) (P : Product A B -> Prop)
         (step : forall (a : A) (b : B), P (Product_introduction a b))
         (p : Product A B) =>
       match p with
       | Product_introduction a b => step a b
       end.

(* A module may carry the type's name; its members read [Product.first]. *)
Module Product.

(* [forall {A : Type} {B : Type}, Product A B -> A] *)
Definition first := fun {A : Type} {B : Type} (p : Product A B) =>
  match p return A with
  | Product_introduction a _ => a
  end.

(* [forall {A : Type} {B : Type}, Product A B -> B] *)
Definition second := fun {A : Type} {B : Type} (p : Product A B) =>
  match p return B with
  | Product_introduction _ b => b
  end.

Theorem introduction_injectivity
  : forall (A : Type) (B : Type) (a1 : A) (b1 : B) (a2 : A) (b2 : B),
      Product_introduction a1 b1 = Product_introduction a2 b2 -> a1 = a2 /\ b1 = b2.
Proof.
  (* The context gains [A], [B], [a1], [b1], [a2], [b2] and
   * [e : Product_introduction a1 b1 = Product_introduction a2 b2]:
   * [|- a1 = a2 /\ b1 = b2]
   *)
  intros A B a1 b1 a2 b2 e.
  (* The context gains
   * [ea : first (Product_introduction a1 b1)
   *     = first (Product_introduction a2 b2)].
   *)
  pose proof (Identity.congruence first e) as ea.
  (* Both [first]s compute: [ea : a1 = a2] *)
  simpl in ea.
  (* The context gains
   * [eb : second (Product_introduction a1 b1)
   *     = second (Product_introduction a2 b2)].
   *)
  pose proof (Identity.congruence second e) as eb.
  (* Both [second]s compute: [eb : b1 = b2] *)
  simpl in eb.
  (* [/\] is built from a proof of each side. *)
  exact (Conjunction_introduction ea eb).
Qed.

(* [Product_introduction] is surjective: every product is the pairing of its
 * own projections. This is the eta rule for products, which an [Inductive]
 * does not compute, so it is proved.
 *)
Theorem introduction_surjectivity
  : forall (A : Type) (B : Type) (p : Product A B),
      p = Product_introduction (first p) (second p).
Proof.
  (* The context gains [A], [B] and [p]:
   * [|- p = Product_introduction (first p) (second p)]
   *)
  intros A B p.
  (* [p] is [Product_introduction a b], with [a] and [b] in the context:
   * [|- Product_introduction a b
   *  = Product_introduction
   *      (first (Product_introduction a b)) (second (Product_introduction a b))]
   *)
  destruct p as [a b].
  (* Both projections compute:
   * [|- Product_introduction a b = Product_introduction a b]
   *)
  simpl in |- *.
  (* Both sides are the same term. *)
  reflexivity.
Qed.

(* [forall {A : Type} {B : Type}, Product A B -> Product B A] *)
Definition swap := fun {A : Type} {B : Type} (p : Product A B) =>
  match p return Product B A with
  | Product_introduction a b => Product_introduction b a
  end.

Theorem swap_involution
  : forall (A : Type) (B : Type) (p : Product A B), swap (swap p) = p.
Proof.
  (* The context gains [A], [B] and [p]: [|- swap (swap p) = p] *)
  intros A B p.
  (* [p] is [Product_introduction a b], with [a] and [b] in the context:
   * [|- swap (swap (Product_introduction a b)) = Product_introduction a b]
   *)
  destruct p as [a b].
  (* Both [swap]s compute:
   * [|- Product_introduction a b = Product_introduction a b]
   *)
  simpl in |- *.
  (* Both sides are the same term. *)
  reflexivity.
Qed.

(* [forall {A : Type} {B : Type} {C : Type},
 *    (A -> C) -> Product A B -> Product C B]
 *)
Definition map_first := fun {A : Type} {B : Type} {C : Type}
                            (f : A -> C) (p : Product A B) =>
  match p return Product C B with
  | Product_introduction a b => Product_introduction (f a) b
  end.

(* [forall {A : Type} {B : Type} {C : Type},
 *    (B -> C) -> Product A B -> Product A C]
 *)
Definition map_second := fun {A : Type} {B : Type} {C : Type}
                             (f : B -> C) (p : Product A B) =>
  match p return Product A C with
  | Product_introduction a b => Product_introduction a (f b)
  end.

(* [forall {A : Type} {B : Type} {C : Type} {D : Type},
 *    (A -> C) -> (B -> D) -> Product A B -> Product C D]
 *)
Definition bimap := fun {A : Type} {B : Type} {C : Type} {D : Type}
                           (f : A -> C) (g : B -> D)
                           (p : Product A B) =>
  match p return Product C D with
  | Product_introduction a b => Product_introduction (f a) (g b)
  end.

(* The functor laws for each component and for both at once: the map
 * preserves the identity function and preserves composition. Stated for
 * every [p] rather than as an equality between functions, since nothing
 * here assumes functional extensionality.
 *)

Theorem map_first_identity
  : forall (A : Type) (B : Type) (p : Product A B),
      map_first (fun (a : A) => a) p = p.
Proof.
  (* The context gains [A], [B] and [p]: [|- map_first (fun a => a) p = p] *)
  intros A B p.
  (* [p] is [Product_introduction a b], with [a] and [b] in the context:
   * [|- map_first (fun a => a) (Product_introduction a b)
   *  = Product_introduction a b]
   *)
  destruct p as [a b].
  (* [map_first] computes and [(fun a => a) a] reduces to [a]:
   * [|- Product_introduction a b = Product_introduction a b]
   *)
  simpl in |- *.
  (* Both sides are the same term. *)
  reflexivity.
Qed.

Theorem map_first_composition
  : forall (A : Type) (B : Type) (C : Type) (D : Type) (f : A -> C) (g : C -> D)
      (p : Product A B),
      map_first g (map_first f p) = map_first (fun (a : A) => g (f a)) p.
Proof.
  (* The context gains [A], [B], [C], [D], [f], [g] and [p]:
   * [|- map_first g (map_first f p) = map_first (fun a => g (f a)) p]
   *)
  intros A B C D f g p.
  (* [p] is [Product_introduction a b], with [a] and [b] in the context:
   * [|- map_first g (map_first f (Product_introduction a b))
   *  = map_first (fun a => g (f a)) (Product_introduction a b)]
   *)
  destruct p as [a b].
  (* The left side computes in two [map_first] steps to
   * [Product_introduction (g (f a)) b], the right side in one step to the
   * same: [|- Product_introduction (g (f a)) b = Product_introduction (g (f a)) b]
   *)
  simpl in |- *.
  (* Both sides are the same term. *)
  reflexivity.
Qed.

Theorem map_second_identity
  : forall (A : Type) (B : Type) (p : Product A B),
      map_second (fun (b : B) => b) p = p.
Proof.
  (* The context gains [A], [B] and [p]: [|- map_second (fun b => b) p = p] *)
  intros A B p.
  (* [p] is [Product_introduction a b], with [a] and [b] in the context:
   * [|- map_second (fun b => b) (Product_introduction a b)
   *  = Product_introduction a b]
   *)
  destruct p as [a b].
  (* [map_second] computes and [(fun b => b) b] reduces to [b]:
   * [|- Product_introduction a b = Product_introduction a b]
   *)
  simpl in |- *.
  (* Both sides are the same term. *)
  reflexivity.
Qed.

Theorem map_second_composition
  : forall (A : Type) (B : Type) (C : Type) (D : Type) (f : B -> C) (g : C -> D)
      (p : Product A B),
      map_second g (map_second f p) = map_second (fun (b : B) => g (f b)) p.
Proof.
  (* The context gains [A], [B], [C], [D], [f], [g] and [p]:
   * [|- map_second g (map_second f p) = map_second (fun b => g (f b)) p]
   *)
  intros A B C D f g p.
  (* [p] is [Product_introduction a b], with [a] and [b] in the context:
   * [|- map_second g (map_second f (Product_introduction a b))
   *  = map_second (fun b => g (f b)) (Product_introduction a b)]
   *)
  destruct p as [a b].
  (* The left side computes in two [map_second] steps to
   * [Product_introduction a (g (f b))], the right side in one step to the
   * same: [|- Product_introduction a (g (f b)) = Product_introduction a (g (f b))]
   *)
  simpl in |- *.
  (* Both sides are the same term. *)
  reflexivity.
Qed.

(* The two maps touch different components, so their order does not
 * matter.
 *)
Theorem map_first_map_second_commutativity
  : forall (A : Type) (B : Type) (C : Type) (D : Type) (f : A -> C) (g : B -> D)
      (p : Product A B),
      map_first f (map_second g p) = map_second g (map_first f p).
Proof.
  (* The context gains [A], [B], [C], [D], [f], [g] and [p]:
   * [|- map_first f (map_second g p) = map_second g (map_first f p)]
   *)
  intros A B C D f g p.
  (* [p] is [Product_introduction a b], with [a] and [b] in the context:
   * [|- map_first f (map_second g (Product_introduction a b))
   *     = map_second g (map_first f (Product_introduction a b))]
   *)
  destruct p as [a b].
  (* Both sides compute in two steps to the same product:
   * [|- Product_introduction (f a) (g b) = Product_introduction (f a) (g b)]
   *)
  simpl in |- *.
  (* Both sides are the same term. *)
  reflexivity.
Qed.

Theorem bimap_identity
  : forall (A : Type) (B : Type) (p : Product A B),
      bimap (fun (a : A) => a) (fun (b : B) => b) p = p.
Proof.
  intros A B p.
  destruct p as [a b].
  simpl in |- *.
  reflexivity.
Qed.

Theorem bimap_composition
  : forall (A : Type) (B : Type) (C : Type) (D : Type) (E : Type) (F : Type)
      (f1 : A -> C) (f2 : B -> D) (g1 : C -> E) (g2 : D -> F) (p : Product A B),
      bimap g1 g2 (bimap f1 f2 p)
      = bimap (fun (a : A) => g1 (f1 a)) (fun (b : B) => g2 (f2 b)) p.
Proof.
  (* The context gains the six types, [f1], [f2], [g1], [g2] and [p]:
   * [|- bimap g1 g2 (bimap f1 f2 p)
   *     = bimap (fun a => g1 (f1 a)) (fun b => g2 (f2 b)) p]
   *)
  intros A B C D E F f1 f2 g1 g2 p.
  (* [p] is [Product_introduction a b], with [a] and [b] in the context:
   * [|- bimap g1 g2 (bimap f1 f2 (Product_introduction a b))
   *  = bimap (fun a => g1 (f1 a)) (fun b => g2 (f2 b)) (Product_introduction a b)]
   *)
  destruct p as [a b].
  (* The left side computes in two [bimap] steps to
   * [Product_introduction (g1 (f1 a)) (g2 (f2 b))], the right side in one
   * step to the same:
   * [|- Product_introduction (g1 (f1 a)) (g2 (f2 b))
   *  = Product_introduction (g1 (f1 a)) (g2 (f2 b))]
   *)
  simpl in |- *.
  (* Both sides are the same term. *)
  reflexivity.
Qed.

Theorem bimap_decomposition
  : forall (A : Type) (B : Type) (C : Type) (D : Type)
      (f : A -> C) (g : B -> D)
      (p : Product A B),
      bimap f g p = map_first f (map_second g p).
Proof.
  (* The context gains [A], [B], [C], [D], [f], [g] and [p]:
   * [|- bimap f g p = map_first f (map_second g p)]
   *)
  intros A B C D f g p.
  (* [p] is [Product_introduction a b], with [a] and [b] in the context:
   * [|- bimap f g (Product_introduction a b)
   *  = map_first f (map_second g (Product_introduction a b))]
   *)
  destruct p as [a b].
  (* The left side computes in one step, the right side in two, to the
   * same product:
   * [|- Product_introduction (f a) (g b)
   *  = Product_introduction (f a) (g b)]
   *)
  simpl in |- *.
  (* Both sides are the same term. *)
  reflexivity.
Qed.

(* [forall {A : Type} {B : Type} {C : Type}, (Product A B -> C) -> A -> B -> C] *)
Definition curry := fun {A : Type} {B : Type} {C : Type}
                        (f : Product A B -> C) (a : A) (b : B) =>
  f (Product_introduction a b).

(* The [match] is what makes [uncurry f] applied to a [Product_introduction]
 * compute to [f a b] outright, which both round trips below rest on.
 *)
(* [forall {A : Type} {B : Type} {C : Type}, (A -> B -> C) -> Product A B -> C] *)
Definition uncurry := fun {A : Type} {B : Type} {C : Type}
                          (f : A -> B -> C) (p : Product A B) =>
  match p return C with
  | Product_introduction a b => f a b
  end.

(* The two round trips, each stated for every argument rather than as an
 * equality between functions, since nothing here assumes functional
 * extensionality.
 *)

Theorem uncurry_curry_identity
  : forall (A : Type) (B : Type) (C : Type) (f : Product A B -> C) (p : Product A B),
      uncurry (curry f) p = f p.
Proof.
  (* The context gains [A], [B], [C], [f] and [p]:
   * [|- uncurry (curry f) p = f p]
   *)
  intros A B C f p.
  (* [p] is [Product_introduction a b], with [a] and [b] in the context:
   * [|- uncurry (curry f) (Product_introduction a b) = f (Product_introduction a b)]
   *)
  destruct p as [a b].
  (* [uncurry] computes on the ctor; [curry] has no [match] to step, so
   * [simpl] leaves it folded:
   * [|- curry f a b = f (Product_introduction a b)]
   *)
  simpl in |- *.
  (* [|- f (Product_introduction a b) = f (Product_introduction a b)] *)
  unfold curry in |- *.
  (* Both sides are the same term. *)
  reflexivity.
Qed.

Theorem curry_uncurry_identity
  : forall (A : Type) (B : Type) (C : Type) (f : A -> B -> C) (a : A) (b : B),
      curry (uncurry f) a b = f a b.
Proof.
  (* The context gains [A], [B], [C], [f], [a] and [b]:
   * [|- curry (uncurry f) a b = f a b]
   *)
  intros A B C f a b.
  (* [|- uncurry f (Product_introduction a b) = f a b] *)
  unfold curry in |- *.
  (* [uncurry] computes on the ctor: [|- f a b = f a b] *)
  simpl in |- *.
  (* Both sides are the same term. *)
  reflexivity.
Qed.

(* The operation of the direct product: each component is combined by its
 * own operation.
 *)
(* [forall {A : Type} {B : Type},
 *    (A -> A -> A) -> (B -> B -> B) -> Product A B -> Product A B -> Product A B]
 *)
Definition product := fun {A : Type} {B : Type}
                          (opA : A -> A -> A) (opB : B -> B -> B)
                          (p1 : Product A B) (p2 : Product A B) =>
  match p1, p2 return Product A B with
  | Product_introduction a1 b1, Product_introduction a2 b2 =>
      Product_introduction (opA a1 a2) (opB b1 b2)
  end.

(* The laws of the direct product follow from the laws of the components,
 * which the class premises supply; [rewrite] finds each one by resolution
 * from the premise in the context.
 *)

Theorem product_associativity
  : forall (A : Type) (opA : A -> A -> A) (B : Type) (opB : B -> B -> B),
      Semigroup opA -> Semigroup opB ->
      forall (p1 : Product A B) (p2 : Product A B) (p3 : Product A B),
        product opA opB (product opA opB p1 p2) p3
        = product opA opB p1 (product opA opB p2 p3).
Proof.
  (* The context gains [A], [opA], [B], [opB], [SA : Semigroup opA],
   * [SB : Semigroup opB], [p1], [p2] and [p3]:
   * [|- product opA opB (product opA opB p1 p2) p3
   *  = product opA opB p1 (product opA opB p2 p3)]
   *)
  intros A opA B opB SA SB p1 p2 p3.
  (* Each product is a [Product_introduction] of two components, which enter
   * the context.
   *)
  destruct p1 as [a1 b1].
  destruct p2 as [a2 b2].
  destruct p3 as [a3 b3].
  (* Both sides compute in two steps:
   * [|- Product_introduction (opA (opA a1 a2) a3) (opB (opB b1 b2) b3)
   *  = Product_introduction (opA a1 (opA a2 a3)) (opB b1 (opB b2 b3))]
   *)
  simpl in |- *.
  (* The first components agree:
   * [|- Product_introduction (opA a1 (opA a2 a3)) (opB (opB b1 b2) b3)
   *  = Product_introduction (opA a1 (opA a2 a3)) (opB b1 (opB b2 b3))]
   *)
  rewrite (Semigroup.associativity a1 a2 a3) in |- *.
  (* The second components agree:
   * [|- Product_introduction (opA a1 (opA a2 a3)) (opB b1 (opB b2 b3))
   *  = Product_introduction (opA a1 (opA a2 a3)) (opB b1 (opB b2 b3))]
   *)
  rewrite (Semigroup.associativity b1 b2 b3) in |- *.
  (* Both sides are the same term. *)
  reflexivity.
Qed.

Theorem product_left_identity
  : forall (A : Type) (opA : A -> A -> A) (eA : A)
      (B : Type) (opB : B -> B -> B) (eB : B),
      Monoid opA eA ->
      Monoid opB eB ->
      forall (p : Product A B),
        product opA opB (Product_introduction eA eB) p = p.
Proof.
  (* The context gains [A], [opA], [eA], [B], [opB], [eB],
   * [MA : Monoid opA eA], [MB : Monoid opB eB] and [p]:
   * [|- product opA opB (Product_introduction eA eB) p = p]
   *)
  intros A opA eA B opB eB MA MB p.
  (* [p] is [Product_introduction a b], with [a] and [b] in the context:
   * [|- product opA opB (Product_introduction eA eB) (Product_introduction a b)
   *  = Product_introduction a b]
   *)
  destruct p as [a b].
  (* The left side computes:
   * [|- Product_introduction (opA eA a) (opB eB b) = Product_introduction a b]
   *)
  simpl in |- *.
  (* The context gains [la : opA eA a = a]. *)
  destruct (Monoid.identity a) as [la _].
  (* [|- Product_introduction a (opB eB b) = Product_introduction a b] *)
  rewrite la in |- *.
  (* The context gains [lb : opB eB b = b]. *)
  destruct (Monoid.identity b) as [lb _].
  (* [|- Product_introduction a b = Product_introduction a b] *)
  rewrite lb in |- *.
  (* Both sides are the same term. *)
  reflexivity.
Qed.

Theorem product_right_identity
  : forall (A : Type) (opA : A -> A -> A) (eA : A)
      (B : Type) (opB : B -> B -> B) (eB : B),
      Monoid opA eA ->
      Monoid opB eB ->
      forall (p : Product A B),
      product opA opB p (Product_introduction eA eB) = p.
Proof.
  (* The context gains [A], [opA], [eA], [B], [opB], [eB],
   * [MA : Monoid opA eA], [MB : Monoid opB eB] and [p]:
   * [|- product opA opB p (Product_introduction eA eB) = p]
   *)
  intros A opA eA B opB eB MA MB p.
  (* [p] is [Product_introduction a b], with [a] and [b] in the context:
   * [|- product opA opB (Product_introduction a b) (Product_introduction eA eB)
   *  = Product_introduction a b]
   *)
  destruct p as [a b].
  (* The left side computes:
   * [|- Product_introduction (opA a eA) (opB b eB)
   *  = Product_introduction a          b]
   *)
  simpl in |- *.
  (* The context gains [ra : opA a eA = a]. *)
  destruct (Monoid.identity a) as [_ ra].
  (* [|- Product_introduction a (opB b eB) = Product_introduction a b] *)
  rewrite ra in |- *.
  (* The context gains [rb : opB b eB = b]. *)
  destruct (Monoid.identity b) as [_ rb].
  (* [|- Product_introduction a b = Product_introduction a b] *)
  rewrite rb in |- *.
  (* Both sides are the same term. *)
  reflexivity.
Qed.

Theorem product_commutativity
  : forall (A : Type) (opA : A -> A -> A) (B : Type) (opB : B -> B -> B),
      Commutative opA ->
      Commutative opB ->
      forall (p1 : Product A B) (p2 : Product A B),
        product opA opB p1 p2 = product opA opB p2 p1.
Proof.
  (* The context gains [A], [opA], [B], [opB], [CA : Commutative opA],
   * [CB : Commutative opB], [p1] and [p2]:
   * [|- product opA opB p1 p2 = product opA opB p2 p1]
   *)
  intros A opA B opB CA CB p1 p2.
  (* Each product is a [Product_introduction] of two components, which enter
   * the context.
   *)
  destruct p1 as [a1 b1].
  destruct p2 as [a2 b2].
  (* Both sides compute:
   * [|- Product_introduction (opA a1 a2) (opB b1 b2)
   *  = Product_introduction (opA a2 a1) (opB b2 b1)]
   *)
  simpl in |- *.
  (* The first components agree:
   * [|- Product_introduction (opA a2 a1) (opB b1 b2)
   *  = Product_introduction (opA a2 a1) (opB b2 b1)]
   *)
  rewrite (Commutative.commutativity a1 a2) in |- *.
  (* The second components agree:
   * [|- Product_introduction (opA a2 a1) (opB b2 b1)
   *  = Product_introduction (opA a2 a1) (opB b2 b1)]
   *)
  rewrite (Commutative.commutativity b1 b2) in |- *.
  (* Both sides are the same term. *)
  reflexivity.
Qed.

End Product.

(* The level is reserved in [Core.Notations]; only the meaning belongs here.
 * Declared at file level, it reaches a client through [Require Export]. A
 * type former sits in [jwa_type_scope] beside [->], so [A * B -> C] needs
 * no delimiter.
 *)
Notation "A * B" := (Product A B)
  : jwa_type_scope.

(* The value-level notations live in [jwa_product_scope], which
 * [Core.Notations] declares without opening: a client writes
 * [(a , b)%product] or opens the scope. [only parsing] keeps them out of
 * printing, so a goal shows [Product_introduction a b] as the code names it
 * rather than [(a, b)%product].
 *)
Notation "( a , b )" := (Product_introduction a b) (only parsing)
  : jwa_product_scope.

(* The projections under their textbook names. Each is a keyword standing
 * for the function itself, so [pi_1 p] is ordinary application and
 * [pi_1 (a , b)] computes as [Product.first (a , b)] does.
 *)
Notation "'pi_1'" := Product.first (only parsing)
  : jwa_product_scope.
Notation "'pi_2'" := Product.second (only parsing)
  : jwa_product_scope.

(* [Product A] is a functor in its second component; [A] is a parameter of
 * the instance, so every first component gets one. The two laws were
 * already proved above, so the instance only hands them over, applied to
 * [A]. [map_second]'s type arguments are maximally inserted, so the bare
 * name collapses to one fixed triple of them; binding [B] and [C] first is
 * what keeps it general enough for the field, as in [Data.Option].
 *)
Instance Product_functor
  : forall (A : Type), Functor (Product A) :=
  fun (A : Type) =>
    {| Functor.map             := fun (B : Type) (C : Type) => Product.map_second
     ; Functor.map_identity    := Product.map_second_identity A
     ; Functor.map_composition := Product.map_second_composition A |}.

Instance Product_semigroup
  : forall (A : Type) (opA : A -> A -> A)
      (B : Type) (opB : B -> B -> B),
      Semigroup opA ->
      Semigroup opB ->
      Semigroup (Product.product opA opB) :=
  fun (A : Type) (opA : A -> A -> A)
      (B : Type) (opB : B -> B -> B)
      (SA : Semigroup opA)
      (SB : Semigroup opB) =>
    {| Semigroup.associativity :=
        Product.product_associativity A opA B opB SA SB |}.

Instance Product_monoid
  : forall (A : Type) (opA : A -> A -> A) (eA : A)
      (B : Type) (opB : B -> B -> B) (eB : B),
      Monoid opA eA ->
      Monoid opB eB ->
      Monoid (Product.product opA opB) (Product_introduction eA eB) :=
  fun (A : Type) (opA : A -> A -> A) (eA : A)
      (B : Type) (opB : B -> B -> B) (eB : B)
      (MA : Monoid opA eA)
      (MB : Monoid opB eB) =>
    {| Monoid.semigroup := Product_semigroup A opA B opB _ _
     ; Monoid.identity :=
         fun (p : Product A B) =>
           Conjunction_introduction
             (Product.product_left_identity A opA eA B opB eB MA MB p)
             (Product.product_right_identity A opA eA B opB eB MA MB p) |}.

Instance Product_commutative
  : forall (A : Type) (opA : A -> A -> A) (B : Type) (opB : B -> B -> B),
      Commutative opA -> Commutative opB ->
      Commutative (Product.product opA opB) :=
  fun (A : Type) (opA : A -> A -> A) (B : Type) (opB : B -> B -> B)
      (CA : Commutative opA) (CB : Commutative opB) =>
    {| Commutative.commutativity :=
        Product.product_commutativity A opA B opB CA CB |}.

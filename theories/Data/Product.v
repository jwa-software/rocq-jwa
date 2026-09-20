(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Algebra.Commutative.
From jwa Require Import Algebra.Monoid.
From jwa Require Import Algebra.Semigroup.
From jwa Require Import Core.All.
From jwa Require Import Data.Functor.

(* A product holds one [A] and one [B], in that order. Both are parameters:
 * the type of each component is fixed for the whole product.
 *)
Inductive Product (A : Type) (B : Type) : Type :=
  | Product_introduction : A -> B -> Product A B.

(* Both types are inferred from the components. *)
Arguments Product_introduction {A} {B} a b.

(* The eliminator behind [induction], written out. Nothing recurses: a
 * product holds no smaller product, so one [match] is the whole content.
 *)
Definition Product_induction
  : forall (A : Type) (B : Type) (P : Product A B -> Prop) .
    (forall (a : A) (b : B) . P (Product_introduction a b)) ->
    (forall (p : Product A B) . P p)
  := fun (A : Type) (B : Type) (P : Product A B -> Prop)
       (step : forall (a : A) (b : B) .
       P (Product_introduction a b)) (p : Product A B) .
       match p with
       | Product_introduction a b => step a b
       end.

(* A module may carry the type's name; its members read [Product.first]. *)
Module Product. (* Product *)

(* [forall {A : Type} {B : Type} . Product A B -> A] *)
Definition first := fun {A : Type} {B : Type} (p : Product A B) .
  match p return A with
  | Product_introduction a _ => a
  end.

(* [forall {A : Type} {B : Type} . Product A B -> B] *)
Definition second := fun {A : Type} {B : Type} (p : Product A B) .
  match p return B with
  | Product_introduction _ b => b
  end.

(* [forall {A : Type} {B : Type} . Product A B -> Product B A] *)
Definition swap := fun {A : Type} {B : Type} (p : Product A B) .
  match p return Product B A with
  | Product_introduction a b => Product_introduction b a
  end.

(* [forall {A : Type} {B : Type} {C : Type} .
 *    (A -> C) -> Product A B -> Product C B]
 *)
Definition map_first := fun {A : Type} {B : Type} {C : Type}
                          (f : A -> C) (p : Product A B) .
  match p return Product C B with
  | Product_introduction a b => Product_introduction (f a) b
  end.

(* [forall {A : Type} {B : Type} {C : Type} .
 *    (B -> C) -> Product A B -> Product A C]
 *)
Definition map_second := fun {A : Type} {B : Type} {C : Type}
                           (f : B -> C) (p : Product A B) .
  match p return Product A C with
  | Product_introduction a b => Product_introduction a (f b)
  end.

(* [forall {A : Type} {B : Type} {C : Type} {D : Type} .
 *    (A -> C) -> (B -> D) -> Product A B -> Product C D]
 *)
Definition bimap := fun {A : Type} {B : Type} {C : Type} {D : Type}
                      (f : A -> C) (g : B -> D)
                      (p : Product A B) .
  match p return Product C D with
  | Product_introduction a b => Product_introduction (f a) (g b)
  end.

(* [forall {A : Type} {B : Type} {C : Type} . (Product A B -> C) -> A -> B -> C] *)
Definition curry := fun {A : Type} {B : Type} {C : Type}
                      (f : Product A B -> C) (a : A) (b : B) .
  f (Product_introduction a b).

(* [forall {A : Type} {B : Type} {C : Type} . (A -> B -> C) -> Product A B -> C] *)
Definition uncurry := fun {A : Type} {B : Type} {C : Type}
                        (f : A -> B -> C) (p : Product A B) .
  match p return C with
  | Product_introduction a b => f a b
  end.

(* [forall {A : Type} {B : Type} .
 *    (A -> A -> A) -> (B -> B -> B) -> Product A B -> Product A B -> Product A B]
 *)
Definition direct_product := fun {A : Type} {B : Type}
                               (f1 : A -> A -> A) (f2 : B -> B -> B)
                               (p1 : Product A B) (p2 : Product A B) .
  match p1, p2 return Product A B with
  | Product_introduction a1 b1, Product_introduction a2 b2 =>
      Product_introduction (f1 a1 a2) (f2 b1 b2)
  end.

Module introduction. (* introduction *)

(* introduction.injectivity *)
Theorem injectivity
  : forall {A : Type} {B : Type} (a1 : A) (b1 : B) (a2 : A) (b2 : B) .
      (Product_introduction a1 b1 = Product_introduction a2 b2) -> (a1 = a2) /\ (b1 = b2).
Proof.
  intros A B a1 b1 a2 b2 e.
  pose proof (Identity.congruence first  e) as a. simpl in a.
  pose proof (Identity.congruence second e) as b. simpl in b.
  exact (Conjunction_introduction a b).
Qed.

(* introduction.surjectivity *)
Theorem surjectivity
  : forall {A : Type} {B : Type} (p : Product A B) .
      p = Product_introduction (first p) (second p).
Proof.
  intros A B p.
  destruct p as [a b].
  simpl in |- *.
  reflexivity.
Qed.

End introduction. (* introduction *)

Module swap. (* swap *)

(* swap.involution *)
Theorem involution
  : forall {A : Type} {B : Type} (p : Product A B) . swap (swap p) = p.
Proof.
  intros A B p.
  destruct p as [a b].
  simpl in |- *.
  reflexivity.
Qed.

End swap. (* swap *)

Module mapping. (* mapping *)

Module first. (* mapping.first *)

(* mapping.first.identity *)
Theorem identity
  : forall {A : Type} {B : Type} (p : Product A B) . map_first (fun (a : A) . a) p = p.
Proof.
  intros A B p.
  destruct p as [a b].
  simpl in |- *.
  reflexivity.
Qed.

(* mapping.first.composition *)
Theorem composition
  : forall {A : Type} {B : Type} {C : Type} {D : Type} (f : A -> C) (g : C -> D) (p : Product A B) .
      map_first g (map_first f p) = map_first (fun (a : A) . g (f a)) p.
Proof.
  intros A B C D f g p.
  destruct p as [a b].
  simpl in |- *.
  reflexivity.
Qed.

End first. (* mapping.first *)

Module second. (* mapping.second *)

(* mapping.second.identity *)
Theorem identity
  : forall {A : Type} {B : Type} (p : Product A B) . map_second (fun (b : B) . b) p = p.
Proof.
  intros A B p.
  destruct p as [a b].
  simpl in |- *.
  reflexivity.
Qed.

(* mapping.second.composition *)
Theorem composition
  : forall {A : Type} {B : Type} {C : Type} {D : Type} (f : B -> C) (g : C -> D) (p : Product A B) .
      map_second g (map_second f p) = map_second (fun (b : B) . g (f b)) p.
Proof.
  intros A B C D f g p.
  destruct p as [a b].
  simpl in |- *.
  reflexivity.
Qed.

End second. (* mapping.second *)

(* mapping.commutativity *)
Theorem commutativity
  : forall {A : Type} {B : Type} {C : Type} {D : Type} (f : A -> C) (g : B -> D) (p : Product A B) .
      map_first f (map_second g p) = map_second g (map_first f p).
Proof.
  intros A B C D f g p.
  destruct p as [a b].
  simpl in |- *.
  reflexivity.
Qed.

Module both. (* mapping.both *)

(* mapping.both.identity *)
Theorem identity
  : forall {A : Type} {B : Type} (p : Product A B) .
      bimap (fun (a : A) . a) (fun (b : B) . b) p = p.
Proof.
  intros A B p.
  destruct p as [a b].
  simpl in |- *.
  reflexivity.
Qed.

(* mapping.both.composition *)
Theorem composition
  : forall {A : Type} {B : Type} {C : Type} {D : Type} {E : Type} {F : Type}
      (f1 : A -> C) (f2 : B -> D) (g1 : C -> E) (g2 : D -> F) (p : Product A B) .
      bimap g1 g2 (bimap f1 f2 p) = bimap (fun (a : A) . g1 (f1 a)) (fun (b : B) . g2 (f2 b)) p.
Proof.
  intros A B C D E F f1 f2 g1 g2 p.
  destruct p as [a b].
  simpl in |- *.
  reflexivity.
Qed.

(* mapping.both.decomposition *)
Theorem decomposition
  : forall {A : Type} {B : Type} {C : Type} {D : Type}
      (f : A -> C) (g : B -> D) (p : Product A B) .
      bimap f g p = map_first f (map_second g p).
Proof.
  intros A B C D f g p.
  destruct p as [a b].
  simpl in |- *.
  reflexivity.
Qed.

End both. (* mapping.both *)

End mapping. (* mapping *)

Module currying. (* currying *)

Module inversion. (* currying.inversion *)

Module of. (* currying.inversion.of *)

(* currying.inversion.of.uncurrying *)
Theorem uncurrying
  : forall {A : Type} {B : Type} {C : Type} (f : A -> B -> C) (a : A) (b : B) .
      curry (uncurry f) a b = f a b.
Proof.
  intros A B C f a b.
  unfold curry in |- *.
  simpl in |- *.
  reflexivity.
Qed.

End of. (* currying.inversion.of *)

End inversion. (* currying.inversion *)

End currying. (* currying *)

Module uncurrying. (* uncurrying *)

Module inversion. (* uncurrying.inversion *)

Module of. (* uncurrying.inversion.of *)

(* uncurrying.inversion.of.currying *)
Theorem currying
  : forall {A : Type} {B : Type} {C : Type} (f : Product A B -> C) (p : Product A B) .
      uncurry (curry f) p = f p.
Proof.
  intros A B C f p.
  destruct p as [a b].
  simpl in |- *.
  unfold curry in |- *.
  reflexivity.
Qed.

End of. (* uncurrying.inversion.of *)

End inversion. (* uncurrying.inversion *)

End uncurrying. (* uncurrying *)

Module direct. (* direct *)

(* direct.associativity *)
Theorem associativity
  : forall {A : Type} {B : Type}
      (f1 : A -> A -> A) (f2 : B -> B -> B) .
      Semigroup f1 ->
      Semigroup f2 ->
      forall (p1 : Product A B) (p2 : Product A B) (p3 : Product A B) .
        direct_product f1 f2 (direct_product f1 f2 p1 p2) p3
      = direct_product f1 f2 p1 (direct_product f1 f2 p2 p3).
Proof.
  intros A B f1 f2 SA SB p1 p2 p3.
  destruct p1 as [a1 b1].
  destruct p2 as [a2 b2].
  destruct p3 as [a3 b3].
  simpl in |- *.
  rewrite (Semigroup.associativity a1 a2 a3) in |- *.
  rewrite (Semigroup.associativity b1 b2 b3) in |- *.
  reflexivity.
Qed.

Module left. (* direct.left *)

(* direct.left.identity *)
Lemma identity
  : forall {A : Type} {B : Type}
      (f1 : A -> A -> A) (eA : A) (f2 : B -> B -> B) (eB : B) .
      Monoid f1 eA ->
      Monoid f2 eB ->
      forall (p : Product A B) .
        direct_product f1 f2 (Product_introduction eA eB) p = p.
Proof.
  intros A B f1 eA f2 eB MA MB p.
  destruct p as [a b].
  simpl in |- *.
  destruct (Monoid.identity a) as [la _].
  destruct (Monoid.identity b) as [lb _].
  rewrite la, lb in |- *.
  reflexivity.
Qed.

End left. (* direct.left *)

Module right. (* direct.right *)

(* direct.right.identity *)
Lemma identity
  : forall {A : Type} {B : Type}
      (f1 : A -> A -> A) (eA : A) (f2 : B -> B -> B) (eB : B) .
      Monoid f1 eA ->
      Monoid f2 eB ->
      forall (p : Product A B) .
      direct_product f1 f2 p (Product_introduction eA eB) = p.
Proof.
  intros A B f1 eA f2 eB MA MB p.
  destruct p as [a b].
  simpl in |- *.
  destruct (Monoid.identity a) as [_ ra].
  destruct (Monoid.identity b) as [_ rb].
  rewrite ra, rb in |- *.
  reflexivity.
Qed.

End right. (* direct.right *)

(* direct.identity *)
Theorem identity
  : forall {A : Type} {B : Type}
      (f1 : A -> A -> A) (eA : A) (f2 : B -> B -> B) (eB : B) .
      Monoid f1 eA ->
      Monoid f2 eB ->
      forall (p : Product A B) .
        (direct_product f1 f2 (Product_introduction eA eB) p = p)
      /\ (direct_product f1 f2 p (Product_introduction eA eB) = p).
Proof.
  intros A B f1 eA f2 eB MA MB p.
  split.
  - exact (direct.left.identity  f1 eA f2 eB MA MB p).
  - exact (direct.right.identity f1 eA f2 eB MA MB p).
Qed.

(* direct.commutativity *)
Theorem commutativity
  : forall {A : Type} {B : Type} (f1 : A -> A -> A) (f2 : B -> B -> B) .
      Commutative f1 ->
      Commutative f2 ->
      forall (p1 : Product A B) (p2 : Product A B) .
        direct_product f1 f2 p1 p2 = direct_product f1 f2 p2 p1.
Proof.
  intros A B f1 f2 CA CB p1 p2.
  destruct p1 as [a1 b1].
  destruct p2 as [a2 b2].
  simpl in |- *.
  rewrite (Commutative.commutativity a1 a2) in |- *.
  rewrite (Commutative.commutativity b1 b2) in |- *.
  reflexivity.
Qed.

End direct. (* direct *)

End Product. (* Product *)

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
  : forall (A : Type) . Functor (Product A) :=
  fun (A : Type) .
    ({| Functor.map             := fun (B : Type) (C : Type) . Product.map_second
      ; Functor.map_identity    := @Product.mapping.second.identity A
      ; Functor.map_composition := @Product.mapping.second.composition A |}).

Instance Product_semigroup
  : forall (A : Type) (opA : A -> A -> A)
      (B : Type) (opB : B -> B -> B) .
      Semigroup opA ->
      Semigroup opB ->
      Semigroup (Product.direct_product opA opB) :=
  fun (A : Type) (opA : A -> A -> A)
      (B : Type) (opB : B -> B -> B)
      (SA : Semigroup opA)
      (SB : Semigroup opB) .
    ({| Semigroup.associativity :=
         Product.direct.associativity opA opB SA SB |}).

Instance Product_monoid
  : forall (A : Type) (opA : A -> A -> A) (eA : A)
      (B : Type) (opB : B -> B -> B) (eB : B) .
      Monoid opA eA ->
      Monoid opB eB ->
      Monoid (Product.direct_product opA opB) (Product_introduction eA eB) :=
  fun (A : Type) (opA : A -> A -> A) (eA : A)
      (B : Type) (opB : B -> B -> B) (eB : B)
      (MA : Monoid opA eA)
      (MB : Monoid opB eB) .
    ({| Monoid.semigroup := Product_semigroup A opA B opB _ _
      ; Monoid.identity  := Product.direct.identity opA eA opB eB MA MB |}).

Instance Product_commutative
  : forall (A : Type) (opA : A -> A -> A)
      (B : Type) (opB : B -> B -> B) .
      Commutative opA ->
      Commutative opB ->
      Commutative (Product.direct_product opA opB) :=
  fun (A : Type) (opA : A -> A -> A)
      (B : Type) (opB : B -> B -> B)
      (CA : Commutative opA)
      (CB : Commutative opB) .
    ({| Commutative.commutativity :=
         Product.direct.commutativity opA opB CA CB |}).

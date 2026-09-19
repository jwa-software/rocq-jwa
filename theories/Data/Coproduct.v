(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Data.Functor.

(* A coproduct holds one [A] or one [B], tagged by which. Both are
 * parameters: the type behind each tag is fixed for the whole coproduct.
 *)
Inductive Coproduct (A : Type) (B : Type) : Type :=
  | Coproduct_introduction_left  : A -> Coproduct A B
  | Coproduct_introduction_right : B -> Coproduct A B.

(* One type is inferred from the value, the other from the expected type; a
 * use that has neither needs [@Coproduct_introduction_left A B a].
 *)
Arguments Coproduct_introduction_left  {A} {B} a.
Arguments Coproduct_introduction_right {A} {B} b.

(* The eliminator behind [induction], written out. Nothing recurses: a
 * coproduct holds no smaller coproduct, so one [match] is the whole content.
 *)
Definition Coproduct_induction
  : forall (A : Type) (B : Type) (P : Coproduct A B -> Prop),
      (forall (a : A), P (Coproduct_introduction_left a)) ->
      (forall (b : B), P (Coproduct_introduction_right b)) ->
      forall (cp : Coproduct A B), P cp
  := fun (A : Type) (B : Type) (P : Coproduct A B -> Prop)
         (left  : forall (a : A), P (Coproduct_introduction_left a))
         (right : forall (b : B), P (Coproduct_introduction_right b))
         (cp : Coproduct A B) =>
       match cp with
       | Coproduct_introduction_left  a => left  a
       | Coproduct_introduction_right b => right b
       end.

(* A module may carry the type's name; its members read [Coproduct.copair]. *)
Module Coproduct.

(* The two ctors under the names a use writes: [Coproduct.left a] and
 * [Coproduct.right b]. An abbreviation is the ctor itself, so it also
 * serves as a pattern; inside this module Rocq prints it as [left a].
 *)
Abbreviation left  := Coproduct_introduction_left.
Abbreviation right := Coproduct_introduction_right.
Abbreviation l     := Coproduct_introduction_left  (only parsing).
Abbreviation r     := Coproduct_introduction_right (only parsing).

(* [forall {A : Type} {B : Type} {C : Type}, (A -> C) -> (B -> C) -> Coproduct A B -> C] *)
Definition copair := fun {A : Type} {B : Type} {C : Type}
                         (f : A -> C) (g : B -> C) (cp : Coproduct A B) =>
  match cp return C with
  | Coproduct.left  a => f a
  | Coproduct.right b => g b
  end.

Theorem left_injectivity
  : forall (A : Type) (B : Type) (a1 : A) (a2 : A),
      (@Coproduct.left A B a1 = @Coproduct.left A B a2) -> (a1 = a2).
Proof.
  intros A B a1 a2 e.
  pose (f := fun (cp : Coproduct A B) =>
             match cp with | Coproduct.left x => x | Coproduct.right _ => a1 end).
  pose proof (Identity.congruence f e) as e'.
  simpl in e'.
  exact e'.
Qed.

Theorem right_injectivity
  : forall (A : Type) (B : Type) (b1 : B) (b2 : B),
      @Coproduct.right A B b1 = @Coproduct.right A B b2 -> b1 = b2.
Proof.
  intros A B b1 b2 e.
  pose (f := fun (cp : Coproduct A B) =>
             match cp with | Coproduct.left _ => b1 | Coproduct.right y => y end).
  pose proof (Identity.congruence f e) as e'.
  simpl in e'.
  exact e'.
Qed.

Theorem distinctness
  : forall (A : Type) (B : Type) (a : A) (b : B),
      ~ (Coproduct.left a = Coproduct.right b).
Proof.
  intros A B a b.
  unfold Negation in |- *.
  intro e.
  discriminate.
Qed.

(* [forall {A : Type} {B : Type}, Coproduct A B -> Coproduct B A] *)
Definition swap := fun {A : Type} {B : Type} (cp : Coproduct A B) =>
  match cp return Coproduct B A with
  | Coproduct.left  a => Coproduct.right a
  | Coproduct.right b => Coproduct.left  b
  end.

Theorem swap_involution
  : forall (A : Type) (B : Type) (cp : Coproduct A B), swap (swap cp) = cp.
Proof.
  intros A B cp.
  destruct cp as [a | b]; simpl in |- *; reflexivity.
Qed.

(* [forall {A : Type} {B : Type} {C : Type}, (A -> C) -> Coproduct A B -> Coproduct C B] *)
Definition map_left := fun {A : Type} {B : Type} {C : Type}
                           (f : A -> C) (cp : Coproduct A B) =>
  match cp return Coproduct C B with
  | Coproduct.left  a => Coproduct.left  (f a)
  | Coproduct.right b => Coproduct.right b
  end.

(* [forall {A : Type} {B : Type} {C : Type}, (B -> C) -> Coproduct A B -> Coproduct A C] *)
Definition map_right := fun {A : Type} {B : Type} {C : Type}
                            (f : B -> C) (cp : Coproduct A B) =>
  match cp return Coproduct A C with
  | Coproduct.left  a => Coproduct.left  a
  | Coproduct.right b => Coproduct.right (f b)
  end.

(* [forall {A : Type} {B : Type} {C : Type} {D : Type},
 *    (A -> C) -> (B -> D) -> Coproduct A B -> Coproduct C D]
 *)
Definition bimap := fun {A : Type} {B : Type} {C : Type} {D : Type}
                        (f : A -> C) (g : B -> D) (cp : Coproduct A B) =>
  match cp return Coproduct C D with
  | Coproduct.left  a => Coproduct.left  (f a)
  | Coproduct.right b => Coproduct.right (g b)
  end.

Theorem map_left_identity
  : forall (A : Type) (B : Type) (cp : Coproduct A B), map_left (fun (a : A) => a) cp = cp.
Proof.
  intros A B cp.
  destruct cp as [a | b]; simpl in |- *; reflexivity.
Qed.

Theorem map_left_composition
  : forall (A : Type) (B : Type) (C : Type) (D : Type) (f : A -> C) (g : C -> D)
      (cp : Coproduct A B),
      map_left g (map_left f cp) = map_left (fun (a : A) => g (f a)) cp.
Proof.
  intros A B C D f g cp.
  destruct cp as [a | b]; simpl in |- *; reflexivity.
Qed.

Theorem map_right_identity
  : forall (A : Type) (B : Type) (cp : Coproduct A B), map_right (fun (b : B) => b) cp = cp.
Proof.
  intros A B cp.
  destruct cp as [a | b]; simpl in |- *; reflexivity.
Qed.

Theorem map_right_composition
  : forall (A : Type) (B : Type) (C : Type) (D : Type) (f : B -> C) (g : C -> D)
      (cp : Coproduct A B),
      map_right g (map_right f cp) = map_right (fun (b : B) => g (f b)) cp.
Proof.
  intros A B C D f g cp.
  destruct cp as [a | b]; simpl in |- *; reflexivity.
Qed.

Theorem map_left_map_right_commutativity
  : forall (A : Type) (B : Type) (C : Type) (D : Type) (f : A -> C) (g : B -> D)
      (cp : Coproduct A B),
      map_left f (map_right g cp) = map_right g (map_left f cp).
Proof.
  intros A B C D f g cp.
  destruct cp as [a | b]; simpl in |- *; reflexivity.
Qed.

Theorem bimap_identity
  : forall (A : Type) (B : Type) (cp : Coproduct A B),
      bimap (fun (a : A) => a) (fun (b : B) => b) cp = cp.
Proof.
  intros A B cp.
  destruct cp as [a | b]; simpl in |- *; reflexivity.
Qed.

Theorem bimap_composition
  : forall (A : Type) (B : Type) (C : Type) (D : Type) (E : Type) (F : Type)
      (f1 : A -> C) (f2 : B -> D) (g1 : C -> E) (g2 : D -> F) (cp : Coproduct A B),
      bimap g1 g2 (bimap f1 f2 cp)
      = bimap (fun (a : A) => g1 (f1 a)) (fun (b : B) => g2 (f2 b)) cp.
Proof.
  intros A B C D E F f1 f2 g1 g2 cp.
  destruct cp as [a | b]; simpl in |- *; reflexivity.
Qed.

Theorem bimap_decomposition
  : forall (A : Type) (B : Type) (C : Type) (D : Type) (f : A -> C) (g : B -> D)
      (cp : Coproduct A B),
      bimap f g cp = map_left f (map_right g cp).
Proof.
  intros A B C D f g cp.
  destruct cp as [a | b]; simpl in |- *; reflexivity.
Qed.

Theorem copair_injections_identity
  : forall (A : Type) (B : Type) (cp : Coproduct A B),
      copair Coproduct.left Coproduct.right cp = cp.
Proof.
  intros A B cp.
  destruct cp as [a | b]; simpl in |- *; reflexivity.
Qed.

Theorem copair_naturality
  : forall (A : Type) (B : Type) (C : Type) (D : Type)
      (f : A -> C) (g : B -> C) (h : C -> D) (cp : Coproduct A B),
      h (copair f g cp) = copair (fun (a : A) => h (f a)) (fun (b : B) => h (g b)) cp.
Proof.
  intros A B C D f g h cp.
  destruct cp as [a | b]; simpl in |- *; reflexivity.
Qed.

End Coproduct.

Notation "A + B" := (Coproduct A B)
  : jwa_type_scope.

Instance Coproduct_functor
  : forall (A : Type), Functor (Coproduct A) :=
  fun (A : Type) =>
    {| Functor.map             := @Coproduct.map_right A
     ; Functor.map_identity    := Coproduct.map_right_identity A
     ; Functor.map_composition := Coproduct.map_right_composition A |}.

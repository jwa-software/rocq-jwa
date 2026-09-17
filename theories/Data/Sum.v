(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Core.All] carries [->] and [=]: with [-noinit] a file has only what it
   requires. [Structures.Functor] is the class the instance at the bottom
   fills. *)
From jwa Require Import Core.All.
From jwa Require Import Structures.Functor.

(* A sum holds one [A] or one [B], tagged by which. Both are parameters: the
   type behind each tag is fixed for the whole sum. The ctors are named as
   the [Disjunction] ctors are, since a sum is to types what [\/] is to
   propositions. *)
Inductive Sum (A : Type) (B : Type) : Type :=
  | Sum_left  : A -> Sum A B
  | Sum_right : B -> Sum A B.

(* One type is inferred from the value, the other from the expected type; a
   use that has neither needs [@Sum_left A B a]. *)
Arguments Sum_left  {A} {B} a.
Arguments Sum_right {A} {B} b.

(* The eliminator behind [induction], written out. Nothing recurses: a sum
   holds no smaller sum, so one [match] is the whole content. *)
Definition Sum_induction
  : forall (A : Type) (B : Type) (P : Sum A B -> Prop),
      (forall (a : A), P (Sum_left a)) ->
      (forall (b : B), P (Sum_right b)) ->
      forall (s : Sum A B), P s
  := fun (A : Type) (B : Type) (P : Sum A B -> Prop)
         (left  : forall (a : A), P (Sum_left a))
         (right : forall (b : B), P (Sum_right b))
         (s : Sum A B) =>
       match s with
       | Sum_left a  => left a
       | Sum_right b => right b
       end.

(* A module may carry the type's name; its members read [Sum.copair]. *)
Module Sum.

(* [forall {A : Type} {B : Type} {C : Type}, (A -> C) -> (B -> C) -> Sum A B -> C]
   The copairing of [f] and [g]: whichever side the sum holds is handed to
   the function for that side. *)
Definition copair := fun {A : Type} {B : Type} {C : Type}
                         (f : A -> C) (g : B -> C) (s : Sum A B) =>
  match s return C with
  | Sum_left a  => f a
  | Sum_right b => g b
  end.

(* Each ctor is injective: a function that unwraps it, applied to both
   sides of the equation, computes to the equation between the payloads.
   The other branch of the unwrapping function never fires; it returns the
   left payload only to have a value of the right type. *)

Theorem left_injectivity
  : forall (A : Type) (B : Type) (a1 : A) (a2 : A),
      @Sum_left A B a1 = Sum_left a2 -> a1 = a2.
Proof.
  (* The context gains [A], [B], [a1], [a2] and [e : Sum_left a1 = Sum_left a2]:
     [|- a1 = a2] *)
  intros A B a1 a2 e.
  (* The context gains
     [e' : (fun s => match s with | Sum_left x => x | Sum_right _ => a1 end)
             (Sum_left a1)
         = (fun s => match s with | Sum_left x => x | Sum_right _ => a1 end)
             (Sum_left a2)]. *)
  pose proof (Equijunction_congruence
                (fun (s : Sum A B) =>
                   match s with | Sum_left x => x | Sum_right _ => a1 end)
                e) as e'.
  (* Both applications compute: [e' : a1 = a2] *)
  simpl in e'.
  (* [e'] is a proof of the goal as it stands. *)
  exact e'.
Qed.

Theorem right_injectivity
  : forall (A : Type) (B : Type) (b1 : B) (b2 : B),
      @Sum_right A B b1 = Sum_right b2 -> b1 = b2.
Proof.
  (* The context gains [A], [B], [b1], [b2] and
     [e : Sum_right b1 = Sum_right b2]: [|- b1 = b2] *)
  intros A B b1 b2 e.
  (* The context gains
     [e' : (fun s => match s with | Sum_left _ => b1 | Sum_right y => y end)
             (Sum_right b1)
         = (fun s => match s with | Sum_left _ => b1 | Sum_right y => y end)
             (Sum_right b2)]. *)
  pose proof (Equijunction_congruence
                (fun (s : Sum A B) =>
                   match s with | Sum_left _ => b1 | Sum_right y => y end)
                e) as e'.
  (* Both applications compute: [e' : b1 = b2] *)
  simpl in e'.
  (* [e'] is a proof of the goal as it stands. *)
  exact e'.
Qed.

(* The two ctors never meet: a sum remembers which side it holds. *)
Theorem left_right_distinctness
  : forall (A : Type) (B : Type) (a : A) (b : B), ~ (Sum_left a = Sum_right b).
Proof.
  (* The context gains [A], [B], [a] and [b]: [|- ~ (Sum_left a = Sum_right b)] *)
  intros A B a b.
  (* [|- Sum_left a = Sum_right b -> Falsum] *)
  unfold Unjunction in |- *.
  (* The context gains [e : Sum_left a = Sum_right b]: [|- Falsum] *)
  intro e.
  (* [e] equates two distinct ctors, which closes any goal. *)
  discriminate.
Qed.

(* [forall {A : Type} {B : Type}, Sum A B -> Sum B A] *)
Definition swap := fun {A : Type} {B : Type} (s : Sum A B) =>
  match s return Sum B A with
  | Sum_left a  => Sum_right a
  | Sum_right b => Sum_left b
  end.

Theorem swap_involution
  : forall (A : Type) (B : Type) (s : Sum A B), swap (swap s) = s.
Proof.
  (* The context gains [A], [B] and [s]: [|- swap (swap s) = s] *)
  intros A B s.
  (* [s] is either [Sum_left a] or [Sum_right b]: one goal per ctor, the
     first with [a : A] and the second with [b : B] in its context. *)
  destruct s as [a | b].
  - (* [|- swap (swap (Sum_left a)) = Sum_left a] *)
    (* Both [swap]s compute: [|- Sum_left a = Sum_left a] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
  - (* [|- swap (swap (Sum_right b)) = Sum_right b] *)
    (* Both [swap]s compute: [|- Sum_right b = Sum_right b] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
Qed.

(* [forall {A : Type} {B : Type} {C : Type}, (A -> C) -> Sum A B -> Sum C B] *)
Definition map_left := fun {A : Type} {B : Type} {C : Type}
                           (f : A -> C) (s : Sum A B) =>
  match s return Sum C B with
  | Sum_left a  => Sum_left (f a)
  | Sum_right b => Sum_right b
  end.

(* [forall {A : Type} {B : Type} {C : Type}, (B -> C) -> Sum A B -> Sum A C] *)
Definition map_right := fun {A : Type} {B : Type} {C : Type}
                            (f : B -> C) (s : Sum A B) =>
  match s return Sum A C with
  | Sum_left a  => Sum_left a
  | Sum_right b => Sum_right (f b)
  end.

(* [forall {A : Type} {B : Type} {C : Type} {D : Type},
     (A -> C) -> (B -> D) -> Sum A B -> Sum C D] *)
Definition bimap := fun {A : Type} {B : Type} {C : Type} {D : Type}
                        (f : A -> C) (g : B -> D) (s : Sum A B) =>
  match s return Sum C D with
  | Sum_left a  => Sum_left (f a)
  | Sum_right b => Sum_right (g b)
  end.

(* The functor laws for each side and for both at once: the map preserves
   the identity function and preserves composition. Stated for every [s]
   rather than as an equality between functions, since nothing here assumes
   functional extensionality. Every proof splits on the ctor, and on each
   side the maps compute to the same term. *)

Theorem map_left_identity
  : forall (A : Type) (B : Type) (s : Sum A B), map_left (fun (a : A) => a) s = s.
Proof.
  (* The context gains [A], [B] and [s]: [|- map_left (fun a => a) s = s] *)
  intros A B s.
  (* One goal per ctor, with [a : A] or [b : B] in its context. *)
  destruct s as [a | b].
  - (* [map_left] computes and [(fun a => a) a] reduces to [a]:
       [|- Sum_left a = Sum_left a] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
  - (* [map_left] leaves the right side alone: [|- Sum_right b = Sum_right b] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
Qed.

Theorem map_left_composition
  : forall (A : Type) (B : Type) (C : Type) (D : Type) (f : A -> C) (g : C -> D)
      (s : Sum A B),
      map_left g (map_left f s) = map_left (fun (a : A) => g (f a)) s.
Proof.
  (* The context gains [A], [B], [C], [D], [f], [g] and [s]:
     [|- map_left g (map_left f s) = map_left (fun a => g (f a)) s] *)
  intros A B C D f g s.
  (* One goal per ctor, with [a : A] or [b : B] in its context. *)
  destruct s as [a | b].
  - (* The left side computes in two steps to [Sum_left (g (f a))], the
       right side in one step to the same:
       [|- Sum_left (g (f a)) = Sum_left (g (f a))] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
  - (* Every [map_left] leaves the right side alone:
       [|- Sum_right b = Sum_right b] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
Qed.

Theorem map_right_identity
  : forall (A : Type) (B : Type) (s : Sum A B), map_right (fun (b : B) => b) s = s.
Proof.
  (* The context gains [A], [B] and [s]: [|- map_right (fun b => b) s = s] *)
  intros A B s.
  (* One goal per ctor, with [a : A] or [b : B] in its context. *)
  destruct s as [a | b].
  - (* [map_right] leaves the left side alone: [|- Sum_left a = Sum_left a] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
  - (* [map_right] computes and [(fun b => b) b] reduces to [b]:
       [|- Sum_right b = Sum_right b] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
Qed.

Theorem map_right_composition
  : forall (A : Type) (B : Type) (C : Type) (D : Type) (f : B -> C) (g : C -> D)
      (s : Sum A B),
      map_right g (map_right f s) = map_right (fun (b : B) => g (f b)) s.
Proof.
  (* The context gains [A], [B], [C], [D], [f], [g] and [s]:
     [|- map_right g (map_right f s) = map_right (fun b => g (f b)) s] *)
  intros A B C D f g s.
  (* One goal per ctor, with [a : A] or [b : B] in its context. *)
  destruct s as [a | b].
  - (* Every [map_right] leaves the left side alone:
       [|- Sum_left a = Sum_left a] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
  - (* The left side computes in two steps to [Sum_right (g (f b))], the
       right side in one step to the same:
       [|- Sum_right (g (f b)) = Sum_right (g (f b))] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
Qed.

(* The two maps touch different sides, so their order does not matter. *)
Theorem map_left_map_right_commutativity
  : forall (A : Type) (B : Type) (C : Type) (D : Type) (f : A -> C) (g : B -> D)
      (s : Sum A B),
      map_left f (map_right g s) = map_right g (map_left f s).
Proof.
  (* The context gains [A], [B], [C], [D], [f], [g] and [s]:
     [|- map_left f (map_right g s) = map_right g (map_left f s)] *)
  intros A B C D f g s.
  (* One goal per ctor, with [a : A] or [b : B] in its context. *)
  destruct s as [a | b].
  - (* Both sides compute in two steps to the same sum:
       [|- Sum_left (f a) = Sum_left (f a)] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
  - (* Both sides compute in two steps to the same sum:
       [|- Sum_right (g b) = Sum_right (g b)] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
Qed.

Theorem bimap_identity
  : forall (A : Type) (B : Type) (s : Sum A B),
      bimap (fun (a : A) => a) (fun (b : B) => b) s = s.
Proof.
  (* The context gains [A], [B] and [s]:
     [|- bimap (fun a => a) (fun b => b) s = s] *)
  intros A B s.
  (* One goal per ctor, with [a : A] or [b : B] in its context. *)
  destruct s as [a | b].
  - (* [bimap] computes and the identity reduces: [|- Sum_left a = Sum_left a] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
  - (* [bimap] computes and the identity reduces:
       [|- Sum_right b = Sum_right b] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
Qed.

Theorem bimap_composition
  : forall (A : Type) (B : Type) (C : Type) (D : Type) (E : Type) (F : Type)
      (f1 : A -> C) (f2 : B -> D) (g1 : C -> E) (g2 : D -> F) (s : Sum A B),
      bimap g1 g2 (bimap f1 f2 s)
      = bimap (fun (a : A) => g1 (f1 a)) (fun (b : B) => g2 (f2 b)) s.
Proof.
  (* The context gains the six types, [f1], [f2], [g1], [g2] and [s]:
     [|- bimap g1 g2 (bimap f1 f2 s)
         = bimap (fun a => g1 (f1 a)) (fun b => g2 (f2 b)) s] *)
  intros A B C D E F f1 f2 g1 g2 s.
  (* One goal per ctor, with [a : A] or [b : B] in its context. *)
  destruct s as [a | b].
  - (* The left side computes in two [bimap] steps to [Sum_left (g1 (f1 a))],
       the right side in one step to the same:
       [|- Sum_left (g1 (f1 a)) = Sum_left (g1 (f1 a))] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
  - (* Likewise on the right side:
       [|- Sum_right (g2 (f2 b)) = Sum_right (g2 (f2 b))] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
Qed.

Theorem bimap_decomposition
  : forall (A : Type) (B : Type) (C : Type) (D : Type) (f : A -> C) (g : B -> D)
      (s : Sum A B),
      bimap f g s = map_left f (map_right g s).
Proof.
  (* The context gains [A], [B], [C], [D], [f], [g] and [s]:
     [|- bimap f g s = map_left f (map_right g s)] *)
  intros A B C D f g s.
  (* One goal per ctor, with [a : A] or [b : B] in its context. *)
  destruct s as [a | b].
  - (* The left side computes in one step, the right side in two, to the
       same sum: [|- Sum_left (f a) = Sum_left (f a)] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
  - (* Likewise on the right side: [|- Sum_right (g b) = Sum_right (g b)] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
Qed.

(* Copairing the two ctors rebuilds the sum: [copair] applied to the
   injections is the identity. *)
Theorem copair_injections_identity
  : forall (A : Type) (B : Type) (s : Sum A B), copair Sum_left Sum_right s = s.
Proof.
  (* The context gains [A], [B] and [s]: [|- copair Sum_left Sum_right s = s] *)
  intros A B s.
  (* One goal per ctor, with [a : A] or [b : B] in its context. *)
  destruct s as [a | b].
  - (* [copair] hands [a] to [Sum_left]: [|- Sum_left a = Sum_left a] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
  - (* [copair] hands [b] to [Sum_right]: [|- Sum_right b = Sum_right b] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
Qed.

(* A function applied after a copairing moves inside both branches. *)
Theorem copair_naturality
  : forall (A : Type) (B : Type) (C : Type) (D : Type)
      (f : A -> C) (g : B -> C) (h : C -> D) (s : Sum A B),
      h (copair f g s) = copair (fun (a : A) => h (f a)) (fun (b : B) => h (g b)) s.
Proof.
  (* The context gains [A], [B], [C], [D], [f], [g], [h] and [s]:
     [|- h (copair f g s) = copair (fun a => h (f a)) (fun b => h (g b)) s] *)
  intros A B C D f g h s.
  (* One goal per ctor, with [a : A] or [b : B] in its context. *)
  destruct s as [a | b].
  - (* Both [copair]s compute: [|- h (f a) = h (f a)] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
  - (* Both [copair]s compute: [|- h (g b) = h (g b)] *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
Qed.

End Sum.

(* The level is reserved in [Core.Notations]; only the meaning belongs here.
   Declared at file level, it reaches a client through [Require Export]. A
   type former sits in [jwa_type_scope] beside [->], so [A + B -> C] needs
   no delimiter. *)
Notation "A + B" := (Sum A B) : jwa_type_scope.

(* [Sum A] is a functor in its right side; [A] is a parameter of the
   instance, so every left side gets one. The two laws were already proved
   above, so the instance only hands them over, applied to [A].
   [map_right]'s type arguments are maximally inserted, so the bare name
   collapses to one fixed triple of them; binding [B] and [C] first is what
   keeps it general enough for the field, as in [Data.Pair]. *)
Instance Sum_functor : forall (A : Type), Functor.T (Sum A) :=
  fun (A : Type) =>
    {| Functor.map             := fun (B : Type) (C : Type) => Sum.map_right
     ; Functor.map_identity    := Sum.map_right_identity A
     ; Functor.map_composition := Sum.map_right_composition A |}.

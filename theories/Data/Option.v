(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Core.All] carries [->]: with [-noinit] a file has only what it requires.
   [Structures.Functor] is the class the instance at the bottom fills. *)
From jwa Require Import Core.All.
From jwa Require Import Structures.Functor.

Inductive Option (A : Type) : Type :=
  | None : Option A
  | Some : A -> Option A.

Arguments None {A}.
Arguments Some {A} a.

(* A module may carry the type's name; its members read [Option.map]. *)
Module Option.

(* [forall {A : Type} {B : Type}, (A -> B) -> Option A -> Option B] *)
Definition map := fun {A : Type} {B : Type} (f : A -> B) (o : Option A) =>
  match o return Option B
  with
  | None   => None
  | Some a => Some (f a)
  end.

(* The two functor laws: [map] preserves the identity function and preserves
   composition. Stated for every [o] rather than as an equality between
   functions, since nothing here assumes functional extensionality. *)

Theorem map_identity
  : forall (A : Type) (o : Option A), map (fun a => a) o = o.
Proof.
  (* The context gains [A : Type] and [o : Option A]; the goal is now
     [map (fun a => a) o = o]. *)
  intros A o.
  (* [o] is either [None] or [Some a]: one goal per ctor, and the second
     one has [a : A] in its context. *)
  destruct o as [| a].
  - (* [unfold map in |- *] replaces every occurrence of [map] in the goal
       ([|- *]) by the definition of [map], here the single one: the goal
       goes from [map (fun a => a) None = None] to a [match] on [None]. *)
    unfold map in |- *.
    (* The [match] on the ctor [None] reduces; the goal is now
       [None = None]. *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
  - (* The goal goes from [map (fun a => a) (Some a) = Some a] to a [match]
       on [Some a]. *)
    unfold map in |- *.
    (* The [match] reduces and [(fun a => a) a] reduces to [a]; the goal is
       now [Some a = Some a]. *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
Qed.

Theorem map_composition
  : forall (A : Type) (B : Type) (C : Type) (f : A -> B) (g : B -> C)
      (o : Option A),
    map g (map f o) = map (fun a => g (f a)) o.
Proof.
  (* The context gains [A], [B], [C], [f], [g] and [o]; the goal is now
     [map g (map f o) = map (fun a => g (f a)) o]. *)
  intros A B C f g o.
  (* [o] is either [None] or [Some a]: one goal per ctor, and the second
     one has [a : A] in its context. *)
  destruct o as [| a].
  - (* All three [map]s compute on [None], as spelled out in [map_identity];
       the goal is now [None = None]. *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
  - (* The left side computes in two [map] steps to [Some (g (f a))], the
       right side in one step to the same; the goal is now
       [Some (g (f a)) = Some (g (f a))]. *)
    simpl in |- *.
    (* Both sides are the same term. *)
    reflexivity.
Qed.

End Option.

(* The two laws were already proved above, so the instance only hands them
   over. [map]'s type arguments are maximally inserted, so the bare name
   collapses to one fixed pair of them; binding [A] and [B] first is what
   keeps it general enough for the field. *)
Instance Option_functor : Functor.T Option :=
  {| Functor.map             := fun (A : Type) (B : Type) => Option.map
   ; Functor.map_identity    := Option.map_identity
   ; Functor.map_composition := Option.map_composition |}.

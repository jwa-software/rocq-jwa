(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Core.All] carries [->]: with [-noinit] a file has only what it requires. *)
From jwa Require Import Core.All.

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
    simpl.
    (* Both sides are the same term. *)
    reflexivity.
  - (* The goal goes from [map (fun a => a) (Some a) = Some a] to a [match]
       on [Some a]. *)
    unfold map in |- *.
    (* The [match] reduces and [(fun a => a) a] reduces to [a]; the goal is
       now [Some a = Some a]. *)
    simpl.
    (* Both sides are the same term. *)
    reflexivity.
Qed.
End Option.

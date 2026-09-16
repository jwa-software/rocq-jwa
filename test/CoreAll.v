(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* Guards [Core.All], imported alone. One name from each module it forwards:
   the scope from [Core.Notations], the connectives from [Core.Logic.All],
   [=] from [Core.Eq]. *)
From jwa Require Import Core.All.

Definition core_all_delivers
  : forall (A : Prop) (B : Prop),
      A /\ B -> B \/ A -> (A <-> B) -> ~ False -> True
  := fun (A : Prop) (B : Prop)
         (_ : A /\ B) (_ : B \/ A)
         (_ : A <-> B)
         (_ : ~ False) => I.

(* [Core.Ltac] is the fourth module, and the only one no type can name:
   without it [Proof] does not parse. *)
Theorem core_all_delivers_proof_mode : forall (A : Type) (x : A), x = x.
Proof.
  (* The context gains [A] and [x]: [|- x = x] *)
  intros A x.
  (* Both sides are the same term. *)
  reflexivity.
Qed.

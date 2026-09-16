(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* Guards [Core.All], imported alone. One name from each module it forwards:
   the scope from [Core.Notations], the connectives from [Core.Logic.All],
   [=] from [Core.Eq], the two ctors from [Core.Bool]. *)
From jwa Require Import Core.All.

Definition core_all_delivers
  : forall (A : Prop) (B : Prop),
      A /\ B -> B \/ A -> (A <-> B) -> False -> ~ (true = false) -> True
  := fun (A : Prop) (B : Prop)
         (_ : A /\ B) (_ : B \/ A)
         (_ : A <-> B)
         (_ : False)
         (_ : ~ (true = false)) => I.

(* [Core.Ltac] is the fifth module, and the only one no type can name:
   without it [Proof] does not parse. *)
Theorem core_all_delivers_proof_mode : forall (b : Bool), b = b.
Proof.
  (* The context gains [b : Bool]; the goal is now [b = b]. *)
  intro b.
  (* Both sides are the same term. *)
  reflexivity.
Qed.

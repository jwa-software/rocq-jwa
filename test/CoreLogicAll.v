(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* Guards [Core.Logic.All], imported alone. The umbrella carries no tactic
   language, so everything below is a term. *)
From jwa Require Import Core.Logic.All.

Definition core_logic_all_delivers
  : forall (A : Prop) (B : Prop),
      A /\ B -> B \/ A -> ~ A -> (A <-> B) -> False -> True
  := fun (A : Prop) (B : Prop)
         (_ : A /\ B) (_ : B \/ A)
         (_ : ~ A) (_ : A <-> B)
         (_ : False) => I.

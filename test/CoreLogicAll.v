(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* Guards [Core.Logic.All], imported alone. The umbrella carries no tactic
   language, so everything below is a term. *)
From jwa Require Import Core.Logic.All.

Definition core_logic_all_delivers
  : forall (A : Prop) (B : Prop) (T : Type) (Q : T -> Prop),
      A /\ B -> B \/ A -> A _\/_ B -> ~ A -> (A <-> B) -> (exists t, Q t)
      -> False -> True
  := fun (A : Prop) (B : Prop) (T : Type) (Q : T -> Prop)
         (_ : A /\ B) (_ : B \/ A) (_ : A _\/_ B)
         (_ : ~ A) (_ : A <-> B)
         (_ : exists t, Q t)
         (_ : False) => I.

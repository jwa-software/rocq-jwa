(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.Logic.All.

Definition core_logic_all_delivers
  : forall (A : Prop) (B : Prop) (T : Type) (Q : T -> Prop) .
      A /\ B -> B \/ A -> A _\/_ B -> ~ A -> (A <-> B) -> A -/> B
      -> (exists t . Q t) -> Falsum -> Verum
  := fun (A : Prop) (B : Prop) (T : Type) (Q : T -> Prop)
         (_ : A /\ B) (_ : B \/ A) (_ : A _\/_ B)
         (_ : ~ A) (_ : A <-> B) (_ : A -/> B)
         (_ : exists t . Q t)
         (_ : Falsum) => I.

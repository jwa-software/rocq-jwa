(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.

Definition core_all_delivers
  : forall (A : Prop) (B : Prop) .
      A /\ B -> B \/ A -> (A <-> B) -> ~ Falsum -> Verum
  := fun (A : Prop) (B : Prop)
         (_ : A /\ B) (_ : B \/ A)
         (_ : A <-> B)
         (_ : ~ Falsum) . I.

Theorem core_all_delivers_proof_mode
  : forall (A : Type) (x : A) . x = x.
Proof.
  intros A x.
  reflexivity.
Qed.

Definition core_all_delivers_identity_hedberg_uniqueness
  : forall (A : Type) .
      (forall (x : A) (y : A) . x = y \/ ~ (x = y))
      -> forall (x : A) (y : A) (p : x = y) (q : x = y) . p = q
  := fun (A : Type) . @Identity.hedberg.uniqueness A.

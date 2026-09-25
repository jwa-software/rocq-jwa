(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Dialect.All.

Theorem dialect_all_delivers
  : forall (A : Prop) (B : Prop) (_ : (fun (X : Prop) => X) A) (_ : B), A.
Proof.
  intros A B a b.
  rm &b.
  simpl in &a.
  mv &a c.
  lemma d : &A.
  {
    ipso &c.
  }
  extro &d.
  intro d.
  let proof e := &d.
  ipso &e.
Qed.

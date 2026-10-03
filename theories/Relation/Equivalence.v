(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Core.Class.
From jwa Require Import Relation.Reflexive.
From jwa Require Import Relation.Symmetric.
From jwa Require Import Relation.Transitive.

Module Equivalence. (* Equivalence *)

Class T {A : Type} (R : A -> A -> Prop) : Prop :=
  { reflexivity  :: Reflexive  R
  ; symmetry     :: Symmetric  R
  ; transitivity :: Transitive R }.

Abbreviation Equivalence := T.

End Equivalence. (* Equivalence *)

Abbreviation Equivalence := Equivalence.T.

(* A [::] field is an instance only where its module is imported;
 * these lines make each one an instance wherever this file is.
 *)
#[export] Existing Instance Equivalence.reflexivity.
#[export] Existing Instance Equivalence.symmetry.
#[export] Existing Instance Equivalence.transitivity.

(* The instances for the two relations of [Core] sit here and not beside
 * them, since [Core] sees no class. Each field is the matching theorem of
 * [Core].
 *)

Instance Biconditional_equivalence
  : Equivalence Biconditional :=
  {| Equivalence.reflexivity :=
       {| Reflexive.reflexivity := Biconditional.reflexivity |}
   ; Equivalence.symmetry :=
       {| Symmetric.symmetry := @Biconditional.symmetry |}
   ; Equivalence.transitivity :=
       {| Transitive.transitivity := @Biconditional.transitivity |} |}.

Instance Identity_equivalence
  : forall (A : Type) . Equivalence (@Identity A) :=
  fun (A : Type) .
    ({| Equivalence.reflexivity :=
          {| Reflexive.reflexivity := @Identity.reflexivity A |}
      ; Equivalence.symmetry :=
          {| Symmetric.symmetry := @Identity.symmetry A |}
      ; Equivalence.transitivity :=
          {| Transitive.transitivity := @Identity.transitivity A |} |}).

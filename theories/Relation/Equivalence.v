(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Relation.Reflexive.
From jwa Require Import Relation.Symmetric.
From jwa Require Import Relation.Transitive.
From jwa Require Import Structures.Class.

Class Equivalence {A : Type} (R : A -> A -> Prop) : Prop :=
  { reflexivity  :: Reflexive  R
  ; symmetry     :: Symmetric  R
  ; transitivity :: Transitive R }.

(* The instances for the two relations of [Core] sit here and not beside
 * them, since [Core] sees no class. Each field is the matching theorem of
 * [Core].
 *)

Instance Biimplication_equivalence
  : Equivalence Biimplication :=
  {| Equivalence.reflexivity :=
       {| Reflexive.reflexivity := Biimplication.reflexivity |}
   ; Equivalence.symmetry :=
       {| Symmetric.symmetry := Biimplication.symmetry |}
   ; Equivalence.transitivity :=
       {| Transitive.transitivity := Biimplication.transitivity |} |}.

Instance Identity_equivalence
  : forall (A : Type), Equivalence (@Identity A) :=
  fun (A : Type) =>
    {| Equivalence.reflexivity :=
         {| Reflexive.reflexivity := @Identity.reflexivity A |}
     ; Equivalence.symmetry :=
         {| Symmetric.symmetry := @Identity.symmetry A |}
     ; Equivalence.transitivity :=
         {| Transitive.transitivity := @Identity.transitivity A |} |}.

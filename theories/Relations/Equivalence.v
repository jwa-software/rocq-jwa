(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [Relations.All] would be circular from inside [Relations]; [Core.All]
   carries [->], [<->] and [=] with the three laws of each,
   [Structures.Class] the hint database, and the three modules below the
   classes this one is built on. *)
From jwa Require Import Core.All.
From jwa Require Import Structures.Class.
From jwa Require Import Relations.Reflexive.
From jwa Require Import Relations.Symmetric.
From jwa Require Import Relations.Transitive.

(* The module is the prefix: the class reads [Equivalence.R] and its
   fields [Equivalence.reflexive] and so on. *)
Module Equivalence.
  (* The three properties together. The [::] on each field declares it an
     instance as well as a projection, which is what lets an
     [Equivalence.R] be used wherever a [Reflexive.R], a
     [Symmetric.R] or a [Transitive.R] is asked for. *)
  Class R (A : Type) (relation : A -> A -> Prop) : Prop :=
    { reflexive  :: Reflexive.R A relation
    ; symmetric  :: Symmetric.R A relation
    ; transitive :: Transitive.R A relation }.
End Equivalence.

(* The instance hints that [::] declares are scoped to the module they are
   declared in; this lets them out while the names stay qualified. Without
   it [Reflexive.R A R] is not found from an [Equivalence.R A R]
   outside the module. *)
Export (hints) Equivalence.

(* The instances for the two relations of [Core] sit here and not beside
   them, since [Core] sees no class. Each field is the matching theorem of
   [Core]. *)

Instance Biconditional_equivalence : Equivalence.R Prop Biconditional :=
  {| Equivalence.reflexive :=
       {| Reflexive.reflexivity := Biconditional_reflexivity |}
   ; Equivalence.symmetric :=
       {| Symmetric.symmetry := Biconditional_symmetry |}
   ; Equivalence.transitive :=
       {| Transitive.transitivity := Biconditional_transitivity |} |}.

(* [@] makes [A] explicit, which the field types need since [R] is applied
   to two elements of [A] and nothing else. *)
Instance Eq_equivalence : forall (A : Type), Equivalence.R A (@Eq A) :=
  fun (A : Type) =>
    {| Equivalence.reflexive :=
         {| Reflexive.reflexivity := @Eq_reflexivity A |}
     ; Equivalence.symmetric :=
         {| Symmetric.symmetry := @Eq_symmetry A |}
     ; Equivalence.transitive :=
         {| Transitive.transitivity := @Eq_transitivity A |} |}.

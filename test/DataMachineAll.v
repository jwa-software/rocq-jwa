(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Data.Machine.All.

Definition data_machine_all_delivers_bit
  : Bit
  := Bit.One.

Definition data_machine_all_delivers_bit_notation
  : forall (b1 : Bit) (b2 : Bit) . (b1 && b2)%bit = (b2 && b1)%bit
  := Bit.conjunction.commutativity.

Definition data_machine_all_binds_bit_scope
  : forall (b : Bit) . Bit.negate (! b) = b
  := Bit.negation.involution.

Definition data_machine_all_delivers_bit_distinctness
  : ~ (Bit.Zero = Bit.One) /\ ~ (Bit.One = Bit.Zero)
  := Bit.distinctness.

Definition data_machine_all_delivers_bit_conversion_retraction
  : forall (b : Bool) . Bit.to_bool (Bit.from_bool b) = b
  := Bit.conversion.retraction.

Definition data_machine_all_delivers_bit_conversion_section
  : forall (b : Bit) . Bit.from_bool (Bit.to_bool b) = b
  := Bit.conversion.section.

Definition data_machine_all_computes_bit_xor
  : (Bit.One ^^ Bit.One)%bit = Bit.Zero
  := Identity.reflexivity Bit.Zero.

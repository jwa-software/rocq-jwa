(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Data.Machine.All.

Definition data_machine_all_delivers_bit
  : Bit
  := Bit.One.

Definition data_machine_all_delivers_bit_notation
  : forall (b1 : Bit) (b2 : Bit) . (b1 && b2)%bit = (b2 && b1)%bit
  := Bit.conjunction.commutativity.

Definition data_machine_all_binds_bit_scope
  : forall (b : Bit) . Bit.flip (~. b) = b
  := Bit.flipping.involution.

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

Definition data_machine_all_delivers_byte
  : Byte
  := Byte.Zero.

Definition data_machine_all_delivers_byte_notation
  : forall (x : Byte) (y : Byte) . (x && y)%byte = (y && x)%byte
  := Byte.conjunction.commutativity.

Definition data_machine_all_binds_byte_scope
  : forall (x : Byte) . Byte.flip (~. x) = x
  := Byte.flipping.involution.

Definition data_machine_all_delivers_byte_rotation_inverse
  : forall (x : Byte) (k : Nat0) . Byte.rotate_right (Byte.rotate_left x k) k = x
  := Byte.rotation.left.inverse.

Definition data_machine_all_computes_byte_shift_right
  : Byte.shift_right (Byte.flip Byte.Zero) 3%n0
      = Byte.Byte_introduction
          Bit.Zero Bit.Zero Bit.Zero Bit.One Bit.One Bit.One Bit.One Bit.One
  := Identity.reflexivity _.

Definition data_machine_all_computes_byte_rotate_left
  : Byte.rotate_left
      (Byte.Byte_introduction
        Bit.One Bit.Zero Bit.Zero Bit.Zero Bit.Zero Bit.Zero Bit.Zero Bit.One)
      1%n0
      = Byte.Byte_introduction
          Bit.Zero Bit.Zero Bit.Zero Bit.Zero Bit.Zero Bit.Zero Bit.One Bit.One
  := Identity.reflexivity _.

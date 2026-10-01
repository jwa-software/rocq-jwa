(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Data.Machine.All.

Definition data_machine_all_delivers_bit
  : Bit
  := Bit.One.

Definition data_machine_all_delivers_bit_notation
  : forall (b1 : Bit) (b2 : Bit) . (b1 &. b2)%bit = (b2 &. b1)%bit
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
  : (Bit.One ^. Bit.One)%bit = Bit.Zero
  := Identity.reflexivity Bit.Zero.

Definition data_machine_all_delivers_byte
  : Byte
  := Byte.Zero.

Definition data_machine_all_delivers_byte_notation
  : forall (x : Byte) (y : Byte) . (x &. y)%byte = (y &. x)%byte
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

Definition data_machine_all_delivers_bit_carry
  : forall (carry : Bit) (a : Bit) (b : Bit) .
      (Bit.to_nat0 carry + Bit.to_nat0 a + Bit.to_nat0 b
        = 2 * Bit.to_nat0 (pi_1 (Bit.add_with_carry carry a b))%product
          + Bit.to_nat0 (pi_2 (Bit.add_with_carry carry a b))%product)%n0
  := Bit.conversion.carry.

Definition data_machine_all_delivers_byte_carry
  : forall (carry : Bit) (x : Byte) (y : Byte) .
      (Bit.to_nat0 carry + Byte.to_nat0 x + Byte.to_nat0 y
        = 256 * Bit.to_nat0 (pi_1 (Byte.add_with_carry carry x y))%product
          + Byte.to_nat0 (pi_2 (Byte.add_with_carry carry x y))%product)%n0
  := Byte.conversion.carry.

Definition data_machine_all_delivers_byte_addition
  : forall (x : Byte) (y : Byte) .
      Byte.to_nat0 (x + y)%byte = ((Byte.to_nat0 x + Byte.to_nat0 y) %. 256)%n0
  := Byte.conversion.addition.

Definition data_machine_all_delivers_byte_multiplication
  : forall (x : Byte) (y : Byte) .
      Byte.to_nat0 (x * y)%byte = ((Byte.to_nat0 x * Byte.to_nat0 y) %. 256)%n0
  := Byte.conversion.multiplication.

Definition data_machine_all_delivers_byte_negation
  : forall (x : Byte) . ((Byte.to_nat0 (- x)%byte + Byte.to_nat0 x) %. 256 = 0)%n0
  := Byte.conversion.negation.

Definition data_machine_all_delivers_byte_left_shift
  : forall (x : Byte) (k : Nat0) .
      Byte.to_nat0 (Byte.shift_left x k) = ((Byte.to_nat0 x * 2 ^ k) %. 256)%n0
  := Byte.conversion.left.shift.

Definition data_machine_all_delivers_byte_distributivity
  : forall (x : Byte) (y : Byte) (z : Byte) .
      (x * (y + z) = (x * y) + (x * z) /\ (y + z) * x = (y * x) + (z * x))%byte
  := Byte.multiplication.distributivity.over.addition.

Definition data_machine_all_computes_byte_reduction
  : Byte.to_nat0 (Byte.from_nat0 300%n0) = 44%n0
  := Identity.reflexivity _.

Definition data_machine_all_computes_byte_multiplication
  : Byte.to_nat0 (Byte.from_nat0 20%n0 * Byte.from_nat0 13%n0)%byte = 4%n0
  := Identity.reflexivity _.

Definition data_machine_all_computes_byte_negation
  : Byte.to_nat0 (- Byte.One)%byte = 255%n0
  := Identity.reflexivity _.

Definition data_machine_all_computes_byte_carry_out
  : (pi_1 (Byte.add_with_carry Bit.Zero (Byte.flip Byte.Zero) Byte.One))%product = Bit.One
  := Identity.reflexivity _.

Definition data_machine_all_computes_byte_comparison
  : Byte.compare Byte.Zero Byte.One = Comparison.Lt
  := Identity.reflexivity _.

Definition data_machine_all_reads_bit_literal
  : Bit.xor 1 1 = 0%bit
  := Identity.reflexivity _.

Fail Definition data_machine_all_refuses_bit_literal_two
  : Bit
  := 2%bit.

Definition data_machine_all_reads_byte_literal
  : Byte.to_nat0 200%byte = 200%n0
  := Identity.reflexivity _.

Definition data_machine_all_reads_byte_literal_hexadecimal
  : 0xFF%byte = Byte.flip Byte.Zero
  := Identity.reflexivity _.

Definition data_machine_all_reads_byte_literal_zero
  : 0%byte = Byte.Zero
  := Identity.reflexivity _.

Definition data_machine_all_reads_byte_literal_arithmetic
  : (100 + 200 = 44)%byte
  := Identity.reflexivity _.

Fail Definition data_machine_all_refuses_byte_literal_large
  : Byte
  := 256%byte.

Fail Definition data_machine_all_refuses_byte_literal_long
  : Byte
  := 99999999999999999999%byte.

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

Definition data_machine_all_delivers_uint8
  : UInt8
  := UInt8.One.

Definition data_machine_all_delivers_uint8_carry
  : forall (carry : Bit) (x : UInt8) (y : UInt8) .
      (Bit.to_nat0 carry + UInt8.to_nat0 x + UInt8.to_nat0 y
        = 256 * Bit.to_nat0 (pi_1 (UInt8.add_with_carry carry x y))%product
          + UInt8.to_nat0 (pi_2 (UInt8.add_with_carry carry x y))%product)%n0
  := UInt8.conversion.carry.

Definition data_machine_all_delivers_uint8_addition
  : forall (x : UInt8) (y : UInt8) .
      UInt8.to_nat0 (x + y)%uint8 = ((UInt8.to_nat0 x + UInt8.to_nat0 y) %. 256)%n0
  := UInt8.conversion.addition.

Definition data_machine_all_delivers_uint8_multiplication
  : forall (x : UInt8) (y : UInt8) .
      UInt8.to_nat0 (x * y)%uint8 = ((UInt8.to_nat0 x * UInt8.to_nat0 y) %. 256)%n0
  := UInt8.conversion.multiplication.

Definition data_machine_all_delivers_uint8_negation
  : forall (x : UInt8) . ((UInt8.to_nat0 (- x)%uint8 + UInt8.to_nat0 x) %. 256 = 0)%n0
  := UInt8.conversion.negation.

Definition data_machine_all_delivers_uint8_left_shift
  : forall (x : UInt8) (k : Nat0) .
      UInt8.to_nat0 (UInt8.shift_left x k) = ((UInt8.to_nat0 x * 2 ^ k) %. 256)%n0
  := UInt8.conversion.left.shift.

Definition data_machine_all_delivers_uint8_distributivity
  : forall (x : UInt8) (y : UInt8) (z : UInt8) .
      (x * (y + z) = (x * y) + (x * z) /\ (y + z) * x = (y * x) + (z * x))%uint8
  := UInt8.multiplication.distributivity.over.addition.

Definition data_machine_all_computes_uint8_reduction
  : UInt8.to_nat0 (UInt8.from_nat0 300%n0) = 44%n0
  := Identity.reflexivity _.

Definition data_machine_all_computes_uint8_multiplication
  : UInt8.to_nat0 (20 * 13)%uint8 = 4%n0
  := Identity.reflexivity _.

Definition data_machine_all_computes_uint8_negation
  : (- UInt8.One = 255)%uint8
  := Identity.reflexivity _.

Definition data_machine_all_computes_uint8_carry_out
  : (pi_1 (UInt8.add_with_carry Bit.Zero 255 1))%product = Bit.One
  := Identity.reflexivity _.

Definition data_machine_all_computes_uint8_comparison
  : UInt8.compare 0 1 = Comparison.Lt
  := Identity.reflexivity _.

Definition data_machine_all_reads_bit_literal
  : Bit.xor 1 1 = 0%bit
  := Identity.reflexivity _.

Fail Definition data_machine_all_refuses_bit_literal_two
  : Bit
  := 2%bit.

Definition data_machine_all_reads_byte_literal
  : 0xFF%byte = Byte.flip Byte.Zero
  := Identity.reflexivity _.

Definition data_machine_all_reads_byte_literal_zero
  : 0x0%byte = Byte.Zero
  := Identity.reflexivity _.

Definition data_machine_all_reads_byte_literal_leading_zeros
  : 0x00F0%byte = Byte.shift_left 0x0F 4%n0
  := Identity.reflexivity _.

Fail Definition data_machine_all_refuses_byte_literal_decimal
  : Byte
  := 200%byte.

Fail Definition data_machine_all_refuses_byte_literal_large
  : Byte
  := 0x1FF%byte.

Definition data_machine_all_reads_uint8_literal
  : UInt8.to_nat0 200%uint8 = 200%n0
  := Identity.reflexivity _.

Definition data_machine_all_reads_uint8_literal_hexadecimal
  : 0xFF%uint8 = UInt8.UInt8_introduction (Byte.flip Byte.Zero)
  := Identity.reflexivity _.

Definition data_machine_all_reads_uint8_literal_arithmetic
  : (100 + 200 = 44)%uint8
  := Identity.reflexivity _.

Fail Definition data_machine_all_refuses_uint8_literal_large
  : UInt8
  := 256%uint8.

Fail Definition data_machine_all_refuses_uint8_literal_long
  : UInt8
  := 99999999999999999999%uint8.

Definition data_machine_all_delivers_int8
  : Int8
  := Int8.One.

Definition data_machine_all_delivers_int8_addition
  : forall (x : Int8) (y : Int8) .
      (pi_1 (Int8.add_with_overflow x y))%product = Bit.Zero ->
      Int8.to_integer (x + y)%int8 = (Int8.to_integer x + Int8.to_integer y)%z
  := Int8.conversion.addition.

Definition data_machine_all_delivers_int8_section
  : forall (x : Int8) . Int8.from_integer (Int8.to_integer x) = x
  := Int8.conversion.section.

Definition data_machine_all_delivers_int8_distributivity
  : forall (x : Int8) (y : Int8) (z : Int8) .
      (x * (y + z) = (x * y) + (x * z) /\ (y + z) * x = (y * x) + (z * x))%int8
  := Int8.multiplication.distributivity.over.addition.

Definition data_machine_all_reads_int8_literal_bounds
  : Int8.to_integer (-128)%int8 = (-128)%z /\ Int8.to_integer 127%int8 = 127%z
  := conjoin (Identity.reflexivity _), (Identity.reflexivity _).

Definition data_machine_all_computes_int8_wrap
  : (127 + 1 = -128)%int8
  := Identity.reflexivity _.

Definition data_machine_all_computes_int8_overflow
  : (pi_1 (Int8.add_with_overflow 127 1))%product = Bit.One
  := Identity.reflexivity _.

Definition data_machine_all_computes_int8_no_overflow
  : (pi_1 (Int8.add_with_overflow 100 (-50)))%product = Bit.Zero
  := Identity.reflexivity _.

Definition data_machine_all_computes_int8_multiplication
  : ((-3) * 5 = -15)%int8
  := Identity.reflexivity _.

Definition data_machine_all_computes_int8_negation
  : (- (-128) = -128)%int8
  := Identity.reflexivity _.

Definition data_machine_all_computes_int8_signed_comparison
  : Int8.compare (-1) 1 = Comparison.Lt
  := Identity.reflexivity _.

Definition data_machine_all_computes_int8_arithmetic_shift
  : Int8.shift_right (-4) 1%n0 = (-2)%int8 /\ Int8.shift_right (-1) 3%n0 = (-1)%int8
  := conjoin (Identity.reflexivity _), (Identity.reflexivity _).

Fail Definition data_machine_all_refuses_int8_literal_large
  : Int8
  := 128%int8.

Fail Definition data_machine_all_refuses_int8_literal_small
  : Int8
  := (-129)%int8.

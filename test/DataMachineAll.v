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

Definition data_machine_all_delivers_bit_binary_carry
  : forall (carry : Bit) (a : Bit) (b : Bit) .
      (Bit.to_bin_with_zero carry + Bit.to_bin_with_zero a + Bit.to_bin_with_zero b
        = 10 * Bit.to_bin_with_zero (pi_1 (Bit.add_with_carry carry a b))%product
          + Bit.to_bin_with_zero (pi_2 (Bit.add_with_carry carry a b))%product)%bin_with_zero
  := Bit.conversion.binary.carry.

Definition data_machine_all_delivers_uint8
  : UInt8
  := UInt8.One.

Definition data_machine_all_computes_uint8_modulus
  : UInt8.modulus = 100000000%bin_base
  := Identity.reflexivity _.

Definition data_machine_all_delivers_uint8_carry
  : forall (carry : Bit) (x : UInt8) (y : UInt8) .
      (Bit.to_bin_with_zero carry + x + y
        = UInt8.modulus * Bit.to_bin_with_zero (pi_1 (UInt8.add_with_carry carry x y))%product
          + (pi_2 (UInt8.add_with_carry carry x y))%product)%bin_with_zero
  := UInt8.conversion.carry.

Definition data_machine_all_delivers_uint8_addition
  : forall (x : UInt8) (y : UInt8) .
      (UInt8.to_bin_with_zero (x + y)%uint8 = (x + y) %. UInt8.modulus)%bin_with_zero
  := UInt8.conversion.addition.

Definition data_machine_all_delivers_uint8_multiplication
  : forall (x : UInt8) (y : UInt8) .
      (UInt8.to_bin_with_zero (x * y)%uint8 = (x * y) %. UInt8.modulus)%bin_with_zero
  := UInt8.conversion.multiplication.

Definition data_machine_all_delivers_uint8_negation
  : forall (x : UInt8) .
      (((- x)%uint8 + x) %. UInt8.modulus = 0)%bin_with_zero
  := UInt8.conversion.negation.

Definition data_machine_all_delivers_uint8_left_shift
  : forall (x : UInt8) (k : Nat0) .
      (UInt8.to_bin_with_zero (UInt8.shift_left x k)
        = BinWithZero.shift_left x k %. UInt8.modulus)%bin_with_zero
  := UInt8.conversion.left.shift.

Definition data_machine_all_delivers_uint8_right_shift
  : forall (x : UInt8) (k : Nat0) .
      UInt8.to_bin_with_zero (UInt8.shift_right x k) = BinWithZero.shift_right x k
  := UInt8.conversion.right.shift.

Definition data_machine_all_delivers_uint8_section
  : forall (x : UInt8) . UInt8.from_bin_with_zero (UInt8.to_bin_with_zero x) = x
  := UInt8.conversion.section.

Definition data_machine_all_computes_uint8_value
  : UInt8.to_bin_with_zero 200%uint8 = 11001000%bin_with_zero
  := Identity.reflexivity _.

Definition data_machine_all_computes_uint8_to_bin
  : UInt8.to_bin 200%uint8 = 11001000%b
  := Identity.reflexivity _.

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

Definition data_machine_all_delivers_uint8_byte_retraction
  : forall (b : Byte) . UInt8.to_byte (UInt8.from_byte b) = b
  := UInt8.conversion.byte.retraction.

Definition data_machine_all_delivers_uint8_byte_section
  : forall (x : UInt8) . UInt8.from_byte (UInt8.to_byte x) = x
  := UInt8.conversion.byte.section.

Theorem data_machine_all_delivers_coercion_uint8_to_bin_with_zero
  : forall (x : UInt8) .
      BinWithZero.add x x = BinWithZero.add (UInt8.to_bin_with_zero x) (UInt8.to_bin_with_zero x).
Proof.
  intro x.
  quod idem est.
Qed.

Theorem data_machine_all_delivers_coercion_uint8_to_nat0
  : forall (x : UInt8) . Nat0.add x x = Nat0.add (UInt8.to_nat0 x) (UInt8.to_nat0 x).
Proof.
  intro x.
  quod idem est.
Qed.

Theorem data_machine_all_delivers_coercion_uint8_to_integer
  : forall (x : UInt8) .
      Integer.negate x = Integer.negate (Integer.from_nat0 (UInt8.to_nat0 x)).
Proof.
  intro x.
  quod idem est.
Qed.

Definition data_machine_all_delivers_int8
  : Int8
  := Int8.One.

Definition data_machine_all_computes_int8_modulus
  : Int8.modulus = 100000000%bin_base
  := Identity.reflexivity _.

Definition data_machine_all_delivers_int8_addition
  : forall (x : Int8) (y : Int8) .
      (pi_1 (Int8.add_with_overflow x y))%product = Bit.Zero ->
      Int8.to_bin (x + y)%int8 = (x + y)%b
  := Int8.conversion.addition.

Definition data_machine_all_delivers_int8_section
  : forall (x : Int8) . Int8.from_bin (Int8.to_bin x) = x
  := Int8.conversion.section.

Definition data_machine_all_delivers_int8_valuation_section
  : forall (x : Int8) . Int8.from_bin_with_zero (Int8.unsigned_value x) = x
  := Int8.valuation.section.

Definition data_machine_all_computes_int8_value
  : Int8.to_bin (-128)%int8 = (-10000000)%b
  := Identity.reflexivity _.

Definition data_machine_all_computes_int8_from_bin
  : Int8.from_bin 11001000%b = (-56)%int8
  := Identity.reflexivity _.

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

Definition data_machine_all_reads_int8_literal_hexadecimal
  : 0x7F%int8 = 127%int8
  := Identity.reflexivity _.

Definition data_machine_all_computes_int8_from_integer
  : Int8.from_integer 200 = (-56)%int8
  := Identity.reflexivity _.

Fail Definition data_machine_all_refuses_int8_literal_large
  : Int8
  := 128%int8.

Fail Definition data_machine_all_refuses_int8_literal_small
  : Int8
  := (-129)%int8.

Definition data_machine_all_delivers_int8_byte_retraction
  : forall (b : Byte) . Int8.to_byte (Int8.from_byte b) = b
  := Int8.conversion.byte.retraction.

Definition data_machine_all_delivers_int8_byte_section
  : forall (x : Int8) . Int8.from_byte (Int8.to_byte x) = x
  := Int8.conversion.byte.section.

Theorem data_machine_all_delivers_coercion_int8_to_bin
  : forall (x : Int8) . Bin.negate x = Bin.negate (Int8.to_bin x).
Proof.
  intro x.
  quod idem est.
Qed.

Theorem data_machine_all_delivers_coercion_int8_to_integer
  : forall (x : Int8) . Integer.negate x = Integer.negate (Int8.to_integer x).
Proof.
  intro x.
  quod idem est.
Qed.

Definition data_machine_all_computes_byte_reinterpretation
  : Int8.from_byte (UInt8.to_byte 255) = (-1)%int8
  := Identity.reflexivity _.

Definition data_machine_all_delivers_hword
  : HWord
  := HWord.Zero Endian.Little.

Definition data_machine_all_delivers_hword_notation
  : forall (x : HWord) (y : HWord) .
      HWord.endian x = Endian.Little ->
      HWord.endian y = Endian.Little ->
      (x &. y)%hword = (y &. x)%hword
  := HWord.conjunction.endian.little.commutativity.

Definition data_machine_all_binds_hword_scope
  : forall (x : HWord) . HWord.flip (~. x) = x
  := HWord.flipping.involution.

Definition data_machine_all_delivers_hword_conversion
  : forall (x : HWord) (y : HWord) .
      (x &. y)%hword = (x &. HWord.with_endian (HWord.endian x) y)%hword
  := HWord.conjunction.endian.conversion.

Definition data_machine_all_delivers_hword_endianness_identity
  : forall (x : HWord) . HWord.with_endian (HWord.endian x) x = x
  := HWord.endianness.identity.

Definition data_machine_all_delivers_hword_rotation_inverse
  : forall (x : HWord) (k : Nat0) . HWord.rotate_right (HWord.rotate_left x k) k = x
  := HWord.rotation.left.inverse.

Definition data_machine_all_reads_hword_literal_little_endian
  : 0x1234%hword = HWord.HWord_introduction Endian.Little 0x34%byte 0x12%byte
  := Identity.reflexivity _.

Definition data_machine_all_reads_hword_literal_little_endian_key
  : 0x1234%hword_little = 0x1234%hword
  := Identity.reflexivity _.

Definition data_machine_all_reads_hword_literal_big_endian
  : 0x1234%hword_big = HWord.HWord_introduction Endian.Big 0x12%byte 0x34%byte
  := Identity.reflexivity _.

Definition data_machine_all_computes_hword_with_endian
  : HWord.with_endian Endian.Big 0x1234 = 0x1234%hword_big
  := Identity.reflexivity _.

Definition data_machine_all_computes_hword_mixed_conjunction
  : (0x00FF &. 0x0F0F%hword_big)%hword = 0x000F%hword
  := Identity.reflexivity _.

Definition data_machine_all_computes_hword_and_big_endian
  : HWord.and_big_endian 0x00FF 0x0F0F = 0x000F%hword_big
  := Identity.reflexivity _.

Definition data_machine_all_computes_hword_shift_left
  : HWord.shift_left 0x0080 1%n0 = 0x0100%hword
  := Identity.reflexivity _.

Definition data_machine_all_computes_hword_shift_left_big_endian
  : HWord.shift_left 0x0080%hword_big 1%n0 = 0x0100%hword_big
  := Identity.reflexivity _.

Definition data_machine_all_computes_hword_rotate_left
  : HWord.rotate_left 0x8001 1%n0 = 0x0003%hword
  := Identity.reflexivity _.

Definition data_machine_all_computes_hword_to_bytes
  : HWord.to_bytes 0x1234 = (0x34%byte :: 0x12%byte :: [])%list
    /\ HWord.to_bytes 0x1234%hword_big = (0x12%byte :: 0x34%byte :: [])%list
  := conjoin (Identity.reflexivity _), (Identity.reflexivity _).

Definition data_machine_all_delivers_hword_bytes_retraction
  : forall (x : HWord) . HWord.from_bytes (HWord.endian x) (HWord.to_bytes x) = Some x
  := HWord.conversion.bytes.retraction.

Fail Definition data_machine_all_refuses_hword_literal_decimal
  : HWord
  := 200%hword.

Fail Definition data_machine_all_refuses_hword_literal_large
  : HWord
  := 0x10000%hword.

Fail Definition data_machine_all_refuses_hword_literal_large_big_endian
  : HWord
  := 0x10000%hword_big.

Definition data_machine_all_delivers_uint16
  : UInt16
  := UInt16.One.

Definition data_machine_all_computes_uint16_modulus
  : UInt16.modulus = 10000000000000000%bin_base
  := Identity.reflexivity _.

Definition data_machine_all_delivers_uint16_carry
  : forall (carry : Bit) (x : UInt16) (y : UInt16) .
      (Bit.to_bin_with_zero carry + x + y
        = UInt16.modulus * Bit.to_bin_with_zero (pi_1 (UInt16.add_with_carry carry x y))%product
          + (pi_2 (UInt16.add_with_carry carry x y))%product)%bin_with_zero
  := UInt16.conversion.carry.

Definition data_machine_all_delivers_uint16_addition
  : forall (x : UInt16) (y : UInt16) .
      (UInt16.to_bin_with_zero (x + y)%uint16 = (x + y) %. UInt16.modulus)%bin_with_zero
  := UInt16.conversion.addition.

Definition data_machine_all_delivers_uint16_multiplication
  : forall (x : UInt16) (y : UInt16) .
      (UInt16.to_bin_with_zero (x * y)%uint16 = (x * y) %. UInt16.modulus)%bin_with_zero
  := UInt16.conversion.multiplication.

Definition data_machine_all_delivers_uint16_negation
  : forall (x : UInt16) .
      (((- x)%uint16 + x) %. UInt16.modulus = 0)%bin_with_zero
  := UInt16.conversion.negation.

Definition data_machine_all_delivers_uint16_left_shift
  : forall (x : UInt16) (k : Nat0) .
      (UInt16.to_bin_with_zero (UInt16.shift_left x k)
        = BinWithZero.shift_left x k %. UInt16.modulus)%bin_with_zero
  := UInt16.conversion.left.shift.

Definition data_machine_all_delivers_uint16_right_shift
  : forall (x : UInt16) (k : Nat0) .
      UInt16.to_bin_with_zero (UInt16.shift_right x k) = BinWithZero.shift_right x k
  := UInt16.conversion.right.shift.

Definition data_machine_all_delivers_uint16_section
  : forall (x : UInt16) . UInt16.from_bin_with_zero (UInt16.to_bin_with_zero x) = x
  := UInt16.conversion.section.

Definition data_machine_all_computes_uint16_value
  : UInt16.to_bin_with_zero 50000%uint16 = 1100001101010000%bin_with_zero
  := Identity.reflexivity _.

Definition data_machine_all_computes_uint16_to_bin
  : UInt16.to_bin 50000%uint16 = 1100001101010000%b
  := Identity.reflexivity _.

Definition data_machine_all_delivers_uint16_distributivity
  : forall (x : UInt16) (y : UInt16) (z : UInt16) .
      (x * (y + z) = (x * y) + (x * z) /\ (y + z) * x = (y * x) + (z * x))%uint16
  := UInt16.multiplication.distributivity.over.addition.

Definition data_machine_all_computes_uint16_reduction
  : UInt16.from_bin_with_zero 10001000101110000%bin_with_zero = 4464%uint16
  := Identity.reflexivity _.

Definition data_machine_all_computes_uint16_multiplication
  : (300 * 300 = 24464)%uint16
  := Identity.reflexivity _.

Definition data_machine_all_computes_uint16_negation
  : (- UInt16.One = 65535)%uint16
  := Identity.reflexivity _.

Definition data_machine_all_computes_uint16_carry_out
  : (pi_1 (UInt16.add_with_carry Bit.Zero 65535 1))%product = Bit.One
  := Identity.reflexivity _.

Definition data_machine_all_computes_uint16_comparison
  : UInt16.compare 255 256 = Comparison.Lt
  := Identity.reflexivity _.

Definition data_machine_all_reads_uint16_literal_hexadecimal
  : 0xFFFF%uint16 = UInt16.UInt16_introduction (Byte.flip Byte.Zero) (Byte.flip Byte.Zero)
  := Identity.reflexivity _.

Definition data_machine_all_reads_uint16_literal_arithmetic
  : (60000 + 10000 = 4464)%uint16
  := Identity.reflexivity _.

Fail Definition data_machine_all_refuses_uint16_literal_large
  : UInt16
  := 65536%uint16.

Fail Definition data_machine_all_refuses_uint16_literal_long
  : UInt16
  := 99999999999999999999%uint16.

Definition data_machine_all_computes_uint16_to_hword
  : UInt16.to_hword Endian.Little 0x1234 = 0x1234%hword
    /\ UInt16.to_hword Endian.Big 0x1234 = 0x1234%hword_big
  := conjoin (Identity.reflexivity _), (Identity.reflexivity _).

Definition data_machine_all_computes_uint16_from_hword
  : UInt16.from_hword 0x1234%hword_big = 0x1234%uint16
  := Identity.reflexivity _.

Definition data_machine_all_delivers_uint16_hword_retraction
  : forall (e : Endian) (x : UInt16) . UInt16.from_hword (UInt16.to_hword e x) = x
  := UInt16.conversion.hword.retraction.

Definition data_machine_all_delivers_uint16_hword_section
  : forall (w : HWord) . UInt16.to_hword (HWord.endian w) (UInt16.from_hword w) = w
  := UInt16.conversion.hword.section.

Theorem data_machine_all_delivers_coercion_uint16_to_bin_with_zero
  : forall (x : UInt16) .
      BinWithZero.add x x = BinWithZero.add (UInt16.to_bin_with_zero x) (UInt16.to_bin_with_zero x).
Proof.
  intro x.
  quod idem est.
Qed.

Theorem data_machine_all_delivers_coercion_uint16_to_nat0
  : forall (x : UInt16) . Nat0.add x x = Nat0.add (UInt16.to_nat0 x) (UInt16.to_nat0 x).
Proof.
  intro x.
  quod idem est.
Qed.

Theorem data_machine_all_delivers_coercion_uint16_to_integer
  : forall (x : UInt16) .
      Integer.negate x = Integer.negate (Integer.from_nat0 (UInt16.to_nat0 x)).
Proof.
  intro x.
  quod idem est.
Qed.

Definition data_machine_all_delivers_int16
  : Int16
  := Int16.One.

Definition data_machine_all_computes_int16_modulus
  : Int16.modulus = 10000000000000000%bin_base
  := Identity.reflexivity _.

Definition data_machine_all_delivers_int16_addition
  : forall (x : Int16) (y : Int16) .
      (pi_1 (Int16.add_with_overflow x y))%product = Bit.Zero ->
      Int16.to_bin (x + y)%int16 = (x + y)%b
  := Int16.conversion.addition.

Definition data_machine_all_delivers_int16_section
  : forall (x : Int16) . Int16.from_bin (Int16.to_bin x) = x
  := Int16.conversion.section.

Definition data_machine_all_delivers_int16_valuation_section
  : forall (x : Int16) . Int16.from_bin_with_zero (Int16.unsigned_value x) = x
  := Int16.valuation.section.

Definition data_machine_all_computes_int16_value
  : Int16.to_bin (-1000)%int16 = (-1111101000)%b
  := Identity.reflexivity _.

Definition data_machine_all_computes_int16_from_bin
  : Int16.from_bin 1001110001000000%b = (-25536)%int16
  := Identity.reflexivity _.

Definition data_machine_all_delivers_int16_distributivity
  : forall (x : Int16) (y : Int16) (z : Int16) .
      (x * (y + z) = (x * y) + (x * z) /\ (y + z) * x = (y * x) + (z * x))%int16
  := Int16.multiplication.distributivity.over.addition.

Definition data_machine_all_reads_int16_literal_bounds
  : Int16.to_bin (-32768)%int16 = (-1000000000000000)%b
    /\ Int16.to_bin 32767%int16 = 111111111111111%b
  := conjoin (Identity.reflexivity _), (Identity.reflexivity _).

Definition data_machine_all_computes_int16_wrap
  : (32767 + 1 = -32768)%int16
  := Identity.reflexivity _.

Definition data_machine_all_computes_int16_overflow
  : (pi_1 (Int16.add_with_overflow 32767 1))%product = Bit.One
  := Identity.reflexivity _.

Definition data_machine_all_computes_int16_no_overflow
  : (pi_1 (Int16.add_with_overflow 1000 (-500)))%product = Bit.Zero
  := Identity.reflexivity _.

Definition data_machine_all_computes_int16_multiplication
  : ((-300) * 300 = -24464)%int16
  := Identity.reflexivity _.

Definition data_machine_all_computes_int16_negation
  : (- (-32768) = -32768)%int16
  := Identity.reflexivity _.

Definition data_machine_all_computes_int16_signed_comparison
  : Int16.compare (-1) 1 = Comparison.Lt
  := Identity.reflexivity _.

Definition data_machine_all_computes_int16_arithmetic_shift
  : Int16.shift_right (-4) 1%n0 = (-2)%int16 /\ Int16.shift_right (-1) 15%n0 = (-1)%int16
  := conjoin (Identity.reflexivity _), (Identity.reflexivity _).

Definition data_machine_all_reads_int16_literal_hexadecimal
  : 0x7FFF%int16 = 32767%int16
  := Identity.reflexivity _.

Definition data_machine_all_computes_int16_from_integer
  : Int16.from_integer (-1000) = (-1000)%int16
  := Identity.reflexivity _.

Fail Definition data_machine_all_refuses_int16_literal_large
  : Int16
  := 32768%int16.

Fail Definition data_machine_all_refuses_int16_literal_small
  : Int16
  := (-32769)%int16.

Definition data_machine_all_delivers_int16_hword_retraction
  : forall (e : Endian) (x : Int16) . Int16.from_hword (Int16.to_hword e x) = x
  := Int16.conversion.hword.retraction.

Definition data_machine_all_delivers_int16_hword_section
  : forall (w : HWord) . Int16.to_hword (HWord.endian w) (Int16.from_hword w) = w
  := Int16.conversion.hword.section.

Theorem data_machine_all_delivers_coercion_int16_to_bin
  : forall (x : Int16) . Bin.negate x = Bin.negate (Int16.to_bin x).
Proof.
  intro x.
  quod idem est.
Qed.

Theorem data_machine_all_delivers_coercion_int16_to_integer
  : forall (x : Int16) . Integer.negate x = Integer.negate (Int16.to_integer x).
Proof.
  intro x.
  quod idem est.
Qed.

Definition data_machine_all_computes_hword_reinterpretation
  : Int16.from_hword (UInt16.to_hword Endian.Big 65535) = (-1)%int16
  := Identity.reflexivity _.

Definition data_machine_all_delivers_word
  : Word
  := Word.Zero Endian.Little.

Definition data_machine_all_delivers_word_notation
  : forall (x : Word) (y : Word) .
      Word.endian x = Endian.Big ->
      Word.endian y = Endian.Big ->
      (x |. y)%word = (y |. x)%word
  := Word.disjunction.endian.big.commutativity.

Definition data_machine_all_binds_word_scope
  : forall (x : Word) . Word.flip (~. x) = x
  := Word.flipping.involution.

Definition data_machine_all_delivers_word_conversion
  : forall (x : Word) (y : Word) .
      (x ^. y)%word = (x ^. Word.with_endian (Word.endian x) y)%word
  := Word.sejunction.endian.conversion.

Definition data_machine_all_delivers_word_endianness_absorption
  : forall (e : Endian) (f : Endian) (x : Word) .
      Word.with_endian e (Word.with_endian f x) = Word.with_endian e x
  := Word.endianness.absorption.

Definition data_machine_all_delivers_word_rotation_inverse
  : forall (x : Word) (k : Nat0) . Word.rotate_left (Word.rotate_right x k) k = x
  := Word.rotation.right.inverse.

Definition data_machine_all_reads_word_literal_little_endian
  : 0x12345678%word
    = Word.Word_introduction Endian.Little 0x78%byte 0x56%byte 0x34%byte 0x12%byte
  := Identity.reflexivity _.

Definition data_machine_all_reads_word_literal_little_endian_key
  : 0x12345678%word_little = 0x12345678%word
  := Identity.reflexivity _.

Definition data_machine_all_reads_word_literal_big_endian
  : 0x12345678%word_big
    = Word.Word_introduction Endian.Big 0x12%byte 0x34%byte 0x56%byte 0x78%byte
  := Identity.reflexivity _.

Definition data_machine_all_computes_word_with_endian
  : Word.with_endian Endian.Big 0x12345678 = 0x12345678%word_big
  := Identity.reflexivity _.

Definition data_machine_all_computes_word_mixed_conjunction
  : (0x0000FFFF &. 0x0F0F0F0F%word_big)%word = 0x00000F0F%word
  := Identity.reflexivity _.

Definition data_machine_all_computes_word_and_big_endian
  : Word.and_big_endian 0x0000FFFF 0x0F0F0F0F = 0x00000F0F%word_big
  := Identity.reflexivity _.

Definition data_machine_all_computes_word_shift_left
  : Word.shift_left 0x00808080 1%n0 = 0x01010100%word
  := Identity.reflexivity _.

Definition data_machine_all_computes_word_shift_right_big_endian
  : Word.shift_right 0x01010100%word_big 1%n0 = 0x00808080%word_big
  := Identity.reflexivity _.

Definition data_machine_all_computes_word_rotate_left
  : Word.rotate_left 0x80000001 1%n0 = 0x00000003%word
  := Identity.reflexivity _.

Definition data_machine_all_computes_word_to_bytes
  : Word.to_bytes 0x12345678 = (0x78%byte :: 0x56%byte :: 0x34%byte :: 0x12%byte :: [])%list
    /\ Word.to_bytes 0x12345678%word_big
      = (0x12%byte :: 0x34%byte :: 0x56%byte :: 0x78%byte :: [])%list
  := conjoin (Identity.reflexivity _), (Identity.reflexivity _).

Definition data_machine_all_delivers_word_bytes_retraction
  : forall (x : Word) . Word.from_bytes (Word.endian x) (Word.to_bytes x) = Some x
  := Word.conversion.bytes.retraction.

Fail Definition data_machine_all_refuses_word_literal_decimal
  : Word
  := 200%word.

Fail Definition data_machine_all_refuses_word_literal_large
  : Word
  := 0x100000000%word.

Fail Definition data_machine_all_refuses_word_literal_large_big_endian
  : Word
  := 0x100000000%word_big.

Definition data_machine_all_delivers_uint32
  : UInt32
  := UInt32.One.

Definition data_machine_all_computes_uint32_modulus
  : UInt32.modulus = 100000000000000000000000000000000%bin_base
  := Identity.reflexivity _.

Definition data_machine_all_delivers_uint32_carry
  : forall (carry : Bit) (x : UInt32) (y : UInt32) .
      (Bit.to_bin_with_zero carry + x + y
        = UInt32.modulus * Bit.to_bin_with_zero (pi_1 (UInt32.add_with_carry carry x y))%product
          + (pi_2 (UInt32.add_with_carry carry x y))%product)%bin_with_zero
  := UInt32.conversion.carry.

Definition data_machine_all_delivers_uint32_addition
  : forall (x : UInt32) (y : UInt32) .
      (UInt32.to_bin_with_zero (x + y)%uint32 = (x + y) %. UInt32.modulus)%bin_with_zero
  := UInt32.conversion.addition.

Definition data_machine_all_delivers_uint32_multiplication
  : forall (x : UInt32) (y : UInt32) .
      (UInt32.to_bin_with_zero (x * y)%uint32 = (x * y) %. UInt32.modulus)%bin_with_zero
  := UInt32.conversion.multiplication.

Definition data_machine_all_delivers_uint32_negation
  : forall (x : UInt32) .
      (((- x)%uint32 + x) %. UInt32.modulus = 0)%bin_with_zero
  := UInt32.conversion.negation.

Definition data_machine_all_delivers_uint32_left_shift
  : forall (x : UInt32) (k : Nat0) .
      (UInt32.to_bin_with_zero (UInt32.shift_left x k)
        = BinWithZero.shift_left x k %. UInt32.modulus)%bin_with_zero
  := UInt32.conversion.left.shift.

Definition data_machine_all_delivers_uint32_right_shift
  : forall (x : UInt32) (k : Nat0) .
      UInt32.to_bin_with_zero (UInt32.shift_right x k) = BinWithZero.shift_right x k
  := UInt32.conversion.right.shift.

Definition data_machine_all_delivers_uint32_section
  : forall (x : UInt32) . UInt32.from_bin_with_zero (UInt32.to_bin_with_zero x) = x
  := UInt32.conversion.section.

Definition data_machine_all_computes_uint32_value
  : UInt32.to_bin_with_zero 3000000000%uint32 = 10110010110100000101111000000000%bin_with_zero
  := Identity.reflexivity _.

Definition data_machine_all_computes_uint32_to_bin
  : UInt32.to_bin 3000000000%uint32 = 10110010110100000101111000000000%b
  := Identity.reflexivity _.

Definition data_machine_all_delivers_uint32_distributivity
  : forall (x : UInt32) (y : UInt32) (z : UInt32) .
      (x * (y + z) = (x * y) + (x * z) /\ (y + z) * x = (y * x) + (z * x))%uint32
  := UInt32.multiplication.distributivity.over.addition.

Definition data_machine_all_computes_uint32_reduction
  : UInt32.from_bin_with_zero 100000000000000000001000101110000%bin_with_zero = 4464%uint32
  := Identity.reflexivity _.

Definition data_machine_all_computes_uint32_multiplication
  : (70000 * 70000 = 605032704)%uint32
  := Identity.reflexivity _.

Definition data_machine_all_computes_uint32_negation
  : (- UInt32.One = 4294967295)%uint32
  := Identity.reflexivity _.

Definition data_machine_all_computes_uint32_carry_out
  : (pi_1 (UInt32.add_with_carry Bit.Zero 4294967295 1))%product = Bit.One
  := Identity.reflexivity _.

Definition data_machine_all_computes_uint32_comparison
  : UInt32.compare 65535 65536 = Comparison.Lt
  := Identity.reflexivity _.

Definition data_machine_all_reads_uint32_literal_hexadecimal
  : 0xFFFFFFFF%uint32
    = UInt32.UInt32_introduction
        (Byte.flip Byte.Zero) (Byte.flip Byte.Zero) (Byte.flip Byte.Zero) (Byte.flip Byte.Zero)
  := Identity.reflexivity _.

Definition data_machine_all_reads_uint32_literal_arithmetic
  : (4000000000 + 300000000 = 5032704)%uint32
  := Identity.reflexivity _.

Fail Definition data_machine_all_refuses_uint32_literal_large
  : UInt32
  := 4294967296%uint32.

Fail Definition data_machine_all_refuses_uint32_literal_long
  : UInt32
  := 99999999999999999999%uint32.

Definition data_machine_all_computes_uint32_to_word
  : UInt32.to_word Endian.Little 0x12345678 = 0x12345678%word
    /\ UInt32.to_word Endian.Big 0x12345678 = 0x12345678%word_big
  := conjoin (Identity.reflexivity _), (Identity.reflexivity _).

Definition data_machine_all_computes_uint32_from_word
  : UInt32.from_word 0x12345678%word_big = 0x12345678%uint32
  := Identity.reflexivity _.

Definition data_machine_all_delivers_uint32_word_retraction
  : forall (e : Endian) (x : UInt32) . UInt32.from_word (UInt32.to_word e x) = x
  := UInt32.conversion.word.retraction.

Definition data_machine_all_delivers_uint32_word_section
  : forall (w : Word) . UInt32.to_word (Word.endian w) (UInt32.from_word w) = w
  := UInt32.conversion.word.section.

Theorem data_machine_all_delivers_coercion_uint32_to_bin_with_zero
  : forall (x : UInt32) .
      BinWithZero.add x x = BinWithZero.add (UInt32.to_bin_with_zero x) (UInt32.to_bin_with_zero x).
Proof.
  intro x.
  quod idem est.
Qed.

Theorem data_machine_all_delivers_coercion_uint32_to_nat0
  : forall (x : UInt32) . Nat0.add x x = Nat0.add (UInt32.to_nat0 x) (UInt32.to_nat0 x).
Proof.
  intro x.
  quod idem est.
Qed.

Theorem data_machine_all_delivers_coercion_uint32_to_integer
  : forall (x : UInt32) .
      Integer.negate x = Integer.negate (Integer.from_nat0 (UInt32.to_nat0 x)).
Proof.
  intro x.
  quod idem est.
Qed.

Definition data_machine_all_delivers_int32
  : Int32
  := Int32.One.

Definition data_machine_all_computes_int32_modulus
  : Int32.modulus = 100000000000000000000000000000000%bin_base
  := Identity.reflexivity _.

Definition data_machine_all_delivers_int32_addition
  : forall (x : Int32) (y : Int32) .
      (pi_1 (Int32.add_with_overflow x y))%product = Bit.Zero ->
      Int32.to_bin (x + y)%int32 = (x + y)%b
  := Int32.conversion.addition.

Definition data_machine_all_delivers_int32_section
  : forall (x : Int32) . Int32.from_bin (Int32.to_bin x) = x
  := Int32.conversion.section.

Definition data_machine_all_delivers_int32_valuation_section
  : forall (x : Int32) . Int32.from_bin_with_zero (Int32.unsigned_value x) = x
  := Int32.valuation.section.

Definition data_machine_all_computes_int32_value
  : Int32.to_bin (-1000000)%int32 = (-11110100001001000000)%b
  := Identity.reflexivity _.

Definition data_machine_all_computes_int32_from_bin
  : Int32.from_bin 10110010110100000101111000000000%b = (-1294967296)%int32
  := Identity.reflexivity _.

Definition data_machine_all_delivers_int32_distributivity
  : forall (x : Int32) (y : Int32) (z : Int32) .
      (x * (y + z) = (x * y) + (x * z) /\ (y + z) * x = (y * x) + (z * x))%int32
  := Int32.multiplication.distributivity.over.addition.

Definition data_machine_all_reads_int32_literal_bounds
  : Int32.to_bin (-2147483648)%int32 = (-10000000000000000000000000000000)%b
    /\ Int32.to_bin 2147483647%int32 = 1111111111111111111111111111111%b
  := conjoin (Identity.reflexivity _), (Identity.reflexivity _).

Definition data_machine_all_computes_int32_wrap
  : (2147483647 + 1 = -2147483648)%int32
  := Identity.reflexivity _.

Definition data_machine_all_computes_int32_overflow
  : (pi_1 (Int32.add_with_overflow 2147483647 1))%product = Bit.One
  := Identity.reflexivity _.

Definition data_machine_all_computes_int32_no_overflow
  : (pi_1 (Int32.add_with_overflow 1000000 (-500000)))%product = Bit.Zero
  := Identity.reflexivity _.

Definition data_machine_all_computes_int32_multiplication
  : ((-70000) * 70000 = -605032704)%int32
  := Identity.reflexivity _.

Definition data_machine_all_computes_int32_negation
  : (- (-2147483648) = -2147483648)%int32
  := Identity.reflexivity _.

Definition data_machine_all_computes_int32_signed_comparison
  : Int32.compare (-1) 1 = Comparison.Lt
  := Identity.reflexivity _.

Definition data_machine_all_computes_int32_arithmetic_shift
  : Int32.shift_right (-4) 1%n0 = (-2)%int32 /\ Int32.shift_right (-1) 31%n0 = (-1)%int32
  := conjoin (Identity.reflexivity _), (Identity.reflexivity _).

Definition data_machine_all_reads_int32_literal_hexadecimal
  : 0x7FFFFFFF%int32 = 2147483647%int32
  := Identity.reflexivity _.

Definition data_machine_all_computes_int32_from_integer
  : Int32.from_integer (-1000) = (-1000)%int32
  := Identity.reflexivity _.

Fail Definition data_machine_all_refuses_int32_literal_large
  : Int32
  := 2147483648%int32.

Fail Definition data_machine_all_refuses_int32_literal_small
  : Int32
  := (-2147483649)%int32.

Definition data_machine_all_delivers_int32_word_retraction
  : forall (e : Endian) (x : Int32) . Int32.from_word (Int32.to_word e x) = x
  := Int32.conversion.word.retraction.

Definition data_machine_all_delivers_int32_word_section
  : forall (w : Word) . Int32.to_word (Word.endian w) (Int32.from_word w) = w
  := Int32.conversion.word.section.

Theorem data_machine_all_delivers_coercion_int32_to_bin
  : forall (x : Int32) . Bin.negate x = Bin.negate (Int32.to_bin x).
Proof.
  intro x.
  quod idem est.
Qed.

Theorem data_machine_all_delivers_coercion_int32_to_integer
  : forall (x : Int32) . Integer.negate x = Integer.negate (Int32.to_integer x).
Proof.
  intro x.
  quod idem est.
Qed.

Definition data_machine_all_computes_word_reinterpretation
  : Int32.from_word (UInt32.to_word Endian.Big 4294967295) = (-1)%int32
  := Identity.reflexivity _.

Definition data_machine_all_delivers_dword
  : DWord
  := DWord.Zero Endian.Big.

Definition data_machine_all_delivers_dword_notation
  : forall (x : DWord) (y : DWord) .
      DWord.endian x = Endian.Little ->
      DWord.endian y = Endian.Little ->
      (x ^. y)%dword = (y ^. x)%dword
  := DWord.sejunction.endian.little.commutativity.

Definition data_machine_all_binds_dword_scope
  : forall (x : DWord) . DWord.flip (~. x) = x
  := DWord.flipping.involution.

Definition data_machine_all_delivers_dword_conversion
  : forall (x : DWord) (y : DWord) .
      (x &. y)%dword = (x &. DWord.with_endian (DWord.endian x) y)%dword
  := DWord.conjunction.endian.conversion.

Definition data_machine_all_delivers_dword_endianness_specification
  : forall (e : Endian) (x : DWord) . DWord.endian (DWord.with_endian e x) = e
  := DWord.endianness.specification.

Definition data_machine_all_delivers_dword_rotation_inverse
  : forall (x : DWord) (k : Nat0) . DWord.rotate_right (DWord.rotate_left x k) k = x
  := DWord.rotation.left.inverse.

Definition data_machine_all_reads_dword_literal_little_endian
  : 0x0123456789ABCDEF%dword
    = DWord.DWord_introduction Endian.Little
        0xEF%byte 0xCD%byte 0xAB%byte 0x89%byte 0x67%byte 0x45%byte 0x23%byte 0x01%byte
  := Identity.reflexivity _.

Definition data_machine_all_reads_dword_literal_big_endian
  : 0x0123456789ABCDEF%dword_big
    = DWord.DWord_introduction Endian.Big
        0x01%byte 0x23%byte 0x45%byte 0x67%byte 0x89%byte 0xAB%byte 0xCD%byte 0xEF%byte
  := Identity.reflexivity _.

Definition data_machine_all_computes_dword_with_endian
  : DWord.with_endian Endian.Big 0x0123456789ABCDEF = 0x0123456789ABCDEF%dword_big
  := Identity.reflexivity _.

Definition data_machine_all_computes_dword_mixed_conjunction
  : (0x00000000FFFFFFFF &. 0x0F0F0F0F0F0F0F0F%dword_big)%dword = 0x000000000F0F0F0F%dword
  := Identity.reflexivity _.

Definition data_machine_all_computes_dword_or_big_endian
  : DWord.or_big_endian 0x00000000000000F0 0x000000000000000F = 0x00000000000000FF%dword_big
  := Identity.reflexivity _.

Definition data_machine_all_computes_dword_shift_left
  : DWord.shift_left 0x0080808080808080 1%n0 = 0x0101010101010100%dword
  := Identity.reflexivity _.

Definition data_machine_all_computes_dword_rotate_right_big_endian
  : DWord.rotate_right 0x0000000000000001%dword_big 1%n0 = 0x8000000000000000%dword_big
  := Identity.reflexivity _.

Definition data_machine_all_computes_dword_to_bytes_big_endian
  : DWord.to_bytes 0x0123456789ABCDEF%dword_big
    = (0x01%byte :: 0x23%byte :: 0x45%byte :: 0x67%byte
        :: 0x89%byte :: 0xAB%byte :: 0xCD%byte :: 0xEF%byte :: [])%list
  := Identity.reflexivity _.

Definition data_machine_all_delivers_dword_bytes_retraction
  : forall (x : DWord) . DWord.from_bytes (DWord.endian x) (DWord.to_bytes x) = Some x
  := DWord.conversion.bytes.retraction.

Fail Definition data_machine_all_refuses_dword_literal_decimal
  : DWord
  := 200%dword.

Fail Definition data_machine_all_refuses_dword_literal_large
  : DWord
  := 0x10000000000000000%dword.

Definition data_machine_all_delivers_qword
  : QWord
  := QWord.Zero Endian.Little.

Definition data_machine_all_delivers_qword_notation
  : forall (x : QWord) (y : QWord) .
      QWord.endian x = Endian.Big ->
      QWord.endian y = Endian.Big ->
      (x |. y)%qword = (y |. x)%qword
  := QWord.disjunction.endian.big.commutativity.

Definition data_machine_all_binds_qword_scope
  : forall (x : QWord) . QWord.flip (~. x) = x
  := QWord.flipping.involution.

Definition data_machine_all_delivers_qword_conversion
  : forall (x : QWord) (y : QWord) .
      (x |. y)%qword = (x |. QWord.with_endian (QWord.endian x) y)%qword
  := QWord.disjunction.endian.conversion.

Definition data_machine_all_delivers_qword_endianness_identity
  : forall (x : QWord) . QWord.with_endian (QWord.endian x) x = x
  := QWord.endianness.identity.

Definition data_machine_all_delivers_qword_rotation_inverse
  : forall (x : QWord) (k : Nat0) . QWord.rotate_left (QWord.rotate_right x k) k = x
  := QWord.rotation.right.inverse.

Definition data_machine_all_reads_qword_literal_little_endian
  : 0x000102030405060708090A0B0C0D0E0F%qword
    = QWord.QWord_introduction Endian.Little
        0x0F%byte 0x0E%byte 0x0D%byte 0x0C%byte 0x0B%byte 0x0A%byte 0x09%byte 0x08%byte
        0x07%byte 0x06%byte 0x05%byte 0x04%byte 0x03%byte 0x02%byte 0x01%byte 0x00%byte
  := Identity.reflexivity _.

Definition data_machine_all_reads_qword_literal_big_endian
  : 0x000102030405060708090A0B0C0D0E0F%qword_big
    = QWord.QWord_introduction Endian.Big
        0x00%byte 0x01%byte 0x02%byte 0x03%byte 0x04%byte 0x05%byte 0x06%byte 0x07%byte
        0x08%byte 0x09%byte 0x0A%byte 0x0B%byte 0x0C%byte 0x0D%byte 0x0E%byte 0x0F%byte
  := Identity.reflexivity _.

Definition data_machine_all_computes_qword_with_endian
  : QWord.with_endian Endian.Big 0x000102030405060708090A0B0C0D0E0F
    = 0x000102030405060708090A0B0C0D0E0F%qword_big
  := Identity.reflexivity _.

Definition data_machine_all_computes_qword_mixed_sejunction
  : (0x0123456789ABCDEF0123456789ABCDEF ^. 0x0123456789ABCDEF0123456789ABCDEF%qword_big)%qword
    = 0x0%qword
  := Identity.reflexivity _.

Definition data_machine_all_computes_qword_xor_big_endian
  : QWord.xor_big_endian 0xFF 0xF0 = 0x0F%qword_big
  := Identity.reflexivity _.

Definition data_machine_all_computes_qword_shift_right
  : QWord.shift_right 0x80000000000000000000000000000000 127%n0 = 0x1%qword
  := Identity.reflexivity _.

Definition data_machine_all_computes_qword_rotate_left
  : QWord.rotate_left 0x80000000000000000000000000000001 1%n0 = 0x3%qword
  := Identity.reflexivity _.

Definition data_machine_all_delivers_qword_bytes_retraction
  : forall (x : QWord) . QWord.from_bytes (QWord.endian x) (QWord.to_bytes x) = Some x
  := QWord.conversion.bytes.retraction.

Fail Definition data_machine_all_refuses_qword_literal_decimal
  : QWord
  := 200%qword.

Fail Definition data_machine_all_refuses_qword_literal_large
  : QWord
  := 0x100000000000000000000000000000000%qword.

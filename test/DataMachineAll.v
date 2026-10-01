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

Definition data_machine_all_delivers_uint8_byte_retraction
  : forall (b : Byte) . UInt8.to_byte (UInt8.from_byte b) = b
  := UInt8.conversion.byte.retraction.

Definition data_machine_all_delivers_uint8_byte_section
  : forall (x : UInt8) . UInt8.from_byte (UInt8.to_byte x) = x
  := UInt8.conversion.byte.section.

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

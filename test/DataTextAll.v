(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Data.Text.All.

Definition data_text_all_delivers_source_byte
  : SourceByte
  := SourceByte.x41.

Definition data_text_all_delivers_source_byte_conversion_retraction
  : forall (b : Byte) . SourceByte.to_byte (SourceByte.from_byte b) = b
  := SourceByte.conversion.byte.retraction.

Definition data_text_all_delivers_source_byte_conversion_section
  : forall (s : SourceByte) . SourceByte.from_byte (SourceByte.to_byte s) = s
  := SourceByte.conversion.byte.section.

Definition data_text_all_computes_source_byte_to_byte
  : SourceByte.to_byte SourceByte.x41 = 0x41%byte
  := Identity.reflexivity _.

Definition data_text_all_computes_source_byte_from_byte
  : SourceByte.from_byte 0xc3%byte = SourceByte.xc3
  := Identity.reflexivity _.

Definition data_text_all_computes_source_byte_ends
  : SourceByte.to_byte SourceByte.x00 = Byte.Zero
    /\ SourceByte.from_byte 0xff%byte = SourceByte.xff
  := conjoin (Identity.reflexivity _), (Identity.reflexivity _).

Definition data_text_all_delivers_ascii
  : Ascii
  := "A"%ac.

Definition data_text_all_delivers_ascii_conversion_retraction
  : forall (b : Byte) . Ascii.to_byte (Ascii.from_byte b) = b
  := Ascii.conversion.byte.retraction.

Definition data_text_all_delivers_ascii_conversion_section
  : forall (c : Ascii) . Ascii.from_byte (Ascii.to_byte c) = c
  := Ascii.conversion.byte.section.

Definition data_text_all_delivers_ascii_source_bytes_section
  : forall (c : Ascii) . Ascii.from_source_bytes (Ascii.to_source_bytes c) = Some c
  := Ascii.conversion.source_bytes.section.

Definition data_text_all_reads_ascii_literal
  : Ascii.to_byte "A"%ac = 0x41%byte
  := Identity.reflexivity _.

Definition data_text_all_binds_ascii_scope
  : Ascii.to_byte "z" = 0x7a%byte
  := Identity.reflexivity _.

Definition data_text_all_reads_ascii_literal_quote
  : Ascii.to_byte """"%ac = 0x22%byte
  := Identity.reflexivity _.

Fail Definition data_text_all_refuses_ascii_literal_empty
  : Ascii
  := ""%ac.

Fail Definition data_text_all_refuses_ascii_literal_long
  : Ascii
  := "ab"%ac.

Definition data_text_all_decodes_ascii_latin1
  : Ascii.from_source_bytes (SourceByte.xc3 :: SourceByte.xa9 :: [])%list
    = Some (Ascii.from_byte 0xe9%byte)
  := Identity.reflexivity _.

Definition data_text_all_encodes_ascii_latin1
  : Ascii.to_source_bytes (Ascii.from_byte 0xe9%byte)
    = (SourceByte.xc3 :: SourceByte.xa9 :: [])%list
  := Identity.reflexivity _.

Definition data_text_all_refuses_ascii_beyond_latin1
  : Ascii.from_source_bytes (SourceByte.xe2 :: SourceByte.x82 :: SourceByte.xac :: [])%list
    = None
  := Identity.reflexivity _.

Definition data_text_all_refuses_ascii_malformed
  : Ascii.from_source_bytes (SourceByte.xc3 :: SourceByte.x41 :: [])%list = None
  := Identity.reflexivity _.

Definition data_text_all_delivers_ascii_code_injectivity
  : forall (x : Ascii) (y : Ascii) . Ascii.code x = Ascii.code y -> x = y
  := @Ascii.conversion.code.injectivity.

Definition data_text_all_delivers_ascii_order_transitivity
  : forall (x : Ascii) (y : Ascii) (z : Ascii) . (x < y)%ac -> (y < z)%ac -> (x < z)%ac
  := @Ascii.order.strict.transitivity.

Definition data_text_all_delivers_ascii_comparison_specification
  : forall (x : Ascii) (y : Ascii) .
      (Ascii.compare x y = Comparison.Lt <-> (x < y)%ac)
      /\ (Ascii.compare x y = Comparison.Eq <-> x = y)
  := Ascii.comparison.specification.

Definition data_text_all_delivers_ascii_comparison_antisymmetry
  : forall (x : Ascii) (y : Ascii) .
      Ascii.compare x y = Comparison.transpose (Ascii.compare y x)
  := Ascii.comparison.antisymmetry.

Definition data_text_all_computes_ascii_code
  : Ascii.code "A"%ac = UInt8.from_byte 0x41%byte
  := Identity.reflexivity _.

Definition data_text_all_computes_ascii_compare
  : Ascii.compare "A"%ac "a"%ac = Comparison.Lt
    /\ Ascii.compare "a"%ac "a"%ac = Comparison.Eq
    /\ Ascii.compare "b"%ac "a"%ac = Comparison.Gt
  := conjoin (Identity.reflexivity _), (conjoin (Identity.reflexivity _), (Identity.reflexivity _)).

Definition data_text_all_computes_ascii_min
  : Ascii.min "z"%ac "0"%ac = "0"%ac
  := Identity.reflexivity _.

Definition data_text_all_delivers_ascii_digit_specification
  : forall (c : Ascii) .
      Ascii.is_digit c = true
      <-> (Ascii.from_byte 0x30%byte <= c /\ c <= Ascii.from_byte 0x39%byte)%ac
  := Ascii.classification.digit.specification.

Definition data_text_all_delivers_ascii_upper_specification
  : forall (c : Ascii) .
      Ascii.is_upper c = true
      <-> (Ascii.from_byte 0x41%byte <= c /\ c <= Ascii.from_byte 0x5a%byte)%ac
  := Ascii.classification.upper.specification.

Definition data_text_all_delivers_ascii_lower_specification
  : forall (c : Ascii) .
      Ascii.is_lower c = true
      <-> (Ascii.from_byte 0x61%byte <= c /\ c <= Ascii.from_byte 0x7a%byte)%ac
  := Ascii.classification.lower.specification.

Definition data_text_all_delivers_ascii_letter_specification
  : forall (c : Ascii) .
      Ascii.is_letter c = true <-> Ascii.is_upper c = true \/ Ascii.is_lower c = true
  := Ascii.classification.letter.specification.

Definition data_text_all_delivers_ascii_whitespace_specification
  : forall (c : Ascii) .
      Ascii.is_whitespace c = true
      <-> c = Ascii.from_byte 0x20%byte
          \/ (Ascii.from_byte 0x09%byte <= c /\ c <= Ascii.from_byte 0x0d%byte)%ac
  := Ascii.classification.whitespace.specification.

Definition data_text_all_delivers_ascii_exclusion
  : forall (c : Ascii) . Bool.and (Ascii.is_upper c) (Ascii.is_lower c) = false
  := Ascii.classification.exclusion.

Definition data_text_all_delivers_ascii_uppercasing_invariance
  : forall (c : Ascii) . Ascii.is_lower c = false -> Ascii.to_upper c = c
  := Ascii.uppercasing.invariance.

Definition data_text_all_delivers_ascii_uppercasing_idempotence
  : forall (c : Ascii) . Ascii.to_upper (Ascii.to_upper c) = Ascii.to_upper c
  := Ascii.uppercasing.idempotence.

Definition data_text_all_delivers_ascii_uppercasing_absorption
  : forall (c : Ascii) . Ascii.to_upper (Ascii.to_lower c) = Ascii.to_upper c
  := Ascii.uppercasing.absorption.

Definition data_text_all_delivers_ascii_uppercasing_inversion
  : forall (c : Ascii) . Ascii.is_upper c = true -> Ascii.to_upper (Ascii.to_lower c) = c
  := Ascii.uppercasing.inversion.of.lowercasing.

Definition data_text_all_delivers_ascii_lowercasing_invariance
  : forall (c : Ascii) . Ascii.is_upper c = false -> Ascii.to_lower c = c
  := Ascii.lowercasing.invariance.

Definition data_text_all_delivers_ascii_lowercasing_idempotence
  : forall (c : Ascii) . Ascii.to_lower (Ascii.to_lower c) = Ascii.to_lower c
  := Ascii.lowercasing.idempotence.

Definition data_text_all_delivers_ascii_lowercasing_absorption
  : forall (c : Ascii) . Ascii.to_lower (Ascii.to_upper c) = Ascii.to_lower c
  := Ascii.lowercasing.absorption.

Definition data_text_all_delivers_ascii_lowercasing_inversion
  : forall (c : Ascii) . Ascii.is_lower c = true -> Ascii.to_lower (Ascii.to_upper c) = c
  := Ascii.lowercasing.inversion.of.uppercasing.

Definition data_text_all_computes_ascii_classes
  : Ascii.is_digit "7"%ac = true
    /\ Ascii.is_digit "a"%ac = false
    /\ Ascii.is_whitespace " "%ac = true
    /\ Ascii.is_whitespace (Ascii.from_byte 0x0a%byte) = true
  := conjoin (Identity.reflexivity _),
       (conjoin (Identity.reflexivity _),
         (conjoin (Identity.reflexivity _), (Identity.reflexivity _))).

Definition data_text_all_computes_ascii_latin1_letter
  : Ascii.is_letter (Ascii.from_byte 0xe9%byte) = false
    /\ Ascii.to_upper (Ascii.from_byte 0xe9%byte) = Ascii.from_byte 0xe9%byte
  := conjoin (Identity.reflexivity _), (Identity.reflexivity _).

Definition data_text_all_computes_ascii_case
  : Ascii.to_upper "a"%ac = "A"%ac
    /\ Ascii.to_upper "A"%ac = "A"%ac
    /\ Ascii.to_upper "1"%ac = "1"%ac
    /\ Ascii.to_lower "Q"%ac = "q"%ac
  := conjoin (Identity.reflexivity _),
       (conjoin (Identity.reflexivity _),
         (conjoin (Identity.reflexivity _), (Identity.reflexivity _))).

Definition data_text_all_delivers_ascii_str
  : AsciiStr
  := "abc"%a.

Definition data_text_all_delivers_ascii_str_conversion_retraction
  : forall (l : List Ascii) . AsciiStr.to_list (AsciiStr.from_list l) = l
  := AsciiStr.conversion.list.retraction.

Definition data_text_all_delivers_ascii_str_conversion_section
  : forall (s : AsciiStr) . AsciiStr.from_list (AsciiStr.to_list s) = s
  := AsciiStr.conversion.list.section.

Definition data_text_all_delivers_ascii_str_source_bytes_section
  : forall (s : AsciiStr) . AsciiStr.from_source_bytes (AsciiStr.to_source_bytes s) = Some s
  := AsciiStr.conversion.source_bytes.section.

Definition data_text_all_delivers_ascii_str_concatenation_associativity
  : forall (s : AsciiStr) (t : AsciiStr) (u : AsciiStr) . ((s ++ t) ++ u = s ++ (t ++ u))%a
  := AsciiStr.concatenation.associativity.

Definition data_text_all_delivers_ascii_str_concatenation_identity
  : forall (s : AsciiStr) . ((AsciiStr.empty ++ s = s) /\ (s ++ AsciiStr.empty = s))%a
  := AsciiStr.concatenation.identity.

Definition data_text_all_delivers_ascii_str_length_additivity
  : forall (s : AsciiStr) (t : AsciiStr) .
      AsciiStr.length (s ++ t)%a = (AsciiStr.length s + AsciiStr.length t)%n0
  := AsciiStr.length.additivity.over.concatenation.

Definition data_text_all_delivers_ascii_str_uppercasing_length
  : forall (s : AsciiStr) . AsciiStr.length (AsciiStr.to_upper s) = AsciiStr.length s
  := AsciiStr.uppercasing.preservation.of.length.

Definition data_text_all_delivers_ascii_str_uppercasing_distributivity
  : forall (s : AsciiStr) (t : AsciiStr) .
      (AsciiStr.to_upper (s ++ t) = AsciiStr.to_upper s ++ AsciiStr.to_upper t)%a
  := AsciiStr.uppercasing.distributivity.over.concatenation.

Definition data_text_all_delivers_ascii_str_lowercasing_length
  : forall (s : AsciiStr) . AsciiStr.length (AsciiStr.to_lower s) = AsciiStr.length s
  := AsciiStr.lowercasing.preservation.of.length.

Definition data_text_all_delivers_ascii_str_lowercasing_distributivity
  : forall (s : AsciiStr) (t : AsciiStr) .
      (AsciiStr.to_lower (s ++ t) = AsciiStr.to_lower s ++ AsciiStr.to_lower t)%a
  := AsciiStr.lowercasing.distributivity.over.concatenation.

Definition data_text_all_computes_ascii_str_case
  : AsciiStr.to_upper "Hello, World"%a = "HELLO, WORLD"%a
    /\ AsciiStr.to_lower "Hello, World"%a = "hello, world"%a
  := conjoin (Identity.reflexivity _), (Identity.reflexivity _).

Definition data_text_all_delivers_ascii_str_indexing_specification
  : forall (s : AsciiStr) (i : Nat0) .
      (forsome (c : Ascii) . AsciiStr.get s i = Some c) <-> (i < AsciiStr.length s)%n0
  := AsciiStr.indexing.specification.

Definition data_text_all_delivers_ascii_str_indexing_left
  : forall (s : AsciiStr) (t : AsciiStr) (i : Nat0) .
      (i < AsciiStr.length s)%n0 -> AsciiStr.get (s ++ t)%a i = AsciiStr.get s i
  := AsciiStr.indexing.left.invariance.

Definition data_text_all_delivers_ascii_str_indexing_right
  : forall (s : AsciiStr) (t : AsciiStr) (i : Nat0) .
      AsciiStr.get (s ++ t)%a (AsciiStr.length s + i)%n0 = AsciiStr.get t i
  := AsciiStr.indexing.right.translation.

Definition data_text_all_delivers_ascii_str_substring_identity
  : forall (s : AsciiStr) . AsciiStr.substring s Nat0.Zero (AsciiStr.length s) = s
  := AsciiStr.substring.identity.

Definition data_text_all_delivers_ascii_str_substring_length
  : forall (s : AsciiStr) (start : Nat0) (len : Nat0) .
      AsciiStr.length (AsciiStr.substring s start len)
      = Nat0.min len (Nat0.saturating_sub (AsciiStr.length s) start)
  := AsciiStr.substring.length.

Definition data_text_all_computes_ascii_str_get
  : AsciiStr.get "abc"%a 1%n0 = Some "b"%ac
    /\ AsciiStr.get "abc"%a 3%n0 = None
  := conjoin (Identity.reflexivity _), (Identity.reflexivity _).

Definition data_text_all_computes_ascii_str_substring
  : AsciiStr.substring "Hello, World"%a 7%n0 5%n0 = "World"%a
    /\ AsciiStr.substring "abc"%a 2%n0 5%n0 = "c"%a
    /\ AsciiStr.substring "abc"%a 5%n0 1%n0 = ""%a
  := conjoin (Identity.reflexivity _),
       (conjoin (Identity.reflexivity _), (Identity.reflexivity _)).

Definition data_text_all_reads_ascii_str_literal
  : AsciiStr.to_list "ab"%a = ("a"%ac :: "b"%ac :: [])%list
  := Identity.reflexivity _.

Definition data_text_all_reads_ascii_str_literal_empty
  : ""%a = AsciiStr.empty
  := Identity.reflexivity _.

Definition data_text_all_reads_ascii_str_literal_quote
  : AsciiStr.to_list "a""b"%a = ("a"%ac :: """"%ac :: "b"%ac :: [])%list
  := Identity.reflexivity _.

Definition data_text_all_binds_ascii_str_scope
  : AsciiStr.length "four" = 4%n0
  := Identity.reflexivity _.

Definition data_text_all_computes_ascii_str_concatenation
  : ("ab" ++ "c")%a = "abc"%a
  := Identity.reflexivity _.

Definition data_text_all_decodes_ascii_str_latin1
  : AsciiStr.from_source_bytes
      (SourceByte.x68 :: SourceByte.xc3 :: SourceByte.xa9 :: SourceByte.x21 :: [])%list
    = Some (AsciiStr.from_list ("h"%ac :: Ascii.from_byte 0xe9%byte :: "!"%ac :: [])%list)
  := Identity.reflexivity _.

Definition data_text_all_encodes_ascii_str_latin1
  : AsciiStr.to_source_bytes (AsciiStr.from_list ("h"%ac :: Ascii.from_byte 0xe9%byte :: [])%list)
    = (SourceByte.x68 :: SourceByte.xc3 :: SourceByte.xa9 :: [])%list
  := Identity.reflexivity _.

Definition data_text_all_refuses_ascii_str_beyond_latin1
  : AsciiStr.from_source_bytes
      (SourceByte.x61 :: SourceByte.xe2 :: SourceByte.x82 :: SourceByte.xac :: [])%list
    = None
  := Identity.reflexivity _.

Definition data_text_all_refuses_ascii_str_truncated
  : AsciiStr.from_source_bytes (SourceByte.x61 :: SourceByte.xc3 :: [])%list = None
  := Identity.reflexivity _.

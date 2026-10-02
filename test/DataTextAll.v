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

Definition data_text_all_delivers_source_byte_bytes_retraction
  : forall (l : List Byte) . List.map SourceByte.to_byte (List.map SourceByte.from_byte l) = l
  := SourceByte.conversion.bytes.retraction.

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

Definition data_text_all_delivers_ascii_str_order_transitivity
  : forall (s : AsciiStr) (t : AsciiStr) (u : AsciiStr) . (s < t -> t < u -> s < u)%a
  := @AsciiStr.order.strict.transitivity.

Definition data_text_all_delivers_ascii_str_comparison_specification
  : forall (s : AsciiStr) (t : AsciiStr) .
      (AsciiStr.compare s t = Comparison.Lt <-> (s < t)%a)
      /\ (AsciiStr.compare s t = Comparison.Eq <-> s = t)
  := AsciiStr.comparison.specification.

Definition data_text_all_delivers_ascii_str_comparison_antisymmetry
  : forall (s : AsciiStr) (t : AsciiStr) .
      AsciiStr.compare s t = Comparison.transpose (AsciiStr.compare t s)
  := AsciiStr.comparison.antisymmetry.

Definition data_text_all_computes_ascii_str_compare
  : AsciiStr.compare "Apple"%a "apple"%a = Comparison.Lt
    /\ AsciiStr.compare "apple"%a "apply"%a = Comparison.Lt
    /\ AsciiStr.compare "app"%a "apple"%a = Comparison.Lt
    /\ AsciiStr.compare "apple"%a "apple"%a = Comparison.Eq
    /\ AsciiStr.compare "b"%a "apple"%a = Comparison.Gt
  := conjoin (Identity.reflexivity _),
       (conjoin (Identity.reflexivity _),
         (conjoin (Identity.reflexivity _),
           (conjoin (Identity.reflexivity _), (Identity.reflexivity _)))).

Definition data_text_all_computes_ascii_str_min
  : AsciiStr.min "pear"%a "peach"%a = "peach"%a
  := Identity.reflexivity _.

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

Definition data_text_all_delivers_utf8
  : Utf8
  := "A"%u8c.

Definition data_text_all_delivers_utf8_bytes_section
  : forall (c : Utf8) . Utf8.from_bytes (Utf8.to_bytes c) = Some c
  := Utf8.conversion.bytes.section.

Definition data_text_all_delivers_utf8_bytes_inversion
  : forall (l : List Byte) (c : Utf8) . Utf8.from_bytes l = Some c -> Utf8.to_bytes c = l
  := Utf8.conversion.bytes.inversion.

Definition data_text_all_delivers_utf8_bytes_injectivity
  : forall (c : Utf8) (d : Utf8) . Utf8.to_bytes c = Utf8.to_bytes d -> c = d
  := @Utf8.conversion.bytes.injectivity.

Definition data_text_all_delivers_utf8_source_bytes_section
  : forall (c : Utf8) . Utf8.from_source_bytes (Utf8.to_source_bytes c) = Some c
  := Utf8.conversion.source_bytes.section.

Definition data_text_all_reads_utf8_literal
  : Utf8.to_bytes "A"%u8c = (0x41%byte :: [])%list
  := Identity.reflexivity _.

Definition data_text_all_binds_utf8_scope
  : Utf8.to_bytes "z" = (0x7a%byte :: [])%list
  := Identity.reflexivity _.

Definition data_text_all_reads_utf8_literal_quote
  : Utf8.to_bytes """"%u8c = (0x22%byte :: [])%list
  := Identity.reflexivity _.

Fail Definition data_text_all_refuses_utf8_literal_empty
  : Utf8
  := ""%u8c.

Fail Definition data_text_all_refuses_utf8_literal_long
  : Utf8
  := "ab"%u8c.

Fail Definition data_text_all_refuses_utf8_overlong_value
  : Utf8
  := Utf8.TwoBytes 0xc0%byte 0x80%byte I.

Definition data_text_all_decodes_utf8_two_bytes
  : Utf8.from_bytes (0xc3%byte :: 0xa9%byte :: [])%list
    = Some (Utf8.TwoBytes 0xc3%byte 0xa9%byte I)
  := Identity.reflexivity _.

Definition data_text_all_decodes_utf8_three_bytes
  : Utf8.from_bytes (0xe2%byte :: 0x82%byte :: 0xac%byte :: [])%list
    = Some (Utf8.ThreeBytes 0xe2%byte 0x82%byte 0xac%byte I)
  := Identity.reflexivity _.

Definition data_text_all_decodes_utf8_four_bytes
  : Utf8.from_bytes (0xf0%byte :: 0x9f%byte :: 0x98%byte :: 0x80%byte :: [])%list
    = Some (Utf8.FourBytes 0xf0%byte 0x9f%byte 0x98%byte 0x80%byte I)
  := Identity.reflexivity _.

Definition data_text_all_decodes_utf8_last
  : Utf8.from_bytes (0xf4%byte :: 0x8f%byte :: 0xbf%byte :: 0xbf%byte :: [])%list
    = Some (Utf8.FourBytes 0xf4%byte 0x8f%byte 0xbf%byte 0xbf%byte I)
  := Identity.reflexivity _.

Definition data_text_all_decodes_utf8_source_bytes
  : Utf8.from_source_bytes (SourceByte.xe2 :: SourceByte.x82 :: SourceByte.xac :: [])%list
    = Some (Utf8.ThreeBytes 0xe2%byte 0x82%byte 0xac%byte I)
  := Identity.reflexivity _.

Definition data_text_all_encodes_utf8_source_bytes
  : Utf8.to_source_bytes (Utf8.TwoBytes 0xc3%byte 0xa9%byte I)
    = (SourceByte.xc3 :: SourceByte.xa9 :: [])%list
  := Identity.reflexivity _.

Definition data_text_all_refuses_utf8_overlong_two_bytes
  : Utf8.from_bytes (0xc0%byte :: 0x80%byte :: [])%list = None
  := Identity.reflexivity _.

Definition data_text_all_refuses_utf8_overlong_three_bytes
  : Utf8.from_bytes (0xe0%byte :: 0x9f%byte :: 0xbf%byte :: [])%list = None
  := Identity.reflexivity _.

Definition data_text_all_refuses_utf8_overlong_four_bytes
  : Utf8.from_bytes (0xf0%byte :: 0x8f%byte :: 0xbf%byte :: 0xbf%byte :: [])%list = None
  := Identity.reflexivity _.

Definition data_text_all_refuses_utf8_surrogate
  : Utf8.from_bytes (0xed%byte :: 0xa0%byte :: 0x80%byte :: [])%list = None
  := Identity.reflexivity _.

Definition data_text_all_refuses_utf8_beyond_last
  : Utf8.from_bytes (0xf4%byte :: 0x90%byte :: 0x80%byte :: 0x80%byte :: [])%list = None
  := Identity.reflexivity _.

Definition data_text_all_refuses_utf8_malformed
  : Utf8.from_bytes (0xff%byte :: [])%list = None
  := Identity.reflexivity _.

Definition data_text_all_refuses_utf8_lone_tail
  : Utf8.from_bytes (0x80%byte :: [])%list = None
  := Identity.reflexivity _.

Definition data_text_all_refuses_utf8_truncated
  : Utf8.from_bytes (0xe2%byte :: 0x82%byte :: [])%list = None
  := Identity.reflexivity _.

Definition data_text_all_refuses_utf8_two_characters
  : Utf8.from_bytes (0x41%byte :: 0x42%byte :: [])%list = None
  := Identity.reflexivity _.

Definition data_text_all_delivers_utf8_str
  : Utf8Str
  := "abc"%u8.

Definition data_text_all_delivers_utf8_str_conversion_retraction
  : forall (l : List Utf8) . Utf8Str.to_list (Utf8Str.from_list l) = l
  := Utf8Str.conversion.list.retraction.

Definition data_text_all_delivers_utf8_str_conversion_section
  : forall (s : Utf8Str) . Utf8Str.from_list (Utf8Str.to_list s) = s
  := Utf8Str.conversion.list.section.

Definition data_text_all_delivers_utf8_str_bytes_section
  : forall (s : Utf8Str) . Utf8Str.from_bytes (Utf8Str.to_bytes s) = Some s
  := Utf8Str.conversion.bytes.section.

Definition data_text_all_delivers_utf8_str_bytes_injectivity
  : forall (s : Utf8Str) (t : Utf8Str) . Utf8Str.to_bytes s = Utf8Str.to_bytes t -> s = t
  := @Utf8Str.conversion.bytes.injectivity.

Definition data_text_all_delivers_utf8_str_source_bytes_section
  : forall (s : Utf8Str) . Utf8Str.from_source_bytes (Utf8Str.to_source_bytes s) = Some s
  := Utf8Str.conversion.source_bytes.section.

Definition data_text_all_delivers_utf8_str_concatenation_associativity
  : forall (s : Utf8Str) (t : Utf8Str) (u : Utf8Str) . ((s ++ t) ++ u = s ++ (t ++ u))%u8
  := Utf8Str.concatenation.associativity.

Definition data_text_all_delivers_utf8_str_concatenation_identity
  : forall (s : Utf8Str) . ((Utf8Str.empty ++ s = s) /\ (s ++ Utf8Str.empty = s))%u8
  := Utf8Str.concatenation.identity.

Definition data_text_all_delivers_utf8_str_length_additivity
  : forall (s : Utf8Str) (t : Utf8Str) .
      Utf8Str.length (s ++ t)%u8 = (Utf8Str.length s + Utf8Str.length t)%n0
  := Utf8Str.length.additivity.over.concatenation.

Definition data_text_all_reads_utf8_str_literal
  : Utf8Str.to_list "ab"%u8 = ("a"%u8c :: "b"%u8c :: [])%list
  := Identity.reflexivity _.

Definition data_text_all_reads_utf8_str_literal_empty
  : ""%u8 = Utf8Str.empty
  := Identity.reflexivity _.

Definition data_text_all_reads_utf8_str_literal_quote
  : Utf8Str.to_list "a""b"%u8 = ("a"%u8c :: """"%u8c :: "b"%u8c :: [])%list
  := Identity.reflexivity _.

Definition data_text_all_binds_utf8_str_scope
  : Utf8Str.length "four" = 4%n0
  := Identity.reflexivity _.

Definition data_text_all_computes_utf8_str_concatenation
  : ("ab" ++ "c")%u8 = "abc"%u8
  := Identity.reflexivity _.

Definition data_text_all_decodes_utf8_str
  : Utf8Str.from_bytes
      (0x68%byte :: 0xc3%byte :: 0xa9%byte :: 0xe2%byte :: 0x82%byte :: 0xac%byte
        :: 0xf0%byte :: 0x9f%byte :: 0x98%byte :: 0x80%byte :: [])%list
    = Some
        (Utf8Str.from_list
          ("h"%u8c
            :: Utf8.TwoBytes 0xc3%byte 0xa9%byte I
            :: Utf8.ThreeBytes 0xe2%byte 0x82%byte 0xac%byte I
            :: Utf8.FourBytes 0xf0%byte 0x9f%byte 0x98%byte 0x80%byte I
            :: [])%list)
  := Identity.reflexivity _.

Definition data_text_all_computes_utf8_str_length
  : Option.map Utf8Str.length
      (Utf8Str.from_bytes
        (0xc3%byte :: 0xa9%byte :: 0xe2%byte :: 0x82%byte :: 0xac%byte :: [])%list)
    = Some 2%n0
  := Identity.reflexivity _.

Definition data_text_all_decodes_utf8_str_source_bytes
  : Utf8Str.from_source_bytes (SourceByte.x68 :: SourceByte.xc3 :: SourceByte.xa9 :: [])%list
    = Some (Utf8Str.from_list ("h"%u8c :: Utf8.TwoBytes 0xc3%byte 0xa9%byte I :: [])%list)
  := Identity.reflexivity _.

Definition data_text_all_encodes_utf8_str
  : Utf8Str.to_bytes (Utf8Str.from_list ("h"%u8c :: Utf8.TwoBytes 0xc3%byte 0xa9%byte I :: [])%list)
    = (0x68%byte :: 0xc3%byte :: 0xa9%byte :: [])%list
  := Identity.reflexivity _.

Definition data_text_all_refuses_utf8_str_truncated
  : Utf8Str.from_bytes (0x61%byte :: 0xe2%byte :: 0x82%byte :: [])%list = None
  := Identity.reflexivity _.

Definition data_text_all_refuses_utf8_str_surrogate
  : Utf8Str.from_bytes (0x61%byte :: 0xed%byte :: 0xa0%byte :: 0x80%byte :: [])%list = None
  := Identity.reflexivity _.

Definition data_text_all_refuses_utf8_str_overlong
  : Utf8Str.from_bytes (0xc0%byte :: 0x80%byte :: 0x61%byte :: [])%list = None
  := Identity.reflexivity _.

Definition data_text_all_delivers_utf8_ascii_retraction
  : forall (a : Ascii) . Utf8.to_ascii (Utf8.from_ascii a) = Some a
  := Utf8.conversion.ascii.retraction.

Definition data_text_all_delivers_utf8_ascii_inversion
  : forall (c : Utf8) (a : Ascii) . Utf8.to_ascii c = Some a -> Utf8.from_ascii a = c
  := Utf8.conversion.ascii.inversion.

Definition data_text_all_computes_utf8_from_ascii
  : Utf8.from_ascii "A"%ac = "A"%u8c
    /\ Utf8.from_ascii (Ascii.from_byte 0xe9%byte) = Utf8.TwoBytes 0xc3%byte 0xa9%byte I
  := conjoin (Identity.reflexivity _), (Identity.reflexivity _).

Definition data_text_all_computes_utf8_to_ascii
  : Utf8.to_ascii "A"%u8c = Some "A"%ac
    /\ Utf8.to_ascii (Utf8.TwoBytes 0xc3%byte 0xa9%byte I) = Some (Ascii.from_byte 0xe9%byte)
  := conjoin (Identity.reflexivity _), (Identity.reflexivity _).

Definition data_text_all_refuses_utf8_to_ascii_beyond_latin1
  : Utf8.to_ascii (Utf8.TwoBytes 0xc4%byte 0x80%byte I) = None
    /\ Utf8.to_ascii (Utf8.ThreeBytes 0xe2%byte 0x82%byte 0xac%byte I) = None
  := conjoin (Identity.reflexivity _), (Identity.reflexivity _).

Definition data_text_all_delivers_utf8_str_ascii_retraction
  : forall (s : AsciiStr) . Utf8Str.to_ascii_str (Utf8Str.from_ascii_str s) = Some s
  := Utf8Str.conversion.ascii.retraction.

Definition data_text_all_delivers_utf8_str_ascii_inversion
  : forall (t : Utf8Str) (s : AsciiStr) .
      Utf8Str.to_ascii_str t = Some s -> Utf8Str.from_ascii_str s = t
  := Utf8Str.conversion.ascii.inversion.

Definition data_text_all_delivers_utf8_str_ascii_length
  : forall (s : AsciiStr) . Utf8Str.length (Utf8Str.from_ascii_str s) = AsciiStr.length s
  := Utf8Str.conversion.ascii.preservation.of.length.

Definition data_text_all_computes_utf8_str_from_ascii_str
  : Utf8Str.from_ascii_str "ab"%a = "ab"%u8
    /\ Utf8Str.from_ascii_str (AsciiStr.from_list ("h"%ac :: Ascii.from_byte 0xe9%byte :: [])%list)
      = Utf8Str.from_list ("h"%u8c :: Utf8.TwoBytes 0xc3%byte 0xa9%byte I :: [])%list
  := conjoin (Identity.reflexivity _), (Identity.reflexivity _).

Definition data_text_all_computes_utf8_str_to_ascii_str
  : Utf8Str.to_ascii_str
      (Utf8Str.from_list ("h"%u8c :: Utf8.TwoBytes 0xc3%byte 0xa9%byte I :: [])%list)
    = Some (AsciiStr.from_list ("h"%ac :: Ascii.from_byte 0xe9%byte :: [])%list)
  := Identity.reflexivity _.

Definition data_text_all_refuses_utf8_str_to_ascii_str_beyond_latin1
  : Utf8Str.to_ascii_str
      (Utf8Str.from_list ("a"%u8c :: Utf8.ThreeBytes 0xe2%byte 0x82%byte 0xac%byte I :: [])%list)
    = None
  := Identity.reflexivity _.

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

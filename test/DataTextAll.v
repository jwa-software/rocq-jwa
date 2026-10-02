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

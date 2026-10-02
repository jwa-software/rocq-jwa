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

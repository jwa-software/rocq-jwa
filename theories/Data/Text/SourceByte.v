(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Data.Collection.List.
From jwa Require Import Data.Machine.Byte.

Module SourceByte. (* SourceByte *)

(* A byte of the source text, as the plugin behind [String Notation] hands a
 * string literal over: the literal's UTF-8 bytes, each found by constructor
 * position, so the type has one argument-free constructor per value, [x00] to
 * [xff] in code order.
 *)
Inductive T : Type :=
  | x00 : T
  | x01 : T
  | x02 : T
  | x03 : T
  | x04 : T
  | x05 : T
  | x06 : T
  | x07 : T
  | x08 : T
  | x09 : T
  | x0a : T
  | x0b : T
  | x0c : T
  | x0d : T
  | x0e : T
  | x0f : T
  | x10 : T
  | x11 : T
  | x12 : T
  | x13 : T
  | x14 : T
  | x15 : T
  | x16 : T
  | x17 : T
  | x18 : T
  | x19 : T
  | x1a : T
  | x1b : T
  | x1c : T
  | x1d : T
  | x1e : T
  | x1f : T
  | x20 : T
  | x21 : T
  | x22 : T
  | x23 : T
  | x24 : T
  | x25 : T
  | x26 : T
  | x27 : T
  | x28 : T
  | x29 : T
  | x2a : T
  | x2b : T
  | x2c : T
  | x2d : T
  | x2e : T
  | x2f : T
  | x30 : T
  | x31 : T
  | x32 : T
  | x33 : T
  | x34 : T
  | x35 : T
  | x36 : T
  | x37 : T
  | x38 : T
  | x39 : T
  | x3a : T
  | x3b : T
  | x3c : T
  | x3d : T
  | x3e : T
  | x3f : T
  | x40 : T
  | x41 : T
  | x42 : T
  | x43 : T
  | x44 : T
  | x45 : T
  | x46 : T
  | x47 : T
  | x48 : T
  | x49 : T
  | x4a : T
  | x4b : T
  | x4c : T
  | x4d : T
  | x4e : T
  | x4f : T
  | x50 : T
  | x51 : T
  | x52 : T
  | x53 : T
  | x54 : T
  | x55 : T
  | x56 : T
  | x57 : T
  | x58 : T
  | x59 : T
  | x5a : T
  | x5b : T
  | x5c : T
  | x5d : T
  | x5e : T
  | x5f : T
  | x60 : T
  | x61 : T
  | x62 : T
  | x63 : T
  | x64 : T
  | x65 : T
  | x66 : T
  | x67 : T
  | x68 : T
  | x69 : T
  | x6a : T
  | x6b : T
  | x6c : T
  | x6d : T
  | x6e : T
  | x6f : T
  | x70 : T
  | x71 : T
  | x72 : T
  | x73 : T
  | x74 : T
  | x75 : T
  | x76 : T
  | x77 : T
  | x78 : T
  | x79 : T
  | x7a : T
  | x7b : T
  | x7c : T
  | x7d : T
  | x7e : T
  | x7f : T
  | x80 : T
  | x81 : T
  | x82 : T
  | x83 : T
  | x84 : T
  | x85 : T
  | x86 : T
  | x87 : T
  | x88 : T
  | x89 : T
  | x8a : T
  | x8b : T
  | x8c : T
  | x8d : T
  | x8e : T
  | x8f : T
  | x90 : T
  | x91 : T
  | x92 : T
  | x93 : T
  | x94 : T
  | x95 : T
  | x96 : T
  | x97 : T
  | x98 : T
  | x99 : T
  | x9a : T
  | x9b : T
  | x9c : T
  | x9d : T
  | x9e : T
  | x9f : T
  | xa0 : T
  | xa1 : T
  | xa2 : T
  | xa3 : T
  | xa4 : T
  | xa5 : T
  | xa6 : T
  | xa7 : T
  | xa8 : T
  | xa9 : T
  | xaa : T
  | xab : T
  | xac : T
  | xad : T
  | xae : T
  | xaf : T
  | xb0 : T
  | xb1 : T
  | xb2 : T
  | xb3 : T
  | xb4 : T
  | xb5 : T
  | xb6 : T
  | xb7 : T
  | xb8 : T
  | xb9 : T
  | xba : T
  | xbb : T
  | xbc : T
  | xbd : T
  | xbe : T
  | xbf : T
  | xc0 : T
  | xc1 : T
  | xc2 : T
  | xc3 : T
  | xc4 : T
  | xc5 : T
  | xc6 : T
  | xc7 : T
  | xc8 : T
  | xc9 : T
  | xca : T
  | xcb : T
  | xcc : T
  | xcd : T
  | xce : T
  | xcf : T
  | xd0 : T
  | xd1 : T
  | xd2 : T
  | xd3 : T
  | xd4 : T
  | xd5 : T
  | xd6 : T
  | xd7 : T
  | xd8 : T
  | xd9 : T
  | xda : T
  | xdb : T
  | xdc : T
  | xdd : T
  | xde : T
  | xdf : T
  | xe0 : T
  | xe1 : T
  | xe2 : T
  | xe3 : T
  | xe4 : T
  | xe5 : T
  | xe6 : T
  | xe7 : T
  | xe8 : T
  | xe9 : T
  | xea : T
  | xeb : T
  | xec : T
  | xed : T
  | xee : T
  | xef : T
  | xf0 : T
  | xf1 : T
  | xf2 : T
  | xf3 : T
  | xf4 : T
  | xf5 : T
  | xf6 : T
  | xf7 : T
  | xf8 : T
  | xf9 : T
  | xfa : T
  | xfb : T
  | xfc : T
  | xfd : T
  | xfe : T
  | xff : T.

Abbreviation SourceByte := T.

(* [SourceByte -> Byte] *)
Definition to_byte := fun (s : SourceByte) .
  match s with
  | x00 => 0x00%byte
  | x01 => 0x01%byte
  | x02 => 0x02%byte
  | x03 => 0x03%byte
  | x04 => 0x04%byte
  | x05 => 0x05%byte
  | x06 => 0x06%byte
  | x07 => 0x07%byte
  | x08 => 0x08%byte
  | x09 => 0x09%byte
  | x0a => 0x0a%byte
  | x0b => 0x0b%byte
  | x0c => 0x0c%byte
  | x0d => 0x0d%byte
  | x0e => 0x0e%byte
  | x0f => 0x0f%byte
  | x10 => 0x10%byte
  | x11 => 0x11%byte
  | x12 => 0x12%byte
  | x13 => 0x13%byte
  | x14 => 0x14%byte
  | x15 => 0x15%byte
  | x16 => 0x16%byte
  | x17 => 0x17%byte
  | x18 => 0x18%byte
  | x19 => 0x19%byte
  | x1a => 0x1a%byte
  | x1b => 0x1b%byte
  | x1c => 0x1c%byte
  | x1d => 0x1d%byte
  | x1e => 0x1e%byte
  | x1f => 0x1f%byte
  | x20 => 0x20%byte
  | x21 => 0x21%byte
  | x22 => 0x22%byte
  | x23 => 0x23%byte
  | x24 => 0x24%byte
  | x25 => 0x25%byte
  | x26 => 0x26%byte
  | x27 => 0x27%byte
  | x28 => 0x28%byte
  | x29 => 0x29%byte
  | x2a => 0x2a%byte
  | x2b => 0x2b%byte
  | x2c => 0x2c%byte
  | x2d => 0x2d%byte
  | x2e => 0x2e%byte
  | x2f => 0x2f%byte
  | x30 => 0x30%byte
  | x31 => 0x31%byte
  | x32 => 0x32%byte
  | x33 => 0x33%byte
  | x34 => 0x34%byte
  | x35 => 0x35%byte
  | x36 => 0x36%byte
  | x37 => 0x37%byte
  | x38 => 0x38%byte
  | x39 => 0x39%byte
  | x3a => 0x3a%byte
  | x3b => 0x3b%byte
  | x3c => 0x3c%byte
  | x3d => 0x3d%byte
  | x3e => 0x3e%byte
  | x3f => 0x3f%byte
  | x40 => 0x40%byte
  | x41 => 0x41%byte
  | x42 => 0x42%byte
  | x43 => 0x43%byte
  | x44 => 0x44%byte
  | x45 => 0x45%byte
  | x46 => 0x46%byte
  | x47 => 0x47%byte
  | x48 => 0x48%byte
  | x49 => 0x49%byte
  | x4a => 0x4a%byte
  | x4b => 0x4b%byte
  | x4c => 0x4c%byte
  | x4d => 0x4d%byte
  | x4e => 0x4e%byte
  | x4f => 0x4f%byte
  | x50 => 0x50%byte
  | x51 => 0x51%byte
  | x52 => 0x52%byte
  | x53 => 0x53%byte
  | x54 => 0x54%byte
  | x55 => 0x55%byte
  | x56 => 0x56%byte
  | x57 => 0x57%byte
  | x58 => 0x58%byte
  | x59 => 0x59%byte
  | x5a => 0x5a%byte
  | x5b => 0x5b%byte
  | x5c => 0x5c%byte
  | x5d => 0x5d%byte
  | x5e => 0x5e%byte
  | x5f => 0x5f%byte
  | x60 => 0x60%byte
  | x61 => 0x61%byte
  | x62 => 0x62%byte
  | x63 => 0x63%byte
  | x64 => 0x64%byte
  | x65 => 0x65%byte
  | x66 => 0x66%byte
  | x67 => 0x67%byte
  | x68 => 0x68%byte
  | x69 => 0x69%byte
  | x6a => 0x6a%byte
  | x6b => 0x6b%byte
  | x6c => 0x6c%byte
  | x6d => 0x6d%byte
  | x6e => 0x6e%byte
  | x6f => 0x6f%byte
  | x70 => 0x70%byte
  | x71 => 0x71%byte
  | x72 => 0x72%byte
  | x73 => 0x73%byte
  | x74 => 0x74%byte
  | x75 => 0x75%byte
  | x76 => 0x76%byte
  | x77 => 0x77%byte
  | x78 => 0x78%byte
  | x79 => 0x79%byte
  | x7a => 0x7a%byte
  | x7b => 0x7b%byte
  | x7c => 0x7c%byte
  | x7d => 0x7d%byte
  | x7e => 0x7e%byte
  | x7f => 0x7f%byte
  | x80 => 0x80%byte
  | x81 => 0x81%byte
  | x82 => 0x82%byte
  | x83 => 0x83%byte
  | x84 => 0x84%byte
  | x85 => 0x85%byte
  | x86 => 0x86%byte
  | x87 => 0x87%byte
  | x88 => 0x88%byte
  | x89 => 0x89%byte
  | x8a => 0x8a%byte
  | x8b => 0x8b%byte
  | x8c => 0x8c%byte
  | x8d => 0x8d%byte
  | x8e => 0x8e%byte
  | x8f => 0x8f%byte
  | x90 => 0x90%byte
  | x91 => 0x91%byte
  | x92 => 0x92%byte
  | x93 => 0x93%byte
  | x94 => 0x94%byte
  | x95 => 0x95%byte
  | x96 => 0x96%byte
  | x97 => 0x97%byte
  | x98 => 0x98%byte
  | x99 => 0x99%byte
  | x9a => 0x9a%byte
  | x9b => 0x9b%byte
  | x9c => 0x9c%byte
  | x9d => 0x9d%byte
  | x9e => 0x9e%byte
  | x9f => 0x9f%byte
  | xa0 => 0xa0%byte
  | xa1 => 0xa1%byte
  | xa2 => 0xa2%byte
  | xa3 => 0xa3%byte
  | xa4 => 0xa4%byte
  | xa5 => 0xa5%byte
  | xa6 => 0xa6%byte
  | xa7 => 0xa7%byte
  | xa8 => 0xa8%byte
  | xa9 => 0xa9%byte
  | xaa => 0xaa%byte
  | xab => 0xab%byte
  | xac => 0xac%byte
  | xad => 0xad%byte
  | xae => 0xae%byte
  | xaf => 0xaf%byte
  | xb0 => 0xb0%byte
  | xb1 => 0xb1%byte
  | xb2 => 0xb2%byte
  | xb3 => 0xb3%byte
  | xb4 => 0xb4%byte
  | xb5 => 0xb5%byte
  | xb6 => 0xb6%byte
  | xb7 => 0xb7%byte
  | xb8 => 0xb8%byte
  | xb9 => 0xb9%byte
  | xba => 0xba%byte
  | xbb => 0xbb%byte
  | xbc => 0xbc%byte
  | xbd => 0xbd%byte
  | xbe => 0xbe%byte
  | xbf => 0xbf%byte
  | xc0 => 0xc0%byte
  | xc1 => 0xc1%byte
  | xc2 => 0xc2%byte
  | xc3 => 0xc3%byte
  | xc4 => 0xc4%byte
  | xc5 => 0xc5%byte
  | xc6 => 0xc6%byte
  | xc7 => 0xc7%byte
  | xc8 => 0xc8%byte
  | xc9 => 0xc9%byte
  | xca => 0xca%byte
  | xcb => 0xcb%byte
  | xcc => 0xcc%byte
  | xcd => 0xcd%byte
  | xce => 0xce%byte
  | xcf => 0xcf%byte
  | xd0 => 0xd0%byte
  | xd1 => 0xd1%byte
  | xd2 => 0xd2%byte
  | xd3 => 0xd3%byte
  | xd4 => 0xd4%byte
  | xd5 => 0xd5%byte
  | xd6 => 0xd6%byte
  | xd7 => 0xd7%byte
  | xd8 => 0xd8%byte
  | xd9 => 0xd9%byte
  | xda => 0xda%byte
  | xdb => 0xdb%byte
  | xdc => 0xdc%byte
  | xdd => 0xdd%byte
  | xde => 0xde%byte
  | xdf => 0xdf%byte
  | xe0 => 0xe0%byte
  | xe1 => 0xe1%byte
  | xe2 => 0xe2%byte
  | xe3 => 0xe3%byte
  | xe4 => 0xe4%byte
  | xe5 => 0xe5%byte
  | xe6 => 0xe6%byte
  | xe7 => 0xe7%byte
  | xe8 => 0xe8%byte
  | xe9 => 0xe9%byte
  | xea => 0xea%byte
  | xeb => 0xeb%byte
  | xec => 0xec%byte
  | xed => 0xed%byte
  | xee => 0xee%byte
  | xef => 0xef%byte
  | xf0 => 0xf0%byte
  | xf1 => 0xf1%byte
  | xf2 => 0xf2%byte
  | xf3 => 0xf3%byte
  | xf4 => 0xf4%byte
  | xf5 => 0xf5%byte
  | xf6 => 0xf6%byte
  | xf7 => 0xf7%byte
  | xf8 => 0xf8%byte
  | xf9 => 0xf9%byte
  | xfa => 0xfa%byte
  | xfb => 0xfb%byte
  | xfc => 0xfc%byte
  | xfd => 0xfd%byte
  | xfe => 0xfe%byte
  | xff => 0xff%byte
  end.

(* [Byte -> SourceByte] *)
Definition from_byte := fun (b : Byte) .
  match b with
  | 0x00%byte => x00
  | 0x01%byte => x01
  | 0x02%byte => x02
  | 0x03%byte => x03
  | 0x04%byte => x04
  | 0x05%byte => x05
  | 0x06%byte => x06
  | 0x07%byte => x07
  | 0x08%byte => x08
  | 0x09%byte => x09
  | 0x0a%byte => x0a
  | 0x0b%byte => x0b
  | 0x0c%byte => x0c
  | 0x0d%byte => x0d
  | 0x0e%byte => x0e
  | 0x0f%byte => x0f
  | 0x10%byte => x10
  | 0x11%byte => x11
  | 0x12%byte => x12
  | 0x13%byte => x13
  | 0x14%byte => x14
  | 0x15%byte => x15
  | 0x16%byte => x16
  | 0x17%byte => x17
  | 0x18%byte => x18
  | 0x19%byte => x19
  | 0x1a%byte => x1a
  | 0x1b%byte => x1b
  | 0x1c%byte => x1c
  | 0x1d%byte => x1d
  | 0x1e%byte => x1e
  | 0x1f%byte => x1f
  | 0x20%byte => x20
  | 0x21%byte => x21
  | 0x22%byte => x22
  | 0x23%byte => x23
  | 0x24%byte => x24
  | 0x25%byte => x25
  | 0x26%byte => x26
  | 0x27%byte => x27
  | 0x28%byte => x28
  | 0x29%byte => x29
  | 0x2a%byte => x2a
  | 0x2b%byte => x2b
  | 0x2c%byte => x2c
  | 0x2d%byte => x2d
  | 0x2e%byte => x2e
  | 0x2f%byte => x2f
  | 0x30%byte => x30
  | 0x31%byte => x31
  | 0x32%byte => x32
  | 0x33%byte => x33
  | 0x34%byte => x34
  | 0x35%byte => x35
  | 0x36%byte => x36
  | 0x37%byte => x37
  | 0x38%byte => x38
  | 0x39%byte => x39
  | 0x3a%byte => x3a
  | 0x3b%byte => x3b
  | 0x3c%byte => x3c
  | 0x3d%byte => x3d
  | 0x3e%byte => x3e
  | 0x3f%byte => x3f
  | 0x40%byte => x40
  | 0x41%byte => x41
  | 0x42%byte => x42
  | 0x43%byte => x43
  | 0x44%byte => x44
  | 0x45%byte => x45
  | 0x46%byte => x46
  | 0x47%byte => x47
  | 0x48%byte => x48
  | 0x49%byte => x49
  | 0x4a%byte => x4a
  | 0x4b%byte => x4b
  | 0x4c%byte => x4c
  | 0x4d%byte => x4d
  | 0x4e%byte => x4e
  | 0x4f%byte => x4f
  | 0x50%byte => x50
  | 0x51%byte => x51
  | 0x52%byte => x52
  | 0x53%byte => x53
  | 0x54%byte => x54
  | 0x55%byte => x55
  | 0x56%byte => x56
  | 0x57%byte => x57
  | 0x58%byte => x58
  | 0x59%byte => x59
  | 0x5a%byte => x5a
  | 0x5b%byte => x5b
  | 0x5c%byte => x5c
  | 0x5d%byte => x5d
  | 0x5e%byte => x5e
  | 0x5f%byte => x5f
  | 0x60%byte => x60
  | 0x61%byte => x61
  | 0x62%byte => x62
  | 0x63%byte => x63
  | 0x64%byte => x64
  | 0x65%byte => x65
  | 0x66%byte => x66
  | 0x67%byte => x67
  | 0x68%byte => x68
  | 0x69%byte => x69
  | 0x6a%byte => x6a
  | 0x6b%byte => x6b
  | 0x6c%byte => x6c
  | 0x6d%byte => x6d
  | 0x6e%byte => x6e
  | 0x6f%byte => x6f
  | 0x70%byte => x70
  | 0x71%byte => x71
  | 0x72%byte => x72
  | 0x73%byte => x73
  | 0x74%byte => x74
  | 0x75%byte => x75
  | 0x76%byte => x76
  | 0x77%byte => x77
  | 0x78%byte => x78
  | 0x79%byte => x79
  | 0x7a%byte => x7a
  | 0x7b%byte => x7b
  | 0x7c%byte => x7c
  | 0x7d%byte => x7d
  | 0x7e%byte => x7e
  | 0x7f%byte => x7f
  | 0x80%byte => x80
  | 0x81%byte => x81
  | 0x82%byte => x82
  | 0x83%byte => x83
  | 0x84%byte => x84
  | 0x85%byte => x85
  | 0x86%byte => x86
  | 0x87%byte => x87
  | 0x88%byte => x88
  | 0x89%byte => x89
  | 0x8a%byte => x8a
  | 0x8b%byte => x8b
  | 0x8c%byte => x8c
  | 0x8d%byte => x8d
  | 0x8e%byte => x8e
  | 0x8f%byte => x8f
  | 0x90%byte => x90
  | 0x91%byte => x91
  | 0x92%byte => x92
  | 0x93%byte => x93
  | 0x94%byte => x94
  | 0x95%byte => x95
  | 0x96%byte => x96
  | 0x97%byte => x97
  | 0x98%byte => x98
  | 0x99%byte => x99
  | 0x9a%byte => x9a
  | 0x9b%byte => x9b
  | 0x9c%byte => x9c
  | 0x9d%byte => x9d
  | 0x9e%byte => x9e
  | 0x9f%byte => x9f
  | 0xa0%byte => xa0
  | 0xa1%byte => xa1
  | 0xa2%byte => xa2
  | 0xa3%byte => xa3
  | 0xa4%byte => xa4
  | 0xa5%byte => xa5
  | 0xa6%byte => xa6
  | 0xa7%byte => xa7
  | 0xa8%byte => xa8
  | 0xa9%byte => xa9
  | 0xaa%byte => xaa
  | 0xab%byte => xab
  | 0xac%byte => xac
  | 0xad%byte => xad
  | 0xae%byte => xae
  | 0xaf%byte => xaf
  | 0xb0%byte => xb0
  | 0xb1%byte => xb1
  | 0xb2%byte => xb2
  | 0xb3%byte => xb3
  | 0xb4%byte => xb4
  | 0xb5%byte => xb5
  | 0xb6%byte => xb6
  | 0xb7%byte => xb7
  | 0xb8%byte => xb8
  | 0xb9%byte => xb9
  | 0xba%byte => xba
  | 0xbb%byte => xbb
  | 0xbc%byte => xbc
  | 0xbd%byte => xbd
  | 0xbe%byte => xbe
  | 0xbf%byte => xbf
  | 0xc0%byte => xc0
  | 0xc1%byte => xc1
  | 0xc2%byte => xc2
  | 0xc3%byte => xc3
  | 0xc4%byte => xc4
  | 0xc5%byte => xc5
  | 0xc6%byte => xc6
  | 0xc7%byte => xc7
  | 0xc8%byte => xc8
  | 0xc9%byte => xc9
  | 0xca%byte => xca
  | 0xcb%byte => xcb
  | 0xcc%byte => xcc
  | 0xcd%byte => xcd
  | 0xce%byte => xce
  | 0xcf%byte => xcf
  | 0xd0%byte => xd0
  | 0xd1%byte => xd1
  | 0xd2%byte => xd2
  | 0xd3%byte => xd3
  | 0xd4%byte => xd4
  | 0xd5%byte => xd5
  | 0xd6%byte => xd6
  | 0xd7%byte => xd7
  | 0xd8%byte => xd8
  | 0xd9%byte => xd9
  | 0xda%byte => xda
  | 0xdb%byte => xdb
  | 0xdc%byte => xdc
  | 0xdd%byte => xdd
  | 0xde%byte => xde
  | 0xdf%byte => xdf
  | 0xe0%byte => xe0
  | 0xe1%byte => xe1
  | 0xe2%byte => xe2
  | 0xe3%byte => xe3
  | 0xe4%byte => xe4
  | 0xe5%byte => xe5
  | 0xe6%byte => xe6
  | 0xe7%byte => xe7
  | 0xe8%byte => xe8
  | 0xe9%byte => xe9
  | 0xea%byte => xea
  | 0xeb%byte => xeb
  | 0xec%byte => xec
  | 0xed%byte => xed
  | 0xee%byte => xee
  | 0xef%byte => xef
  | 0xf0%byte => xf0
  | 0xf1%byte => xf1
  | 0xf2%byte => xf2
  | 0xf3%byte => xf3
  | 0xf4%byte => xf4
  | 0xf5%byte => xf5
  | 0xf6%byte => xf6
  | 0xf7%byte => xf7
  | 0xf8%byte => xf8
  | 0xf9%byte => xf9
  | 0xfa%byte => xfa
  | 0xfb%byte => xfb
  | 0xfc%byte => xfc
  | 0xfd%byte => xfd
  | 0xfe%byte => xfe
  | 0xff%byte => xff
  end.

Module conversion. (* conversion *)

Module byte. (* conversion.byte *)

(* [g (f a) = a]: [f] is a section of [g], [g] a retraction of [f]. Each law
 * below is named by what [to_byte] is:
 *
 *   retraction   to_byte (from_byte b) = b   to_byte is a retraction of from_byte
 *   section      from_byte (to_byte s) = s   to_byte is a section of from_byte
 *)
(* conversion.byte.retraction *)
Theorem retraction : forall (b : Byte) . to_byte (from_byte b) = b.
Proof.
  intros b.
  match &b with | introduction b7 b6 b5 b4 b3 b2 b1 b0 end.
  match &b7 with | Zero | One end;
    match &b6 with | Zero | One end;
    match &b5 with | Zero | One end;
    match &b4 with | Zero | One end;
    match &b3 with | Zero | One end;
    match &b2 with | Zero | One end;
    match &b1 with | Zero | One end;
    match &b0 with | Zero | One end;
    simpl in |- *;
    quod idem est.
Qed.

(* conversion.byte.section *)
Theorem section : forall (s : SourceByte) . from_byte (to_byte s) = s.
Proof.
  intros s.
  match &s with
  | x00 | x01 | x02 | x03 | x04 | x05 | x06 | x07 | x08 | x09 | x0a | x0b | x0c | x0d | x0e | x0f
  | x10 | x11 | x12 | x13 | x14 | x15 | x16 | x17 | x18 | x19 | x1a | x1b | x1c | x1d | x1e | x1f
  | x20 | x21 | x22 | x23 | x24 | x25 | x26 | x27 | x28 | x29 | x2a | x2b | x2c | x2d | x2e | x2f
  | x30 | x31 | x32 | x33 | x34 | x35 | x36 | x37 | x38 | x39 | x3a | x3b | x3c | x3d | x3e | x3f
  | x40 | x41 | x42 | x43 | x44 | x45 | x46 | x47 | x48 | x49 | x4a | x4b | x4c | x4d | x4e | x4f
  | x50 | x51 | x52 | x53 | x54 | x55 | x56 | x57 | x58 | x59 | x5a | x5b | x5c | x5d | x5e | x5f
  | x60 | x61 | x62 | x63 | x64 | x65 | x66 | x67 | x68 | x69 | x6a | x6b | x6c | x6d | x6e | x6f
  | x70 | x71 | x72 | x73 | x74 | x75 | x76 | x77 | x78 | x79 | x7a | x7b | x7c | x7d | x7e | x7f
  | x80 | x81 | x82 | x83 | x84 | x85 | x86 | x87 | x88 | x89 | x8a | x8b | x8c | x8d | x8e | x8f
  | x90 | x91 | x92 | x93 | x94 | x95 | x96 | x97 | x98 | x99 | x9a | x9b | x9c | x9d | x9e | x9f
  | xa0 | xa1 | xa2 | xa3 | xa4 | xa5 | xa6 | xa7 | xa8 | xa9 | xaa | xab | xac | xad | xae | xaf
  | xb0 | xb1 | xb2 | xb3 | xb4 | xb5 | xb6 | xb7 | xb8 | xb9 | xba | xbb | xbc | xbd | xbe | xbf
  | xc0 | xc1 | xc2 | xc3 | xc4 | xc5 | xc6 | xc7 | xc8 | xc9 | xca | xcb | xcc | xcd | xce | xcf
  | xd0 | xd1 | xd2 | xd3 | xd4 | xd5 | xd6 | xd7 | xd8 | xd9 | xda | xdb | xdc | xdd | xde | xdf
  | xe0 | xe1 | xe2 | xe3 | xe4 | xe5 | xe6 | xe7 | xe8 | xe9 | xea | xeb | xec | xed | xee | xef
  | xf0 | xf1 | xf2 | xf3 | xf4 | xf5 | xf6 | xf7 | xf8 | xf9 | xfa | xfb | xfc | xfd | xfe | xff
  end;
    simpl in |- *;
    quod idem est.
Qed.

End byte. (* conversion.byte *)

Module bytes. (* conversion.bytes *)

(* [conversion.byte.retraction] for every byte of a list. *)
(* conversion.bytes.retraction *)
Theorem retraction : forall (l : List Byte) . List.map to_byte (List.map from_byte l) = l.
Proof.
  intros l.
  match &l with | Nil | Cons b (l' by IH) end per List.induction.
  - simpl in |- *.
    quod idem est.
  - simpl in |- *.
    leibniz (conversion.byte.retraction &b), &IH in |- *.
    quod idem est.
Qed.

End bytes. (* conversion.bytes *)

End conversion. (* conversion *)

End SourceByte. (* SourceByte *)

(* The counterpart of the abbreviation inside the module: a client writes
 * [SourceByte], not [SourceByte.T].
 *)
Abbreviation SourceByte := SourceByte.T.

(* The plugin finds the byte type of a string literal by this name. *)
Register SourceByte.T as core.byte.type.

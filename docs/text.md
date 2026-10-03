<!-- Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. -->

# Text

`jwa.Data` holds the text types under `Data/Text/`:

| Type | What it is | Literals |
|:---|:---|:---|
| `SourceByte` | A byte of the source text, the form a string literal arrives in | -- |
| `Ascii` | A character of one byte: ASCII below 128, Latin-1 from 128 to 255 | One character: `"A"%ac`, `""""%ac` (a quote) |
| `AsciiStr` | A string of `Ascii` characters | `"abc"%a`, `""%a` (empty), `"a""b"%a` |
| `Utf8` | A Unicode character, held as the one to four bytes UTF-8 spells it with | One character: `"A"%u8c`, `""""%u8c` (a quote) |
| `Utf8Str` | A string of `Utf8` characters | `"abc"%u8`, `""%u8` (empty), `"a""b"%u8` |

Where one of these types is expected, the key can go: `Ascii.to_byte "z"`, `AsciiStr.length "four"`, `Utf8Str.length "four"`. A quote inside a literal is written twice; a backslash escapes nothing.

---

## How a literal is read

1. **Rocq reads the literal as the UTF-8 bytes it is written in.** The plugin behind `String Notation`, loaded by `theories/Data/Literal.v`, hands them over as a `List SourceByte`: `"ab"` is `x61 :: x62 :: []`, and a character from U+0080 to U+00FF is two bytes, U+00E9 being `xc3 :: xa9 :: []`.
2. **The type reads the list.** Each type's `from_source_bytes` answers `Some` with the value or `None`, and `None` refuses the file when it is compiled: `""%ac` and `""%u8c`, `"ab"%ac` and `"ab"%u8c`, and, for `Ascii` and `AsciiStr`, any character above U+00FF.
3. **A closed value prints back** through `to_source_bytes`, as the same bytes.

The plugin finds each type by the name it is registered under, and every registration sits in the type's own file: `SourceByte` as `core.byte.type`, `List` as `core.list.type`, `Option` as `core.option.type`. It builds terms by constructor position, so `SourceByte` has one constructor per byte value, `x00` to `xff` in code order, and `List.Nil` and `List.Cons` stay its first and second constructors.

---

## Ascii

`Ascii` wraps a `Byte` and is not one: `Byte.flip "A"%ac` is a type error, and `Ascii.to_byte` and `Ascii.from_byte` cross between the two.

- **The codes:** 0 to 127 are ASCII; 128 to 255 are Latin-1, which maps them one to one onto U+0080 to U+00FF.
- **The byte conversions:** `Ascii.conversion.byte.retraction` is `to_byte (from_byte b) = b`, and `Ascii.conversion.byte.section` is `from_byte (to_byte c) = c`.
- **Reading and printing agree:** `Ascii.conversion.source_bytes.section` states `from_source_bytes (to_source_bytes c) = Some c` for every character.
- **Control characters print as they are:** a newline prints as a line break between the quotes, and DEL or U+0080 print as nothing visible, though they read back.
- **Characters are ordered by their codes.** `Ascii.code` gives the code as a `UInt8`, and `Ascii.compare`, `<`, `<=`, `Ascii.min` and `Ascii.max` go by it: `("A" < "a")%ac`. The instance `Ascii.comparable` carries the order's laws.
- **The classes are ASCII only.** `Ascii.is_digit`, `is_upper`, `is_lower`, `is_letter` and `is_whitespace` answer a `Bool`, and a Latin-1 letter such as U+00E9 is no letter. Each class is pinned to its range of codes by its specification, `Ascii.classification.digit.specification` stating `is_digit c = true` exactly from code 0x30 to 0x39.
- **Case changes only the 52 ASCII letters.** `Ascii.to_upper` clears the bit 0x20 of a lower case letter and `Ascii.to_lower` sets it on an upper case one; every other character stays as it is (`Ascii.uppercasing.invariance`), and a letter changed and changed back is itself (`Ascii.lowercasing.inversion.uppercasing`).

---

## AsciiStr

`AsciiStr` wraps a `List Ascii`, the first character first; `AsciiStr.to_list` and `AsciiStr.from_list` cross between the two, with `conversion.list.retraction` and `conversion.list.section`.

- **Operations:** `AsciiStr.empty`, `AsciiStr.concat`, written `(s ++ t)%a`, and `AsciiStr.length`, a `Nat0`: `("ab" ++ "c")%a` is `"abc"%a`.
- **Laws:** `AsciiStr.concatenation.associativity` and `AsciiStr.concatenation.identity` make `concat` and `empty` a monoid, the instance `AsciiStr_concat_monoid`, and `AsciiStr.length.additivity.over.concatenation` states `length (s ++ t) = length s + length t`.
- **Reading and printing agree:** `AsciiStr.conversion.source_bytes.section` states `from_source_bytes (to_source_bytes s) = Some s` for every string.
- **Case applies to every character:** `AsciiStr.to_upper "Hello, World"` is `"HELLO, WORLD"%a`, and `AsciiStr.to_lower` goes the other way; both keep the length and distribute over `++`.
- **Indexing counts from 0.** `AsciiStr.get s i` is `Some` of the character at position `i` exactly when `i < length s` (`AsciiStr.indexing.specification`), and `None` from there on: `AsciiStr.get "abc" 1%n0` is `Some "b"%ac`.
- **A substring stops where the string does.** `AsciiStr.substring s start len` takes `len` characters from position `start`, fewer near the end: `AsciiStr.substring "Hello, World" 7%n0 5%n0` is `"World"%a`, and `substring s 0 (length s)` is `s` (`AsciiStr.substring.identity`).
- **Strings are ordered lexicographically** by their characters' codes, a proper prefix first: `"Apple" < "apple" < "apply"` and `"app" < "apple"`. `AsciiStr.compare` is `List.compare Ascii.compare`, and the instance `AsciiStr.comparable` carries the order's laws.

---

## Utf8

`Utf8` holds a Unicode character, U+0000 to U+10FFFF without the surrogates U+D800 to U+DFFF, as the bytes UTF-8 spells it with, the first byte first.

- **Four constructors, one per length.** Each takes its bytes and a proof that they spell a character, by the rules of RFC 3629, section 4. Below, `x` is a bit of the character's code:

  | Constructor | Bytes | Characters |
  |:---|:---|:---|
  | `Utf8.OneByte` | `0xxxxxxx` | U+0000 to U+007F |
  | `Utf8.TwoBytes` | `110xxxxx 10xxxxxx` | U+0080 to U+07FF |
  | `Utf8.ThreeBytes` | `1110xxxx 10xxxxxx 10xxxxxx` | U+0800 to U+FFFF, without U+D800 to U+DFFF |
  | `Utf8.FourBytes` | `11110xxx 10xxxxxx 10xxxxxx 10xxxxxx` | U+10000 to U+10FFFF |

- **Only characters can be built.** The proof is `Assert` of a check on the bytes, such as `Utf8.is_two_bytes`: it is `I` where the check computes to `true`, and there is none where it computes to `false`. `Utf8.TwoBytes 0xc3%byte 0xa9%byte I` is U+00E9, while `Utf8.TwoBytes 0xc0%byte 0x80%byte I` is a type error, `C0 80` being U+0000 spelled a second time. Such overlong spellings, the surrogates and anything past U+10FFFF are refused alike.
- **The byte conversions:** `Utf8.to_bytes` gives the bytes, and `Utf8.from_bytes` answers `Some` when a list spells exactly one character and `None` otherwise, building the character through `Assert.guard`. `Utf8.conversion.bytes.section` states `from_bytes (to_bytes c) = Some c`, `Utf8.conversion.bytes.inversion` that `from_bytes l = Some c` only for `l = to_bytes c`, and `Utf8.conversion.bytes.injectivity` that two characters with the same bytes are equal.
- **Reading and printing agree:** `Utf8.conversion.source_bytes.section` states `from_source_bytes (to_source_bytes c) = Some c` for every character.
- **Latin-1 joins it to `Ascii`.** `Utf8.from_ascii` reads an `Ascii` character as U+0000 to U+00FF, and `Utf8.to_ascii` gives it back, `None` from U+0100 on: `Utf8.conversion.ascii.retraction` states `to_ascii (from_ascii a) = Some a`, and `Utf8.conversion.ascii.inversion` that `to_ascii c = Some a` only for `c = from_ascii a`.
- **Each character has its code point.** `Utf8.code` gives it as a `UInt32`, and `Utf8.from_code` answers `Some` of the character a code stands for and `None` for a surrogate or a code past U+10FFFF: `Utf8.code "A"` is `0x41%uint32`, `Utf8.from_code 0x20ac%uint32` is U+20AC, the euro sign, and `Utf8.from_code 0xd800%uint32` is `None`. `Utf8.conversion.code.section` states `from_code (code c) = Some c`, `Utf8.conversion.code.inversion` that `from_code u = Some c` only for `code c = u`, and `Utf8.conversion.code.injectivity` that two characters with one code are equal. `Utf8.encode` and `Utf8.decode` are the bit layouts in between, from a code to its bytes and back.
- **Characters are ordered by their codes.** `Utf8.compare`, `<`, `<=`, `Utf8.min` and `Utf8.max` go by `Utf8.code`: `("A" < "a")%u8c`. The instance `Utf8.comparable` carries the order's laws.
- **The classes and case are those of `Ascii`.** `Utf8.is_digit`, `is_upper`, `is_lower`, `is_letter` and `is_whitespace` hold of the same ranges as `Ascii`'s, each pinned by its specification. `Utf8.to_upper` and `Utf8.to_lower` change the 52 ASCII letters by `Ascii.to_upper` and `Ascii.to_lower` and leave every other character as it is, U+00E9 and U+20AC included. `Utf8.conversion.ascii.uppercasing` states `to_upper (from_ascii a) = from_ascii (Ascii.to_upper a)`, and `Utf8.uppercasing` and `Utf8.lowercasing` hold the laws `Ascii` has.

---

## Utf8Str

`Utf8Str` wraps a `List Utf8`, the first character first; `Utf8Str.to_list` and `Utf8Str.from_list` cross between the two, with `conversion.list.retraction` and `conversion.list.section`.

- **Operations:** `Utf8Str.empty`, `Utf8Str.concat`, written `(s ++ t)%u8`, and `Utf8Str.length`, a `Nat0` that counts characters, not bytes: `("ab" ++ "c")%u8` is `"abc"%u8`.
- **Laws:** `Utf8Str.concatenation.associativity` and `Utf8Str.concatenation.identity` make `concat` and `empty` a monoid, the instance `Utf8Str_concat_monoid`, and `Utf8Str.length.additivity.over.concatenation` states `length (s ++ t) = length s + length t`.
- **The byte conversions:** `Utf8Str.to_bytes` gives each character's bytes in turn, and `Utf8Str.from_bytes` reads a list of bytes as characters, answering `None` when any part of it spells none, a sequence cut short included. The five bytes `C3 A9 E2 82 AC` read as two characters, U+00E9 and U+20AC, of `length` 2. `Utf8Str.conversion.bytes.section` and `Utf8Str.conversion.bytes.injectivity` hold as they do for `Utf8`.
- **Reading and printing agree:** `Utf8Str.conversion.source_bytes.section` states `from_source_bytes (to_source_bytes s) = Some s` for every string.
- **Latin-1 joins it to `AsciiStr`.** `Utf8Str.from_ascii_str` and `Utf8Str.to_ascii_str` convert character by character, `Utf8Str.from_ascii_str "ab"%a` being `"ab"%u8`, with `conversion.ascii.retraction`, `conversion.ascii.inversion` and `conversion.ascii.preservation.length`.
- **Case applies to every character:** `Utf8Str.to_upper "Hello, World"` is `"HELLO, WORLD"%u8`, and `Utf8Str.to_lower` goes the other way; both keep the length and distribute over `++`.
- **Indexing counts characters from 0, not bytes.** `Utf8Str.get s i` is `Some` of the character at position `i` exactly when `i < length s` (`Utf8Str.indexing.specification`), and `None` from there on: in the string of `a`, U+20AC and `b`, position 2 is `b`, though `b` is its fifth byte.
- **A substring counts characters too, and stops where the string does.** `Utf8Str.substring s start len` takes `len` characters from position `start`, fewer near the end: `Utf8Str.substring "Hello, World" 7%n0 5%n0` is `"World"%u8`, and `substring s 0 (length s)` is `s` (`Utf8Str.substring.identity`).
- **Strings are ordered lexicographically** by their characters' codes, a proper prefix first: `"Apple" < "apple"` and `"app" < "apple"`. `Utf8Str.compare` is `List.compare Utf8.compare`, and the instance `Utf8Str.comparable` carries the order's laws.

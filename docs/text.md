<!-- Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. -->

# Text

`jwa.Data` holds the text types under `Data/Text/`:

| Type | What it is | Literals |
|:---|:---|:---|
| `SourceByte` | A byte of the source text, the form a string literal arrives in | -- |
| `Ascii` | A character of one byte: ASCII below 128, Latin-1 from 128 to 255 | One character: `"A"%ac`, `""""%ac` (a quote) |
| `AsciiStr` | A string of `Ascii` characters | `"abc"%a`, `""%a` (empty), `"a""b"%a` |

Where one of these types is expected, the key can go: `Ascii.to_byte "z"`, `AsciiStr.length "four"`. A quote inside a literal is written twice; a backslash escapes nothing.

---

## How a literal is read

1. **Rocq reads the literal as the UTF-8 bytes it is written in.** The plugin behind `String Notation`, loaded by `theories/Data/Literal.v`, hands them over as a `List SourceByte`: `"ab"` is `x61 :: x62 :: []`, and a character from U+0080 to U+00FF is two bytes, U+00E9 being `xc3 :: xa9 :: []`.
2. **The type reads the list.** `Ascii.from_source_bytes` and `AsciiStr.from_source_bytes` answer `Some` with the value or `None`, and `None` refuses the file when it is compiled: `""%ac`, `"ab"%ac`, and any character above U+00FF.
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
- **Case changes only the 52 ASCII letters.** `Ascii.to_upper` clears the bit 0x20 of a lower case letter and `Ascii.to_lower` sets it on an upper case one; every other character stays as it is (`Ascii.uppercasing.invariance`), and a letter changed and changed back is itself (`Ascii.lowercasing.inversion.of.uppercasing`).

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

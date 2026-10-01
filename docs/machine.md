<!-- Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. -->

# Machine units

`jwa.Data` holds the units of fixed width, and the byte order of the wider ones, under `Data/Machine/`:

| Type | What it is | Literals |
|:---|:---|:---|
| `Bit` | One binary digit | `0%bit`, `1%bit` |
| `Byte` | Eight bits, the most significant first | Hexadecimal only: `0xFF%byte` |
| `Endian` | The order a word lays its bytes out in: `Endian.Little` or `Endian.Big` | -- |
| `HWord` | A half word: 16 bits, two bytes | Hexadecimal only: `0x1234%hword` |
| `Word` | A word: 32 bits, four bytes | Hexadecimal only: `0x12345678%word` |
| `DWord` | A double word: 64 bits, eight bytes | Hexadecimal only: `0x0123456789ABCDEF%dword` |
| `QWord` | A quad word: 128 bits, sixteen bytes | Hexadecimal only, up to 32 digits: `0xFF%qword` |
| `UInt8` | A byte read as a number from 0 to 255 | Decimal or hexadecimal: `200%uint8`, `0xFF%uint8` |
| `Int8` | A byte read in two's complement, from -128 to 127 | Decimal or hexadecimal, with a sign: `100%int8`, `(-100)%int8`, `0x7F%int8` |

A literal too wide for its type is refused when the file is compiled, whatever its length. A closed value prints back as a literal: a byte or a word in hexadecimal, a `UInt8` or an `Int8` in decimal.

---

## Bits and bytes

- **A bit is a datum, not a truth value.** `Bit` and `Bool` are separate types, crossed by `Bit.from_bool` and `Bit.to_bool`.
- **The bitwise operations carry a dot**, `~.`, `&.`, `|.` and `^.`, apart from `Bool`'s `!`, `&&`, `||` and `^^`. They group as in C, `~.` tightest, then `&.`, `^.` and `|.`, so `(~. x &. y |. z)%byte` is `((~. x) &. y) |. z`.
- **A `Byte` shifts and rotates** by a `Nat0` count, and a rotation by eight places gives the byte back (`Byte.rotation.left.period`).
- **A `Byte` has no arithmetic.** Reading it as a number is what `UInt8` and `Int8` do.

---

## Words

`HWord`, `Word`, `DWord` and `QWord` hold 16, 32, 64 and 128 bits, the half word, word, double word and quad word of ARM and RISC-V; x86 names them differently, its word being 16 bits and its doubleword 32. Each is built from `Byte`s directly and depends on no other word. Like a `Byte`, a word is bits and has no arithmetic.

- **A word carries its byte order.** Its first field is an `Endian`, and its bytes follow in the order that tag names: `0x1234%hword` is `HWord.HWord_introduction Endian.Little 0x34 0x12`, and `0x1234%hword_big` is `HWord.HWord_introduction Endian.Big 0x12 0x34`.
- **Little-endian is the default.** The plain key `%hword` reads a literal little-endian, and `%hword_little` and `%hword_big` name the order outright. A closed word prints in hexadecimal with every digit, under the plain key when it is little-endian and under `_big` when it is not: `0x00ff%hword`, `0x00ff%hword_big`. The other words have the same three keys: `%word`, `%dword`, `%qword`, each with `_little` and `_big`.
- **The bytes are read by significance, whatever the order.** `HWord.low` and `HWord.high` give the least and the most significant byte, and `Word.byte0` to `Word.byte3` the bytes from the least significant up, as far as `QWord.byte15`. `make e` takes the bytes in the same order and lays them out as `e` names.
- **`with_endian e x` lays the value of `x` out in the order `e`**, and `Zero e` is the zero word laid out in that order.
- **Operands of different orders are converted, then combined.** `~.`, `&.`, `|.` and `^.` act on the value, and the result takes the order of the left operand (`HWord.conjunction.endian.conversion`): `(0x00FF &. 0x0F0F%hword_big)%hword` is `0x000F%hword`.
- **A forced version fixes the order of the result.** `and_little_endian` and `and_big_endian` convert both operands to the order they name before combining them, and `flip`, `or` and `xor` have the same pair: `HWord.and_big_endian 0x00FF 0x0F0F` is `0x000F%hword_big`.
- **Shifts and rotations count by significance**, a `Nat0` number of places, whatever the order: `HWord.shift_left 0x0080 1%n0` is `0x0100%hword`, and `0x0080%hword_big` shifts to `0x0100%hword_big`. A rotation by the full width gives the word back (`HWord.rotation.left.period`).
- **`to_bytes` lists the bytes as they are laid out**, and `from_bytes e` reads such a list back as a word of order `e`, or `None` when its length is wrong: `HWord.to_bytes 0x1234` lists `0x34` then `0x12`, and `HWord.to_bytes 0x1234%hword_big` lists `0x12` then `0x34`.
- **Every law holds in either order, commutativity excepted.** Associativity, identity, distributivity and the rotation laws are stated for any word; `x &. y = y &. x` is stated only for two words of one order (`HWord.conjunction.endian.little.commutativity`, `HWord.conjunction.endian.big.commutativity`), since the result takes the left operand's order. For that reason, and because the identity `Zero (endian x)` depends on the operand, no word type has an instance of the algebraic classes.

---

## UInt8

`UInt8` wraps a `Byte`. `+`, `UInt8.sub`, `-` (two's complement) and `*` wrap modulo 256.

- `UInt8.add_with_carry` and `UInt8.sub_with_borrow` ripple a carry or a borrow through the eight places and return it, so that they chain into wider numbers.
- Every operation is stated against the value `UInt8.to_nat0`: `UInt8.conversion.addition` is `to_nat0 (x + y) = (to_nat0 x + to_nat0 y) %. 256`, and `UInt8.conversion.left.shift` makes a shift to the left a multiplication by a power of two.
- `+` and `*` form a ring, `UInt8.from_nat0` reads a `Nat0` modulo 256, and `UInt8.compare` orders by value.
- Under `%uint8`, `- 1` is read as a negative literal and refused; the negation of a literal is written `- UInt8.One` or `UInt8.negate 1`.

---

## Int8

`Int8` wraps a `Byte` of its own and **shares no code with `UInt8`**. Its `+`, `Int8.sub`, `-` and `*` wrap modulo 256 as well: `(127 + 1)%int8` is `-128`, and so is `(- (-128))%int8`.

- Every operation is stated against the signed value `Int8.to_integer`.
- `Int8.add_with_overflow` returns the sum with a flag, set when the operands share a sign that the sum does not; `Int8.conversion.addition` makes `to_integer (x + y)` the sum `to_integer x + to_integer y` whenever that flag is clear.
- `Int8.shift_right` is arithmetic: it copies the sign bit, so a shift by one place halves the value rounding down (`Int8.conversion.right.halving`), and `Int8.shift_right (-1) 3` is still `-1`.
- `+` and `*` form a ring, `Int8.from_integer` reads an `Integer` modulo 256, and `Int8.compare` orders by the signed value, `-1` before `1`.

---

## Conversions

- **`UInt8` and `Int8` meet only at `Byte`**, through `to_byte` and `from_byte`: `Int8.from_byte (UInt8.to_byte 255)` is `-1`.
- **Both widen without being written**, as the number types do: a `UInt8` stands wherever a `Nat0` or an `Integer` is expected, as its `UInt8.to_nat0`, and an `Int8` wherever an `Integer` is, as its `Int8.to_integer`. Each conversion is printed in the goal.
- **The operators are then the numbers' own**: `(x + y)%n0`, with `x` and `y` of type `UInt8`, adds their values without wrapping, where `(x + y)%uint8` wraps.

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
| `UInt8` | A byte read as a number from 0 to 255 (2^8 - 1) | Decimal or hexadecimal: `200%uint8`, `0xFF%uint8` |
| `Int8` | A byte read in two's complement, from -128 (-2^7) to 127 (2^7 - 1) | Decimal or hexadecimal, with a sign: `100%int8`, `(-100)%int8`, `0x7F%int8` |
| `UInt16` | Two bytes read as a number from 0 to 65535 (2^16 - 1) | Decimal or hexadecimal: `60000%uint16`, `0xFFFF%uint16` |
| `Int16` | Two bytes read in two's complement, from -32768 (-2^15) to 32767 (2^15 - 1) | Decimal or hexadecimal, with a sign: `(-30000)%int16`, `0x7FFF%int16` |
| `UInt32` | Four bytes read as a number from 0 to 4294967295 (2^32 - 1) | Decimal or hexadecimal: `4000000000%uint32`, `0xFFFFFFFF%uint32` |
| `Int32` | Four bytes read in two's complement, from -2147483648 (-2^31) to 2147483647 (2^31 - 1) | Decimal or hexadecimal, with a sign: `(-2000000000)%int32`, `0x7FFFFFFF%int32` |
| `UInt64` | Eight bytes read as a number from 0 to 18446744073709551615 (2^64 - 1) | Decimal or hexadecimal: `10000000000000000000%uint64`, `0xFFFFFFFFFFFFFFFF%uint64` |
| `Int64` | Eight bytes read in two's complement, from -9223372036854775808 (-2^63) to 9223372036854775807 (2^63 - 1) | Decimal or hexadecimal, with a sign: `(-1000000000000)%int64`, `0x7FFFFFFFFFFFFFFF%int64` |

A literal too wide for its type is refused when the file is compiled, whatever its length. A closed value prints back as a literal: a byte or a word in hexadecimal, a fixed-width integer in decimal.

---

## Bits and bytes

- **A bit is a datum, not a truth value.** `Bit` and `Bool` are separate types, crossed by `Bit.from_bool` and `Bit.to_bool`.
- **The bitwise operations carry a dot**, `~.`, `&.`, `|.` and `^.`, apart from `Bool`'s `!`, `&&`, `||` and `^^`. They group as in C, `~.` tightest, then `&.`, `^.` and `|.`, so `(~. x &. y |. z)%byte` is `((~. x) &. y) |. z`.
- **A `Byte` shifts and rotates** by a `Nat0` count, and a rotation by eight places gives the byte back (`Byte.rotation.left.period`).
- **A `Byte` has no arithmetic.** Reading bytes as a number is what the fixed-width integers do.

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

## Fixed-width integers

The fixed-width integers come in pairs, one per width: `UInt8` and `Int8` hold one byte, `UInt16` and `Int16` two, `UInt32` and `Int32` four, `UInt64` and `Int64` eight, the most significant byte first. Every width is built the same way, so what this page says of `UInt8` holds of `UInt16`, `UInt32` and `UInt64` with the width changed, and what it says of `Int8` holds of the other signed types.

- **The values compute in binary.** An unsigned value is read as a `BinWithZero` (`UInt8.to_bin_with_zero`), a signed one as a `Bin` (`Int8.to_bin`), and `compare`, the literals and the printing all go through that value, so 64-bit arithmetic computes at once where a unary `Nat0` would build the value one successor at a time.
- **Each type names its modulus.** `UInt8.modulus` is 256 (2^8) as a `BinBase`, `UInt64.modulus` is 2^64, and the laws are stated with it.
- **No fixed-width integer shares code with another.** `Int8` wraps a `Byte` of its own and imports nothing of `UInt8`, and no width imports a narrower one.

---

## Unsigned integers

`UInt8`'s `+`, `UInt8.sub`, `-` (two's complement) and `*` wrap modulo `UInt8.modulus`: `(200 + 100)%uint8` is `44`.

- **The carry and the borrow are returned.** `UInt8.add_with_carry` and `UInt8.sub_with_borrow` ripple a carry or a borrow through every place and return it with the result.
- **Every operation is stated against the value.** `UInt8.conversion.addition` is `to_bin_with_zero (x + y)%uint8 = (x + y) %. modulus` in `BinWithZero`, the right side adding the values without wrapping, and `UInt8.conversion.left.shift` makes a shift to the left a multiplication by a power of two.
- **The arithmetic is a ring.** `+` and `*` form one, `UInt8.from_bin_with_zero` and `UInt8.from_nat0` read a number modulo `UInt8.modulus`, `UInt8.to_bin` gives the value as a `Bin`, and `UInt8.compare` orders by value.
- **A negative literal is refused.** Under `%uint8` and the other unsigned keys, `- 1` is read as a negative literal and refused; the negation of a literal is written `- UInt8.One` or `UInt8.negate 1`.

---

## Signed integers

`Int8`'s `+`, `Int8.sub`, `-` and `*` wrap modulo `Int8.modulus` as well: `(127 + 1)%int8` is `-128`, and so is `(- (-128))%int8`.

- **Every operation is stated against the signed value.** The laws go through `Int8.unsigned_value`, the value of the bit pattern from 0 to 255 (the `Int8.valuation` laws), and from it `Int8.to_bin` takes the signed value.
- **The overflow is a flag.** `Int8.add_with_overflow` returns the sum with a flag, set when the operands share a sign that the sum does not; `Int8.conversion.addition` makes `to_bin (x + y)` the sum `to_bin x + to_bin y` in `Bin` whenever that flag is clear.
- **The right shift is arithmetic.** `Int8.shift_right` copies the sign bit, so a shift by one place halves the value rounding down (`Int8.conversion.right.halving`), and `Int8.shift_right (-1) 3` is still `-1`.
- **The arithmetic is a ring.** `+` and `*` form one, `Int8.from_bin` and `Int8.from_integer` read a number modulo `Int8.modulus`, and `Int8.compare` orders by the signed value, `-1` before `1`.

---

## Conversions

- **The two types of a width meet only at its bytes**: `to_byte` and `from_byte` at 8 bits, `to_hword e` and `from_hword` at 16, `to_word e` and `from_word` at 32, `to_dword e` and `from_dword` at 64, the word laid out in the order `e` names. `Int8.from_byte (UInt8.to_byte 255)` is `-1`, and so is `Int64.from_dword (UInt64.to_dword Endian.Big 18446744073709551615)`.
- **No width converts to another.**
- **Every fixed-width integer widens without being written**, as the number types do: an unsigned value stands wherever a `BinWithZero` or a `Nat0` is expected, a signed one wherever a `Bin` or an `Integer` is. Each conversion is printed in the goal.
- **The unary conversions are for stating and proving.** `UInt8.to_nat0` and `Int8.to_integer` go through the binary value; computing is done in `BinWithZero` or `Bin`.
- **The operators are then the numbers' own**: `(x + y)%bin_with_zero` or `(x + y)%n0`, with `x` and `y` of type `UInt8`, adds their values without wrapping, where `(x + y)%uint8` wraps.

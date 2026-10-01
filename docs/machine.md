<!-- Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. -->

# Machine units

`jwa.Data` holds the units of fixed width under `Data/Machine/`:

| Type | What it is | Literals |
|:---|:---|:---|
| `Bit` | One binary digit | `0%bit`, `1%bit` |
| `Byte` | Eight bits, the most significant first | Hexadecimal only: `0xFF%byte` |
| `UInt8` | A byte read as a number from 0 to 255 | Decimal or hexadecimal: `200%uint8`, `0xFF%uint8` |
| `Int8` | A byte read in two's complement, from -128 to 127 | Decimal or hexadecimal, with a sign: `100%int8`, `(-100)%int8`, `0x7F%int8` |

A literal too wide for its type is refused when the file is compiled, whatever its length. A closed value prints back as a literal: a byte in hexadecimal, a `UInt8` or an `Int8` in decimal.

---

## Bits and bytes

- **A bit is a datum, not a truth value.** `Bit` and `Bool` are separate types, crossed by `Bit.from_bool` and `Bit.to_bool`.
- **The bitwise operations carry a dot**, `~.`, `&.`, `|.` and `^.`, apart from `Bool`'s `!`, `&&`, `||` and `^^`. They group as in C, `~.` tightest, then `&.`, `^.` and `|.`, so `(~. x &. y |. z)%byte` is `((~. x) &. y) |. z`.
- **A `Byte` shifts and rotates** by a `Nat0` count, and a rotation by eight places gives the byte back (`Byte.rotation.left.period`).
- **A `Byte` has no arithmetic.** Reading it as a number is what `UInt8` and `Int8` do.

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

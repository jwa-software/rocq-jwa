<!-- Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. -->

# Numbers

`jwa.Data` holds seven number types:

| Type | Values | Scope key |
|:---|:---|:---|
| `Nat` | from 1 | `%n` |
| `Nat0` | from 0 | `%n0` |
| `Integer` | every integer | `%z` |
| `Rational` | every fraction | `%q` |
| `BinBase` | from 1, in binary | `%bin_base` |
| `BinWithZero` | from 0, in binary | `%bin_with_zero` |
| `Bin` | every integer, in binary | `%b` |

---

## Conversions

**Upward, without being written.** A `Nat` stands wherever a `Nat0`, an `Integer` or a `Rational` is expected, and so on up; a `BinBase` stands wherever a `BinWithZero` or a `Bin` is. So `(numerator x * denominator y)%z` multiplies an `Integer` by a `Nat`. **Every such conversion is still printed** in the goal, as `Integer.Positive (denominator y)`, so a `leibniz` step can be aimed at what the goal shows.

**Downward, by name, into an `Option`**, since there may be no answer: `Nat0.to_nat`, `Integer.to_nat0`, `Integer.to_nat`, `Rational.to_integer`, `Rational.to_nat0` and `Rational.to_nat`. Each is `None` exactly where the value has no counterpart below, such as `Integer.to_nat0` below zero or `Rational.to_integer` at a denominator other than one. Its laws sit in a `narrowing` module:

- `retraction`: going up, then down, gives the value back (`Rational.narrowing.integer.retraction`);
- `specification`: `to_integer x = Some n` holds exactly when `x` is `n`;
- `failure`: when the answer is `None`.

Take the value out with `Option.unwrap_or d o`, which falls back to `d`, or with `Option.unwrap o h`, where `h` proves `~ (o = None)`: nothing fails at run time, so the proof takes the place of the failure.

---

## Arithmetic and literals

Arithmetic is written with each type's notation and scope key, `(a + b)%n`, `(p /. q)%n0`, `(x * y)%q`, `(m && n)%bin_with_zero`, and goals print the operations by name, `Rational.mul x y`.

**`Nat`, `Nat0` and `Integer` are written in decimal or hexadecimal**: `3%n`, `0x1F%n0`, `(-5)%z`. A closed value prints back in decimal, and `0%n` is refused, `Nat` having no zero.

- Where one of the three types is expected, the key can go: `Nat0.add 3 4`.
- Under `Data.Number.All` a numeral with no key is an `Integer`, `3` and `-3` alike, and a bare `a + b` is `Integer.add`.
- These types spend one constructor per unit, so a `Nat0` or `Integer` literal of 5000 or more stays a call to its parsing function until something computes it, and a `Nat` literal that large, which is built in full, draws a warning.

---

## Binary numbers

**They compute.** A `BinBase` is `One` with bits appended at the low end, `b0` for a 0 and `b1` for a 1; `BinWithZero` adds zero, and `Bin` adds a sign. Their arithmetic works bit by bit, so `(10 ^ 11001000)%bin_with_zero`, two to the power two hundred, reduces in the kernel at once, where a `Nat` that large could not even be written out.

**They are written in binary digits**: `1011%bin_base`, `1011%bin_with_zero` and `1011%b` are eleven, and `(-1011)%b` is minus eleven. A closed value prints the same way. Any other digit is refused, and so is a `BinBase` literal opening with 0. The short key `%b` goes to `Bin` because only its literals can carry a sign.

**Division takes a `BinBase` divisor, which is never zero:**

- `(1011 /. 11%bin_base)%bin_with_zero` is three, and `(1011 %. 11%bin_base)%bin_with_zero` is two;
- `Bin` divides the magnitude and keeps the sign, so `((-1011) /. 11%bin_base)%b` is minus three, and it has no remainder, as `Integer` has none.

**`BinWithZero` also has:**

- `BinWithZero.gcd`, by Euclid's algorithm; a quotient or a gcd of two 64-bit numbers reduces in the kernel at once;
- the bitwise `&&`, `||` and `^^`, with `shift_left`, `shift_right` and `test_bit`; `shift_right` is division by a power of two (`BinWithZero.shift.right.quotient`).

**Their laws are proved through the unary types.** `BinBase.to_nat`, `BinWithZero.to_nat0` and `Bin.to_integer` convert each to its counterpart, and the laws go through them (`BinWithZero.conversion.addition`, `Bin.conversion.difference`). The algebraic laws and instances are those of `Nat`, `Nat0` and `Integer`: `Bin` is a ring, and its addition an abelian group.

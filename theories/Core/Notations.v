(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* [-noinit] keeps [Corelib.Init.Prelude] out, so every notation, [->]
   included, is declared by this tree: the scope and the levels here, each
   meaning beside the thing it denotes. *)

(* The scope name carries no mechanism; [Bind] below is what makes it apply
   where a type is expected. *)
Declare Scope jwa_type_scope.
Delimit Scope jwa_type_scope with jwa_type.

(* [Bind] covers type positions, [Open] the ones Rocq cannot classify. *)
Bind Scope jwa_type_scope with Sortclass.
Open Scope jwa_type_scope.

(* The list notations, delimited but not opened: [[]] is
   the empty list and [++] is [List.concat] only where a file opens the
   scope or writes [(...)%list], so the same spellings stay free for other
   containers in scopes of their own. *)
Declare Scope jwa_list_scope.
Delimit Scope jwa_list_scope with list.

(* The same spellings again for the non-empty list, in a scope of its own:
   [a :: x] and [x ++ y] read there as the ctor and the join of that type,
   and a file picks which by opening one scope or by writing [(...)%list]
   or [(...)%non_empty_list]. The level of each token is reserved once
   below, so the two readings agree on how they parse and differ only in
   what they mean. *)
Declare Scope jwa_non_empty_list_scope.
Delimit Scope jwa_non_empty_list_scope with non_empty_list.

(* The product notations, delimited but not opened. [A * B] is not in it: a
 * type former belongs in [jwa_type_scope] beside [->].
 *)
Declare Scope jwa_product_scope.
Delimit Scope jwa_product_scope with product.

(* The [Bool] operations, delimited but not opened. The spellings are
 * contested: [&&] and [||] are what a closed notation elsewhere would take
 * away, and [!] is the boolean negation beside the logical [~], which stays
 * in [jwa_type_scope] because a proposition is what the tree is mostly about.
 *)
Declare Scope jwa_bool_scope.
Delimit Scope jwa_bool_scope with bool.

(* The [Bit] operations, delimited but not opened, each spelled with a dot
 * ([~.], [&.], [|.], [^.]) apart from the [Bool] ones: a bit is a binary
 * digit and a [Bool] a truth value.
 *)
Declare Scope jwa_bit_scope.
Delimit Scope jwa_bit_scope with bit.

(* The [Byte] operations, the [Bit] ones taken field by field, delimited but
 * not opened under the same spellings.
 *)
Declare Scope jwa_byte_scope.
Delimit Scope jwa_byte_scope with byte.

(* The [UInt8] arithmetic, delimited but not opened. *)
Declare Scope jwa_uint8_scope.
Delimit Scope jwa_uint8_scope with uint8.

(* The [Int8] arithmetic, delimited but not opened. *)
Declare Scope jwa_int8_scope.
Delimit Scope jwa_int8_scope with int8.

(* The [UInt16] arithmetic, delimited but not opened. *)
Declare Scope jwa_uint16_scope.
Delimit Scope jwa_uint16_scope with uint16.

(* The [Int16] arithmetic, delimited but not opened. *)
Declare Scope jwa_int16_scope.
Delimit Scope jwa_int16_scope with int16.

(* The [UInt32] arithmetic, delimited but not opened. *)
Declare Scope jwa_uint32_scope.
Delimit Scope jwa_uint32_scope with uint32.

(* The [Int32] arithmetic, delimited but not opened. *)
Declare Scope jwa_int32_scope.
Delimit Scope jwa_int32_scope with int32.

(* The [UInt64] arithmetic, delimited but not opened. *)
Declare Scope jwa_uint64_scope.
Delimit Scope jwa_uint64_scope with uint64.

(* The [Int64] arithmetic, delimited but not opened. *)
Declare Scope jwa_int64_scope.
Delimit Scope jwa_int64_scope with int64.

(* The [HWord] operations, the [Byte] ones taken byte by byte, delimited but
 * not opened under the same spellings; a literal under it is little-endian.
 *)
Declare Scope jwa_hword_scope.
Delimit Scope jwa_hword_scope with hword.

(* [HWord] literals laid out little-endian. *)
Declare Scope jwa_hword_little_scope.
Delimit Scope jwa_hword_little_scope with hword_little.

(* [HWord] literals laid out big-endian. *)
Declare Scope jwa_hword_big_scope.
Delimit Scope jwa_hword_big_scope with hword_big.

(* The [Word] operations, the [Byte] ones taken byte by byte, delimited but
 * not opened under the same spellings; a literal under it is little-endian.
 *)
Declare Scope jwa_word_scope.
Delimit Scope jwa_word_scope with word.

(* [Word] literals laid out little-endian. *)
Declare Scope jwa_word_little_scope.
Delimit Scope jwa_word_little_scope with word_little.

(* [Word] literals laid out big-endian. *)
Declare Scope jwa_word_big_scope.
Delimit Scope jwa_word_big_scope with word_big.

(* The [DWord] operations, the [Byte] ones taken byte by byte, delimited but
 * not opened under the same spellings; a literal under it is little-endian.
 *)
Declare Scope jwa_dword_scope.
Delimit Scope jwa_dword_scope with dword.

(* [DWord] literals laid out little-endian. *)
Declare Scope jwa_dword_little_scope.
Delimit Scope jwa_dword_little_scope with dword_little.

(* [DWord] literals laid out big-endian. *)
Declare Scope jwa_dword_big_scope.
Delimit Scope jwa_dword_big_scope with dword_big.

(* The [QWord] operations, the [Byte] ones taken byte by byte, delimited but
 * not opened under the same spellings; a literal under it is little-endian.
 *)
Declare Scope jwa_qword_scope.
Delimit Scope jwa_qword_scope with qword.

(* [QWord] literals laid out little-endian. *)
Declare Scope jwa_qword_little_scope.
Delimit Scope jwa_qword_little_scope with qword_little.

(* [QWord] literals laid out big-endian. *)
Declare Scope jwa_qword_big_scope.
Delimit Scope jwa_qword_big_scope with qword_big.

(* One scope per numeral type, delimited but not opened, so that [+] and [*]
   name that type's operations only under its delimiter: [(m + n)%n],
   [(m + n)%n0]. Two types cannot share a scope, since one spelling would
   then have two meanings.

   A key is short where it is written often: the scope name says which type
   it is for, so the key only has to be unambiguous. The scope name itself
   is never abbreviated, being named for the context it disambiguates. *)
Declare Scope jwa_nat_scope.
Delimit Scope jwa_nat_scope with n.
Declare Scope jwa_nat0_scope.
Delimit Scope jwa_nat0_scope with n0.
Declare Scope jwa_integer_scope.
Delimit Scope jwa_integer_scope with z.
Declare Scope jwa_rational_scope.
Delimit Scope jwa_rational_scope with q.
Declare Scope jwa_bin_base_scope.
Delimit Scope jwa_bin_base_scope with bin_base.
Declare Scope jwa_bin_with_zero_scope.
Delimit Scope jwa_bin_with_zero_scope with bin_with_zero.

(* [b] is the shortest key in the tree and it goes to the type whose literals
   cover the most ground: [Bin] reads both [1011%b] and [(-1011)%b],
   where [BinWithZero] could never spell the second. A key is worth its
   brevity when literals are written under it, not when the type is named
   briefly. *)
Declare Scope jwa_bin_scope.
Delimit Scope jwa_bin_scope with b.

(* Precedence follows the textbook order, [~] tightest and [->] loosest with
   [forsome] beyond them, so a formula reads without parentheses; [_\/_] sits
   between [/\] and [\/] as [^^] sits between [&&] and [||], and [!] is to
   that boolean row what [~] is to this one, below all of it. The quotes
   make [contains_member] a keyword rather than a variable. *)
Reserved Notation "x -> y"
  (at level 99, right associativity, y at level 200).
Reserved Notation "x = y"
  (at level 70, no associativity).
Reserved Notation "x < y"
  (at level 70, no associativity).
Reserved Notation "x <= y"
  (at level 70, no associativity).
Reserved Notation "x > y"
  (at level 70, no associativity).
Reserved Notation "x >= y"
  (at level 70, no associativity).
Reserved Notation "x /\ y"
  (at level 80, right associativity).
Reserved Notation "x _\/_ y"
  (at level 82, right associativity).
Reserved Notation "x \/ y"
  (at level 85, right associativity).
Reserved Notation "x -/> y"
  (at level 90, no associativity).
Reserved Notation "x <-> y"
  (at level 95, no associativity).
Reserved Notation "~ x"
  (at level 75, right associativity).
Reserved Notation "x ^ y"
  (at level 30, right associativity).
Reserved Notation "! b"
  (at level 35, right associativity).
(* [~] is reserved below [=] for propositions, so the bit complement takes a
 * token of its own at the level of [!].
 *)
Reserved Notation "~. b"
  (at level 35, right associativity).
Reserved Notation "x && y"
  (at level 40, left associativity).
Reserved Notation "x &. y"
  (at level 40, left associativity).
Reserved Notation "x * y"
  (at level 40, left associativity).
(* [x % y] is the scope delimiter's own syntax, so the quotient and the
 * remainder both carry a dot.
 *)
Reserved Notation "x /. y"
  (at level 40, left associativity).
Reserved Notation "x %. y"
  (at level 40, left associativity).
Reserved Notation "x ^^ y"
  (at level 45, left associativity).
Reserved Notation "x ^. y"
  (at level 45, left associativity).
Reserved Notation "x || y"
  (at level 50, left associativity).
Reserved Notation "x |. y"
  (at level 50, left associativity).
Reserved Notation "x + y"
  (at level 50, left associativity).
Reserved Notation "x ++ y"
  (at level 60, right associativity).
Reserved Notation "++ n"
  (at level 35, right associativity).
Reserved Notation "a :: l"
  (at level 60, right associativity).
Reserved Notation "l 'contains_member' a"
  (at level 70, no associativity).
Reserved Notation "a 'belongs_to' l"
  (at level 70, no associativity).
Reserved Notation "l 'does_not_contain_member' a"
  (at level 70, no associativity).
Reserved Notation "a 'does_not_belong_to' l"
  (at level 70, no associativity).

(* The syllogisms written as terms, so that one may stand where its
 * conclusion is wanted and nest inside another. Their meanings belong to
 * [Tactics.Syllogism], beside the tactics that carry the same names; only
 * the levels are fixed here, as every other level is.
 *)
Reserved Notation "'hs' Hab , Hbc"
  (at level 10, Hab at next level, Hbc at next level).
Reserved Notation "'hypothetical' 'syllogism' Hab , Hbc"
  (at level 10, Hab at next level, Hbc at next level).
Reserved Notation "'barbara' Hmp , Hsm"
  (at level 10, Hmp at next level, Hsm at next level).

(* The modi written as terms, for the same reason and at the same level.
 * Their meanings belong to [Tactics.Modus].
 *)
Reserved Notation "'modus' 'ponens' H1 , H2"
  (at level 10, H1 at next level, H2 at next level).
Reserved Notation "'modus' 'ponendo' 'ponens' H1 , H2"
  (at level 10, H1 at next level, H2 at next level).
Reserved Notation "'modus' 'tollens' H1 , H2"
  (at level 10, H1 at next level, H2 at next level).
Reserved Notation "'modus' 'tollendo' 'tollens' H1 , H2"
  (at level 10, H1 at next level, H2 at next level).
Reserved Notation "'modus' 'tollendo' 'ponens' H1 , H2"
  (at level 10, H1 at next level, H2 at next level).
Reserved Notation "'modus' 'ponendo' 'tollens' H1 , H2"
  (at level 10, H1 at next level, H2 at next level).
Reserved Notation "'modus' 'aequans' H1 , H2"
  (at level 10, H1 at next level, H2 at next level).

(* Double negation written as terms, for the same reason and at the same
 * level. Their meanings belong to [Tactics.DoubleNegation].
 *)
Reserved Notation "'dni' H"
  (at level 10, H at next level).
Reserved Notation "'dne' H"
  (at level 10, H at next level).

(* De Morgan written as a term, for the same reason and at the same level.
 * Its meaning belongs to [Tactics.DeMorgan].
 *)
Reserved Notation "'de' 'morgan' H"
  (at level 10, H at next level).

(* The symmetry, the transitivity and the congruence of [=] written as terms,
 * for the same reason and at the same level. Their meanings belong to
 * [Tactics.Equation].
 *)
Reserved Notation "'symm' H"
  (at level 10, H at next level).
Reserved Notation "'trans' H1 , H2"
  (at level 10, H1 at next level, H2 at next level).
Reserved Notation "'congru' F , H"
  (at level 10, F at next level, H at next level).

(* The introduction of each junction written as a term, at the same level.
 * Their meanings belong beside each connective in [Core.Logic], and the
 * tactics of the same names to [Tactics.Join]. [_] marks the side of a
 * disjunction that comes from the expected type.
 *)
Reserved Notation "'conjoin' A , B"
  (at level 10, A at next level, B at next level).
#[warnings="-closed-notation-not-level-0"]
Reserved Notation "'disjoin' A , '_'"
  (at level 10, A at next level).
Reserved Notation "'disjoin' '_' , B"
  (at level 10, B at next level).
Reserved Notation "'sejoin' A , B"
  (at level 10, A at next level, B at next level).
Reserved Notation "'abjoin' A , B"
  (at level 10, A at next level, B at next level).

(* [x binder] is what lets [x] be written with or without its type, and the
   [..] is what lets one [forsome] carry several of them. *)
Reserved Notation "'forsome' x .. y '.' p"
  (at level 200, x binder, y binder, right associativity).

(* The lambda as it is written on paper, [fun x . body], beside the
 * kernel's [fun x => body], which keeps working. It is declared here and
 * not beside a definition of its own, since the term it denotes is the
 * kernel's and belongs to no file of this tree. The [.] is what ends a
 * sentence for the lexer, but inside this rule the parser reads it as the
 * separator. It prints as well, so a goal shows what the source says.
 *)
Notation "'fun' x .. y '.' body" := (fun x => .. (fun y => body) ..)
  (at level 200, x binder, y binder, right associativity).

(* The quantifier written the same way, [forall x . p] beside the kernel's
 * [forall x, p]. [forsome] gets its dotted spelling in [Core.Logic.Exists],
 * where its meaning is.
 *)
Notation "'forall' x .. y '.' p" := (forall x, .. (forall y, p) ..)
  (at level 200, x binder, y binder, right associativity).

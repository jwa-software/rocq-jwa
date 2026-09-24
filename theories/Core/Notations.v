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

(* A second scope for the list notations, delimited but not opened: [[]] is
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

(* A third scope for the product notations, delimited but not opened like
 * the list one. [A * B] is not in it: a type former belongs in
 * [jwa_type_scope] beside [->].
 *)
Declare Scope jwa_product_scope.
Delimit Scope jwa_product_scope with product.

(* A fourth scope, for the [Bool] operations, delimited but not opened like
 * the two above. The spellings are contested: [&&] and [||] are what a
 * closed notation elsewhere would take away, and [!] is the boolean
 * negation beside the logical [~], which stays in [jwa_type_scope] because
 * a proposition is what the tree is mostly about.
 *)
Declare Scope jwa_bool_scope.
Delimit Scope jwa_bool_scope with bool.

(* One scope per numeral type, delimited but not opened, so that [+] and [*]
   name that type's operations only under its delimiter: [(m + n)%nat],
   [(m + n)%nat_with_zero]. Two types cannot share a scope, since one
   spelling would then have two meanings. *)
Declare Scope jwa_nat_scope.
Delimit Scope jwa_nat_scope with nat.
Declare Scope jwa_nat_with_zero_scope.
Delimit Scope jwa_nat_with_zero_scope with nat_with_zero.
Declare Scope jwa_integer_scope.
Delimit Scope jwa_integer_scope with integer.
Declare Scope jwa_rational_scope.
Delimit Scope jwa_rational_scope with rational.

(* Precedence follows the textbook order, [~] tightest and [->] loosest with
   [exists] beyond them, so a formula reads without parentheses; [_\/_] sits
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
Reserved Notation "! b"
  (at level 35, right associativity).
Reserved Notation "x && y"
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
Reserved Notation "x || y"
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

(* The symmetry and the transitivity of [=] written as terms, for the same
 * reason and at the same level. Their meanings belong to [Tactics.Equation].
 *)
Reserved Notation "'symm' H"
  (at level 10, H at next level).
Reserved Notation "'trans' H1 , H2"
  (at level 10, H1 at next level, H2 at next level).

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
   [..] is what lets one [exists] carry several of them. *)
Reserved Notation "'exists' x .. y '.' p"
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
 * [forall x, p]. [exists] gets its dotted spelling in [Core.Logic.Exists],
 * where its meaning is.
 *)
Notation "'forall' x .. y '.' p" := (forall x, .. (forall y, p) ..)
  (at level 200, x binder, y binder, right associativity).

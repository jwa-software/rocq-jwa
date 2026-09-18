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
   the empty list and [++] is [List.append] only where a file opens the
   scope or writes [(...)%list], so the same spellings stay free for other
   containers in scopes of their own. *)
Declare Scope jwa_list_scope.
Delimit Scope jwa_list_scope with list.

(* A third scope for the product notations, delimited but not opened like
 * the list one. [A * B] is not in it: a type former belongs in
 * [jwa_type_scope] beside [->].
 *)
Declare Scope jwa_product_scope.
Delimit Scope jwa_product_scope with product.

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

(* Precedence follows the textbook order, [~] tightest and [->] loosest with
   [exists] beyond them, so a formula reads without parentheses; [_\/_] sits
   between [/\] and [\/] as [^^] sits between [&&] and [||]. The quotes make
   [contains_member] a keyword rather than a variable. *)
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
Reserved Notation "x && y"
  (at level 40, left associativity).
Reserved Notation "x * y"
  (at level 40, left associativity).
Reserved Notation "x ^^ y"
  (at level 45, left associativity).
Reserved Notation "x || y"
  (at level 50, left associativity).
Reserved Notation "x + y"
  (at level 50, left associativity).
Reserved Notation "x ++ y"
  (at level 60, right associativity).
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

(* [x binder] is what lets [x] be written with or without its type, and the
   [..] is what lets one [exists] carry several of them. *)
Reserved Notation "'exists' x .. y , p"
  (at level 200, x binder, y binder, right associativity).

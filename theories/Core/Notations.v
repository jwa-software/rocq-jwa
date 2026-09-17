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

(* A level is a claim against every other notation in the library, so all of
   them are declared here, while every meaning is supplied elsewhere: [=] in
   [Core.Equijunction]; [->], [-/>], [~], [/\], [_\/_], [\/], [<->] and
   [exists] in [Core.Logic]; [&&], [^^] and [||] in [Data.Bool]; [::], [++],
   [contains_member], [belongs_to] and their negations
   [does_not_contain_member], [does_not_belong_to] in [Data.List]. *)

(* The ordering is the load-bearing part: 70 < 75 < 80 < 82 < 85 < 90 < 95
   < 99 is what reads [~ x = y /\ P -> Q] as [((~ (x = y)) /\ P) -> Q], and
   [A \/ B <-> C] as [(A \/ B) <-> C]; [_\/_] sits between [/\] and [\/] as
   [^^] sits between [&&] and [||]. [-/>] at 90 binds tighter than [->], so
   [A -/> B -> C] is [(A -/> B) -> C], and looser than [\/], so
   [A \/ B -/> C] is [(A \/ B) -/> C]. At 200 [exists] is looser than all of
   them, so its body runs to the end: [exists n, P n -> Q] is
   [exists n, (P n -> Q)]. The boolean operators sit below [=] at
   40 < 45 < 50, so [a && b = c] is [(a && b) = c] and [a && b ^^ c || d] is
   [((a && b) ^^ c) || d]. [++] at 60 sits between them and [=], right
   associative, so [l1 ++ l2 ++ l3 = l] is [(l1 ++ (l2 ++ l3)) = l]; [::]
   shares that level and associativity, so [a :: l1 ++ l2] is
   [a :: (l1 ++ l2)] and [a :: b :: l] is [a :: (b :: l)].
   [contains_member] is a relation like [=], at 70 with no associativity,
   so [l1 ++ l2 contains_member a] is [(l1 ++ l2) contains_member a] and
   [~ l contains_member a \/ l contains_member b] is
   [(~ (l contains_member a)) \/ (l contains_member b)]. The quotes make
   [contains_member] a keyword rather than a variable;
   [belongs_to] is the same relation read from the element's side, at the
   same level. *)
Reserved Notation "x -> y"
  (at level 99, right associativity, y at level 200).
Reserved Notation "x = y"
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
Reserved Notation "x ^^ y"
  (at level 45, left associativity).
Reserved Notation "x || y"
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

(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Algebra.Monoid.
From jwa Require Import Algebra.Semigroup.
From jwa Require Import Core.All.
From jwa Require Import Data.Collection.List.
From jwa Require Import Data.Literal.
From jwa Require Import Data.Machine.Bit.
From jwa Require Import Data.Machine.Byte.
From jwa Require Import Data.Number.Nat0.
From jwa Require Import Data.Option.
From jwa Require Import Data.Text.Ascii.
From jwa Require Import Data.Text.SourceByte.
From jwa Require Import Tactics.Equation.

Module AsciiStr. (* AsciiStr *)

(* A string of [Ascii] characters, the first character first. *)
Inductive T : Type :=
  | introduction : List Ascii -> T.

Abbreviation AsciiStr := T.

Local Open Scope jwa_list_scope.

(* [AsciiStr -> List Ascii] *)
Definition to_list := fun (s : AsciiStr) .
  match s with
  | AsciiStr.introduction l => l
  end.

(* [List Ascii -> AsciiStr] *)
Definition from_list := fun (l : List Ascii) . AsciiStr.introduction l.

(* [AsciiStr] *)
Definition empty := AsciiStr.introduction [].

(* [AsciiStr -> AsciiStr -> AsciiStr] *)
Definition concat := fun (s : AsciiStr) (t : AsciiStr) .
  AsciiStr.introduction (to_list s ++ to_list t).

(* [only parsing] keeps goals printing the operation by name. *)
Notation "s ++ t" := (concat s t) (only parsing)
  : jwa_ascii_str_scope.

(* [AsciiStr -> Nat0] *)
Definition length := fun (s : AsciiStr) . List.length (to_list s).

(* Every character of [s] by [Ascii.to_upper]. *)
(* [AsciiStr -> AsciiStr] *)
Definition to_upper := fun (s : AsciiStr) .
  AsciiStr.introduction (List.map Ascii.to_upper (to_list s)).

(* Every character of [s] by [Ascii.to_lower]. *)
(* [AsciiStr -> AsciiStr] *)
Definition to_lower := fun (s : AsciiStr) .
  AsciiStr.introduction (List.map Ascii.to_lower (to_list s)).

(* Reads the UTF-8 bytes of a string literal as characters, one at a time, by
 * [Ascii.from_source_bytes]:
 *
 *   Some cs   every character reads, from one byte or else from two
 *   None      otherwise
 *)
(* [List SourceByte -> Option (List Ascii)] *)
Fixpoint list_from_source_bytes (l : List SourceByte) : Option (List Ascii) :=
  match l with
  | [] => Some []
  | s :: rest =>
      match Ascii.from_source_bytes (s :: []) with
      | Some c => Option.map (List.Cons c) (list_from_source_bytes rest)
      | None =>
          match rest with
          | [] => None
          | s2 :: rest' =>
              match Ascii.from_source_bytes (s :: s2 :: []) with
              | Some c => Option.map (List.Cons c) (list_from_source_bytes rest')
              | None => None
              end
          end
      end
  end.

(* [List SourceByte -> Option AsciiStr] *)
Definition from_source_bytes := fun (l : List SourceByte) .
  Option.map AsciiStr.introduction (list_from_source_bytes l).

(* The UTF-8 bytes of [s], each character's bytes by [Ascii.to_source_bytes]. *)
(* [AsciiStr -> List SourceByte] *)
Definition to_source_bytes := fun (s : AsciiStr) .
  List.fold_right
    (fun (c : Ascii) (bytes : List SourceByte) . Ascii.to_source_bytes c ++ bytes)
    []
    (to_list s).

Module conversion. (* conversion *)

Module list. (* conversion.list *)

(* [g (f a) = a]: [f] is a section of [g], [g] a retraction of [f]. Each law
 * below is named by what [to_list] is:
 *
 *   retraction   to_list (from_list l) = l   to_list is a retraction of from_list
 *   section      from_list (to_list s) = s   to_list is a section of from_list
 *)
(* conversion.list.retraction *)
Theorem retraction : forall (l : List Ascii) . to_list (from_list l) = l.
Proof.
  intros l.
  simpl to_list, from_list in |- *.
  quod idem est.
Qed.

(* conversion.list.section *)
Theorem section : forall (s : AsciiStr) . from_list (to_list s) = s.
Proof.
  intros s.
  match &s with | introduction l end.
  simpl to_list, from_list in |- *.
  quod idem est.
Qed.

End list. (* conversion.list *)

Module source_bytes. (* conversion.source_bytes *)

(* A character's bytes, read off the front of a longer list, give that
 * character and leave the rest to be read.
 *)
(* conversion.source_bytes.prefix *)
Lemma prefix
  : forall (c : Ascii) (rest : List SourceByte) .
      list_from_source_bytes (Ascii.to_source_bytes c ++ rest)
      = Option.map (List.Cons c) (list_from_source_bytes rest).
Proof.
  intros c rest.
  match &c with | introduction b end.
  match &b with | introduction b7 b6 b5 b4 b3 b2 b1 b0 end.
  match &b7 with | Zero | One end.
  - simpl Ascii.to_source_bytes in |- *.
    let x := SourceByte.from_byte (Byte.introduction Bit.Zero &b6 &b5 &b4 &b3 &b2 &b1 &b0)
      in |- *.
    let proof hx
      : SourceByte.to_byte &x = Byte.introduction Bit.Zero &b6 &b5 &b4 &b3 &b2 &b1 &b0
      := SourceByte.conversion.byte.retraction
           (Byte.introduction Bit.Zero &b6 &b5 &b4 &b3 &b2 &b1 &b0).
    let proof x := &x.
    simpl in |- *.
    leibniz &hx in |- *.
    simpl in |- *.
    quod idem est.
  - simpl Ascii.to_source_bytes in |- *.
    let x1 :=
      SourceByte.from_byte
        (Byte.introduction Bit.One Bit.One Bit.Zero Bit.Zero Bit.Zero Bit.Zero Bit.One &b6)
      in |- *.
    let x2 := SourceByte.from_byte (Byte.introduction Bit.One Bit.Zero &b5 &b4 &b3 &b2 &b1 &b0)
      in |- *.
    let proof hx1
      : SourceByte.to_byte &x1
        = Byte.introduction Bit.One Bit.One Bit.Zero Bit.Zero Bit.Zero Bit.Zero Bit.One &b6
      := SourceByte.conversion.byte.retraction
           (Byte.introduction Bit.One Bit.One Bit.Zero Bit.Zero Bit.Zero Bit.Zero Bit.One &b6).
    let proof hx2
      : SourceByte.to_byte &x2 = Byte.introduction Bit.One Bit.Zero &b5 &b4 &b3 &b2 &b1 &b0
      := SourceByte.conversion.byte.retraction
           (Byte.introduction Bit.One Bit.Zero &b5 &b4 &b3 &b2 &b1 &b0).
    let proof x1 := &x1.
    let proof x2 := &x2.
    simpl in |- *.
    leibniz &hx1, &hx2 in |- *.
    simpl in |- *.
    quod idem est.
Qed.

(* [from_source_bytes (to_source_bytes s) = Some s]: [to_source_bytes] is a
 * section of [from_source_bytes], so every string prints as a literal that
 * reads back.
 *)
(* conversion.source_bytes.section *)
Theorem section : forall (s : AsciiStr) . from_source_bytes (to_source_bytes s) = Some s.
Proof.
  intros s.
  match &s with | introduction l end.
  lemma characters
    : forall (cs : List Ascii) .
        list_from_source_bytes
          (List.fold_right
            (fun (c : Ascii) (bytes : List SourceByte) . Ascii.to_source_bytes c ++ bytes)
            [] cs)
        = Some cs.
  {
    intros cs.
    match cs with | Nil | Cons c (cs' by IH) end per List.induction.
    - simpl in |- *.
      quod idem est.
    - lemma unfolding
        : List.fold_right
            (fun (c : Ascii) (bytes : List SourceByte) . Ascii.to_source_bytes c ++ bytes)
            [] (&c :: &cs')
          = Ascii.to_source_bytes &c
            ++ List.fold_right
                 (fun (c : Ascii) (bytes : List SourceByte) . Ascii.to_source_bytes c ++ bytes)
                 [] &cs'.
      {
        simpl in |- *.
        quod idem est.
      }
      leibniz
        &unfolding,
        (conversion.source_bytes.prefix &c
          (List.fold_right
            (fun (c : Ascii) (bytes : List SourceByte) . Ascii.to_source_bytes c ++ bytes)
            [] &cs')),
        &IH
        in |- *.
      simpl in |- *.
      quod idem est.
  }
  simpl from_source_bytes, to_source_bytes, to_list in |- *.
  leibniz (&characters &l) in |- *.
  simpl in |- *.
  quod idem est.
Qed.

End source_bytes. (* conversion.source_bytes *)

End conversion. (* conversion *)

Module concatenation. (* concatenation *)

(* concatenation.associativity *)
Theorem associativity
  : forall (s : AsciiStr) (t : AsciiStr) (u : AsciiStr) . ((s ++ t) ++ u = s ++ (t ++ u))%a.
Proof.
  intros s t u.
  match &s with | introduction l1 end.
  match &t with | introduction l2 end.
  match &u with | introduction l3 end.
  simpl concat, to_list in |- *.
  leibniz (List.concatenation.associativity &l1 &l2 &l3) in |- *.
  quod idem est.
Qed.

(* concatenation.identity *)
Theorem identity
  : forall (s : AsciiStr) . ((empty ++ s = s) /\ (s ++ empty = s))%a.
Proof.
  intros s.
  match &s with | introduction l end.
  match (List.concatenation.identity &l) with | left right end.
  divide et impera.
  - simpl concat, to_list, empty in |- *.
    leibniz &left in |- *.
    quod idem est.
  - simpl concat, to_list, empty in |- *.
    leibniz &right in |- *.
    quod idem est.
Qed.

End concatenation. (* concatenation *)

Module length. (* length *)

Module additivity. (* length.additivity *)

Module over. (* length.additivity.over *)

(* length.additivity.over.concatenation *)
Theorem concatenation
  : forall (s : AsciiStr) (t : AsciiStr) .
      length (s ++ t)%a = (length s + length t)%n0.
Proof.
  intros s t.
  match &s with | introduction l1 end.
  match &t with | introduction l2 end.
  simpl length, concat, to_list in |- *.
  ipso (List.length.additivity.over.concatenation &l1 &l2).
Qed.

End over. (* length.additivity.over *)

End additivity. (* length.additivity *)

End length. (* length *)

Module uppercasing. (* uppercasing *)

Module preservation. (* uppercasing.preservation *)

Module of. (* uppercasing.preservation.of *)

(* uppercasing.preservation.of.length *)
Theorem length : forall (s : AsciiStr) . length (to_upper s) = length s.
Proof.
  intros s.
  match &s with | introduction l end.
  simpl length, to_upper, to_list in |- *.
  ipso (List.mapping.preservation.of.length Ascii.to_upper &l).
Qed.

End of. (* uppercasing.preservation.of *)

End preservation. (* uppercasing.preservation *)

Module distributivity. (* uppercasing.distributivity *)

Module over. (* uppercasing.distributivity.over *)

(* uppercasing.distributivity.over.concatenation *)
Theorem concatenation
  : forall (s : AsciiStr) (t : AsciiStr) . (to_upper (s ++ t) = to_upper s ++ to_upper t)%a.
Proof.
  intros s t.
  match &s with | introduction l1 end.
  match &t with | introduction l2 end.
  simpl to_upper, concat, to_list in |- *.
  ipso
    (congru AsciiStr.introduction,
      (List.mapping.distributivity.over.concatenation Ascii.to_upper &l1 &l2)).
Qed.

End over. (* uppercasing.distributivity.over *)

End distributivity. (* uppercasing.distributivity *)

End uppercasing. (* uppercasing *)

Module lowercasing. (* lowercasing *)

Module preservation. (* lowercasing.preservation *)

Module of. (* lowercasing.preservation.of *)

(* lowercasing.preservation.of.length *)
Theorem length : forall (s : AsciiStr) . length (to_lower s) = length s.
Proof.
  intros s.
  match &s with | introduction l end.
  simpl length, to_lower, to_list in |- *.
  ipso (List.mapping.preservation.of.length Ascii.to_lower &l).
Qed.

End of. (* lowercasing.preservation.of *)

End preservation. (* lowercasing.preservation *)

Module distributivity. (* lowercasing.distributivity *)

Module over. (* lowercasing.distributivity.over *)

(* lowercasing.distributivity.over.concatenation *)
Theorem concatenation
  : forall (s : AsciiStr) (t : AsciiStr) . (to_lower (s ++ t) = to_lower s ++ to_lower t)%a.
Proof.
  intros s t.
  match &s with | introduction l1 end.
  match &t with | introduction l2 end.
  simpl to_lower, concat, to_list in |- *.
  ipso
    (congru AsciiStr.introduction,
      (List.mapping.distributivity.over.concatenation Ascii.to_lower &l1 &l2)).
Qed.

End over. (* lowercasing.distributivity.over *)

End distributivity. (* lowercasing.distributivity *)

End lowercasing. (* lowercasing *)

End AsciiStr. (* AsciiStr *)

(* The counterpart of the abbreviation inside the module: a client writes
 * [AsciiStr], not [AsciiStr.T].
 *)
Abbreviation AsciiStr := AsciiStr.T.

(* Makes [++] usable in every file that imports this one, as [(s ++ t)%a] or
 * under an opened [jwa_ascii_str_scope].
 *)
Export (notations) AsciiStr.

(* A string is written as a string literal under its key, ["abc"%a], and a
 * closed one prints back so.
 *)
String Notation AsciiStr.T AsciiStr.from_source_bytes AsciiStr.to_source_bytes
  : jwa_ascii_str_scope.

(* Where an [AsciiStr] is expected, a literal reads in this scope without its
 * [%a].
 *)
Bind Scope jwa_ascii_str_scope with AsciiStr.T.

Instance AsciiStr_concat_monoid
  : Monoid AsciiStr.concat AsciiStr.empty :=
  {| Monoid.semigroup :=
      {| Semigroup.associativity := AsciiStr.concatenation.associativity |}
  ; Monoid.identity := AsciiStr.concatenation.identity |}.

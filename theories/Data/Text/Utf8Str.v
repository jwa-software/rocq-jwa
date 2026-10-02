(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Algebra.Monoid.
From jwa Require Import Algebra.Semigroup.
From jwa Require Import Core.All.
From jwa Require Import Data.Assert.
From jwa Require Import Data.Collection.List.
From jwa Require Import Data.Literal.
From jwa Require Import Data.Machine.Byte.
From jwa Require Import Data.Number.Nat0.
From jwa Require Import Data.Option.
From jwa Require Import Data.Text.Ascii.
From jwa Require Import Data.Text.AsciiStr.
From jwa Require Import Data.Text.SourceByte.
From jwa Require Import Data.Text.Utf8.
From jwa Require Import Tactics.Equation.

Module Utf8Str. (* Utf8Str *)

(* A string of [Utf8] characters, the first character first. *)
Inductive T : Type :=
  | introduction : List Utf8 -> T.

Abbreviation Utf8Str := T.

Local Open Scope jwa_list_scope.

(* [Utf8Str -> List Utf8] *)
Definition to_list := fun (s : Utf8Str) .
  match s with
  | Utf8Str.introduction l => l
  end.

(* [List Utf8 -> Utf8Str] *)
Definition from_list := fun (l : List Utf8) . Utf8Str.introduction l.

(* [Utf8Str] *)
Definition empty := Utf8Str.introduction [].

(* [Utf8Str -> Utf8Str -> Utf8Str] *)
Definition concat := fun (s : Utf8Str) (t : Utf8Str) .
  Utf8Str.introduction (to_list s ++ to_list t).

(* [only parsing] keeps goals printing the operation by name. *)
Notation "s ++ t" := (concat s t) (only parsing)
  : jwa_utf8_str_scope.

(* The number of characters, which is not the number of bytes. *)
(* [Utf8Str -> Nat0] *)
Definition length := fun (s : Utf8Str) . List.length (to_list s).

(* The UTF-8 bytes of [s], each character's bytes in turn. *)
(* [Utf8Str -> List Byte] *)
Definition to_bytes := fun (s : Utf8Str) .
  List.fold_right (fun (c : Utf8) (bytes : List Byte) . Utf8.to_bytes c ++ bytes) [] (to_list s).

(* Reads bytes as characters, one at a time, each from the fewest bytes
 * [Utf8.from_bytes] reads one from:
 *
 *   Some cs   every character reads
 *   None      otherwise
 *
 * No character's bytes begin another's, so the fewest are the only ones.
 *)
(* [List Byte -> Option (List Utf8)] *)
Fixpoint list_from_bytes (l : List Byte) : Option (List Utf8) :=
  match l with
  | [] => Some []
  | x :: l1 =>
      match Utf8.from_bytes (x :: []) with
      | Some c => Option.map (List.Cons c) (list_from_bytes l1)
      | None =>
          match l1 with
          | [] => None
          | y :: l2 =>
              match Utf8.from_bytes (x :: y :: []) with
              | Some c => Option.map (List.Cons c) (list_from_bytes l2)
              | None =>
                  match l2 with
                  | [] => None
                  | z :: l3 =>
                      match Utf8.from_bytes (x :: y :: z :: []) with
                      | Some c => Option.map (List.Cons c) (list_from_bytes l3)
                      | None =>
                          match l3 with
                          | [] => None
                          | w :: l4 =>
                              match Utf8.from_bytes (x :: y :: z :: w :: []) with
                              | Some c => Option.map (List.Cons c) (list_from_bytes l4)
                              | None => None
                              end
                          end
                      end
                  end
              end
          end
      end
  end.

(* [List Byte -> Option Utf8Str] *)
Definition from_bytes := fun (l : List Byte) .
  Option.map Utf8Str.introduction (list_from_bytes l).

(* Reads the UTF-8 bytes of a string literal, by [from_bytes]. *)
(* [List SourceByte -> Option Utf8Str] *)
Definition from_source_bytes := fun (l : List SourceByte) .
  from_bytes (List.map SourceByte.to_byte l).

(* The UTF-8 bytes of [s], which are its own bytes. *)
(* [Utf8Str -> List SourceByte] *)
Definition to_source_bytes := fun (s : Utf8Str) .
  List.map SourceByte.from_byte (to_bytes s).

(* Every character of [s] by [Utf8.from_ascii], read as Latin-1. *)
(* [AsciiStr -> Utf8Str] *)
Definition from_ascii_str := fun (s : AsciiStr) .
  Utf8Str.introduction (List.map Utf8.from_ascii (AsciiStr.to_list s)).

(* Every character by [Utf8.to_ascii]: [Some] of them all, or [None] when one
 * is past U+00FF.
 *)
(* [List Utf8 -> Option (List Ascii)] *)
Fixpoint list_to_ascii (l : List Utf8) : Option (List Ascii) :=
  match l with
  | [] => Some []
  | c :: rest =>
      match Utf8.to_ascii c with
      | Some a => Option.map (List.Cons a) (list_to_ascii rest)
      | None => None
      end
  end.

(* [Some] of the same characters as an [AsciiStr] when each is U+0000 to
 * U+00FF, [None] otherwise.
 *)
(* [Utf8Str -> Option AsciiStr] *)
Definition to_ascii_str := fun (s : Utf8Str) .
  Option.map AsciiStr.introduction (list_to_ascii (to_list s)).

Module conversion. (* conversion *)

Module list. (* conversion.list *)

(* [g (f a) = a]: [f] is a section of [g], [g] a retraction of [f]. Each law
 * below is named by what [to_list] is:
 *
 *   retraction   to_list (from_list l) = l   to_list is a retraction of from_list
 *   section      from_list (to_list s) = s   to_list is a section of from_list
 *)
(* conversion.list.retraction *)
Theorem retraction : forall (l : List Utf8) . to_list (from_list l) = l.
Proof.
  intros l.
  simpl to_list, from_list in |- *.
  quod idem est.
Qed.

(* conversion.list.section *)
Theorem section : forall (s : Utf8Str) . from_list (to_list s) = s.
Proof.
  intros s.
  match &s with | introduction l end.
  simpl to_list, from_list in |- *.
  quod idem est.
Qed.

End list. (* conversion.list *)

Module bytes. (* conversion.bytes *)

(* A character's bytes, read off the front of a longer list, give that
 * character and leave the rest to be read.
 *)
(* conversion.bytes.prefix *)
Lemma prefix
  : forall (c : Utf8) (rest : List Byte) .
      list_from_bytes (Utf8.to_bytes c ++ rest)
      = Option.map (List.Cons c) (list_from_bytes rest).
Proof.
  intros c rest.
  match &c with
  | OneByte x p | TwoBytes x y p | ThreeBytes x y z p | FourBytes x y z w p
  end.
  - let proof one
      : Assert.guard (Utf8.is_one_byte &x) (Utf8.OneByte &x) = Some (Utf8.OneByte &x &p)
      := Assert.guarding.evaluation (Utf8.is_one_byte &x) (Utf8.OneByte &x) &p.
    simpl in |- *.
    leibniz &one in |- *.
    simpl in |- *.
    quod idem est.
  (* The first byte, [110xxxxx], reads as no character on its own. *)
  - lemma one : Assert.guard (Utf8.is_one_byte &x) (Utf8.OneByte &x) = None.
    {
      match &x with | introduction b7 b6 b5 b4 b3 b2 b1 b0 end.
      match &b7 with | Zero | One end.
      - simpl in &p.
        ex &p quodlibet.
      - simpl in |- *.
        quod idem est.
    }
    let proof two
      : Assert.guard (Utf8.is_two_bytes &x &y) (Utf8.TwoBytes &x &y)
        = Some (Utf8.TwoBytes &x &y &p)
      := Assert.guarding.evaluation (Utf8.is_two_bytes &x &y) (Utf8.TwoBytes &x &y) &p.
    simpl in |- *.
    leibniz &one, &two in |- *.
    simpl in |- *.
    quod idem est.
  (* The first byte, [1110xxxx], reads as no character alone or with one more. *)
  - lemma one : Assert.guard (Utf8.is_one_byte &x) (Utf8.OneByte &x) = None.
    {
      match &x with | introduction b7 b6 b5 b4 b3 b2 b1 b0 end.
      match &b7 with | Zero | One end.
      - simpl in &p.
        ex &p quodlibet.
      - simpl in |- *.
        quod idem est.
    }
    lemma two : Assert.guard (Utf8.is_two_bytes &x &y) (Utf8.TwoBytes &x &y) = None.
    {
      match &x with | introduction b7 b6 b5 b4 b3 b2 b1 b0 end.
      match &b7 with | Zero | One end.
      - simpl in &p.
        ex &p quodlibet.
      - match &b6 with | Zero | One end.
        + simpl in &p.
          ex &p quodlibet.
        + match &b5 with | Zero | One end.
          * simpl in &p.
            ex &p quodlibet.
          * simpl in |- *.
            quod idem est.
    }
    let proof three
      : Assert.guard (Utf8.is_three_bytes &x &y &z) (Utf8.ThreeBytes &x &y &z)
        = Some (Utf8.ThreeBytes &x &y &z &p)
      := Assert.guarding.evaluation
        (Utf8.is_three_bytes &x &y &z) (Utf8.ThreeBytes &x &y &z) &p.
    simpl in |- *.
    leibniz &one, &two, &three in |- *.
    simpl in |- *.
    quod idem est.
  (* The first byte, [11110xxx], reads as no character alone or with one or
   * two more.
   *)
  - lemma one : Assert.guard (Utf8.is_one_byte &x) (Utf8.OneByte &x) = None.
    {
      match &x with | introduction b7 b6 b5 b4 b3 b2 b1 b0 end.
      match &b7 with | Zero | One end.
      - simpl in &p.
        ex &p quodlibet.
      - simpl in |- *.
        quod idem est.
    }
    lemma two : Assert.guard (Utf8.is_two_bytes &x &y) (Utf8.TwoBytes &x &y) = None.
    {
      match &x with | introduction b7 b6 b5 b4 b3 b2 b1 b0 end.
      match &b7 with | Zero | One end.
      - simpl in &p.
        ex &p quodlibet.
      - match &b6 with | Zero | One end.
        + simpl in &p.
          ex &p quodlibet.
        + match &b5 with | Zero | One end.
          * simpl in &p.
            ex &p quodlibet.
          * simpl in |- *.
            quod idem est.
    }
    lemma three
      : Assert.guard (Utf8.is_three_bytes &x &y &z) (Utf8.ThreeBytes &x &y &z) = None.
    {
      match &x with | introduction b7 b6 b5 b4 b3 b2 b1 b0 end.
      match &b7 with | Zero | One end.
      - simpl in &p.
        ex &p quodlibet.
      - match &b6 with | Zero | One end.
        + simpl in &p.
          ex &p quodlibet.
        + match &b5 with | Zero | One end.
          * simpl in &p.
            ex &p quodlibet.
          * match &b4 with | Zero | One end.
            -- simpl in &p.
               ex &p quodlibet.
            -- simpl in |- *.
               quod idem est.
    }
    let proof four
      : Assert.guard (Utf8.is_four_bytes &x &y &z &w) (Utf8.FourBytes &x &y &z &w)
        = Some (Utf8.FourBytes &x &y &z &w &p)
      := Assert.guarding.evaluation
        (Utf8.is_four_bytes &x &y &z &w) (Utf8.FourBytes &x &y &z &w) &p.
    simpl in |- *.
    leibniz &one, &two, &three, &four in |- *.
    simpl in |- *.
    quod idem est.
Qed.

(* [from_bytes (to_bytes s) = Some s]: [to_bytes] is a section of
 * [from_bytes], so a string's bytes read back as that string.
 *)
(* conversion.bytes.section *)
Theorem section : forall (s : Utf8Str) . from_bytes (to_bytes s) = Some s.
Proof.
  intros s.
  match &s with | introduction l end.
  lemma characters
    : forall (cs : List Utf8) .
        list_from_bytes
          (List.fold_right (fun (c : Utf8) (bytes : List Byte) . Utf8.to_bytes c ++ bytes) [] cs)
        = Some cs.
  {
    intros cs.
    match &cs with | Nil | Cons c (cs' by IH) end per List.induction.
    - simpl in |- *.
      quod idem est.
    - lemma unfolding
        : List.fold_right
            (fun (c : Utf8) (bytes : List Byte) . Utf8.to_bytes c ++ bytes) [] (&c :: &cs')
          = Utf8.to_bytes &c
            ++ List.fold_right
              (fun (c : Utf8) (bytes : List Byte) . Utf8.to_bytes c ++ bytes) [] &cs'.
      {
        simpl in |- *.
        quod idem est.
      }
      leibniz
        &unfolding,
        (conversion.bytes.prefix &c
          (List.fold_right
            (fun (c : Utf8) (bytes : List Byte) . Utf8.to_bytes c ++ bytes) [] &cs')),
        &IH
        in |- *.
      simpl in |- *.
      quod idem est.
  }
  simpl from_bytes, to_bytes, to_list in |- *.
  leibniz (&characters &l) in |- *.
  simpl in |- *.
  quod idem est.
Qed.

(* conversion.bytes.injectivity *)
Theorem injectivity : forall {s : Utf8Str} {t : Utf8Str} . to_bytes s = to_bytes t -> s = t.
Proof.
  intros s t e.
  congru from_bytes, &e |- f.
  leibniz (conversion.bytes.section &s), (conversion.bytes.section &t) in &f.
  ipso (Option.some.injectivity &f).
Qed.

End bytes. (* conversion.bytes *)

Module source_bytes. (* conversion.source_bytes *)

(* [from_source_bytes (to_source_bytes s) = Some s]: [to_source_bytes] is a
 * section of [from_source_bytes], so every string prints as a literal that
 * reads back.
 *)
(* conversion.source_bytes.section *)
Theorem section : forall (s : Utf8Str) . from_source_bytes (to_source_bytes s) = Some s.
Proof.
  intros s.
  simpl from_source_bytes, to_source_bytes in |- *.
  leibniz (SourceByte.conversion.bytes.retraction (to_bytes &s)) in |- *.
  ipso (conversion.bytes.section &s).
Qed.

End source_bytes. (* conversion.source_bytes *)

Module ascii. (* conversion.ascii *)

(* [to_ascii_str (from_ascii_str s) = Some s]: [to_ascii_str] is a
 * retraction of [from_ascii_str], so every [AsciiStr] comes back from its
 * [Utf8Str] form.
 *)
(* conversion.ascii.retraction *)
Theorem retraction : forall (s : AsciiStr) . to_ascii_str (from_ascii_str s) = Some s.
Proof.
  intros s.
  match &s with | introduction l end.
  lemma characters
    : forall (cs : List Ascii) . list_to_ascii (List.map Utf8.from_ascii cs) = Some cs.
  {
    intros cs.
    match &cs with | Nil | Cons a (cs' by IH) end per List.induction.
    - simpl in |- *.
      quod idem est.
    - simpl in |- *.
      leibniz (Utf8.conversion.ascii.retraction &a) in |- *.
      simpl in |- *.
      leibniz &IH in |- *.
      simpl in |- *.
      quod idem est.
  }
  simpl to_ascii_str, from_ascii_str, to_list, AsciiStr.to_list in |- *.
  leibniz (&characters &l) in |- *.
  simpl in |- *.
  quod idem est.
Qed.

(* [to_ascii_str t = Some s] only for [t = from_ascii_str s]: the strings
 * that read as [AsciiStr] are those [from_ascii_str] gives.
 *)
(* conversion.ascii.inversion *)
Theorem inversion
  : forall (t : Utf8Str) (s : AsciiStr) . to_ascii_str t = Some s -> from_ascii_str s = t.
Proof.
  intros t s h.
  match &t with | introduction l end.
  match &s with | introduction m end.
  lemma characters
    : forall (cs : List Utf8) (bs : List Ascii) .
        list_to_ascii cs = Some bs -> List.map Utf8.from_ascii bs = cs.
  {
    intros cs.
    match &cs with | Nil | Cons c (cs' by IH) end per List.induction.
    - intros bs k.
      simpl in &k.
      let proof e := Option.some.injectivity &k.
      leibniz <- &e in |- *.
      simpl in |- *.
      quod idem est.
    - intros bs k.
      simpl in &k.
      match (Utf8.to_ascii &c) with | | a end |- ec.
      + ex &k quodlibet.
      + match (list_to_ascii &cs') with | | bs' end |- ek.
        * simpl in &k.
          ex &k quodlibet.
        (* The case split wrote [Some bs'] for [list_to_ascii cs'] in [IH]
         * too, so its premise is now met by reflexivity.
         *)
        * simpl in &k.
          let proof e := Option.some.injectivity &k.
          leibniz <- &e in |- *.
          simpl in |- *.
          leibniz
            (Utf8.conversion.ascii.inversion &c &a &ec),
            (&IH &bs' (Identity.reflexivity _))
            in |- *.
          quod idem est.
  }
  simpl to_ascii_str, to_list in &h.
  match (list_to_ascii &l) with | | bs end |- e.
  - simpl in &h.
    ex &h quodlibet.
  - simpl in &h.
    let proof f := Option.some.injectivity &h.
    congru AsciiStr.to_list, &f |- g.
    simpl AsciiStr.to_list in &g.
    simpl from_ascii_str, AsciiStr.to_list in |- *.
    leibniz <- &g, <- (&characters &l &bs &e) in |- *.
    quod idem est.
Qed.

Module preservation. (* conversion.ascii.preservation *)

Module of. (* conversion.ascii.preservation.of *)

(* conversion.ascii.preservation.of.length *)
Theorem length : forall (s : AsciiStr) . length (from_ascii_str s) = AsciiStr.length s.
Proof.
  intros s.
  simpl length, from_ascii_str, to_list, AsciiStr.length in |- *.
  ipso (List.mapping.preservation.of.length Utf8.from_ascii (AsciiStr.to_list &s)).
Qed.

End of. (* conversion.ascii.preservation.of *)

End preservation. (* conversion.ascii.preservation *)

End ascii. (* conversion.ascii *)

End conversion. (* conversion *)

Module concatenation. (* concatenation *)

(* concatenation.associativity *)
Theorem associativity
  : forall (s : Utf8Str) (t : Utf8Str) (u : Utf8Str) . ((s ++ t) ++ u = s ++ (t ++ u))%u8.
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
  : forall (s : Utf8Str) . ((empty ++ s = s) /\ (s ++ empty = s))%u8.
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
  : forall (s : Utf8Str) (t : Utf8Str) .
      length (s ++ t)%u8 = (length s + length t)%n0.
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

End Utf8Str. (* Utf8Str *)

(* The counterpart of the abbreviation inside the module: a client writes
 * [Utf8Str], not [Utf8Str.T].
 *)
Abbreviation Utf8Str := Utf8Str.T.

(* Makes [++] usable in every file that imports this one, as [(s ++ t)%u8] or
 * under an opened [jwa_utf8_str_scope].
 *)
Export (notations) Utf8Str.

(* A string is written as a string literal under its key, ["abc"%u8], and a
 * closed one prints back so.
 *)
String Notation Utf8Str.T Utf8Str.from_source_bytes Utf8Str.to_source_bytes
  : jwa_utf8_str_scope.

(* Where a [Utf8Str] is expected, a literal reads in this scope without its
 * [%u8].
 *)
Bind Scope jwa_utf8_str_scope with Utf8Str.T.

Instance Utf8Str_concat_monoid
  : Monoid Utf8Str.concat Utf8Str.empty :=
  {| Monoid.semigroup :=
      {| Semigroup.associativity := Utf8Str.concatenation.associativity |}
  ; Monoid.identity := Utf8Str.concatenation.identity |}.

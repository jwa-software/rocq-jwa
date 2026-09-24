(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.Logic.Exists.
From jwa Require Import Core.Notations.
From jwa Require Import Dialect.Local.
From jwa Require Import Dialect.Ltac.
From Ltac2 Require Array Constr Control Int List Message Std.

(* The introduction of [forsome], goal first:
 *
 *   exists <w>                 |- forsome x . P x     becomes   |- P w
 *   exists <w1>, ..., <wn>     |- forsome x1 .. xn . P    each in turn
 *
 * The goal must be a [forsome] as written. The goal left is [P] with the
 * witness put for its variable, and nothing reduced beyond that; the
 * witnesses are given in the order the variables are bound.
 *)

Ltac2 witness_refuse (parts : message list) :=
  Control.zero
    (Tactic_failure
       (Some (List.fold_right Message.concat parts (Message.of_string "")))).

(* <w> read as an [A]; when it is none, the refusal says what it is. *)
Ltac2 witness_of (w : preterm) (a : constr) : constr :=
  Control.once_plus
    (fun () =>
      Constr.Pretype.pretype
        Constr.Pretype.Flags.constr_flags (Constr.Pretype.expected_oftype a) w)
    (fun e =>
      match
        Control.once_plus
          (fun () =>
            Some (Constr.Pretype.pretype
                    Constr.Pretype.Flags.constr_flags
                    Constr.Pretype.expected_without_type_constraint w))
          (fun _ => None)
      with
      | Some alone =>
          witness_refuse
            [Message.of_string "exists: "; Message.of_constr alone;
             Message.of_string " has type "; Message.of_constr (Constr.type alone);
             Message.of_string ", but the goal quantifies over "; Message.of_constr a]
      | None => Control.zero e
      end).

Ltac2 one_witness (w : preterm) :=
  let goal := Control.goal () in
  let not_forsome () :=
    witness_refuse [Message.of_string "exists: the goal is not forsome x . P x: ";
                    Message.of_constr goal] in
  match Constr.Unsafe.kind goal with
  | Constr.Unsafe.App head args =>
      if Constr.equal head constr:(@Exists)
      then
        if Int.equal (Array.length args) 2
        then
          let a := Array.get args 0 in
          let p := Array.get args 1 in
          let w := witness_of w a in
          let after :=
            match Constr.Unsafe.kind p with
            | Constr.Unsafe.Lambda _ body => Constr.Unsafe.substnl [w] 0 body
            | _ => Constr.Unsafe.make (Constr.Unsafe.App p [| w |])
            end in
          Control.refine (fun () =>
            open_constr:(@Exists_introduction $a $p $w (_ : $after)))
        else not_forsome ()
      else not_forsome ()
  | _ => not_forsome ()
  end.

Ltac2 Notation "exists" ws(list1(preterm, ",")) :=
  Control.enter (fun () =>
    (Local.check_preterms "exists" ws;
     List.iter one_witness ws)).

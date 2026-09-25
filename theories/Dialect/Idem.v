(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Export Dialect.Ltac.
From Ltac2 Require Array Constr Control Int Message Std.

(* quod idem est    closes a goal <a> = <b> whose two sides are the same term
 *
 * Latin for "which is the same thing". The sides are compared as written,
 * up to the names of bound variables, and nothing is reduced: a side that
 * only computes to the other is refused, and the step that computes it is
 * written before, with [simpl] or [leibniz]. Any other goal is refused,
 * one a constructor proves included: [ipso <constructor>] closes that. A
 * tactic notation, not a term notation, so [quod], [idem] and [est] stay
 * free as names.
 *)
Ltac2 idem_refuse (m : message) :=
  Control.zero (Tactic_failure (Some (Message.concat (Message.of_string "quod idem est: ") m))).

(* The type [=] stands for, set with [Ltac2 Set] by the file that defines
 * it; until then every goal is refused.
 *)
Ltac2 mutable equality : unit -> constr option := fun () => None.

Ltac2 is_equality (head : constr) : bool :=
  match equality () with
  | Some e => Constr.equal head e
  | None => false
  end.

(* The sides are the last two arguments, [<a> = <b>] carrying its type
 * argument in front of them.
 *)
Ltac2 quod_idem_est () :=
  Control.enter (fun () =>
    let goal := Control.goal () in
    let not_an_equation () :=
      idem_refuse
        (Message.concat (Message.of_string "the goal is not an equation: ") (Message.of_constr goal)) in
    match Constr.Unsafe.kind goal with
    | Constr.Unsafe.App head args =>
        let n := Array.length args in
        if Int.lt n 2
        then not_an_equation ()
        else if is_equality head
        then
          let a := Array.get args (Int.sub n 2) in
          let b := Array.get args (Int.sub n 1) in
          if Constr.equal a b
          then Std.reflexivity ()
          else
            idem_refuse
              (Message.concat (Message.of_string "the sides differ, ")
                 (Message.concat (Message.of_constr a)
                    (Message.concat (Message.of_string " and ")
                       (Message.concat (Message.of_constr b)
                          (Message.of_string "; make them the same first")))))
        else not_an_equation ()
    | _ => not_an_equation ()
    end).

Ltac2 Notation "quod" "idem" "est" :=
  quod_idem_est ().

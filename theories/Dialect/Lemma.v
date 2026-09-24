(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Export Dialect.Ltac.
From jwa Require Import Dialect.Local.
From Ltac2 Require Control Ident List Message Std.

(* lemma <H> : <T>    assert (<H> : <T>)
 *
 * Opens <T> as the first goal; once it is proved, the goal it was stated in
 * gains <H> : <T>. The proof follows at once, in a block:
 *
 *   lemma H : T.
 *   {
 *     intro a.
 *     ipso (f &a).
 *   }
 *
 * <H> must be a new name; one already in the context is refused.
 *)
Ltac2 lemma_named (h : ident) (t : constr) :=
  if List.exist (fun x => match x with (y, _, _) => Ident.equal h y end) (Control.hyps ())
  then
    Control.zero
      (Tactic_failure
         (Some (Message.concat (Message.of_string "lemma: ")
               (Message.concat (Message.of_ident h)
                               (Message.of_string " is already in the context")))))
  else Std.assert (Std.AssertType (Some (Std.IntroNaming (Std.IntroIdentifier h))) t None).

Ltac2 Notation "lemma" h(ident) ":" t(thunk(lconstr)) :=
  Control.enter (fun () => lemma_named h (Local.checked "lemma" t)).

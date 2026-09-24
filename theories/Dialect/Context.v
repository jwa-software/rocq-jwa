(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Export Dialect.Ltac.
From Ltac2 Require Control Std.

(* Tidying the context:
 *
 *   mv <H> <name>          rename <H> into <name>
 *   rm <H1> ... <Hn>       clear <H1> ... <Hn>
 *
 * [mv] takes exactly the old name and then the new one. It never overwrites:
 * a new name already in the context is an error, and nothing changes. [rm]
 * takes one name or more, space-separated, and fails without clearing any
 * of them when another hypothesis or the goal still depends on one.
 *)

Ltac2 Notation "mv" h(ident) name(ident) :=
  Control.enter (fun () => Std.rename [(h, name)]).

Ltac2 Notation "rm" hypotheses(list1(ident)) :=
  Control.enter (fun () => Std.clear hypotheses).

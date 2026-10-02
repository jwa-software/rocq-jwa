(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* The plugin behind [Number Notation] and [String Notation]: a file declaring
 * either command requires this one, which loads the plugin and so makes the
 * command exist.
 *)
Declare ML Module "rocq-runtime.plugins.number_string_notation".

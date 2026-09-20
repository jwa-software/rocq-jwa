(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import All.

Definition jwa_all_delivers
  : forall (A : Prop) (T : Type) (o : Option T) .
      A /\ ~ A -> Option.map (fun (t : T) . t) o = o -> Verum
  := fun (A : Prop) (T : Type) (o : Option T)
         (_ : A /\ ~ A) (_ : Option.map (fun (t : T) . t) o = o) . I.

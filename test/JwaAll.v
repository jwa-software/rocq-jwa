(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

(* Guards [jwa.All], imported alone. It is the one entry point that reaches
   every layer at once, so one name from [Core] and one from [Data] is what
   it has to answer for. *)
From jwa Require Import All.

Definition jwa_all_delivers
  : forall (A : Prop) (T : Type) (o : Option T),
      A /\ ~ A -> Option.map (fun (t : T) => t) o = o -> True
  := fun (A : Prop) (T : Type) (o : Option T)
         (_ : A /\ ~ A) (_ : Option.map (fun (t : T) => t) o = o) =>
      I.

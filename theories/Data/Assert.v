(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Import Core.All.
From jwa Require Import Data.Bool.
From jwa Require Import Tactics.ModusPonens.

(* The bridge from a computed answer to a statement. [Assert true] is
 * [Verum] and [Assert false] is [Falsum] by reduction, so case analysis on
 * a [Bool] turns each law below into a concrete implication in both
 * directions.
 *
 * It stands in a file of its own rather than inside [Module Bool]: the
 * boolean operations are one subject and the crossing into [Prop] is
 * another, and a client that wants only the algebra should not be handed
 * the bridge.
 *)
(* [Bool -> Prop] *)
Definition Assert := fun (b : Bool) .
  match b with
  | true  => Verum
  | false => Falsum
  end.

(* The laws carry the name of what they are about, as a type's do; the
 * bridge itself is declared above them.
 *)
Module Assert. (* Assert *)

(* [&&], [||], [^^] and [!] are exported by [Data.Bool] into
 * [jwa_bool_scope], which every law below reads.
 *)
Local Open Scope jwa_bool_scope.

(* Assert.conjunction *)
Theorem conjunction
  : forall (b1 : Bool) (b2 : Bool) .
      Assert (b1 && b2) <-> Assert b1 /\ Assert b2.
Proof.
  intros b1 b2.
  destruct b1 as [|];
      destruct b2 as [|]; simpl in |- *;
          split; intro h.
  - split; exact I.
  - exact I.
  - contradiction h.
  - destruct h as [_ h].
    exact h.
  - contradiction h.
  - destruct h as [h _].
    exact h.
  - contradiction h.
  - destruct h as [h _].
    exact h.
Qed.

(* Assert.disjunction *)
Theorem disjunction
  : forall (b1 : Bool) (b2 : Bool) .
      Assert (b1 || b2) <-> Assert b1 \/ Assert b2.
Proof.
  intros b1 b2.
  destruct b1 as [|];
      destruct b2 as [|]; simpl in |- *;
          split; intro h.
  - exact (Disjunction.left I).
  - exact I.
  - exact (Disjunction.left I).
  - exact I.
  - exact (Disjunction.right I).
  - exact I.
  - contradiction h.
  - destruct h as [h1 | h2].
    + exact h1.
    + exact h2.
Qed.

(* Assert.sejunction *)
Theorem sejunction
  : forall (b1 : Bool) (b2 : Bool) .
      Assert (b1 ^^ b2) <-> Assert b1 _\/_ Assert b2.
Proof.
  intros b1 b2.
  destruct b1 as [|];
      destruct b2 as [|];
          simpl in |- *;
            split;
              intro h.
  - contradiction h.
  - destruct h as [t nt | nt t]; modus ponens nt t.
  - exact (Sejunction.left  I (fun (f : Falsum) . f)).
  - exact I.
  - exact (Sejunction.right (fun (f : Falsum) . f) I).
  - exact I.
  - contradiction h.
  - destruct h as [f _ | _ f]; exact f.
Qed.

(* Assert.negation *)
Theorem negation
  : forall (b : Bool) . Assert (! b) <-> ~ Assert b.
Proof.
  intros b.
  unfold Negation in |- *.
  destruct b as [|];
      simpl in |- *;
          split;
            intro h.
  - contradiction h.
  - modus ponens h I.
  - intro k.
    destruct k.
  - exact I.
Qed.

(* Assert.specification *)
Theorem specification : forall (b : Bool) . Assert b <-> b = true.
Proof.
  intros b.
  destruct b as [|]; simpl in |- *; split; intro h.
  - reflexivity.
  - exact I.
  - contradiction h.
  - discriminate h.
Qed.

End Assert. (* Assert *)

(* Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. *)

From jwa Require Export Dialect.Ltac.
From jwa Require Import Dialect.Local.
From Ltac2 Require Array Constr Control Env Ident Ind Int List Message Std.

(* match <H> with end                          destruct <H>
 * match <H> with | <b1> | ... | <bn> end      destruct <H> as [<b1> | ... | <bn>]
 * match <H> with end |- <E>                   destruct <H> eqn:<E>
 * match <H> with | <b1> | ... end |- <E>      destruct <H> as [...] eqn:<E>
 * match <H> with | ... end per <I>            induction <H> as [...] using <I>
 * match <H> with | ... end per <I> for <P>    induction <H> as [...] using <I> with (P := <P>)
 *
 * Case analysis on <H>, one goal per constructor of its type; the proof term
 * built is a [match] on <H>. The branch <bi> names the arguments of the i-th
 * constructor in order, each a name or [_], and may be empty; [with end]
 * leaves the names to Rocq. A branch may open with its constructor's name,
 * [| One | Successor n'], and then every branch does, in the order the type
 * declares them. [|- <E>] adds to each goal the equation <E> between <H> and
 * that goal's constructor. A branch takes one constructor apart and no more:
 * an argument to be taken apart in turn is named, then matched again.
 *
 * [per <I>], with <I> an eliminator such as [Nat.induction], makes it an
 * induction on the variable <H>. Each recursive argument is written
 * [<x> by <IH>], or [(<x> by <IH>)], naming the hypothesis that the goal
 * holds of <x>, or [<x> by _] to drop it; [by] goes on recursive arguments
 * only. [for <P>] states the motive: <P> applied to <H> must be the goal as
 * written. <I> must list each hypothesis right after its argument, as the
 * eliminators of this library do. [|- <E>] and [per] do not go together.
 *
 *   match n with
 *   | One
 *   | Successor (n' by IH)
 *   end per Nat.induction.
 *
 * <H> is a [constr], a term at level 8, so an application is parenthesised.
 * Declared at level 5 beside Ltac2's own [match <v> with <branches> end],
 * which it shadows: in a proof, and in any file importing this one, Ltac2's
 * [match] no longer parses.
 *)

(* The helpers come first: they use Ltac2's [match], which the notation below
 * takes over.
 *)

Ltac2 match_refuse (parts : message list) :=
  Control.zero
    (Tactic_failure
       (Some (List.fold_right Message.concat parts (Message.of_string "")))).

(* A branch item: a name or [_], with the name given to its induction
 * hypothesis if [by] follows ([Some None] for [by _]); or a bracketed pattern,
 * kept only to be refused.
 *)
Ltac2 Type match_item := [ Named (ident option, ident option option) | Nested ].

Ltac2 Custom Entry match_name.

Ltac2 Notation x(ident) : match_name(0) := Some x.

Ltac2 Notation "_" : match_name(0) := None.

Ltac2 Custom Entry match_item.

Ltac2 Notation x(match_name) h(opt(seq("by", match_name))) : match_item(0) := Named x h.

Ltac2 Notation "(" i(match_item) ")" : match_item(0) := i.

Ltac2 Notation "[" l(list0(match_item)) r(list0(seq("|", list0(match_item)))) "]"
  : match_item(0) := Nested.

Ltac2 name_message (x : ident option) : message :=
  match x with
  | Some x => Message.of_ident x
  | None => Message.of_string "_"
  end.

Ltac2 name_pattern (x : ident option) : Std.intro_pattern :=
  match x with
  | Some x => Std.IntroNaming (Std.IntroIdentifier x)
  | None => Std.IntroAction Std.IntroWildcard
  end.

Ltac2 refuse_nested () :=
  match_refuse
    [Message.of_string "match: a branch takes names and _ only; name the part and match it again"].

Ltac2 head_of (t : constr) : constr :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f _ => f
  | _ => t
  end.

Ltac2 constructor_names (h : constr) : ident list :=
  match Constr.Unsafe.kind (head_of (Std.eval_hnf (Constr.type h))) with
  | Constr.Unsafe.Ind ind _ =>
      let d := Ind.data ind in
      List.map
        (fun i => List.last (Env.path (Std.ConstructRef (Ind.get_constructor d i))))
        (List.seq 0 1 (Ind.nconstructors d))
  | _ => []
  end.

Ltac2 opens_with_constructor (names : ident list) (branch : match_item list) : bool :=
  match branch with
  | Named (Some x) None :: _ => List.exist (Ident.equal x) names
  | _ => false
  end.

(* Once one branch opens with a constructor's name, all of them must, in the
 * declared order; the names are then dropped and the branches read as
 * positional ones.
 *)
Ltac2 strip_constructors (names : ident list) (branches : match_item list list)
  : match_item list list :=
  if List.exist (opens_with_constructor names) branches then
    if Int.equal (List.length branches) (List.length names) then
      List.map
        (fun p =>
           match p with
           | (c, branch) =>
               match branch with
               | Named (Some x) None :: rest =>
                   if Ident.equal x c then rest
                   else
                     match_refuse
                       [Message.of_string "match: the branches follow the constructors in order, ";
                        Message.of_string "so this one opens with ";
                        Message.of_ident c; Message.of_string ", not "; Message.of_ident x]
               | _ =>
                   match_refuse
                     [Message.of_string "match: every branch opens with its constructor's name, ";
                      Message.of_string "or none does; this one needs "; Message.of_ident c]
               end
           end)
        (List.combine names branches)
    else
      match_refuse
        [Message.of_string "match: one branch per constructor, ";
         Message.of_int (List.length names);
         Message.of_string " of them, not ";
         Message.of_int (List.length branches)]
  else branches.

Ltac2 destruct_pattern (branch : match_item list) : Std.intro_pattern list :=
  List.map
    (fun item =>
       match item with
       | Named x None => name_pattern x
       | Named x (Some _) =>
           match_refuse
             [Message.of_string "match: "; name_message x;
              Message.of_string " by names an induction hypothesis; add per <eliminator> after end"]
       | Nested => refuse_nested ()
       end)
    branch.

Ltac2 destruct_run (h : constr) (branches : match_item list list) (e : ident option) :=
  let pattern :=
    match branches with
    | [] => None
    | _ => Some (Std.IntroOrPattern (List.map destruct_pattern branches))
    end in
  let equation :=
    match e with
    | Some e => Some (Std.IntroIdentifier e)
    | None => None
    end in
  Std.destruct false
    [{ Std.indcl_arg := Std.ElimOnConstr (fun () => (h, Std.NoBindings));
       Std.indcl_eqn := equation;
       Std.indcl_as := pattern;
       Std.indcl_in := None }]
    None.

Ltac2 rec ends_in_sort (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Prod _ c => ends_in_sort c
  | Constr.Unsafe.Sort _ => true
  | _ => false
  end.

Ltac2 is_family (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Prod _ c => ends_in_sort c
  | _ => false
  end.

Ltac2 rec take_premises (t : constr) (n : int) : constr list :=
  if Int.equal n 0 then []
  else
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.Prod b c => Constr.Binder.type b :: take_premises c (Int.sub n 1)
    | _ => []
    end.

(* The motive is the first premise of the eliminator whose type is a family
 * of sorts ([P : Nat -> Prop]); the next <n> premises are the branches.
 *)
Ltac2 rec motive_and_branches (t : constr) (n : int) : (ident option * constr list) option :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Prod b c =>
      if is_family (Constr.Binder.type b)
      then Some (Constr.Binder.name b, take_premises c n)
      else motive_and_branches c n
  | _ => None
  end.

Ltac2 is_hypothesis (t : constr) (motive : int) : bool :=
  match Constr.Unsafe.kind (head_of t) with
  | Constr.Unsafe.Rel k => Int.equal k motive
  | _ => false
  end.

Ltac2 about_previous (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App _ args =>
      match Constr.Unsafe.kind (Array.get args (Int.sub (Array.length args) 1)) with
      | Constr.Unsafe.Rel k => Int.equal k 1
      | _ => false
      end
  | _ => false
  end.

(* For each argument of a branch premise, whether an induction hypothesis
 * follows it; [None] when a hypothesis is not about the argument just before
 * it. [motive] is the de Bruijn index of the motive at [t]; [acc] is reversed.
 *)
Ltac2 rec premise_arguments (t : constr) (motive : int) (acc : bool list) : bool list option :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Prod b c =>
      let ty := Constr.Binder.type b in
      if is_hypothesis ty motive then
        match acc with
        | false :: rest =>
            if about_previous ty
            then premise_arguments c (Int.add motive 1) (true :: rest)
            else None
        | _ => None
        end
      else premise_arguments c (Int.add motive 1) (false :: acc)
  | _ => Some (List.rev acc)
  end.

Ltac2 induction_item (item : match_item) (recursive : bool) : Std.intro_pattern list :=
  match item with
  | Named x None =>
      if recursive then
        match_refuse
          [Message.of_string "match: "; name_message x;
           Message.of_string " is recursive; name its induction hypothesis, ";
           name_message x; Message.of_string " by <IH>, or drop it, ";
           name_message x; Message.of_string " by _"]
      else [name_pattern x]
  | Named x (Some ih) =>
      if recursive then [name_pattern x; name_pattern ih]
      else
        match_refuse
          [Message.of_string "match: "; name_message x;
           Message.of_string " is not recursive, so it has no induction hypothesis to name"]
  | Nested => refuse_nested ()
  end.

Ltac2 induction_run
  (x : ident) (h : constr) (names : ident list) (branches : match_item list list)
  (elim : unit -> constr) (motive : (unit -> constr) option) :=
  let el := Local.checked "match" elim in
  let n := List.length names in
  let (motive_name, premises) :=
    match motive_and_branches (Constr.type el) n with
    | Some r => r
    | None =>
        match_refuse
          [Message.of_string "match: "; Message.of_constr el;
           Message.of_string " is no eliminator: none of its premises is a motive"]
    end in
  let shapes :=
    List.mapi
      (fun j p =>
         match premise_arguments p (Int.add j 1) [] with
         | Some s => s
         | None =>
             match_refuse
               [Message.of_string "match: "; Message.of_constr el;
                Message.of_string " states an induction hypothesis away from its argument"]
         end)
      premises in
  let pattern :=
    match branches with
    | [] =>
        if List.exist (List.exist (fun r => r)) shapes then
          match_refuse
            [Message.of_string "match: name the branches, and each induction hypothesis with by"]
        else None
    | _ =>
        if Int.equal (List.length branches) n then
          Some
            (Std.IntroOrPattern
               (List.map
                  (fun p =>
                     match p with
                     | ((branch, shape), c) =>
                         if Int.equal (List.length branch) (List.length shape) then
                           List.flat_map
                             (fun q => match q with (item, r) => induction_item item r end)
                             (List.combine branch shape)
                         else
                           match_refuse
                             [Message.of_string "match: the branch of "; Message.of_ident c;
                              Message.of_string " names ";
                              Message.of_int (List.length branch);
                              Message.of_string " where it takes ";
                              Message.of_int (List.length shape)]
                     end)
                  (List.combine (List.combine branches shapes) names)))
        else
          match_refuse
            [Message.of_string "match: one branch per constructor, ";
             Message.of_int n;
             Message.of_string " of them, not ";
             Message.of_int (List.length branches)]
    end in
  let bindings :=
    match motive with
    | None => Std.NoBindings
    | Some p =>
        let p := Local.checked "match" p in
        let applied :=
          match Constr.Unsafe.kind p with
          | Constr.Unsafe.Lambda _ body => Constr.Unsafe.substnl [h] 0 body
          | _ => Constr.Unsafe.make (Constr.Unsafe.App p [| h |])
          end in
        if Constr.equal applied (Control.goal ()) then
          match motive_name with
          | Some m => Std.ExplicitBindings [(Std.NamedHyp m, p)]
          | None =>
              match_refuse
                [Message.of_string "match: the motive of "; Message.of_constr el;
                 Message.of_string " has no name to bind"]
          end
        else
          match_refuse
            [Message.of_string "match: the motive applied to "; Message.of_ident x;
             Message.of_string " is "; Message.of_constr applied;
             Message.of_string ", not the goal "; Message.of_constr (Control.goal ())]
    end in
  Std.induction false
    [{ Std.indcl_arg := Std.ElimOnIdent x;
       Std.indcl_eqn := None;
       Std.indcl_as := pattern;
       Std.indcl_in := None }]
    (Some (el, bindings)).

Ltac2 match_run
  (h : unit -> constr) (branches : match_item list list)
  (elim : ((unit -> constr) * (unit -> constr) option) option) (e : ident option) :=
  Control.enter (fun () =>
    let h := Local.checked "match" h in
    let names := constructor_names h in
    let branches := strip_constructors names branches in
    match elim with
    | None => destruct_run h branches e
    | Some (i, motive) =>
        match e with
        | Some e =>
            match_refuse
              [Message.of_string "match: an induction takes no equation; drop |- ";
               Message.of_ident e]
        | None => ()
        end;
        match Constr.Unsafe.kind h with
        | Constr.Unsafe.Var x => induction_run x h names branches i motive
        | _ =>
            match_refuse
              [Message.of_string "match: per takes apart a variable, and ";
               Message.of_constr h;
               Message.of_string " is not one; state the law for a variable, then apply it"]
        end
    end).

Ltac2 Notation "match" h(thunk(constr)) "with"
  branches(list0(seq("|", list0(match_item)))) "end"
  i(opt(seq("per", thunk(constr), opt(seq("for", thunk(constr))))))
  e(opt(seq("|-", ident))) : 5 :=
  match_run h branches i e.

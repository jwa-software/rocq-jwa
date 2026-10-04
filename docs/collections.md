<!-- Copyright (c) 2026 Junzhe Wang, licensed under the MIT License. -->

# Collections

`jwa.Data` holds the containers, and the interfaces they share, under `Data/Collection/`:

| Type | What it is | Written as |
|:---|:---|:---|
| `List A` | Any number of elements of type `A`, in order | `(1 :: 2 :: 3 :: [])%list`, `[]%list` (empty) |
| `NonEmptyList A` | One element or more, in order | `(1 :: 2 :: [3])%non_empty_list`, `[1]%non_empty_list` |
| `BinaryTree A` | A leaf, which holds nothing, or a node: one element between two subtrees | `BinaryTree.Node BinaryTree.Leaf 1 BinaryTree.Leaf` |

`From jwa Require Import Data.Collection.All` brings the three types, the interfaces, and what their operations and laws name: the types `Nat0`, `Nat`, `Bool`, `Option` and `Comparison`, and the class `Comparable`. The examples on this page take their numbers in `Nat0` and are written with `jwa_list_scope` and `jwa_nat0_scope` open.

---

## List

`List` has the ctors `List.Nil` and `List.Cons`, written `[]` and `a :: l`. Its notations live in `jwa_list_scope`, under the key `%list`.

- **Building:** `l1 ++ l2` is `List.concat`, and `List.append l a` puts `a` after the last element: `(1 :: 2 :: []) ++ (3 :: [])` and `List.append (1 :: 2 :: []) 3` are both `1 :: 2 :: 3 :: []`. `List.replicate 3 7` is `7 :: 7 :: 7 :: []`.
- **Length and order:** `List.length l`, written `(|| l ||)`, is a `Nat0`, and `List.reverse (1 :: 2 :: 3 :: [])` is `3 :: 2 :: 1 :: []`.
- **Every element at once:** `List.map Nat0.inc (1 :: 2 :: [])` is `2 :: 3 :: []`, `List.filter (Nat0.le 2) (1 :: 2 :: 3 :: [])` keeps `2 :: 3 :: []`, `List.count` counts what `List.filter` keeps, and `List.fold_right Nat0.add 0 (1 :: 2 :: 3 :: [])` is `6`. `List.partition` gives what a test accepts and what it rejects, `List.zip` pairs two lists as far as the shorter one goes, and `List.unzip` splits a list of pairs.
- **The ends return an `Option`**, `None` on the empty list: `List.head`, `List.last`, `List.tail`, `List.initial` (all but the last element) and `List.pop` (the head with the tail). `List.head (5 :: 6 :: 7 :: [])` is `Some 5`, and `List.initial` of the same list is `Some (5 :: 6 :: [])`.
- **Indexing counts from 0.** `List.nth l i` is `Some` of the element at position `i` exactly when `i < (|| l ||)` (`List.indexing.specification`), and `None` from there on: `List.nth (5 :: 6 :: 7 :: []) 1` is `Some 6`.
- **A list splits at a position.** `List.take n l` is the first `n` elements and `List.drop n l` the rest, all of `l` and nothing where `l` is shorter: `List.take 2 (5 :: 6 :: 7 :: [])` is `5 :: 6 :: []`, and `take n l ++ drop n l = l` (`List.splitting.decomposition`).
- **Membership and the quantifiers are propositions.** `List.Contains a l` is written `l contains_member a` or `a belongs_to l`, and its negation `l does_not_contain_member a` or `a does_not_belong_to l`. `List.All P l` and `List.Any P l` state that every element, or some element, satisfies `P`; `List.quantification.all.specification` and `List.quantification.any.specification` state both through membership.
- **Numbers:** `List.sum` and `List.product` fold a `List Nat0`. `List.range 2 5` is `2 :: 3 :: 4 :: []` and `List.range_inclusive 2 5` reaches `5` as well; a range whose `stop` is not past its `start` is empty. `List.range.membership.specification` states `range start stop contains_member i <-> start <= i /\ i < stop`.
- **An order is an argument.** `List.insert`, `List.insertion_sort`, `List.maximum_of` and `List.minimum_of` take a test `le : A -> A -> Bool` that answers whether its first argument may come first, and `List.Sorted le l` states that every element may precede all that follow it. `List.insertion_sort Nat0.le (3 :: 1 :: 2 :: [])` is `1 :: 2 :: 3 :: []`, and `List.maximum_of Nat0.le` of the same list is `Some 3`.
- **The laws of an order take its properties as premises.** For a `le` that is total and transitive, `List.sorting.sortedness` states `Sorted le (insertion_sort le l)`, and `List.maximum.bound` that every element may precede the maximum. `List.sorting.preservation.membership` and `List.sorting.preservation.length` hold of any `le`.
- **Lists are ordered lexicographically.** `List.compare cmp l m` goes by `cmp` on the elements, a proper prefix first: with `Nat0.compare`, `1 :: 2 :: []` comes before `1 :: 3 :: []`, and `1 :: []` before `1 :: 2 :: []`. `List.comparison.specification`, `List.comparison.antisymmetry` and `List.comparison.transitivity` hold for any `cmp` that is `Comparable`.
- **The laws are grouped by operation.** `List.concatenation.associativity` and `List.concatenation.identity` make `++` and `[]` a monoid, the instance `List_concat_monoid`; `List.length.additivity.over.concatenation` states `(|| l1 ++ l2 ||) = (|| l1 ||) + (|| l2 ||)`; `List.reversal.involution` states `reverse (reverse l) = l`; and `mapping`, `filtering`, `membership`, `quantification` and `reversal` each state how their operation meets `++`. A `catamorphism` law states its operation as a `List.fold_right`, as `List.mapping.catamorphism` does for `List.map`.
- **Induction:** `List.induction` is the eliminator, and a proof names its hypothesis in the branch: `match l with | Nil | Cons a (l' by IH) end per List.induction`.

---

## NonEmptyList

`NonEmptyList` has the ctors `NonEmptyList.One` and `NonEmptyList.Cons`, written `[a]` and `a :: x`: a value ends with an element where a list ends with `[]`, so none is empty. Its notations live in `jwa_non_empty_list_scope`, under the key `%non_empty_list`.

- **The ends are total.** `NonEmptyList.head` and `NonEmptyList.last` return the element itself, with no `Option`: on `5 :: 6 :: [7]` they are `5` and `7`.
- **The length is a `Nat`**, the number type with no zero: `NonEmptyList.length (5 :: 6 :: [7])` is `3%n`.
- **Operations:** `x ++ y` is `NonEmptyList.concat`, beside `NonEmptyList.reverse`, `NonEmptyList.map` and the membership `NonEmptyList.Contains`, with the notations `List` has. `(1 :: [2]) ++ [3]` is `1 :: 2 :: [3]`.
- **The extrema are total too.** `NonEmptyList.maximum_of` and `NonEmptyList.minimum_of` take a test `le` as `List`'s do and return the element outright: `NonEmptyList.maximum_of Nat0.le (3 :: 1 :: [2])` is `3`.
- **Laws:** `NonEmptyList.concatenation.associativity`, `NonEmptyList.length.additivity.over.concatenation`, `NonEmptyList.membership.distributivity.over.concatenation`, `NonEmptyList.reversal.involution`, `NonEmptyList.mapping.identity` and `NonEmptyList.mapping.composition`; and, for a `le` that is total and transitive, `NonEmptyList.maximum.bound` and `NonEmptyList.minimum.bound`.
- **`NonEmptyList.to_list` gives the same elements as a `List`**, and the `conversion` laws carry each operation to `List`'s: `NonEmptyList.conversion.distributivity.over.concatenation`, `NonEmptyList.conversion.length`, `NonEmptyList.conversion.membership`, and `NonEmptyList.conversion.maximum`, which states `List.maximum_of le (to_list x) = Some (maximum_of le x)`, with `NonEmptyList.conversion.minimum` beside it.
- **Induction:** `match x with | One a | Cons a (x' by IH) end per NonEmptyList.induction`.

---

## BinaryTree

`BinaryTree` has the ctors `BinaryTree.Leaf`, the tree that holds nothing, and `BinaryTree.Node l a r`, the element `a` between the subtrees `l` and `r`. It has no notation. Below, `t` is the tree with `2` at the root, `1` on its left and `3` on its right, `Node (Node Leaf 1 Leaf) 2 (Node Leaf 3 Leaf)` with each ctor under its prefix.

- **`size` counts the elements and `height` the levels.** `BinaryTree.size t` is `3` and `BinaryTree.height t` is `2`; a leaf has `0` for both. `BinaryTree.height.bound` states `height t <= size t`.
- **`to_list` reads the tree in order:** the left subtree, the node's element, the right subtree. `BinaryTree.to_list t` is `1 :: 2 :: 3 :: []`.
- **`map` keeps the shape.** `BinaryTree.map Nat0.inc t` holds `2`, `3` and `4` where `t` holds `1`, `2` and `3`. `BinaryTree.mapping.identity` and `BinaryTree.mapping.composition` are its two laws, and `BinaryTree.mapping.preservation` states that the size and the height stay, and that a member `a` of `t` gives the member `f a` of `map f t`.
- **`mirror` exchanges the two subtrees of every node.** `BinaryTree.mirror t` lists as `3 :: 2 :: 1 :: []`. `BinaryTree.mirroring.involution` states `mirror (mirror t) = t`, and `BinaryTree.mirroring.preservation` that the size, the height and the members stay.
- **Membership and the quantifiers are propositions:** `BinaryTree.Contains a t`, `BinaryTree.All P t` and `BinaryTree.Any P t`, each read in the order of `to_list`.
- **The `conversion` laws carry each operation to `List`'s.** `BinaryTree.conversion.size` states `(|| to_list t ||) = size t`; `BinaryTree.conversion.mapping` and `BinaryTree.conversion.mirroring` state that `to_list` turns `map` into `List.map` and `mirror` into `List.reverse`; `BinaryTree.conversion.membership`, `BinaryTree.conversion.all` and `BinaryTree.conversion.any` state `Contains`, `All` and `Any` through `List`'s. Along them a statement about a tree moves to the list of its elements, and a `List` law comes back.
- **Two trees may hold the same elements and differ.** `Node Leaf 1 (Node Leaf 2 Leaf)` and `Node (Node Leaf 1 Leaf) 2 Leaf` both list as `1 :: 2 :: []` and are two values, so a statement about what a tree holds goes through `to_list` or `Contains`, not through `=`.
- **Induction has one hypothesis per subtree:** `match t with | Leaf | Node (l by IHl) a (r by IHr) end per BinaryTree.induction`.

---

## Interfaces

Each interface is a class over a container `F : Type -> Type`, and each type on this page has an instance of all three. `Functor` has a section of its own after this one.

| Class | What it holds | `List` | `NonEmptyList` | `BinaryTree` |
|:---|:---|:---|:---|:---|
| `Functor` | `Functor.map`, with the laws `Functor.identity` and `Functor.composition` | `List.map` | `NonEmptyList.map` | `BinaryTree.map` |
| `Sized` | `Sized.cardinality`, a `Nat0` | `List.length` | `NonEmptyList.length`, as a `Nat0` | `BinaryTree.size` |
| `Membership` | `Membership.Contains`, a proposition | `List.Contains` | `NonEmptyList.Contains` | `BinaryTree.Contains` |

- **One name serves every container.** `Sized.cardinality (1 :: 2 :: 3 :: [])` and `Sized.cardinality t` are both `3`, and `Functor.map Nat0.inc` maps a list or a tree.
- **`Sized` derives emptiness.** `Sized.is_empty` and `Sized.is_not_empty` answer a `Bool`, and `Sized.emptiness.reflection` states `Assert (is_empty x) <-> cardinality x = Nat0.Zero`.
- **`Sized` and `Membership` state no law.** A count alone, or a relation alone, constrains nothing; a law that relates one of them to another operation is the container's own, as `List.length.additivity.over.concatenation` is.

---

## Functor

- **The problem.** One change is applied to every element of a container, whatever the container: add one to each number of a list, of a tree, of an `Option`. Each type has a `map` of its own. A function or a proof written once for all of them needs one name for it, and the laws that make "apply to every element" mean the same everywhere.
- **The class.** `Functor F`, for a container `F : Type -> Type`, has the operation `Functor.map : (A -> B) -> F A -> F B` and two laws. `Functor.identity` is `map (fun a . a) x = x`: a `map` that changes no element changes nothing. `Functor.composition` is `map g (map f x) = map (fun a . g (f a)) x`: two passes are one pass that makes both changes.
- **Instances.** `List_functor`, `NonEmptyList_functor` and `BinaryTree_functor`. `Option_functor`, under which `Functor.map Nat0.inc (Some 1)` is `Some 2` and `None` stays `None`. `Product_functor` and `Coproduct_functor`, which map the second component of a pair and the right side of a coproduct.
- **In a proof.** `Functor.map Nat0.inc` maps a list, a tree or an `Option`, the instance found from its argument. `Functor.composition A B C f g x` is the second law for whichever container `x` is in, so a statement proved from it holds of all six.
- **What it does not say.** How many elements there are, or in which order. That `map` keeps the length of a list, or the size of a tree, is each container's own law: `List.mapping.preservation.length`, `BinaryTree.mapping.preservation.size`.

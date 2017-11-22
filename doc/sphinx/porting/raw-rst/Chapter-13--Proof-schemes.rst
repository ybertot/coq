

+ `Home`_
+ `About Coq`_
+ `Get Coq`_
+ `Documentation`_
+ `Community`_

` `_ `The Coq Proof Assistant`_


Chapter 13 Proof schemes
========================


+ `13.1 Generation of induction principles with Scheme`_
+ `13.2 Generation of induction principles with Functional Scheme`_
+ `13.3 Generation of inversion principles with Derive Inversion`_




13.1 Generation of induction principles with Scheme
---------------------------------------------------



The Scheme command is a high-level tool for generating automatically
(possibly mutual) induction principles for given types and sorts. Its
syntax follows the schema:
Scheme ident 1 := Induction for ident’ 1 Sort sort 1
with
…
with ident m := Induction for ident’ m Sortsort m
where ident’ 1 … ident’ m are different inductive type identifiers
belonging to the same package of mutual inductive definitions. This
command generates ident 1 … ident m to be mutually recursive
definitions. Each term ident i proves a general principle of mutual
induction for objects in type term i .


Variants:


#. Scheme ident 1 := Minimality for ident’ 1 Sort sort 1 with … with
   ident m := Minimality for ident’ m Sortsort m Same as before but
   defines a non-dependent elimination principle more natural in case of
   inductively defined relations.
#. Scheme Equality for ident 1 Tries to generate a Boolean equality
   and a proof of the decidability of the usual equality. If ident i
   involves some other inductive types, their equality has to be defined
   first.
#. Scheme Induction for ident 1 Sort sort 1 with … with Induction for
   ident m Sortsort m If you do not provide the name of the schemes, they
   will be automatically computed from the sorts involved (works also
   with Minimality).





Example 1: Induction scheme for tree and forest

The definition of principle of mutual induction for tree andforest
over the sort Set is defined by the command:
Coq < Inductive tree : Set :=
node : A -> forest -> tree
with forest : Set :=
| leaf : B -> forest
| cons : tree -> forest -> forest.

Coq < Scheme tree_forest_rec := Induction for tree Sort Set
with forest_tree_rec := Induction for forest Sort Set.

You may now look at the type of tree_forest_rec:
Coq < Check tree_forest_rec.
tree_forest_rec
: forall (P : tree -> Set) (P0 : forest -> Set),
(forall (a : A) (f : forest), P0 f -> P (node a f)) ->
(forall b : B, P0 (leaf b)) ->
(forall t : tree, P t -> forall f1 : forest, P0 f1 -> P0 (cons t f1))
->
forall t : tree, P t

This principle involves two different predicates for trees andforests;
it also has three premises each one corresponding to a constructor of
one of the inductive definitions.

The principle forest_tree_rec shares exactly the same premises, only
the conclusion now refers to the property of forests.
Coq < Check forest_tree_rec.
forest_tree_rec
: forall (P : tree -> Set) (P0 : forest -> Set),
(forall (a : A) (f : forest), P0 f -> P (node a f)) ->
(forall b : B, P0 (leaf b)) ->
(forall t : tree, P t -> forall f1 : forest, P0 f1 -> P0 (cons t f1))
->
forall f2 : forest, P0 f2


Example 2: Predicates odd and even on naturals

Let odd and even be inductively defined as:
Coq < Inductive odd : nat -> Prop :=
oddS : forall n:nat, even n -> odd (S n)
with even : nat -> Prop :=
| evenO : even 0
| evenS : forall n:nat, odd n -> even (S n).

The following command generates a powerful elimination principle:
Coq < Scheme odd_even := Minimality for odd Sort Prop
with even_odd := Minimality for even Sort Prop.
even_odd is defined
odd_even is defined
odd_even, even_odd are recursively defined

The type of odd_even for instance will be:
Coq < Check odd_even.
odd_even
: forall P P0 : nat -> Prop,
(forall n : nat, even n -> P0 n -> P (S n)) ->
P0 0 ->
(forall n : nat, odd n -> P n -> P0 (S n)) ->
forall n : nat, odd n -> P n

The type of even_odd shares the same premises but the conclusion is
(n:nat)(even n)->(Q n).


13.1.1 Automatic declaration of schemes
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

It is possible to deactivate the automatic declaration of the
induction principles when defining a new inductive type with theUnset
Elimination Schemes command. It may be reactivated at any time with
Set Elimination Schemes.

The types declared with the keywords Variant (see `1.3.3`_) and Record
(see `2.1`_) do not have an automatic declaration of the induction
principles. It can be activated with the command Set Nonrecursive
Elimination Schemes. It can be deactivated again with Unset
Nonrecursive Elimination Schemes.

In addition, the Case Analysis Schemes flag governs the generation of
case analysis lemmas for inductive types, i.e. corresponding to the
pattern-matching term alone and without fixpoint.
You can also activate the automatic declaration of those Boolean
equalities (see the second variant of Scheme) with respectively the
commands Set Boolean Equality Schemes andSet Decidable Equality
Schemes. However you have to be careful with this option sinceCoq may
now reject well-defined inductive types because it cannot compute a
Boolean equality for them.


13.1.2 Combined Scheme
~~~~~~~~~~~~~~~~~~~~~~



The Combined Scheme command is a tool for combining induction
principles generated by the Scheme command. Its syntax follows the
schema :
Combined Scheme ident 0 from ident 1 , .., ident n
whereident 1 …ident n are different inductive principles that must
belong to the same package of mutual inductive principle definitions.
This command generates ident 0 to be the conjunction of the
principles: it is built from the common premises of the principles and
concluded by the conjunction of their conclusions.


Example: We can define the induction principles for trees and forests
using:
Coq < Scheme tree_forest_ind := Induction for tree Sort Prop
with forest_tree_ind := Induction for forest Sort Prop.
forest_tree_ind is defined
tree_forest_ind is defined
tree_forest_ind, forest_tree_ind are recursively defined

Then we can build the combined induction principle which gives the
conjunction of the conclusions of each individual principle:
Coq < Combined Scheme tree_forest_mutind from tree_forest_ind,
forest_tree_ind.
tree_forest_mutind is defined
tree_forest_mutind is recursively defined

The type of tree_forest_mutrec will be:
Coq < Check tree_forest_mutind.
tree_forest_mutind
: forall (P : tree -> Prop) (P0 : forest -> Prop),
(forall (a : A) (f : forest), P0 f -> P (node a f)) ->
(forall b : B, P0 (leaf b)) ->
(forall t : tree, P t -> forall f1 : forest, P0 f1 -> P0 (cons t f1))
->
(forall t : tree, P t) /\ (forall f2 : forest, P0 f2)



13.2 Generation of induction principles with Functional Scheme
--------------------------------------------------------------



The Functional Scheme command is a high-level experimental tool for
generating automatically induction principles corresponding to
(possibly mutually recursive) functions. First, it must be made
available via Require Import FunInd. Its syntax then follows the
schema:
Functional Scheme ident 1 := Induction for ident’ 1 Sort sort 1
with
…
with ident m := Induction for ident’ m Sortsort m
where ident’ 1 … ident’ m are different mutually defined function
names (they must be in the same order as when they were defined). This
command generates the induction principlesident 1 …ident m , following
the recursive structure and case analyses of the functions ident’ 1 …
ident’ m .


Remark: There is a difference between obtaining an induction scheme by
usingFunctional Scheme on a function defined by Function or not.
Indeed Function generally produces smaller principles, closer to the
definition written by the user.


Example 1: Induction scheme for div2

We define the function div2 as follows:
Coq < Require Import Arith.

Coq < Fixpoint div2 (n:nat) : nat :=
match n with
| O => 0
| S O => 0
| S (S n') => S (div2 n')
end.

The definition of a principle of induction corresponding to the
recursive structure of div2 is defined by the command:
Coq < Functional Scheme div2_ind := Induction for div2 Sort Prop.
div2_equation is defined
div2_ind is defined

You may now look at the type of div2_ind:
Coq < Check div2_ind.
div2_ind
: forall P : nat -> nat -> Prop,
(forall n : nat, n = 0 -> P 0 0) ->
(forall n n0 : nat, n = S n0 -> n0 = 0 -> P 1 0) ->
(forall n n0 : nat,
n = S n0 ->
forall n' : nat,
n0 = S n' -> P n' (div2 n') -> P (S (S n')) (S (div2 n'))) ->
forall n : nat, P n (div2 n)

We can now prove the following lemma using this principle:
Coq < Lemma div2_le' : forall n:nat, div2 n <= n.

Coq < intro n.

Coq < pattern n , (div2 n).
Coq < apply div2_ind; intros.
3 subgoals

n, n0 : nat
e : n0 = 0
============================
0 <= 0
subgoal 2 is:
0 <= 1
subgoal 3 is:
S (div2 n') <= S (S n')
Coq < auto with arith.

Coq < auto with arith.

Coq < simpl; auto with arith.

Coq < Qed.

We can use directly the functional induction (`8.5.5`_) tactic instead
of the pattern/apply trick:
Coq < Reset div2_le'.

Coq < Lemma div2_le : forall n:nat, div2 n <= n.

Coq < intro n.
Coq < functional induction (div2 n).
3 subgoals

============================
0 <= 0
subgoal 2 is:
0 <= 1
subgoal 3 is:
S (div2 n') <= S (S n')
Coq < auto with arith.

Coq < auto with arith.

Coq < auto with arith.

Coq < Qed.


Remark: There is a difference between obtaining an induction scheme
for a function by using Function (see Section `2.3`_) and by using
Functional Scheme after a normal definition usingFixpoint or
Definition. See `2.3`_ for details.


Example 2: Induction scheme for tree_size

We define trees by the following mutual inductive type:
Coq < Variable A : Set.

Coq < Inductive tree : Set :=
node : A -> forest -> tree
with forest : Set :=
| empty : forest
| cons : tree -> forest -> forest.

We define the function tree_size that computes the size of a tree or a
forest. Note that we use Function which generally produces better
principles.
Coq < Require Import FunInd.

Coq < Function tree_size (t:tree) : nat :=
match t with
| node A f => S (forest_size f)
end
with forest_size (f:forest) : nat :=
match f with
| empty => 0
| cons t f' => (tree_size t + forest_size f')
end.


Remark: Function generates itself non mutual induction principles
tree_size_ind and forest_size_ind:
Coq < Check tree_size_ind.
tree_size_ind
: forall P : tree -> nat -> Prop,
(forall (t : tree) (A : A) (f : forest),
t = node A f -> P (node A f) (S (forest_size f))) ->
forall t : tree, P t (tree_size t)

The definition of mutual induction principles following the recursive
structure of tree_size and forest_size is defined by the command:
Coq < Functional Scheme tree_size_ind2 := Induction for tree_size Sort
Prop
with forest_size_ind2 := Induction for forest_size Sort Prop.

You may now look at the type of tree_size_ind2:
Coq < Check tree_size_ind2.
tree_size_ind2
: forall (P : tree -> nat -> Prop) (P0 : forest -> nat -> Prop),
(forall (t : tree) (A : A) (f : forest),
t = node A f ->
P0 f (forest_size f) -> P (node A f) (S (forest_size f))) ->
(forall f0 : forest, f0 = empty -> P0 empty 0) ->
(forall (f1 : forest) (t : tree) (f' : forest),
f1 = cons t f' ->
P t (tree_size t) ->
P0 f' (forest_size f') ->
P0 (cons t f') (tree_size t + forest_size f')) ->
forall t : tree, P t (tree_size t)



13.3 Generation of inversion principles with Derive Inversion
-------------------------------------------------------------



The syntax of Derive Inversion follows the schema:
Derive Inversion ident with forall(x : T), I t Sort sort
This command generates an inversion principle for theinversion … using
tactic. Let I be an inductive predicate and x the variables occurring
in t. This command generates and stocks the inversion lemma for the
sort sort corresponding to the instance ∀ (x:T), I t with the name
ident in the global environment. When applied, it is equivalent to
having inverted the instance with the tactic inversion.


Variants:


#. Derive Inversion_clear ident with forall(x:T), I t Sort sort When
   applied, it is equivalent to having inverted the instance with the
   tactic inversion replaced by the tactic inversion_clear.
#. Derive Dependent Inversion ident with forall(x:T), I t Sort sort
   When applied, it is equivalent to having inverted the instance with
   the tactic dependent inversion.
#. Derive Dependent Inversion_clear ident with forall(x:T), I t Sort
   sort When applied, it is equivalent to having inverted the instance
   with the tactic dependent inversion_clear.



Example:

Let us consider the relation Le over natural numbers and the following
variable:
Coq < Inductive Le : nat -> nat -> Set :=
| LeO : forall n:nat, Le 0 n
| LeS : forall n m:nat, Le n m -> Le (S n) (S m).

Coq < Variable P : nat -> nat -> Prop.

To generate the inversion lemma for the instance(Le (S n) m) and the
sort Prop, we do:
Coq < Derive Inversion_clear leminv with (forall n m:nat, Le (S n) m)
Sort Prop.
Coq < Check leminv.
leminv
: forall (n m : nat) (P : nat -> nat -> Prop),
(forall m0 : nat, Le n m0 -> P n (S m0)) -> Le (S n) m -> P n m

Then we can use the proven inversion lemma:
Coq < Show.
1 subgoal

n, m : nat
H : Le (S n) m
============================
P n m
Coq < inversion H using leminv.
1 subgoal

n, m : nat
H : Le (S n) m
============================
forall m0 : nat, Le n m0 -> P n (S m0)



Navigation
----------


+ `Cover`_
+ `Table of contents`_
+ Index

    + `General`_
    + `Commands`_
    + `Options`_
    + `Tactics`_
    + `Errors`_




+ `webmaster`_
+ `xhtml valid`_
+ `CSS valid`_


.. _Scheme: :///home/steck/schemes.html#sec652
.. _Get Coq: :///download
.. _Functional Scheme: :///home/steck/schemes.html#sec655
.. _Derive Inversion: :///home/steck/schemes.html#sec656
.. _About Coq: :///about-coq
.. _CSS valid: http://jigsaw.w3.org/css-validator/
.. _Cover: :///home/steck/index.html
.. _Errors: :///home/steck/error-index.html
.. _Table of contents: :///home/steck/toc.html
.. _Community: :///community
.. _8.5.5: :///home/steck/tactics.html#FunInduction
.. _Commands: :///home/steck/command-index.html
.. _2.3: :///home/steck/gallina-ext.html#Function
.. _2.1: :///home/steck/gallina-ext.html#Record
.. _xhtml valid: http://validator.w3.org/
.. _Tactics: :///home/steck/tactic-index.html
.. _General: :///home/steck/general-index.html
.. _Options: :///home/steck/option-index.html
.. _The Coq Proof Assistant: :///
.. _Documentation: :///documentation
.. _1.3.3: :///home/steck/gallina.html#Variant
.. _webmaster: mailto:coq-www_@_inria.fr



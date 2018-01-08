

+ `Home`_
+ `About Coq`_
+ `Get Coq`_
+ `Documentation`_
+ `Community`_

` `_ `The Coq Proof Assistant`_


Chapter 3 The Coq library
=========================


+ `3.1 The basic library`_
+ `3.2 The standard library`_
+ `3.3 Users’ contributions`_


The Coq library is structured into two parts:

:The initial library:: it contains elementary logical notions and
  data-types. It constitutes the basic state of the system directly
  available when runningCoq;
:The standard library:: general-purpose libraries containing various
  developments of Coq axiomatizations about sets, lists, sorting,
  arithmetic, etc. This library comes with the system and its modules
  are directly accessible through the `Require` command (see Section
  `6.5.1`_);


In addition, user-provided libraries or developments are provided
byCoq users’ community. These libraries and developments are available
for download at `http://coq.inria.fr`_ (see Section 3.3).

The chapter briefly reviews the Coq libraries whose contents can also
be browsed at `http://coq.inria.fr/stdlib`_.


3.1 The basic library
---------------------

This section lists the basic notions and results which are directly
available in the standard Coq system 1 .


3.1.1 Notations
~~~~~~~~~~~~~~~

This module defines the parsing and pretty-printing of many symbols
(infixes, prefixes, etc.). However, it does not assign a meaning to
these notations. The purpose of this is to define and fix once for all
the precedence and associativity of very common notations. The main
notations fixed in the initial state are listed on Figure 3.1.



Notation Precedence Associativity `_ <-> _` 95 no `_ \/ _` 85 right `_
/\ _` 80 right `~ _` 75 right `_ = _` 70 no `_ = _ = _` 70 no `_ = _
:> _` 70 no `_ <> _` 70 no `_ <> _ :> _` 70 no `_ < _` 70 no `_ > _`
70 no `_ <= _` 70 no `_ >= _` 70 no `_ < _ < _` 70 no `_ < _ <= _` 70
no `_ <= _ < _` 70 no `_ <= _ <= _` 70 no `_ + _` 50 left `_ || _` 50
left `_ - _` 50 left `_ * _` 40 left `_ && _` 40 left `_ / _` 40 left
`- _` 35 right `/ _` 35 right `_ ^ _` 30 right Figure 3.1: Notations
in the initial state





3.1.2 Logic
~~~~~~~~~~~



form ::= True (True) | False (False) | ~ form (not) | form /\ form
(and) | form \/ form (or) | form -> form ( *primitive implication* *)*
| form <-> form (iff) | forall ident : type ,form ( *primitive for
all* *)* | exists ident [: specif] , form (ex) | exists2 ident [:
specif] , form & form (ex2) | term = term (eq) | term = term :> specif
(eq) Figure 3.2: Syntax of formulas



The basic library of Coq comes with the definitions of standard
(intuitionistic) logical connectives (they are defined as inductive
constructions). They are equipped with an appealing syntax enriching
the (subclass form) of the syntactic class term. The syntax extension
is shown on Figure 3.2.


Remark: Implication is not defined but primitive (it is a non-
dependent product of a proposition over another proposition). There is
also a primitive universal quantification (it is a dependent product
over a proposition). The primitive universal quantification allows
both first-order and higher-order quantification.


Propositional Connectives
`````````````````````````

First, we find propositional calculus connectives:
Coq < Inductive True : Prop := I.

Coq < Inductive False : Prop := .

Coq < Definition not (A: Prop) := A -> False.

Coq < Inductive and (A B:Prop) : Prop := conj (_:A) (_:B).

Coq < Section Projections.

Coq < Variables A B : Prop.

Coq < Theorem proj1 : A /\ B -> A.

Coq < Theorem proj2 : A /\ B -> B.
Coq < End Projections.


Coq < Inductive or (A B:Prop) : Prop :=
| or_introl (_:A)
| or_intror (_:B).

Coq < Definition iff (P Q:Prop) := (P -> Q) /\ (Q -> P).

Coq < Definition IF_then_else (P Q R:Prop) := P /\ Q \/ ~ P /\ R.



Quantifiers
```````````

Then we find first-order quantifiers:
Coq < Definition all (A:Set) (P:A -> Prop) := forall x:A, P x.

Coq < Inductive ex (A: Set) (P:A -> Prop) : Prop :=
ex_intro (x:A) (_:P x).

Coq < Inductive ex2 (A:Set) (P Q:A -> Prop) : Prop :=
ex_intro2 (x:A) (_:P x) (_:Q x).

The following abbreviations are allowed:
`exists x:A, P` `ex A (fun x:A => P)` `exists x, P` `ex _ (fun x =>
P)` `exists2 x:A, P & Q` `ex2 A (fun x:A => P) (fun x:A => Q)`
`exists2 x, P & Q` `ex2 _ (fun x => P) (fun x => Q)`
The type annotation “:A” can be omitted when A can be synthesized by
the system.


Equality
````````

Then, we find equality, defined as an inductive relation. That is,
given a type `A` and an `x` of type `A`, the predicate `(eq A x)` is
the smallest one which contains `x`. This definition, due to Christine
Paulin-Mohring, is equivalent to define `eq` as the smallest reflexive
relation, and it is also equivalent to Leibniz’ equality.


Coq < Inductive eq (A:Type) (x:A) : A -> Prop :=
eq_refl : eq A x x.



Lemmas
``````

Finally, a few easy lemmas are provided.


Coq < Theorem absurd : forall A C:Prop, A -> ~ A -> C.


Coq < Section equality.

Coq < Variables A B : Type.

Coq < Variable f : A -> B.

Coq < Variables x y z : A.

Coq < Theorem eq_sym : x = y -> y = x.

Coq < Theorem eq_trans : x = y -> y = z -> x = z.

Coq < Theorem f_equal : x = y -> f x = f y.

Coq < Theorem not_eq_sym : x <> y -> y <> x.


Coq < End equality.

Coq < Definition eq_ind_r :
forall (A:Type) (x:A) (P:A->Prop), P x -> forall y:A, y = x -> P y.

Coq < Definition eq_rec_r :
forall (A:Type) (x:A) (P:A->Set), P x -> forall y:A, y = x -> P y.

Coq < Definition eq_rect_r :
forall (A:Type) (x:A) (P:A->Type), P x -> forall y:A, y = x -> P y.
Coq < Hint Immediate eq_sym not_eq_sym : core.



The theorem f_equal is extended to functions with two to five
arguments. The theorem are names f_equal2, f_equal3, f_equal4 and
f_equal5. For instance f_equal3 is defined the following way.
Coq < Theorem f_equal3 :
forall (A1 A2 A3 B:Type) (f:A1 -> A2 -> A3 -> B)
(x1 y1:A1) (x2 y2:A2) (x3 y3:A3),
x1 = y1 -> x2 = y2 -> x3 = y3 -> f x1 x2 x3 = f y1 y2 y3.



3.1.3 Datatypes
~~~~~~~~~~~~~~~



specif ::= specif * specif (prod) | specif + specif (sum) | specif + {
specif } (sumor) | { specif } + { specif } (sumbool) | { ident :
specif | form } (sig) | { ident : specif | form &form } (sig2) | {
ident : specif & specif } (sigT) | { ident : specif & specif & specif
} (sigT2) term ::= ( term , term ) (pair) Figure 3.3: Syntax of data-
types and specifications



In the basic library, we find the definition 2 of the basic data-types
of programming, again defined as inductive constructions over the sort
`Set`. Some of them come with a special syntax shown on Figure 3.3.


Programming
```````````
Coq < Inductive unit : Set := tt.

Coq < Inductive bool : Set := true | false.

Coq < Inductive nat : Set := O | S (n:nat).

Coq < Inductive option (A:Set) : Set := Some (_:A) | None.

Coq < Inductive identity (A:Type) (a:A) : A -> Type :=
refl_identity : identity A a a.

Note that zero is the letter `O`, and not the numeral `0`.

The predicate identity is logically equivalent to equality but it
lives in sort Type. It is mainly maintained for compatibility.

We then define the disjoint sum of `A+B` of two sets `A` and `B`, and
their product `A*B`.
Coq < Inductive sum (A B:Set) : Set := inl (_:A) | inr (_:B).

Coq < Inductive prod (A B:Set) : Set := pair (_:A) (_:B).

Coq < Section projections.

Coq < Variables A B : Set.

Coq < Definition fst (H: prod A B) := match H with
| pair _ _ x y => x
end.

Coq < Definition snd (H: prod A B) := match H with
| pair _ _ x y => y
end.

Coq < End projections.

Some operations on bool are also provided: andb (with infix notation
&&), orb (with infix notation ||), xorb, implb and negb.


3.1.4 Specification
~~~~~~~~~~~~~~~~~~~

The following notions 3 allow to build new data-types and
specifications. They are available with the syntax shown on Figure
3.3.

For instance, given `A:Type` and `P:A->Prop`, the construct `{x:A | P
x}` (in abstract syntax `(sig A P)`) is a `Type`. We may build
elements of this set as `(exist x p)` whenever we have a witness `x:A`
with its justification `p:P x`.

From such a `(exist x p)` we may in turn extract its witness `x:A`
(using an elimination construct such as `match`) butnot its
justification, which stays hidden, like in an abstract data-type. In
technical terms, one says that `sig` is a “weak (dependent) sum”. A
variant `sig2` with two predicates is also provided.


Coq < Inductive sig (A:Set) (P:A -> Prop) : Set := exist (x:A) (_:P
x).

Coq < Inductive sig2 (A:Set) (P Q:A -> Prop) : Set :=
exist2 (x:A) (_:P x) (_:Q x).

A “strong (dependent) sum” `{x:A & P x}` may be also defined, when the
predicate `P` is now defined as a constructor of types in `Type`.


Coq < Inductive sigT (A:Type) (P:A -> Type) : Type := existT (x:A)
(_:P x).

Coq < Section Projections2.

Coq < Variable A : Type.

Coq < Variable P : A -> Type.

Coq < Definition projT1 (H:sigT A P) := let (x, h) := H in x.

Coq < Definition projT2 (H:sigT A P) :=
match H return P (projT1 H) with
existT _ _ x h => h
end.

Coq < End Projections2.

Coq < Inductive sigT2 (A: Type) (P Q:A -> Type) : Type :=
existT2 (x:A) (_:P x) (_:Q x).

A related non-dependent construct is the constructive sum `{A}+{B}` of
two propositions `A` and `B`.
Coq < Inductive sumbool (A B:Prop) : Set := left (_:A) | right (_:B).

This `sumbool` construct may be used as a kind of indexed boolean
data-type. An intermediate between `sumbool` and `sum` is the mixed
`sumor` which combines `A:Set` and `B:Prop` in the `Set` `A+{B}`.
Coq < Inductive sumor (A:Set) (B:Prop) : Set :=
| inleft (_:A)
| inright (_:B).

We may define variants of the axiom of choice, like in Martin-Löf’s
Intuitionistic Type Theory.
Coq < Lemma Choice :
forall (S S':Set) (R:S -> S' -> Prop),
(forall x:S, {y : S' | R x y}) ->
{f : S -> S' | forall z:S, R z (f z)}.

Coq < Lemma Choice2 :
forall (S S':Set) (R:S -> S' -> Set),
(forall x:S, {y : S' & R x y}) ->
{f : S -> S' & forall z:S, R z (f z)}.

Coq < Lemma bool_choice :
forall (S:Set) (R1 R2:S -> Prop),
(forall x:S, {R1 x} + {R2 x}) ->
{f : S -> bool |
forall x:S, f x = true /\ R1 x \/ f x = false /\ R2 x}.

The next construct builds a sum between a data-type `A:Type` and an
exceptional value encoding errors:


Coq < Definition Exc := option.

Coq < Definition value := Some.

Coq < Definition error := None.

This module ends with theorems, relating the sorts `Set` or `Type` and
`Prop` in a way which is consistent with the realizability
interpretation.
Coq < Definition except := False_rec.

Coq < Theorem absurd_set : forall (A:Prop) (C:Set), A -> ~ A -> C.

Coq < Theorem and_rect2 :
forall (A B:Prop) (P:Type), (A -> B -> P) -> A /\ B -> P.



3.1.5 Basic Arithmetics
~~~~~~~~~~~~~~~~~~~~~~~

The basic library includes a few elementary properties of natural
numbers, together with the definitions of predecessor, addition and
multiplication 4 . It also provides a scope nat_scope gathering
standard notations for common operations (+, *) and a decimal notation
for numbers. That is he can write 3 for (S (S (S O))). This also works
on the left hand side of a match expression (see for example section
`8.2.3`_). This scope is opened by default.

The following example is not part of the standard library, but it
shows the usage of the notations:
Coq < Fixpoint even (n:nat) : bool :=
match n with
| 0 => true
| 1 => false
| S (S n) => even n
end.


Coq < Theorem eq_S : forall x y:nat, x = y -> S x = S y.
Coq < Definition pred (n:nat) : nat :=
match n with
| 0 => 0
| S u => u
end.

Coq < Theorem pred_Sn : forall m:nat, m = pred (S m).

Coq < Theorem eq_add_S : forall n m:nat, S n = S m -> n = m.

Coq < Hint Immediate eq_add_S : core.

Coq < Theorem not_eq_S : forall n m:nat, n <> m -> S n <> S m.
Coq < Definition IsSucc (n:nat) : Prop :=
match n with
| 0 => False
| S p => True
end.

Coq < Theorem O_S : forall n:nat, 0 <> S n.

Coq < Theorem n_Sn : forall n:nat, n <> S n.
Coq < Fixpoint plus (n m:nat) {struct n} : nat :=
match n with
| 0 => m
| S p => S (p + m)
end
where "n + m" := (plus n m) : nat_scope.

Coq < Lemma plus_n_O : forall n:nat, n = n + 0.

Coq < Lemma plus_n_Sm : forall n m:nat, S (n + m) = n + S m.
Coq < Fixpoint mult (n m:nat) {struct n} : nat :=
match n with
| 0 => 0
| S p => m + p * m
end
where "n * m" := (mult n m) : nat_scope.

Coq < Lemma mult_n_O : forall n:nat, 0 = n * 0.

Coq < Lemma mult_n_Sm : forall n m:nat, n * m + n = n * (S m).

Finally, it gives the definition of the usual orderings `le`, `lt`,
`ge`, and `gt`.
Coq < Inductive le (n:nat) : nat -> Prop :=
| le_n : le n n
| le_S : forall m:nat, n <= m -> n <= (S m)
where "n <= m" := (le n m) : nat_scope.

Coq < Definition lt (n m:nat) := S n <= m.

Coq < Definition ge (n m:nat) := m <= n.

Coq < Definition gt (n m:nat) := m < n.

Properties of these relations are not initially known, but may be
required by the user from modules `Le` and `Lt`. Finally, `Peano`
gives some lemmas allowing pattern-matching, and a double induction
principle.


Coq < Theorem nat_case :
forall (n:nat) (P:nat -> Prop),
P 0 -> (forall m:nat, P (S m)) -> P n.
Coq < Theorem nat_double_ind :
forall R:nat -> nat -> Prop,
(forall n:nat, R 0 n) ->
(forall n:nat, R (S n) 0) ->
(forall n m:nat, R n m -> R (S n) (S m)) -> forall n m:nat, R n m.



3.1.6 Well-founded recursion
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The basic library contains the basics of well-founded recursion and
well-founded induction 5 .
Coq < Section Well_founded.

Coq < Variable A : Type.

Coq < Variable R : A -> A -> Prop.

Coq < Inductive Acc (x:A) : Prop :=
Acc_intro : (forall y:A, R y x -> Acc y) -> Acc x.

Coq < Lemma Acc_inv x : Acc x -> forall y:A, R y x -> Acc y.
Coq < Definition well_founded := forall a:A, Acc a.

Coq < Hypothesis Rwf : well_founded.

Coq < Theorem well_founded_induction :
forall P:A -> Set,
(forall x:A, (forall y:A, R y x -> P y) -> P x) -> forall a:A, P a.

Coq < Theorem well_founded_ind :
forall P:A -> Prop,
(forall x:A, (forall y:A, R y x -> P y) -> P x) -> forall a:A, P a.

The automatically generated scheme Acc_rect can be used to define
functions by fixpoints using well-founded relations to justify
termination. Assuming extensionality of the functional used for the
recursive call, the fixpoint equation can be proved.
Coq < Section FixPoint.

Coq < Variable P : A -> Type.

Coq < Variable F : forall x:A, (forall y:A, R y x -> P y) -> P x.

Coq < Fixpoint Fix_F (x:A) (r:Acc x) {struct r} : P x :=
F x (fun (y:A) (p:R y x) => Fix_F y (Acc_inv x r y p)).

Coq < Definition Fix (x:A) := Fix_F x (Rwf x).

Coq < Hypothesis F_ext :
forall (x:A) (f g:forall y:A, R y x -> P y),
(forall (y:A) (p:R y x), f y p = g y p) -> F x f = F x g.

Coq < Lemma Fix_F_eq :
forall (x:A) (r:Acc x),
F x (fun (y:A) (p:R y x) => Fix_F y (Acc_inv x r y p)) = Fix_F x r.

Coq < Lemma Fix_F_inv : forall (x:A) (r s:Acc x), Fix_F x r = Fix_F x
s.

Coq < Lemma fix_eq : forall x:A, Fix x = F x (fun (y:A) (p:R y x) =>
Fix y).
Coq < End FixPoint.

Coq < End Well_founded.



3.1.7 Accessing the Type level
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The basic library includes the definitions 6 of the counterparts of
some data-types and logical quantifiers at the `Type` level: negation,
pair, and properties of identity.


Coq < Definition notT (A:Type) := A -> False.

Coq < Inductive prodT (A B:Type) : Type := pairT (_:A) (_:B).

At the end, it defines data-types at the Type level.


3.1.8 Tactics
~~~~~~~~~~~~~

A few tactics defined at the user level are provided in the initial
state 7 . They are listed at`http://coq.inria.fr/stdlib`_ (paragraph
Init, link Tactics).


3.2 The standard library
------------------------


3.2.1 Survey
~~~~~~~~~~~~

The rest of the standard library is structured into the following
subdirectories:
Logic Classical logic and dependent equality Arith Basic Peano
arithmetic PArith Basic positive integer arithmetic NArith Basic
binary natural number arithmetic ZArith Basic relative integer
arithmetic Numbers Various approaches to natural, integer and cyclic
numbers (currently axiomatically and on top of 2 31 binary words) Bool
Booleans (basic functions and results) Lists Monomorphic and
polymorphic lists (basic functions and results), Streams (infinite
sequences defined with co-inductive types) Sets Sets (classical,
constructive, finite, infinite, power set, etc.) FSets Specification
and implementations of finite sets and finite maps (by lists and by
AVL trees) Reals Axiomatization of real numbers (classical, basic
functions, integer part, fractional part, limit, derivative, Cauchy
series, power series and results,...) Relations Relations (definitions
and basic results) Sorting Sorted list (basic definitions and heapsort
correctness) Strings 8-bits characters and strings Wellfounded Well-
founded relations (basic results)



These directories belong to the initial load path of the system, and
the modules they provide are compiled at installation time. So they
are directly accessible with the command `Require` (see Chapter `6`_).

The different modules of the Coq standard library are described in the
additional document `Library.dvi`. They are also accessible on the WWW
through the Coq homepage 8 .


3.2.2 Notations for integer arithmetics
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

On Figure 3.4 is described the syntax of expressions for integer
arithmetics. It is provided by requiring and opening the module ZArith
and opening scope Z_scope.





Notation Interpretation Precedence Associativity `_ < _` Z.lt `x <= y`
Z.le `_ > _` Z.gt `x >= y` Z.ge `x < y < z` x < y `/\` y < z `x < y <=
z` x < y `/\` y <= z `x <= y < z` x <= y `/\` y < z `x <= y <= z` x <=
y `/\` y <= z `_ ?= _` Z.compare 70 no `_ + _` Z.add `_ - _` Z.sub `_
* _` Z.mul `_ / _` Z.div `_ mod _` Z.modulo 40 no `- _` Z.opp `_ ^ _`
Z.pow Figure 3.4: Definition of the scope for integer arithmetics
(Z_scope)



Figure 3.4 shows the notations provided by Z_scope. It specifies how
notations are interpreted and, when not already reserved, the
precedence and associativity.
Coq < Require Import ZArith.

Coq < Check (2 + 3)%Z.
(2 + 3)%Z
: Z

Coq < Open Scope Z_scope.

Coq < Check 2 + 3.
2 + 3
: Z



3.2.3 Peano’s arithmetic (nat)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

While in the initial state, many operations and predicates of Peano’s
arithmetic are defined, further operations and results belong to other
modules. For instance, the decidability of the basic predicates are
defined here. This is provided by requiring the module Arith.

Figure 3.5 describes notation available in scope nat_scope.



Notation Interpretation `_ < _` lt `x <= y` le `_ > _` gt `x >= y` ge
`x < y < z` x < y `/\` y < z `x < y <= z` x < y `/\` y <= z `x <= y <
z` x <= y `/\` y < z `x <= y <= z` x <= y `/\` y <= z `_ + _` plus `_
- _` minus `_ * _` mult Figure 3.5: Definition of the scope for
natural numbers (nat_scope)





3.2.4 Real numbers library
~~~~~~~~~~~~~~~~~~~~~~~~~~


Notations for real numbers
``````````````````````````

This is provided by requiring and opening the module Reals and opening
scope R_scope. This set of notations is very similar to the notation
for integer arithmetics. The inverse function was added.



Notation Interpretation `_ < _` Rlt `x <= y` Rle `_ > _` Rgt `x >= y`
Rge `x < y < z` x < y `/\` y < z `x < y <= z` x < y `/\` y <= z `x <=
y < z` x <= y `/\` y < z `x <= y <= z` x <= y `/\` y <= z `_ + _`
Rplus `_ - _` Rminus `_ * _` Rmult `_ / _` Rdiv `- _` Ropp `/ _` Rinv
`_ ^ _` pow Figure 3.6: Definition of the scope for real arithmetics
(R_scope)


Coq < Require Import Reals.

Coq < Check (2 + 3)%R.
(2 + 3)%R
: R

Coq < Open Scope R_scope.

Coq < Check 2 + 3.
2 + 3
: R



Some tactics
````````````

In addition to the `ring`, `field` and `fourier` tactics (see Chapter
`8`_) there are:


+ discrR Proves that a real integer constant c 1 is different from
  another real integer constant c 2 . Coq < Require Import DiscrR. Coq <
  Goal 5 <> 0. Coq < discrR. No more subgoals.
+ split_Rabs allows unfolding the Rabs constant and splits
  corresponding conjunctions. Coq < Require Import SplitAbsolu. Coq <
  Goal forall x:R, x <= Rabs x. Coq < intro; split_Rabs. 2 subgoals x :
  R Hlt : x < 0 ============================ x <= - x subgoal 2 is: x <=
  x
+ split_Rmult splits a condition that a product is non null into
  subgoals corresponding to the condition on each operand of the
  product. Coq < Require Import SplitRmult. Coq < Goal forall x y z:R, x
  * y * z <> 0. Coq < intros; split_Rmult. 3 subgoals x, y, z : R
  ============================ x <> 0 subgoal 2 is: y <> 0 subgoal 3 is:
  z <> 0


These tactics has been written with the tactic language Ltac described
in Chapter `9`_.


3.2.5 List library
~~~~~~~~~~~~~~~~~~

Some elementary operations on polymorphic lists are defined here. They
can be accessed by requiring module List.

It defines the following notions:
length length head first element (with default) tail all but first
element app concatenation rev reverse nth accessing n-th element (with
default) map applying a function flat_map applying a function
returning lists fold_left iterator (from head to tail) fold_right
iterator (from tail to head)
Table show notations available when opening scope list_scope.



Notation Interpretation Precedence Associativity `_ ++ _` app 60 right
`_ :: _` cons 60 right Figure 3.7: Definition of the scope for lists
(list_scope)





3.3 Users’ contributions
------------------------

Numerous users’ contributions have been collected and are available at
URL `http://coq.inria.fr/contribs/`_. On this web page, you have a
list of all contributions with informations (author, institution,
quick description, etc.) and the possibility to download them one by
one. You will also find informations on how to submit a new
contribution.



:1: Most of these constructions are defined in thePrelude module in
  directory theories/Init at the Coq root directory; this includes the
  modulesNotations,Logic,Datatypes,Specif,Peano,Wf and Tactics. Module
  Logic_Type also makes it in the initial state
:2: They are in Datatypes.v
:3: They are defined in module Specif.v
:4: This is in module Peano.v
:5: This is defined in module Wf.v
:6: This is in moduleLogic_Type.v
:7: This is in module Tactics.v
:8: `http://coq.inria.fr`_




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


.. _Get Coq: :///download
.. _9: :///home/steck/ltac.html#TacticLanguage
.. _CSS valid: http://jigsaw.w3.org/css-validator/
.. _6: :///home/steck/vernacular.html#Other-commands
.. _Cover: :///home/steck/index.html
.. _Errors: :///home/steck/error-index.html
.. _Table of contents: :///home/steck/toc.html
.. _Community: :///community
.. _3.2  The standard library: :///home/steck/stdlib.html#sec157
.. _http://coq.inria.fr/stdlib: http://coq.inria.fr/stdlib
.. _3.1  The basic library: :///home/steck/stdlib.html#Prelude
.. _Commands: :///home/steck/command-index.html
.. _About Coq: :///about-coq
.. _http://coq.inria.fr/contribs/: http://coq.inria.fr/contribs/
.. _General: :///home/steck/general-index.html
.. _xhtml valid: http://validator.w3.org/
.. _Tactics: :///home/steck/tactic-index.html
.. _8: :///home/steck/tactics.html#Tactics
.. _Options: :///home/steck/option-index.html
.. _6.5.1: :///home/steck/vernacular.html#Require
.. _http://coq.inria.fr: http://coq.inria.fr
.. _The Coq Proof Assistant: :///
.. _8.2.3: :///home/steck/tactics.html#refine-example
.. _Documentation: :///documentation
.. _3.3  Users’ contributions: :///home/steck/stdlib.html#Contributions
.. _webmaster: mailto:coq-www_@_inria.fr



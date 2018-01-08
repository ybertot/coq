

+ `Home`_
+ `About Coq`_
+ `Get Coq`_
+ `Documentation`_
+ `Community`_

` `_ `The Coq Proof Assistant`_


Chapter 30 Miscellaneous extensions
===================================


+ `30.1 Program derivation`_




30.1 Program derivation
-----------------------

Coq comes with an extension called Derive, which supports program
derivation. Typically in the style of Bird and Meertens or derivations
of program refinements. To use the Derive extension it must first be
required with Require Coq.Derive.Derive. When the extension is loaded,
it provides the following command.


30.1.1 Derive ident 1 SuchThat term As ident 2
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The name ident 1 can appear in term. This command opens a new proof
presenting the user with a goal for term in which the nameident 1 is
bound to a existential variables ?x (formally, there are other goals
standing for the existential variables but they are shelved, as
described in Section `8.17.4`_).

When the proof ends two constants are defined:


+ The first one is name ident 1 and is defined as the proof of the
  shelved goal (which is also the value of ?x). It is always
  transparent.
+ The second one is name ident 2 . It has type term, and its body is
  the proof of the initially visible goal. It is opaque if the proof
  ends with Qed, and transparent if the proof ends with Defined.



Example:
Coq < Require Coq.derive.Derive.

Coq < Require Import Coq.Numbers.Natural.Peano.NPeano.

Coq < Section P.

Coq < Variables (n m k:nat).

Coq < Derive p SuchThat ((k*n)+(k*m) = p) As h.
1 focused subgoal
(shelved: 1)

n, m, k : nat
p := ?Goal : nat
============================
k * n + k * m = p

Coq < Proof.
1 focused subgoal
(shelved: 1)

n, m, k : nat
p := ?Goal : nat
============================
k * n + k * m = p

Coq < rewrite <- Nat.mul_add_distr_l.
1 focused subgoal
(shelved: 1)

n, m, k : nat
p := ?Goal : nat
============================
k * (n + m) = p

Coq < subst p.
1 focused subgoal
(shelved: 1)

n, m, k : nat
============================
k * (n + m) = ?Goal

Coq < reflexivity.
No more subgoals.

Coq < Qed.

Coq < End P.

Coq < Print p.
p = fun n m k : nat => k * (n + m)
: nat -> nat -> nat -> nat
Argument scopes are [nat_scope nat_scope nat_scope]

Coq < Check h.
h
: forall n m k : nat, k * n + k * m = p n m k

Any property can be used as term, not only an equation. In particular,
it could be an order relation specifying some form of program
refinement or a non-executable property from which deriving a program
is convenient.



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


.. _Commands: :///home/steck/command-index.html
.. _Get Coq: :///download
.. _8.17.4: :///home/steck/tactics.html#shelve
.. _Options: :///home/steck/option-index.html
.. _About Coq: :///about-coq
.. _Cover: :///home/steck/index.html
.. _CSS valid: http://jigsaw.w3.org/css-validator/
.. _The Coq Proof Assistant: :///
.. _Errors: :///home/steck/error-index.html
.. _30.1  Program derivation: :///home/steck/miscellaneous.html#sec892
.. _General: :///home/steck/general-index.html
.. _Documentation: :///documentation
.. _xhtml valid: http://validator.w3.org/
.. _Table of contents: :///home/steck/toc.html
.. _Community: :///community
.. _webmaster: mailto:coq-www_@_inria.fr
.. _Tactics: :///home/steck/tactic-index.html





+ `Home`_
+ `About Coq`_
+ `Get Coq`_
+ `Documentation`_
+ `Community`_

` `_ `The Coq Proof Assistant`_


Chapter 24 Program
==================


+ `24.1 Elaborating programs`_
+ `24.2 Solving obligations`_
+ `24.3 Frequently Asked Questions`_


Matthieu Sozeau



We present here the Program tactic commands, used to build
certifiedCoq programs, elaborating them from their algorithmic
skeleton and a rich specification [`135`_]. It can be thought of as a
dual of extraction (see Chapter `23`_). The goal of Program is to
program as in a regular functional programming language whilst using
as rich a specification as desired and proving that the code meets the
specification using the whole Coq proof apparatus. This is done using
a technique originating from the “Predicate subtyping” mechanism of
PVS[`132`_], which generates type-checking conditions while typing a
term constrained to a particular type. Here we insert existential
variables in the term, which must be filled with proofs to get a
complete Coq term. Program replaces theProgram tactic by Catherine
Parent [`121`_] which had a similar goal but is no longer maintained.

The languages available as input are currently restricted to Coq’s
term language, but may be extended to Objective Caml, Haskell and
others in the future. We use the same syntax as Coq and permit to use
implicit arguments and the existing coercion mechanism. Input terms
and types are typed in an extended system (Russell) and interpreted
into Coq terms. The interpretation process may produce some proof
obligations which need to be resolved to create the final term.


24.1 Elaborating programs
-------------------------

The main difference from Coq is that an object in a type T : Set can
be considered as an object of type { x : T | P} for any wellformed P :
Prop. If we go from T to the subset of T verifying property P, we must
prove that the object under consideration verifies it. Russell will
generate an obligation for every such coercion. In the other
direction,Russell will automatically insert a projection.

Another distinction is the treatment of pattern-matching. Apart from
the following differences, it is equivalent to the standard match
operation (see Section `4.5.3`_).


+ Generation of equalities. A match expression is always generalized
  by the corresponding equality. As an example, the expression:

::

      match x with
      | 0 => t
      | S n => u
      end.

  will be first rewritten to:

::

      (match x as y return (x = y -> _) with
      | 0 => fun H : x = 0 -> t
      | S n => fun H : x = S n -> u
      end) (eq_refl n).

  This permits to get the proper equalities in the context of proof
  obligations inside clauses, without which reasoning is very limited.
+ Generation of inequalities. If a pattern intersects with a previous
  one, an inequality is added in the context of the second branch. See
  for example the definition of div2 below, where the second branch is
  typed in a context where ∀ p, _ <> S (S p).
+ Coercion. If the object being matched is coercible to an inductive
  type, the corresponding coercion will be automatically inserted. This
  also works with the previous mechanism.


There are options to control the generation of equalities and
coercions.


+ Unset Program Cases This deactivates the special treatment of
  pattern-matching generating equalities and inequalities when using
  Program (it is on by default). All pattern-matchings and let-patterns
  are handled using the standard algorithm of Coq (see Section `17`_)
  when this option is deactivated.
+ Unset Program Generalized Coercion This deactivates the coercion of
  general inductive types when using Program (the option is on by
  default). Coercion of subset types and pairs is still active in this
  case.



24.1.1 Syntactic control over equalities
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

To give more control over the generation of equalities, the
typechecker will fall back directly to Coq’s usual typing of dependent
pattern-matching if a return or in clause is specified. Likewise, the
if construct is not treated specially by Program so boolean tests in
the code are not automatically reflected in the obligations. One can
use the dec combinator to get the correct hypotheses as in:
Coq < Program Definition id (n : nat) : { x : nat | x = n } :=
if dec (leb n 0) then 0
else S (pred n).
id has type-checked, generating 2 obligations
Solving obligations automatically...
2 obligations remaining
Obligation 1 of id:
(forall n : nat, (n <=? 0) = true -> (fun x : nat => x = n) 0).

Obligation 2 of id:
(forall n : nat,
(n <=? 0) = false -> (fun x : nat => x = n) (S (Init.Nat.pred n))).


The let tupling construct let (x1, ..., xn) := t in b does not produce
an equality, contrary to the let pattern construct let ’(x1, ..., xn)
:= t in b. Also, term:> explicitly asks the system to coerce term to
its support type. It can be useful in notations, for example:
Coq < Notation " x `= y " := (@eq _ (x :>) (y :>)) (only parsing).

This notation denotes equality on subset types using equality on their
support types, avoiding uses of proof-irrelevance that would come up
when reasoning with equality on the subset types themselves.

The next two commands are similar to their standard counterparts
Definition (see Section `1.3.2`_) and Fixpoint (see Section `1.3.4`_)
in that they define constants. However, they may require the user to
prove some goals to construct the final definitions.


24.1.2 Program Definition ident := term.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command types the value term in Russell and generates proof
obligations. Once solved using the commands shown below, it binds the
finalCoq term to the name ident in the environment.


Error messages:


#. ident already exists



Variants:


#. Program Definition ident :term 1 :=term 2 . It interprets the type
   term 1 , potentially generating proof obligations to be resolved. Once
   done with them, we have a Coq typeterm 1 ′. It then checks that the
   type of the interpretation ofterm 2 is coercible to term 1 ′, and
   registers ident as being of type term 1 ′ once the set of obligations
   generated during the interpretation of term 2 and the aforementioned
   coercion derivation are solved.
#. Program Definition ident binder 1 …binder n :term 1 := term 2 .
   This is equivalent to Program Definition ident : forall binder 1
   …binder n , term 1 := fun binder 1 …binder n => term 2 .



Error messages:


#. In environment … the term: term 2 does not have typeterm 1 .
   Actually, it has type term 3 .



See also: Sections `6.10.1`_, `6.10.2`_, `8.7.5`_


24.1.3 Program Fixpoint ident params {order} : type := term
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The structural fixpoint operator behaves just like the one of Coq (see
Section `1.3.4`_), except it may also generate obligations. It works
with mutually recursive definitions too.
Coq < Program Fixpoint div2 (n : nat) : { x : nat | n = 2 * x \/ n = 2
* x + 1 } :=
match n with
| S (S p) => S (div2 p)
| _ => O
end.
Solving obligations automatically...
4 obligations remaining

Here we have one obligation for each branch (branches for `0` and `(S
0)` are automatically generated by the pattern-matching compilation
algorithm).
Coq < Obligation 1.
1 subgoal

p, x : nat
o : p = x + (x + 0) \/ p = x + (x + 0) + 1
============================
S (S p) = S (x + S (x + 0)) \/ S (S p) = S (x + S (x + 0) + 1)

One can use a well-founded order or a measure as termination orders
using the syntax:
Coq < Program Fixpoint div2 (n : nat) {measure n} :
{ x : nat | n = 2 * x \/ n = 2 * x + 1 } :=
match n with
| S (S p) => S (div2 p)
| _ => O
end.

The order annotation can be either:


+ measure f (R)? where f is a value of type X computed on any subset
  of the arguments and the optional (parenthesised) term (R) is a
  relation on X. By default X defaults to nat and R tolt.
+ wf R x which is equivalent to measure x (R).



Caution
+++++++

When defining structurally recursive functions, the generated
obligations should have the prototype of the currently defined
functional in their context. In this case, the obligations should be
transparent (e.g. defined using Defined) so that the guardedness
condition on recursive calls can be checked by the kernel’s type-
checker. There is an optimization in the generation of obligations
which gets rid of the hypothesis corresponding to the functional when
it is not necessary, so that the obligation can be declared opaque
(e.g. using Qed). However, as soon as it appears in the context, the
proof of the obligation is *required* to be declared transparent.

No such problems arise when using measures or well-founded recursion.


24.1.4 Program Lemma ident : type.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The Russell language can also be used to type statements of logical
properties. It will generate obligations, try to solve them
automatically and fail if some unsolved obligations remain. In this
case, one can first define the lemma’s statement using Program
Definition and use it as the goal afterwards. Otherwise the proof will
be started with the elaborated version as a goal. The Program prefix
can similarly be used as a prefix for Variable, Hypothesis, Axiom
etc...


24.2 Solving obligations
------------------------

The following commands are available to manipulate obligations. The
optional identifier is used when multiple functions have unsolved
obligations (e.g. when defining mutually recursive blocks). The
optional tactic is replaced by the default one if not specified.


+ [Local|Global] Obligation Tactic := expr Sets the default obligation
  solving tactic applied to all obligations automatically, whether to
  solve them or when starting to prove one, e.g. using Next. Local makes
  the setting last only for the current module. Inside sections, local
  is the default.
+ Show Obligation Tactic Displays the current default tactic.
+ Obligations [of ident] Displays all remaining obligations.
+ Obligation num [of ident] Start the proof of obligation num.
+ Next Obligation [of ident] Start the proof of the next unsolved
  obligation.
+ Solve Obligations [of ident] [withexpr] Tries to solve each
  obligation of identusing the given tactic or the default one.
+ Solve All Obligations [with expr] Tries to solve each obligation of
  every program using the given tactic or the default one (useful for
  mutually recursive definitions).
+ Admit Obligations [of ident] Admits all obligations (does not work
  with structurally recursive programs).
+ Preterm [of ident] Shows the term that will be fed to the kernel
  once the obligations are solved. Useful for debugging.
+ Set Transparent Obligations Control whether all obligations should
  be declared as transparent (the default), or if the system should
  infer which obligations can be declared opaque.
+ Set Hide Obligations Control whether obligations appearing in the
  term should be hidden as implicit arguments of the special
  constantProgram.Tactics.obligation.
+ Set Shrink Obligations *Deprecated since 8.7* This option (on by
  default) controls whether obligations should have their context
  minimized to the set of variables used in the proof of the obligation,
  to avoid unnecessary dependencies.


The module Coq.Program.Tactics defines the default tactic for solving
obligations called program_simpl. Importing Coq.Program.Program also
adds some useful notations, as documented in the file itself.


24.3 Frequently Asked Questions
-------------------------------


+ Ill-formed recursive definitions This error can happen when one
  tries to define a function by structural recursion on a subset object,
  which means the Coq function looks like: `Program Fixpoint f (x : A |
  P) := match x with A b => f b end.`Supposing b : A, the argument at
  the recursive call to f is not a direct subterm of x as b is wrapped
  inside an exist constructor to build an object of type `{x : A | P}`.
  Hence the definition is rejected by the guardedness condition checker.
  However one can use wellfounded recursion on subset objects like this:

::

    Program Fixpoint f (x : A | P) { measure (size x) } :=
      match x with A b => f b end.

  One will then just have to prove that the measure decreases at each
  recursive call. There are three drawbacks though:

    #. A measure function has to be defined;
    #. The reduction is a little more involved, although it works well
       using lazy evaluation;
    #. Mutual recursion on the underlying inductive type isn’t possible
       anymore, but nested mutual recursion is always possible.





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


.. _1.3.4: :///home/steck/gallina.html#Fixpoint
.. _Get Coq: :///download
.. _23: :///home/steck/extraction.html#Extraction
.. _About Coq: :///about-coq
.. _CSS valid: http://jigsaw.w3.org/css-validator/
.. _6.10.1: :///home/steck/vernacular.html#Opaque
.. _Cover: :///home/steck/index.html
.. _Errors: :///home/steck/error-index.html
.. _121: :///home/steck/biblio.html#Parent95b
.. _Table of contents: :///home/steck/toc.html
.. _Community: :///community
.. _8.7.5: :///home/steck/tactics.html#unfold
.. _17: :///home/steck/cases.html#Mult-match-full
.. _24.3  Frequently Asked Questions
: :///home/steck/program.html#ProgramFAQ
.. _24.1  Elaborating programs: :///home/steck/program.html#sec828
.. _132: :///home/steck/biblio.html#Rushby98
.. _1.3.2: :///home/steck/gallina.html#Basic-definitions
.. _Commands: :///home/steck/command-index.html
.. _xhtml valid: http://validator.w3.org/
.. _Tactics: :///home/steck/tactic-index.html
.. _6.10.2: :///home/steck/vernacular.html#Transparent
.. _General: :///home/steck/general-index.html
.. _Options: :///home/steck/option-index.html
.. _135: :///home/steck/biblio.html#Sozeau06
.. _The Coq Proof Assistant: :///
.. _24.2  Solving obligations: :///home/steck/program.html#sec834
.. _4.5.3: :///home/steck/cic.html#Caseexpr
.. _Documentation: :///documentation
.. _webmaster: mailto:coq-www_@_inria.fr



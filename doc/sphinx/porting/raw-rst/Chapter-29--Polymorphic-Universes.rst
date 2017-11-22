

+ `Home`_
+ `About Coq`_
+ `Get Coq`_
+ `Documentation`_
+ `Community`_

` `_ `The Coq Proof Assistant`_


Chapter 29 Polymorphic Universes
================================


+ `29.1 General Presentation`_
+ `29.2 Polymorphic, Monomorphic`_
+ `29.3 Cumulative, NonCumulative`_
+ `29.4 Global and local universes`_
+ `29.5 Conversion and unification`_
+ `29.6 Minimization`_
+ `29.7 Explicit Universes`_


Matthieu Sozeau






29.1 General Presentation
-------------------------
*The status of Universe Polymorphism is experimental.*
This section describes the universe polymorphic extension of Coq.
Universe polymorphism makes it possible to write generic definitions
making use of universes and reuse them at different and sometimes
incompatible universe levels.

A standard example of the difference between universe *polymorphic*
and *monomorphic* definitions is given by the identity function:
Coq < Definition identity {A : Type} (a : A) := a.

By default, constant declarations are monomorphic, hence the identity
function declares a global universe (say Top.1) for its domain.
Subsequently, if we try to self-apply the identity, we will get an
error:
Coq < Fail Definition selfid := identity (@identity).
The command has indeed failed with message:
The term "@identity" has type "forall A : Type@{Top.1}, A -> A"
while it is expected to have type "?A"
(unable to find a well-typed instantiation for
"?A": cannot ensure that "Type@{Top.1+1}" is a subtype of
"Type@{Top.1}").

Indeed, the global level Top.1 would have to be strictly smaller than
itself for this self-application to typecheck, as the type of
(@identity) isforall (A : Type@Top.1), A -> A whose type is itself
Type@Top.1+1.

A universe polymorphic identity function binds its domain universe
level at the definition level instead of making it global.
Coq < Polymorphic Definition pidentity {A : Type} (a : A) := a.
pidentity is defined

Coq < About pidentity.
pidentity@{Top.2} : forall A : Type@{Top.2}, A -> A
(* Top.2 |= *)
pidentity is universe polymorphic
Argument A is implicit and maximally inserted
Argument scopes are [type_scope _]
pidentity is transparent
Expands to: Constant Top.pidentity

It is then possible to reuse the constant at different levels, like
so:
Coq < Definition selfpid := pidentity (@pidentity).
selfpid is defined

Of course, the two instances of pidentity in this definition are
different. This can be seen when Set Printing Universes is on:
Coq < Print selfpid.
selfpid =
pidentity@{Top.3} (@pidentity@{Top.4})
: forall A : Type@{Top.4}, A -> A
(* Top.3 Top.4 |= Top.4 < Top.3
*)
Argument scopes are [type_scope _]

Now pidentity is used at two different levels: at the head of the
application it is instantiated at Top.3 while in the argument position
it is instantiated at Top.4. This definition is only valid as long as
Top.4 is strictly smaller thanTop.3, as show by the constraints. Note
that this definition is monomorphic (not universe polymorphic), so the
two universes (in this case Top.3 and Top.4) are actually global
levels.

Inductive types can also be declared universes polymorphic on
universes appearing in their parameters or fields. A typical example
is given by monoids:
Coq < Polymorphic Record Monoid := { mon_car :> Type; mon_unit :
mon_car;
mon_op : mon_car -> mon_car -> mon_car }.
Monoid is defined
mon_car is defined
mon_unit is defined
mon_op is defined

Coq < Print Monoid.
Polymorphic NonCumulative Record Monoid : Type@{Top.6+1}
:= Build_Monoid
{ mon_car : Type@{Top.6};
mon_unit : mon_car;
mon_op : mon_car -> mon_car -> mon_car }
For Build_Monoid: Argument scopes are [type_scope _ function_scope]

The Monoid’s carrier universe is polymorphic, hence it is possible to
instantiate it for example with Monoid itself. First we build the
trivial unit monoid in Set:
Coq < Definition unit_monoid : Monoid :=
{| mon_car := unit; mon_unit := tt; mon_op x y := tt |}.
unit_monoid is defined

From this we can build a definition for the monoid ofSet-monoids
(where multiplication would be given by the product of monoids).
Coq < Polymorphic Definition monoid_monoid : Monoid.

Coq < refine (@Build_Monoid Monoid unit_monoid (fun x y => x)).

Coq < Defined.

Coq < Print monoid_monoid.
Polymorphic monoid_monoid@{Top.10} =
{|
mon_car := Monoid@{Set};
mon_unit := unit_monoid;
mon_op := fun x _ : Monoid@{Set} => x |}
: Monoid@{Top.10}
(* Top.10 |= Set < Top.10
*)
monoid_monoid is universe polymorphic

As one can see from the constraints, this monoid is “large”, it lives
in a universe strictly higher than Set.


29.2 Polymorphic, Monomorphic
-----------------------------



As shown in the examples, polymorphic definitions and inductives can
be declared using the Polymorphic prefix. There also exists an option
Set Universe Polymorphism which will implicitly prepend it to any
definition of the user. In that case, to make a definition producing
global universe constraints, one can use theMonomorphic prefix. Many
other commands support thePolymorphic flag, including:


+ Lemma, Axiom, and all the other “definition” keywords support
  polymorphism.
+ Variables, Context, Universe andConstraint in a section support
  polymorphism. This means that the universe variables (and associated
  constraints) are discharged polymorphically over definitions that use
  them. In other words, two definitions in the section sharing a common
  variable will both get parameterized by the universes produced by the
  variable declaration. This is in contrast to a “mononorphic” variable
  which introduces global universes and constraints, making the two
  definitions depend on the *same* global universes associated to the
  variable.
+ Hint {Resolve, Rewrite} will use the auto/rewrite hint
  polymorphically, not at a single instance.



29.3 Cumulative, NonCumulative
------------------------------



Polymorphic inductive types, coinductive types, variants and records
can be declared cumulative using the Cumulative. Alternatively, there
is an option Set Polymorphic Inductive Cumulativity which when set,
makes all subsequent *polymorphic* inductive definitions cumulative.
When set, inductive types and the like can be enforced to be *non-
cumulative* using the NonCumulative prefix. Consider the examples
below.
Coq < Polymorphic Cumulative Inductive list {A : Type} :=
| nil : list
| cons : A -> list -> list.

Coq < Print list.
Polymorphic Cumulative Inductive
list@{Top.13} (A : Type@{Top.13}) : Type@{max(Set, Top.13)} :=
nil : list@{Top.13} | cons : A -> list@{Top.13} -> list@{Top.13}
(* Top.13 |=

~@{Top.13} <= ~@{Top.15} iff
*)
For list: Argument A is implicit and maximally inserted
For nil: Argument A is implicit and maximally inserted
For cons: Argument A is implicit and maximally inserted
For list: Argument scope is [type_scope]
For nil: Argument scope is [type_scope]
For cons: Argument scopes are [type_scope _ _]

When printing list, the part of the output of the form∼@{i} <= ∼@{j}
iff indicates the universe constraints in order to have the
subtypingE[Γ] ⊢ list@{i} A ≤ βδιζη list@{j} B (for fully applied
instances of list) whenever E[Γ] ⊢ A = βδιζη B. In the case of list
there is no constraint! This also means that any two instances of list
are convertible:E[Γ] ⊢ list@{i} A = βδιζη list@{j} B whenever E[Γ] ⊢ A
= βδιζη B and furthermore their corresponding (when fully applied to
convertible arguments) constructors. See Chapter `4`_ for more details
on convertibility and subtyping. The following is an example of a
record with non-trivial subtyping relation:
Coq < Polymorphic Cumulative Record packType := {pk : Type}.

Coq < Print packType.
Polymorphic Cumulative Record packType : Type@{Top.20+1}
:= Build_packType
{ pk : Type@{Top.20} }
(* Top.20 |=

~@{Top.20} <= ~@{Top.21} iff
Top.20 <= Top.21
*)
For Build_packType: Argument scope is [type_scope]

Notice that as expected, packType@{i} and packType@{j} are convertible
if and only if i = j.

Cumulative inductive types, coninductive types, variants and records
only make sense when they are universe polymorphic. Therefore, an
error is issued whenever the user uses the Cumulative orNonCumulative
prefix in a monomorphic context. Notice that this is not the case for
the option Set Polymorphic Inductive Cumulativity. That is, this
option, when set, makes all subsequent *polymorphic* inductive
declarations cumulative (unless, of course the NonCumulative prefix is
used) but has no effect on *monomorphic* inductive declarations.
Consider the following examples.
Coq < Monomorphic Cumulative Inductive Unit := unit.
Toplevel input, characters 0-46:
> Monomorphic Cumulative Inductive Unit := unit.
> ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: The Cumulative prefix can only be used in a polymorphic
context.

Coq < Monomorphic NonCumulative Inductive Unit := unit.
Toplevel input, characters 0-49:
> Monomorphic NonCumulative Inductive Unit := unit.
> ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: The NonCumulative prefix can only be used in a polymorphic
context.

Coq < Set Polymorphic Inductive Cumulativity.

Coq < Inductive Unit := unit.

Coq < Print Unit.
Inductive Unit : Prop := unit : Unit



An example of a proof using cumulativity
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Coq < Set Universe Polymorphism.

Coq < Set Polymorphic Inductive Cumulativity.

Coq < Inductive eq@{i} {A : Type@{i}} (x : A) : A -> Type@{i} :=
eq_refl : eq x x.
eq is defined
eq_rect is defined
eq_ind is defined
eq_rec is defined

Coq < Definition funext_type@{a b e} (A : Type@{a}) (B : A ->
Type@{b})
:= forall f g : (forall a, B a),
(forall x, eq@{e} (f x) (g x))
-> eq@{e} f g.
funext_type is defined

Coq < Section down.

Coq < Universes a b e e'.

Coq < Constraint e' < e.

Coq < Lemma funext_down {A B}
(H : @funext_type@{a b e} A B) : @funext_type@{a b e'} A B.
1 subgoal

A : Type@{Top.41}
B : A -> Type@{Top.42}
H : funext_type@{a b e} A B
============================
funext_type@{a b e'} A B

Coq < Proof.
1 subgoal

A : Type@{Top.41}
B : A -> Type@{Top.42}
H : funext_type@{a b e} A B
============================
funext_type@{a b e'} A B

Coq < exact H.
No more subgoals.

Coq < Defined.
funext_down is defined



29.4 Global and local universes
-------------------------------

Each universe is declared in a global or local environment before it
can be used. To ensure compatibility, every *global* universe is set
to be strictly greater than Set when it is introduced, while every
*local* (i.e. polymorphically quantified) universe is introduced as
greater or equal to Set.


29.5 Conversion and unification
-------------------------------

The semantics of conversion and unification have to be modified a
little to account for the new universe instance arguments to
polymorphic references. The semantics respect the fact that
definitions are transparent, so indistinguishable from their bodies
during conversion.

This is accomplished by changing one rule of unification, the first-
order approximation rule, which applies when two applicative terms
with the same head are compared. It tries to short-cut unfolding by
comparing the arguments directly. In case the constant is universe
polymorphic, we allow this rule to fire only when unifying the
universes results in instantiating a so-called flexible universe
variables (not given by the user). Similarly for conversion, if such
an equation of applicative terms fail due to a universe comparison not
being satisfied, the terms are unfolded. This change implies that
conversion and unification can have different unfolding behaviors on
the same development with universe polymorphism switched on or off.


29.6 Minimization
-----------------



Universe polymorphism with cumulativity tends to generate many useless
inclusion constraints in general. Typically at each application of a
polymorphic constant f, if an argument has expected type `Type@{i}`
and is given a term of type `Type@{j}`, a j ≤ i constraint will be
generated. It is however often the case that an equation j = i would
be more appropriate, when f’s universes are fresh for example.
Consider the following example:
Coq < Definition id0 := @pidentity nat 0.
id0 is defined

Coq < Print id0.
id0@{} = pidentity@{Set} 0
: nat
id0 is universe polymorphic

This definition is elaborated by minimizing the universe of id to
levelSet while the more general definition would keep the fresh level
i generated at the application of id and a constraint that Set ≤ i.
This minimization process is applied only to fresh universe variables.
It simply adds an equation between the variable and its lower bound if
it is an atomic universe (i.e. not an algebraic max() universe).

The option Unset Universe Minimization ToSet disallows minimization to
the sort Set and only collapses floating universes between themselves.


29.7 Explicit Universes
-----------------------

The syntax has been extended to allow users to explicitly bind names
to universes and explicitly instantiate polymorphic definitions.


29.7.1 Universe ident.
~~~~~~~~~~~~~~~~~~~~~~

In the monorphic case, this command declares a new global universe
namedident. It supports the polymorphic flag only in sections, meaning
the universe quantification will be discharged on each section
definition independently. One cannot mix polymorphic and monomorphic
declarations in the same section.


29.7.2 Constraint ident ord ident.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command declares a new constraint between named universes. The
order relation can be one of <, ≤ or =. If consistent, the constraint
is then enforced in the global environment. LikeUniverse, it can be
used with the Polymorphic prefix in sections only to declare
constraints discharged at section closing time. One cannot declare a
global constraint on polymorphic universes.


Error messages:


#. Undeclared universe ident.
#. Universe inconsistency



29.7.3 Polymorphic definitions
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

For polymorphic definitions, the declaration of (all) universe levels
introduced by a definition uses the following syntax:
Coq < Polymorphic Definition le@{i j} (A : Type@{i}) : Type@{j} := A.

Coq < Print le.
le@{i j} =
fun A : Type@{i} => A
: Type@{i} -> Type@{j}
(* i j |= i <= j
*)
le is universe polymorphic
Argument scope is [type_scope]

During refinement we find that j must be larger or equal than i, as we
are using A : Type@i <= Type@j, hence the generated constraint. At the
end of a definition or proof, we check that the only remaining
universes are the ones declared. In the term and in general in proof
mode, introduced universe names can be referred to in terms. Note that
local universe names shadow global universe names. During a proof, one
can use Show Universes to display the current context of universes.

Definitions can also be instantiated explicitly, giving their full
instance:
Coq < Check (pidentity@{Set}).
pidentity@{Set}
: ?A -> ?A
where
?A : [ |- Set]

Coq < Universes k l.

Coq < Check (le@{k l}).
le@{k l}
: Type@{k} -> Type@{l}
(* |= k <= l
*)

User-named universes and the anonymous universe implicitly attached to
an explicit Type are considered rigid for unification and are never
minimized. Flexible anonymous universes can be produced with an
underscore or by omitting the annotation to a polymorphic definition.
Coq < Check (fun x => x) : Type -> Type.
(fun x : Type@{Top.48} => x) : Type@{Top.48} -> Type@{Top.49}
: Type@{Top.48} -> Type@{Top.49}
(* Top.48 Top.49 |= Top.48 <= Top.49
*)

Coq < Check (fun x => x) : Type -> Type@{_}.
(fun x : Type@{Top.50} => x) : Type@{Top.50} -> Type@{Top.50}
: Type@{Top.50} -> Type@{Top.50}
(* Top.50 |= *)

Coq < Check le@{k _}.
le@{k k}
: Type@{k} -> Type@{k}

Coq < Check le.
le@{Top.53 Top.53}
: Type@{Top.53} -> Type@{Top.53}
(* Top.53 |= *)



29.7.4 Unset Strict Universe Declaration.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The command Unset Strict Universe Declaration allows one to freely use
identifiers for universes without declaring them first, with the
semantics that the first use declares it. In this mode, the universe
names are not associated with the definition or proof once it has been
defined. This is meant mainly for debugging purposes.



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
.. _29.1  General Presentation: :///home/steck/universes.html#sec879
.. _About Coq: :///about-coq
.. _CSS valid: http://jigsaw.w3.org/css-validator/
.. _Cover: :///home/steck/index.html
.. _4: :///home/steck/cic.html#Cic
.. _Table of contents: :///home/steck/toc.html
.. _Community: :///community
.. _29.7  Explicit Universes: :///home/steck/universes.html#sec886
.. _29.6  Minimization: :///home/steck/universes.html#sec885
.. _29.5  Conversion and unification: :///home/steck/universes.html#sec884
.. _29.4  Global and local universes: :///home/steck/universes.html#sec883
.. _Cumulative, NonCumulative: :///home/steck/universes.html#sec881
.. _Polymorphic, Monomorphic: :///home/steck/universes.html#sec880
.. _Commands: :///home/steck/command-index.html
.. _xhtml valid: http://validator.w3.org/
.. _Tactics: :///home/steck/tactic-index.html
.. _General: :///home/steck/general-index.html
.. _Options: :///home/steck/option-index.html
.. _The Coq Proof Assistant: :///
.. _Errors: :///home/steck/error-index.html
.. _Documentation: :///documentation
.. _webmaster: mailto:coq-www_@_inria.fr



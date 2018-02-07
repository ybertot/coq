

+ `Home`_
+ `About Coq`_
+ `Get Coq`_
+ `Documentation`_
+ `Community`_

` `_ `The Coq Proof Assistant`_


Chapter 20 Type Classes
=======================


+ `20.1 Class and Instance declarations`_
+ `20.2 Binding classes`_
+ `20.3 Parameterized Instances`_
+ `20.4 Sections and contexts`_
+ `20.5 Building hierarchies`_
+ `20.6 Summary of the commands`_


Matthieu Sozeau



This chapter presents a quick reference of the commands related to
type classes. For an actual introduction to type classes, there is a
description of the system [`136`_] and the literature on type classes
in Haskell which also applies.


20.1 Class and Instance declarations
------------------------------------



The syntax for class and instance declarations is the same as record
syntax of Coq:
Class Id (α 1 : τ 1 ) ⋯ (α n : τ n ) [: sort] := { f 1 : type 1 ; ⋮ f
m : type m }. Instance ident : Id term 1 ⋯ term n := { f 1 := term f 1
; ⋮ f m := term f m }.
The α i : τ i variables are called the *parameters* of the class and
the f k : type k are called the *methods*. Each class definition gives
rise to a corresponding record declaration and each instance is a
regular definition whose name is given by ident and type is an
instantiation of the record type.

We’ll use the following example class in the rest of the chapter:
Coq < Class EqDec (A : Type) := {
eqb : A -> A -> bool ;
eqb_leibniz : forall x y, eqb x y = true -> x = y }.

This class implements a boolean equality test which is compatible with
Leibniz equality on some type. An example implementation is:
Coq < Instance unit_EqDec : EqDec unit :=
{ eqb x y := true ;
eqb_leibniz x y H :=
match x, y return x = y with tt, tt => eq_refl tt end }.

If one does not give all the members in the Instance declaration, Coq
enters the proof-mode and the user is asked to build inhabitants of
the remaining fields, e.g.:
Coq < Instance eq_bool : EqDec bool :=
{ eqb x y := if x then y else negb y }.

Coq < Proof. intros x y H.
1 subgoal

============================
forall x y : bool, (if x then y else negb y) = true -> x = y
1 subgoal

x, y : bool
H : (if x then y else negb y) = true
============================
x = y

Coq < destruct x ; destruct y ; (discriminate || reflexivity).
No more subgoals.

Coq < Defined.
eq_bool is defined

One has to take care that the transparency of every field is
determined by the transparency of the Instance proof. One can use
alternatively the Program Instance variant which has richer facilities
for dealing with obligations.


20.2 Binding classes
--------------------

Once a type class is declared, one can use it in class binders:
Coq < Definition neqb {A} {eqa : EqDec A} (x y : A) := negb (eqb x y).
neqb is defined

When one calls a class method, a constraint is generated that is
satisfied only in contexts where the appropriate instances can be
found. In the example above, a constraint EqDec A is generated and
satisfied by eqa : EqDec A. In case no satisfying constraint can be
found, an error is raised:
Coq < Fail Definition neqb' (A : Type) (x y : A) := negb (eqb x y).
The command has indeed failed with message:
Unable to satisfy the following constraints:
In environment:
A : Type
x, y : A
?EqDec : "EqDec A"

The algorithm used to solve constraints is a variant of the eauto
tactic that does proof search with a set of lemmas (the instances). It
will use local hypotheses as well as declared lemmas in
thetypeclass_instances database. Hence the example can also be
written:
Coq < Definition neqb' A (eqa : EqDec A) (x y : A) := negb (eqb x y).
neqb' is defined

However, the generalizing binders should be used instead as they have
particular support for type classes:


+ They automatically set the maximally implicit status for type class
  arguments, making derived functions as easy to use as class methods.
  In the example above, A and eqa should be set maximally implicit.
+ They support implicit quantification on partially applied type
  classes (§`2.7.19`_). Any argument not given as part of a type class
  binder will be automatically generalized.
+ They also support implicit quantification on superclasses (§20.5.1)


Following the previous example, one can write:
Coq < Definition neqb_impl `{eqa : EqDec A} (x y : A) := negb (eqb x
y).
neqb_impl is defined

Here A is implicitly generalized, and the resulting function is
equivalent to the one above.


20.3 Parameterized Instances
----------------------------

One can declare parameterized instances as in Haskell simply by giving
the constraints as a binding context before the instance, e.g.:
Coq < Instance prod_eqb `(EA : EqDec A, EB : EqDec B) : EqDec (A * B)
:=
{ eqb x y := match x, y with
| (la, ra), (lb, rb) => andb (eqb la lb) (eqb ra rb)
end }.

These instances are used just as well as lemmas in the instance hint
database.


20.4 Sections and contexts
--------------------------

To ease the parametrization of developments by type classes, we
provide a new way to introduce variables into section contexts,
compatible with the implicit argument mechanism. The new command works
similarly to the Variables vernacular (see `1.3.1`_), except it
accepts any binding context as argument. For example:
Coq < Section EqDec_defs.

Coq < Context `{EA : EqDec A}.
A is declared
EA is declared
Coq < Global Instance option_eqb : EqDec (option A) :=
{ eqb x y := match x, y with
| Some x, Some y => eqb x y
| None, None => true
| _, _ => false
end }.
Coq < End EqDec_defs.

Coq < About option_eqb.
option_eqb : forall A : Type, EqDec A -> EqDec (option A)
Arguments A, EA are implicit and maximally inserted
Argument scopes are [type_scope _]
option_eqb is transparent
Expands to: Constant Top.option_eqb

Here the Global modifier redeclares the instance at the end of the
section, once it has been generalized by the context variables it
uses.


20.5 Building hierarchies
-------------------------


20.5.1 Superclasses
~~~~~~~~~~~~~~~~~~~

One can also parameterize classes by other classes, generating a
hierarchy of classes and superclasses. In the same way, we give the
superclasses as a binding context:
Coq < Class Ord `(E : EqDec A) :=
{ le : A -> A -> bool }.

Contrary to Haskell, we have no special syntax for superclasses, but
this declaration is morally equivalent to:

::

    Class `(E : EqDec A) => Ord A :=
      { le : A -> A -> bool }.


This declaration means that any instance of the Ord class must have an
instance of EqDec. The parameters of the subclass contain at least all
the parameters of its superclasses in their order of appearance (here
A is the only one). As we have seen, Ord is encoded as a record type
with two parameters: a type A and an E of type EqDec A. However, one
can still use it as if it had a single parameter inside generalizing
binders: the generalization of superclasses will be done
automatically.
Coq < Definition le_eqb `{Ord A} (x y : A) := andb (le x y) (le y x).

In some cases, to be able to specify sharing of structures, one may
want to give explicitly the superclasses. It is is possible to do it
directly in regular binders, and using the ! modifier in class
binders. For example:
Coq < Definition lt `{eqa : EqDec A, ! Ord eqa} (x y : A) :=
andb (le x y) (neqb x y).

The ! modifier switches the way a binder is parsed back to the regular
interpretation of Coq. In particular, it uses the implicit arguments
mechanism if available, as shown in the example.


20.5.2 Substructures
~~~~~~~~~~~~~~~~~~~~

Substructures are components of a class which are instances of a class
themselves. They often arise when using classes for logical
properties, e.g.:
Coq < Class Reflexive (A : Type) (R : relation A) :=
reflexivity : forall x, R x x.

Coq < Class Transitive (A : Type) (R : relation A) :=
transitivity : forall x y z, R x y -> R y z -> R x z.

This declares singleton classes for reflexive and transitive
relations, (see 1 for an explanation). These may be used as part of
other classes:
Coq < Class PreOrder (A : Type) (R : relation A) :=
{ PreOrder_Reflexive :> Reflexive A R ;
PreOrder_Transitive :> Transitive A R }.

The syntax :> indicates that each PreOrder can be seen as a Reflexive
relation. So each time a reflexive relation is needed, a preorder can
be used instead. This is very similar to the coercion mechanism of
Structure declarations. The implementation simply declares each
projection as an instance.

One can also declare existing objects or structure projections using
the Existing Instance command to achieve the same effect.


20.6 Summary of the commands
----------------------------


20.6.1 Class ident binder 1 … binder n : sort:= { field 1 ; …; field k
}.
~~



The Class command is used to declare a type class with parameters
binder 1 to binder n and fields field 1 tofield k .


Variants:


#. Class ident binder 1 …binder n : sort:= ident 1 : type 1 . This
   variant declares a *singleton* class whose only method isident 1 .
   This singleton class is a so-called definitional class, represented
   simply as a definition ident binder 1 …binder n := type 1 and whose
   instances are themselves objects of this type. Definitional classes
   are not wrapped inside records, and the trivial projection of an
   instance of such a class is convertible to the instance itself. This
   can be useful to make instances of existing objects easily and to
   reduce proof size by not inserting useless projections. The class
   constant itself is declared rigid during resolution so that the class
   abstraction is maintained.
#. Existing Class ident. This variant declares a class a posteriori
   from a constant or inductive definition. No methods or instances are
   defined.



20.6.2 Instance ident binder 1 …binder n :Class t 1 …t n [| priority]
:= { field 1 := b 1 ; …; field i := b i }
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~



The Instance command is used to declare a type class instance named
ident of the class *Class* with parameters t 1 to t n and fields b 1
to b i , where each field must be a declared field of the class.
Missing fields must be filled in interactive proof mode.

An arbitrary context of the form binder 1 …binder n can be put after
the name of the instance and before the colon to declare a
parameterized instance. An optional priority can be declared, 0 being
the highest priority as for auto hints. If the priority is not
specified, it defaults ton, the number of binders of the instance.


Variants:


#. Instance ident binder 1 …binder n : forall binder n+1 …binder m
   ,Class t 1 …t n [| priority] := term This syntax is used for
   declaration of singleton class instances or for directly giving an
   explicit term of typeforall binder n+1 …binder m , Class t 1 …t n .
   One need not even mention the unique field name for singleton classes.
#. Global Instance One can use the Global modifier on instances
   declared in a section so that their generalization is automatically
   redeclared after the section is closed.
#. Program Instance Switches the type-checking to Program (chapter
   `24`_) and uses the obligation mechanism to manage missing fields.
#. Declare Instance In a Module Type, this command states that a
   corresponding concrete instance should exist in any implementation of
   thisModule Type. This is similar to the distinction betweenParameter
   vs. Definition, or between Declare Module and Module.


Besides the Class and Instance vernacular commands, there are a few
other commands related to type classes.


20.6.3 Existing Instance ident [| priority]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~



This commands adds an arbitrary constant whose type ends with an
applied type class to the instance database with an optional priority.
It can be used for redeclaring instances at the end of sections, or
declaring structure projections as instances. This is almost
equivalent to Hint Resolveident : typeclass_instances.


Variants:


#. Existing Instances ident 1 …ident n [| priority] With this command,
   several existing instances can be declared at once.



20.6.4 Context binder 1 …binder n
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~



Declares variables according to the given binding context, which might
use implicit generalization (see 20.4).


20.6.5 typeclasses eauto
~~~~~~~~~~~~~~~~~~~~~~~~



The typeclasses eauto tactic uses a different resolution engine than
eauto and auto. The main differences are the following:


+ Contrary to eauto and auto, the resolution is done entirely in the
  new proof engine (as of Coq v8.6), meaning that backtracking is
  available among dependent subgoals, and shelving goals is supported.
  typeclasses eauto is a multi-goal tactic. It analyses the dependencies
  between subgoals to avoid backtracking on subgoals that are entirely
  independent.
+ When called with no arguments, typeclasses eauto uses
  thetypeclass_instances database by default (instead of core).
  Dependent subgoals are automatically shelved, and shelved goals can
  remain after resolution ends (following the behavior ofCoq 8.5).
  *Note: * As of Coq 8.6, all:once (typeclasses eauto) faithfully
  mimicks what happens during typeclass resolution when it is called
  during refinement/type-inference, except that *only* declared class
  subgoals are considered at the start of resolution during type
  inference, while “all” can select non-class subgoals as well. It might
  move to all:typeclasses eauto in future versions when the refinement
  engine will be able to backtrack.
+ When called with specific databases (e.g. with), typeclasses eauto
  allows shelved goals to remain at any point during search and treat
  typeclasses goals like any other.
+ The transparency information of databases is used consistently for
  all hints declared in them. It is always used when calling the
  unifier. When considering the local hypotheses, we use the transparent
  state of the first hint database given. Using an empty database
  (created with Create HintDb for example) with unfoldable variables and
  constants as the first argument of typeclasses eauto hence makes
  resolution with the local hypotheses use full conversion during
  unification.



Variants:


#. typeclasses eauto [num] *Warning:* The semantics for the limit num
   is different than for auto. By default, if no limit is given the
   search is unbounded. Contrary to auto, introduction steps (intro) are
   counted, which might result in larger limits being necessary when
   searching with typeclasses eauto than auto.
#. typeclasses eauto with ident 1 …ident n . This variant runs
   resolution with the given hint databases. It treats typeclass subgoals
   the same as other subgoals (no shelving of non-typeclass goals in
   particular).



20.6.6 autoapply term with ident
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~



The tactic autoapply applies a term using the transparency information
of the hint database ident, and does *no* typeclass resolution. This
can be used in Hint Extern’s for typeclass instances (in hint db
typeclass_instances) to allow backtracking on the typeclass subgoals
created by the lemma application, rather than doing type class
resolution locally at the hint application time.


20.6.7 Typeclasses Transparent, Opaque ident 1 …ident n
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~



This commands defines the transparency of ident 1 …ident n during type
class resolution. It is useful when some constants prevent some
unifications and make resolution fail. It is also useful to declare
constants which should never be unfolded during proof-search, like
fixpoints or anything which does not look like an abbreviation. This
can additionally speed up proof search as the typeclass map can be
indexed by such rigid constants (see `8.9.1`_). By default, all
constants and local variables are considered transparent. One should
take care not to make opaque any constant that is used to abbreviate a
type, like relation A := A -> A -> Prop.

This is equivalent to Hint Transparent,Opaque ident :
typeclass_instances.


20.6.8 Set Typeclasses Dependency Order
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~



This option (on by default since 8.6) respects the dependency order
between subgoals, meaning that subgoals which are depended on by other
subgoals come first, while the non-dependent subgoals were put before
the dependent ones previously (Coq v8.5 and below). This can result in
quite different performance behaviors of proof search.


20.6.9 Set Typeclasses Filtered Unification
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~



This option, available since Coq 8.6 and off by default, switches the
hint application procedure to a filter-then-unify strategy. To apply a
hint, we first check that the goal *matches* syntactically the
inferred or specified pattern of the hint, and only then try to
*unify* the goal with the conclusion of the hint. This can drastically
improve performance by calling unification less often, matching
syntactic patterns being very quick. This also provides more control
on the triggering of instances. For example, forcing a constant to
explicitely appear in the pattern will make it never apply on a goal
where there is a hole in that place.


20.6.10 Set Typeclasses Legacy Resolution
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

*Deprecated since 8.7*

This option (off by default) uses the 8.5 implementation of
resolution. Use for compatibility purposes only (porting and
debugging).


20.6.11 Set Typeclasses Module Eta
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

*Deprecated since 8.7*

This option allows eta-conversion for functions and records during
unification of type-classes. This option is unsupported since 8.6
withTypeclasses Filtered Unification set, but still affects the
default unification strategy, and the one used in Legacy Resolution
mode. It is *unset* by default. If Typeclasses Filtered Unification is
set, this has no effect and unification will find solutions up-to eta
conversion. Note however that syntactic pattern-matching is not up-to
eta.


20.6.12 Set Typeclasses Limit Intros
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~



This option (on by default) controls the ability to apply hints while
avoiding (functional) eta-expansions in the generated proof term. It
does so by allowing hints that conclude in a product to apply to a
goal with a matching product directly, avoiding an introduction.
*Warning:* this can be expensive as it requires rebuilding hint
clauses dynamically, and does not benefit from the invertibility
status of the product introduction rule, resulting in potentially more
expensive proof-search (i.e. more useless backtracking).


20.6.13 Set Typeclass Resolution After Apply
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

*Deprecated since 8.6*

This option (off by default in Coq 8.6 and 8.5) controls the
resolution of typeclass subgoals generated by the apply tactic.


20.6.14 Set Typeclass Resolution For Conversion
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~



This option (on by default) controls the use of typeclass resolution
when a unification problem cannot be solved during elaboration/type-
inference. With this option on, when a unification fails, typeclass
resolution is tried before launching unification once again.


20.6.15 Set Typeclasses Strict Resolution
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~



Typeclass declarations introduced when this option is set have a
stricter resolution behavior (the option is off by default). When
looking for unifications of a goal with an instance of this class, we
“freeze” all the existentials appearing in the goals, meaning that
they are considered rigid during unification and cannot be
instantiated.


20.6.16 Set Typeclasses Unique Solutions
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~



When a typeclass resolution is launched we ensure that it has a single
solution or fail. This ensures that the resolution is canonical, but
can make proof search much more expensive.


20.6.17 Set Typeclasses Unique Instances
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~



Typeclass declarations introduced when this option is set have a more
efficient resolution behavior (the option is off by default). When a
solution to the typeclass goal of this class is found, we never
backtrack on it, assuming that it is canonical.


20.6.18 Typeclasses eauto := [debug] [(dfs) | (bfs)] [ *depth*]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~



This command allows more global customization of the type class
resolution tactic. The semantics of the options are:


+ debug In debug mode, the trace of successfully applied tactics is
  printed.
+ dfs, bfs This sets the search strategy to depth-first search (the
  default) or breadth-first search.
+ *depth* This sets the depth limit of the search.



20.6.19 Set Typeclasses Debug [Verbosity num]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~



These options allow to see the resolution steps of typeclasses that
are performed during search. The Debug option is synonymous to Debug
Verbosity 1, and Debug Verbosity 2 provides more information (tried
tactics, shelving of goals, etc…).


20.6.20 Set Refine Instance Mode
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~



The option Refine Instance Mode allows to switch the behavior of
instance declarations made through the Instance command.


+ When it is on (the default), instances that have unsolved holes in
  their proof-term silently open the proof mode with the remaining
  obligations to prove.
+ When it is off, they fail with an error instead.




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
.. _About Coq: :///about-coq
.. _CSS valid: http://jigsaw.w3.org/css-validator/
.. _Cover: :///home/steck/index.html
.. _Errors: :///home/steck/error-index.html
.. _Table of contents: :///home/steck/toc.html
.. _Community: :///community
.. _8.9.1: :///home/steck/tactics.html#HintTransparency
.. _2.7.19: :///home/steck/gallina-ext.html#implicit-generalization
.. _Options: :///home/steck/option-index.html
.. _Commands: :///home/steck/command-index.html
.. _136: :///home/steck/biblio.html#sozeau08
.. _20.6  Summary of the commands
: :///home/steck/type-classes.html#TypeClassCommands
.. _24: :///home/steck/program.html#Program
.. _1.3.1: :///home/steck/gallina.html#Variable
.. _xhtml valid: http://validator.w3.org/
.. _Tactics: :///home/steck/tactic-index.html
.. _General: :///home/steck/general-index.html
.. _20.2  Binding classes: :///home/steck/type-classes.html#sec766
.. _20.3  Parameterized Instances: :///home/steck/type-classes.html#sec767
.. _20.1  Class and Instance declarations: :///home/steck/type-classes.html#sec765
.. _20.4  Sections and contexts: :///home/steck/type-classes.html#sec768
.. _20.5  Building hierarchies: :///home/steck/type-classes.html#sec769
.. _The Coq Proof Assistant: :///
.. _Documentation: :///documentation
.. _webmaster: mailto:coq-www_@_inria.fr



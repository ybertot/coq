

+ `Home`_
+ `About Coq`_
+ `Get Coq`_
+ `Documentation`_
+ `Community`_

` `_ `The Coq Proof Assistant`_


Chapter 19 Canonical Structures
===============================


+ `19.1 Notation overloading`_
+ `19.2 Hierarchy of structures`_


Assia Mahboubi and Enrico Tassi





This chapter explains the basics of Canonical Structure and how they
can be used to overload notations and build a hierarchy of algebraic
structures. The examples are taken from [`103`_]. We invite the
interested reader to refer to this paper for all the details that are
omitted here for brevity. The interested reader shall also find in
[`76`_] a detailed description of another, complementary, use of
Canonical Structures: advanced proof search. This latter papers also
presents many techniques one can employ to tune the inference of
Canonical Structures.


19.1 Notation overloading
-------------------------

We build an infix notation == for a comparison predicate. Such
notation will be overloaded, and its meaning will depend on the types
of the terms that are compared.
Coq < Module EQ.
Interactive Module EQ started

Coq < Record class (T : Type) := Class { cmp : T -> T -> Prop }.
class is defined
cmp is defined

Coq < Structure type := Pack { obj : Type; class_of : class obj }.
type is defined
obj is defined
class_of is defined

Coq < Definition op (e : type) : obj e -> obj e -> Prop :=
let 'Pack _ (Class _ the_cmp) := e in the_cmp.
op is defined

Coq < Check op.
op
: forall e : type, obj e -> obj e -> Prop

Coq < Arguments op {e} x y : simpl never.

Coq < Arguments Class {T} cmp.

Coq < Module theory.
Interactive Module theory started

Coq < Notation "x == y" := (op x y) (at level 70).

Coq < End theory.
Module theory is defined

Coq < End EQ.
Module EQ is defined

We use Coq modules as name spaces. This allows us to follow the same
pattern and naming convention for the rest of the chapter. The base
name space contains the definitions of the algebraic structure. To
keep the example small, the algebraic structure EQ.type we are
defining is very simplistic, and characterizes terms on which a binary
relation is defined, without requiring such relation to validate any
property. The inner theory module contains the overloaded notation ==
and will eventually contain lemmas holding on all the instances of the
algebraic structure (in this case there are no lemmas).

Note that in practice the user may want to declare EQ.obj as a
coercion, but we will not do that here.

The following line tests that, when we assume a type e that is in
theEQ class, then we can relates two of its objects with ==.
Coq < Import EQ.theory.

Coq < Check forall (e : EQ.type) (a b : EQ.obj e), a == b.
forall (e : EQ.type) (a b : EQ.obj e), a == b
: Prop

Still, no concrete type is in the EQ class. We amend that by equipping
nat with a comparison relation.
Coq < Fail Check 3 == 3.
The command has indeed failed with message:
The term "3" has type "nat" while it is expected to have type
"EQ.obj ?e".

Coq < Definition nat_eq (x y : nat) := nat_compare x y = Eq.
nat_eq is defined

Coq < Definition nat_EQcl : EQ.class nat := EQ.Class nat_eq.
nat_EQcl is defined

Coq < Canonical Structure nat_EQty : EQ.type := EQ.Pack nat nat_EQcl.
nat_EQty is defined

Coq < Check 3 == 3.
3 == 3
: Prop

Coq < Eval compute in 3 == 4.
= Lt = Eq
: Prop

This last test shows that Coq is now not only able to typecheck 3==3,
but also that the infix relation was bound to the nat_eq relation.
This relation is selected whenever == is used on terms of type nat.
This can be read in the line declaring the canonical structure
nat_EQty, where the first argument to Pack is the key and its second
argument a group of canonical values associated to the key. In this
case we associate to nat only one canonical value (since its class,
nat_EQcl has just one member). The use of the projection op requires
its argument to be in the class EQ, and uses such a member (function)
to actually compare its arguments.

Similarly, we could equip any other type with a comparison relation,
and use the == notation on terms of this type.


19.1.1 Derived Canonical Structures
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

We know how to use == on base types, like nat, bool, Z. Here we show
how to deal with type constructors, i.e. how to make the following
example work:
Coq < Fail Check forall (e : EQ.type) (a b : EQ.obj e), (a,b) ==
(a,b).
The command has indeed failed with message:
In environment
e : EQ.type
a : EQ.obj e
b : EQ.obj e
The term "(a, b)" has type "(EQ.obj e * EQ.obj e)%type"
while it is expected to have type "EQ.obj ?e".

The error message is telling that Coq has no idea on how to compare
pairs of objects. The following construction is telling Coq exactly
how to do that.
Coq < Definition pair_eq (e1 e2 : EQ.type) (x y : EQ.obj e1 * EQ.obj
e2) :=
fst x == fst y /\ snd x == snd y.
pair_eq is defined

Coq < Definition pair_EQcl e1 e2 := EQ.Class (pair_eq e1 e2).
pair_EQcl is defined

Coq < Canonical Structure pair_EQty (e1 e2 : EQ.type) : EQ.type :=
EQ.Pack (EQ.obj e1 * EQ.obj e2) (pair_EQcl e1 e2).
pair_EQty is defined

Coq < Check forall (e : EQ.type) (a b : EQ.obj e), (a,b) == (a,b).
forall (e : EQ.type) (a b : EQ.obj e), (a, b) == (a, b)
: Prop

Coq < Check forall n m : nat, (3,4) == (n,m).
forall n m : nat, (3, 4) == (n, m)
: Prop

Thanks to the pair_EQty declaration, Coq is able to build a comparison
relation for pairs whenever it is able to build a comparison relation
for each component of the pair. The declaration associates to the key*
(the type constructor of pairs) the canonical comparison
relationpair_eq whenever the type constructor * is applied to two
types being themselves in the EQ class.


19.2 Hierarchy of structures
----------------------------

To get to an interesting example we need another base class to be
available. We choose the class of types that are equipped with an
order relation, to which we associate the infix <= notation.
Coq < Module LE.
Interactive Module LE started

Coq < Record class T := Class { cmp : T -> T -> Prop }.
class is defined
cmp is defined

Coq < Structure type := Pack { obj : Type; class_of : class obj }.
type is defined
obj is defined
class_of is defined

Coq < Definition op (e : type) : obj e -> obj e -> Prop :=
let 'Pack _ (Class _ f) := e in f.
op is defined

Coq < Arguments op {_} x y : simpl never.

Coq < Arguments Class {T} cmp.

Coq < Module theory.
Interactive Module theory started

Coq < Notation "x <= y" := (op x y) (at level 70).

Coq < End theory.
Module theory is defined

Coq < End LE.
Module LE is defined

As before we register a canonical LE class for nat.
Coq < Import LE.theory.

Coq < Definition nat_le x y := nat_compare x y <> Gt.
nat_le is defined

Coq < Definition nat_LEcl : LE.class nat := LE.Class nat_le.
nat_LEcl is defined

Coq < Canonical Structure nat_LEty : LE.type := LE.Pack nat nat_LEcl.
nat_LEty is defined

And we enable Coq to relate pair of terms with <=.
Coq < Definition pair_le e1 e2 (x y : LE.obj e1 * LE.obj e2) :=
fst x <= fst y /\ snd x <= snd y.
pair_le is defined

Coq < Definition pair_LEcl e1 e2 := LE.Class (pair_le e1 e2).
pair_LEcl is defined

Coq < Canonical Structure pair_LEty (e1 e2 : LE.type) : LE.type :=
LE.Pack (LE.obj e1 * LE.obj e2) (pair_LEcl e1 e2).
pair_LEty is defined

Coq < Check (3,4,5) <= (3,4,5).
(3, 4, 5) <= (3, 4, 5)
: Prop

At the current stage we can use == and <= on concrete types, like
tuples of natural numbers, but we can’t develop an algebraic theory
over the types that are equipped with both relations.
Coq < Check 2 <= 3 /\ 2 == 2.
2 <= 3 /\ 2 == 2
: Prop

Coq < Fail Check forall (e : EQ.type) (x y : EQ.obj e), x <= y -> y <=
x -> x == y.
The command has indeed failed with message:
In environment
e : EQ.type
x : EQ.obj e
y : EQ.obj e
The term "x" has type "EQ.obj e" while it is expected to have type
"LE.obj ?e".

Coq < Fail Check forall (e : LE.type) (x y : LE.obj e), x <= y -> y <=
x -> x == y.
The command has indeed failed with message:
In environment
e : LE.type
x : LE.obj e
y : LE.obj e
The term "x" has type "LE.obj e" while it is expected to have type
"EQ.obj ?e".

We need to define a new class that inherits from both EQ and LE.
Coq < Module LEQ.
Interactive Module LEQ started

Coq < Record mixin (e : EQ.type) (le : EQ.obj e -> EQ.obj e -> Prop)
:=
Mixin { compat : forall x y : EQ.obj e, le x y /\ le y x <-> x == y }.
mixin is defined
compat is defined

Coq < Record class T := Class {
EQ_class : EQ.class T;
LE_class : LE.class T;
extra : mixin (EQ.Pack T EQ_class) (LE.cmp T LE_class) }.
class is defined
EQ_class is defined
LE_class is defined
extra is defined

Coq < Structure type := _Pack { obj : Type; class_of : class obj }.
type is defined
obj is defined
class_of is defined

Coq < Arguments Mixin {e le} _.

Coq < Arguments Class {T} _ _ _.

The mixin component of the LEQ class contains all the extra content we
are adding to EQ and LE. In particular it contains the requirement
that the two relations we are combining are compatible.

Unfortunately there is still an obstacle to developing the algebraic
theory of this new class.
Coq < Module theory.
Interactive Module theory started

Coq < Fail Check forall (le : type) (n m : obj le), n <= m -> n <= m
-> n == m.
The command has indeed failed with message:
In environment
le : type
n : obj le
m : obj le
The term "n" has type "obj le" while it is expected to have type
"LE.obj ?e".

The problem is that the two classes LE and LEQ are not yet related by
a subclass relation. In other words Coq does not see that an object of
the LEQ class is also an object of the LE class.

The following two constructions tell Coq how to canonically build the
LE.type and EQ.type structure given an LEQ.type structure on the same
type.
Coq < Definition to_EQ (e : type) : EQ.type :=
EQ.Pack (obj e) (EQ_class _ (class_of e)).
to_EQ is defined

Coq < Canonical Structure to_EQ.

Coq < Definition to_LE (e : type) : LE.type :=
LE.Pack (obj e) (LE_class _ (class_of e)).
to_LE is defined

Coq < Canonical Structure to_LE.

We can now formulate out first theorem on the objects of the LEQ
structure.
Coq < Lemma lele_eq (e : type) (x y : obj e) : x <= y -> y <= x -> x
== y.
1 subgoal

e : type
x, y : obj e
============================
x <= y -> y <= x -> x == y

Coq < now intros; apply (compat _ _ (extra _ (class_of e)) x y);
split. Qed.
No more subgoals.
lele_eq is defined

Coq < Arguments lele_eq {e} x y _ _.

Coq < End theory.
Module theory is defined

Coq < End LEQ.
Module LEQ is defined

Coq < Import LEQ.theory.

Coq < Check lele_eq.
lele_eq
: forall x y : LEQ.obj ?e, x <= y -> y <= x -> x == y
where
?e : [ |- LEQ.type]

Of course one would like to apply results proved in the algebraic
setting to any concrete instate of the algebraic structure.
Coq < Example test_algebraic (n m : nat) : n <= m -> m <= n -> n == m.
1 subgoal

n, m : nat
============================
n <= m -> m <= n -> n == m

Coq < Fail apply (lele_eq n m). Abort.
The command has indeed failed with message:
In environment
n, m : nat
The term "n" has type "nat" while it is expected to have type
"LEQ.obj ?e".
1 subgoal

n, m : nat
============================
n <= m -> m <= n -> n == m

Coq < Example test_algebraic2 (l1 l2 : LEQ.type) (n m : LEQ.obj l1 *
LEQ.obj l2) :
n <= m -> m <= n -> n == m.
1 subgoal

l1, l2 : LEQ.type
n, m : LEQ.obj l1 * LEQ.obj l2
============================
n <= m -> m <= n -> n == m

Coq < Fail apply (lele_eq n m). Abort.
The command has indeed failed with message:
In environment
l1, l2 : LEQ.type
n, m : LEQ.obj l1 * LEQ.obj l2
The term "n" has type "(LEQ.obj l1 * LEQ.obj l2)%type"
while it is expected to have type "LEQ.obj ?e".
1 subgoal

l1, l2 : LEQ.type
n, m : LEQ.obj l1 * LEQ.obj l2
============================
n <= m -> m <= n -> n == m

Again one has to tell Coq that the type nat is in the LEQ class, and
how the type constructor * interacts with the LEQ class. In the
following proofs are omitted for brevity.
Coq < Lemma nat_LEQ_compat (n m : nat) : n <= m /\ m <= n <-> n == m.
1 subgoal

n, m : nat
============================
n <= m /\ m <= n <-> n == m
Coq < Definition nat_LEQmx := LEQ.Mixin nat_LEQ_compat.
nat_LEQmx is defined

Coq < Lemma pair_LEQ_compat (l1 l2 : LEQ.type) (n m : LEQ.obj l1 *
LEQ.obj l2) :
n <= m /\ m <= n <-> n == m.
1 subgoal

l1, l2 : LEQ.type
n, m : LEQ.obj l1 * LEQ.obj l2
============================
n <= m /\ m <= n <-> n == m
Coq < Definition pair_LEQmx l1 l2 := LEQ.Mixin (pair_LEQ_compat l1
l2).
pair_LEQmx is defined

The following script registers an LEQ class for nat and for the type
constructor *. It also tests that they work as expected.

Unfortunately, these declarations are very verbose. In the following
subsection we show how to make these declaration more compact.
Coq < Module Add_instance_attempt.
Interactive Module Add_instance_attempt started

Coq < Canonical Structure nat_LEQty : LEQ.type :=
LEQ._Pack nat (LEQ.Class nat_EQcl nat_LEcl nat_LEQmx).
nat_LEQty is defined

Coq < Canonical Structure pair_LEQty (l1 l2 : LEQ.type) : LEQ.type :=
LEQ._Pack (LEQ.obj l1 * LEQ.obj l2)
(LEQ.Class
(EQ.class_of (pair_EQty (to_EQ l1) (to_EQ l2)))
(LE.class_of (pair_LEty (to_LE l1) (to_LE l2)))
(pair_LEQmx l1 l2)).
pair_LEQty is defined
Toplevel input, characters 2-263:
> Canonical Structure pair_LEQty (l1 l2 : LEQ.type) : LEQ.type :=
> LEQ._Pack (LEQ.obj l1 * LEQ.obj l2)
> (LEQ.Class
> (EQ.class_of (pair_EQty (to_EQ l1) (to_EQ l2)))
> (LE.class_of (pair_LEty (to_LE l1) (to_LE l2)))
> (pair_LEQmx l1 l2)).
Warning: Ignoring canonical projection to LEQ.Class by LEQ.class_of in
pair_LEQty: redundant with nat_LEQty
[redundant-canonical-projection,typechecker]

Coq < Example test_algebraic (n m : nat) : n <= m -> m <= n -> n == m.
1 subgoal

n, m : nat
============================
n <= m -> m <= n -> n == m

Coq < now apply (lele_eq n m). Qed.
No more subgoals.
test_algebraic is defined

Coq < Example test_algebraic2 (n m : nat * nat) : n <= m -> m <= n ->
n == m.
1 subgoal

n, m : nat * nat
============================
n <= m -> m <= n -> n == m

Coq < now apply (lele_eq n m). Qed.
No more subgoals.
test_algebraic2 is defined

Coq < End Add_instance_attempt.
Module Add_instance_attempt is defined

Note that no direct proof of n <= m -> m <= n -> n == m is provided by
the user for n and m of type nat * nat. What the user provides is a
proof of this statement for n and m of type nat and a proof that the
pair constructor preserves this property. The combination of these two
facts is a simple form of proof search that Coq performs automatically
while inferring canonical structures.


19.2.1 Compact declaration of Canonical Structures
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

We need some infrastructure for that.
Coq < Require Import Strings.String.

Coq < Module infrastructure.
Interactive Module infrastructure started

Coq < Inductive phantom {T : Type} (t : T) : Type := Phantom.
phantom is defined
phantom_rect is defined
phantom_ind is defined
phantom_rec is defined

Coq < Definition unify {T1 T2} (t1 : T1) (t2 : T2) (s : option string)
:=
phantom t1 -> phantom t2.
unify is defined

Coq < Definition id {T} {t : T} (x : phantom t) := x.
id is defined

Coq < Notation "[find v | t1 ~ t2 ] p" := (fun v (_ : unify t1 t2
None) => p)
(at level 50, v ident, only parsing).

Coq < Notation "[find v | t1 ~ t2 | s ] p" := (fun v (_ : unify t1 t2
(Some s)) => p)
(at level 50, v ident, only parsing).

Coq < Notation "'Error : t : s" := (unify _ t (Some s))
(at level 50, format "''Error' : t : s").

Coq < Open Scope string_scope.

Coq < End infrastructure.
Module infrastructure is defined

To explain the notation [find v | t1 ~t2] let us pick one of its
instances: [find e | EQ.obj e ~T | "is not an EQ.type" ]. It should be
read as: “find a class e such that its objects have type T or fail
with message "T is not an EQ.type"”.

The other utilities are used to ask Coq to solve a specific
unification problem, that will in turn require the inference of some
canonical structures. They are explained in mode details in [`103`_].

We now have all we need to create a compact “packager” to declare
instances of the LEQ class.
Coq < Import infrastructure.

Coq < Definition packager T e0 le0 (m0 : LEQ.mixin e0 le0) :=
[find e | EQ.obj e ~ T | "is not an EQ.type" ]
[find o | LE.obj o ~ T | "is not an LE.type" ]
[find ce | EQ.class_of e ~ ce ]
[find co | LE.class_of o ~ co ]
[find m | m ~ m0 | "is not the right mixin" ]
LEQ._Pack T (LEQ.Class ce co m).
packager is defined

Coq < Notation Pack T m := (packager T _ _ m _ id _ id _ id _ id _
id).

The object Pack takes a type T (the key) and a mixin m. It infers all
the other pieces of the class LEQ and declares them as canonical
values associated to the T key. All in all, the only new piece of
information we add in the LEQ class is the mixin, all the rest is
already canonical for T and hence can be inferred by Coq.

Pack is a notation, hence it is not type checked at the time of its
declaration. It will be type checked when it is used, an in that caseT
is going to be a concrete type. The odd arguments _ and id we pass to
the packager represent respectively the classes to be inferred (like
e, o, etc) and a token (id) to force their inference. Again, for all
the details the reader can refer to [`103`_].

The declaration of canonical instances can now be way more compact:
Coq < Canonical Structure nat_LEQty := Eval hnf in Pack nat nat_LEQmx.
nat_LEQty is defined

Coq < Canonical Structure pair_LEQty (l1 l2 : LEQ.type) :=
Eval hnf in Pack (LEQ.obj l1 * LEQ.obj l2) (pair_LEQmx l1 l2).
pair_LEQty is defined
Toplevel input, characters 0-117:
> Canonical Structure pair_LEQty (l1 l2 : LEQ.type) :=
> Eval hnf in Pack (LEQ.obj l1 * LEQ.obj l2) (pair_LEQmx l1 l2).
Warning: Ignoring canonical projection to LEQ.Class by LEQ.class_of in
pair_LEQty: redundant with nat_LEQty
[redundant-canonical-projection,typechecker]

Error messages are also quite intelligible (if one skips to the end of
the message).
Coq < Fail Canonical Structure err := Eval hnf in Pack bool nat_LEQmx.
The command has indeed failed with message:
The term "id" has type "phantom (EQ.obj ?e) -> phantom (EQ.obj ?e)"
while it is expected to have type
"'Error : bool : "is not an EQ.type"".



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
.. _19.2  Hierarchy of structures: :///home/steck/canonical-structures.html#sec762
.. _76: :///home/steck/biblio.html#CSlessadhoc
.. _About Coq: :///about-coq
.. _Errors: :///home/steck/error-index.html
.. _The Coq Proof Assistant: :///
.. _103: :///home/steck/biblio.html#CSwcu
.. _Cover: :///home/steck/index.html
.. _General: :///home/steck/general-index.html
.. _19.1  Notation overloading: :///home/steck/canonical-structures.html#sec760
.. _CSS valid: http://jigsaw.w3.org/css-validator/
.. _Documentation: :///documentation
.. _Options: :///home/steck/option-index.html
.. _xhtml valid: http://validator.w3.org/
.. _Table of contents: :///home/steck/toc.html
.. _Community: :///community
.. _webmaster: mailto:coq-www_@_inria.fr
.. _Tactics: :///home/steck/tactic-index.html



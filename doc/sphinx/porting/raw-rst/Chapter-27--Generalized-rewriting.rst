

+ `Home`_
+ `About Coq`_
+ `Get Coq`_
+ `Documentation`_
+ `Community`_

` `_ `The Coq Proof Assistant`_


Chapter 27 Generalized rewriting
================================


+ `27.1 Introduction to generalized rewriting`_
+ `27.2 Commands and tactics`_
+ `27.3 Extensions`_
+ `27.4 Strategies for rewriting`_


Matthieu Sozeau



This chapter presents the extension of several equality related
tactics to work over user-defined structures (called setoids) that are
equipped with ad-hoc equivalence relations meant to behave as
equalities. Actually, the tactics have also been generalized to
relations weaker then equivalences (e.g. rewriting systems). The
toolbox also extends the automatic rewriting capabilities of the
system, allowing the specification of custom strategies for rewriting.

This documentation is adapted from the previous setoid documentation
by Claudio Sacerdoti Coen (based on previous work by Clément Renard).
The new implementation is a drop-in replacement for the old one, 1
hence most of the documentation still applies.

The work is a complete rewrite of the previous implementation, based
on the type class infrastructure. It also improves on and generalizes
the previous implementation in several ways:


+ User-extensible algorithm. The algorithm is separated in two parts:
  generations of the rewriting constraints (done in ML) and solving of
  these constraints using type class resolution. As type class
  resolution is extensible using tactics, this allows users to define
  general ways to solve morphism constraints.
+ Sub-relations. An example extension to the base algorithm is the
  ability to define one relation as a subrelation of another so that
  morphism declarations on one relation can be used automatically for
  the other. This is done purely using tactics and type class search.
+ Rewriting under binders. It is possible to rewrite under binders in
  the new implementation, if one provides the proper morphisms. Again,
  most of the work is handled in the tactics.
+ First-class morphisms and signatures. Signatures and morphisms are
  ordinary Coq terms, hence they can be manipulated inside Coq, put
  inside structures and lemmas about them can be proved inside the
  system. Higher-order morphisms are also allowed.
+ Performance. The implementation is based on a depth-first search for
  the first solution to a set of constraints which can be as fast as
  linear in the size of the term, and the size of the proof term is
  linear in the size of the original term. Besides, the extensibility
  allows the user to customize the proof search if necessary.



27.1 Introduction to generalized rewriting
------------------------------------------


27.1.1 Relations and morphisms
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

A parametric *relation* R is any term of typeforall (x 1 :T 1 ) …(x n
:T n ), relation A. The expression A, which depends on x 1 …x n , is
called the *carrier* of the relation and R is said to be a relation
over A; the list x 1 ,…,x n is the (possibly empty) list of parameters
of the relation.
Example 1 (Parametric relation) * It is possible to implement finite
sets of elements of type * *A* * as unordered list of elements of type
* *A* *. The function* *set_eq: forall (A: Type), relation (list A)* *
satisfied by two lists with the same elements is a parametric relation
over * *(list A)* * with one parameter * *A* *. The type of * *set_eq*
* is convertible with* *forall (A: Type), list A -> list A -> Prop*
*.*
An *instance* of a parametric relation R with n parameters is any term
(R t 1 …t n ).

Let R be a relation over A with n parameters. A term is a parametric
proof of reflexivity for R if it has typeforall (x 1 :T 1 ) …(x n :T n
), reflexive (R x 1 …x n ). Similar definitions are given for
parametric proofs of symmetry and transitivity.
Example 2 (Parametric relation (cont.)) * The * *set_eq* * relation of
the previous example can be proved to be reflexive, symmetric and
transitive.*
A parametric unary function f of typeforall (x 1 :T 1 ) …(x n :T n ),
A 1 -> A 2 covariantly respects two parametric relation instances R 1
and R 2 if, whenever x, y satisfy R 1 x y, their images (f x) and (f
y) satisfy R 2 (f x) (f y) . An f that respects its input and output
relations will be called a unary covariant *morphism*. We can also say
that f is a monotone function with respect to R 1 and R 2 . The
sequence x 1 ,… x n represents the parameters of the morphism.

Let R 1 and R 2 be two parametric relations. The *signature* of a
parametric morphism of typeforall (x 1 :T 1 ) …(x n :T n ), A 1 -> A 2
that covariantly respects two instances I R 1 and I R 2 of R 1 and R 2
is written I R 1 ++> I R 2 . Notice that the special arrow ++>, which
reminds the reader of covariance, is placed between the two relation
instances, not between the two carriers. The signature relation
instances and morphism will be typed in a context introducing
variables for the parameters.

The previous definitions are extended straightforwardly to n-ary
morphisms, that are required to be simultaneously monotone on every
argument.

Morphisms can also be contravariant in one or more of their arguments.
A morphism is contravariant on an argument associated to the relation
instanceR if it is covariant on the same argument when the inverse
relationR −1 (inverse R in Coq) is considered. The special arrow -->
is used in signatures for contravariant morphisms.

Functions having arguments related by symmetric relations instances
are both covariant and contravariant in those arguments. The special
arrow==> is used in signatures for morphisms that are both covariant
and contravariant.

An instance of a parametric morphism f with n parameters is any termf
t 1 …t n .
Example 3 (Morphisms) * Continuing the previous example, let* *union:
forall (A: Type), list A -> list A -> list A* * perform the union of
two sets by appending one list to the other. * *union* * is a binary
morphism parametric over * *A* * that respects the relation instance*
*(set_eq A)* *. The latter condition is proved by showing* *forall (A:
Type) (S1 S1’ S2 S2’: list A), set_eq A S1 S1’ -> set_eq A S2 S2’ ->
set_eq A (union A S1 S2) (union A S1’ S2’)* *.*
*The signature of the function * *union A* * is* *set_eq A ==> set_eq
A ==> set_eq A* * for all * *A* *.*
Example 4 (Contravariant morphism) * The division function * *Rdiv: R
-> R -> R* * is a morphism of signature * *le ++> le --> le* * where *
*le* * is the usual order relation over real numbers. Notice that
division is covariant in its first argument and contravariant in its
second argument.*
Leibniz equality is a relation and every function is a morphism that
respects Leibniz equality. Unfortunately, Leibniz equality is not
always the intended equality for a given structure.

In the next section we will describe the commands to register terms as
parametric relations and morphisms. Several tactics that deal with
equality in Coq can also work with the registered relations. The exact
list of tactic will be given in Sect. 27.2.2. For instance, the tactic
reflexivity can be used to close a goal R n n wheneverR is an instance
of a registered reflexive relation. However, the tactics that replace
in a context C[] one term with another one related by R must verify
that C[] is a morphism that respects the intended relation. Currently
the verification consists in checking whether C[] is a syntactic
composition of morphism instances that respects some obvious
compatibility constraints.
Example 5 (Rewriting) * Continuing the previous examples, suppose that
the user must prove* *set_eq int (union int (union int S1 S2) S2) (f
S1 S2)* * under the hypothesis * *H: set_eq int S2 (@nil int)* *. It
is possible to use the * *rewrite* * tactic to replace the first two
occurrences of* *S2* * with * *@nil int* * in the goal since the
context* *set_eq int (union int (union int S1 nil) nil) (f S1 S2)* *,
being a composition of morphisms instances, is a morphism. However the
tactic will fail replacing the third occurrence of * *S2* * unless *
*f* * has also been declared as a morphism.*


27.1.2 Adding new relations and morphisms
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

A parametric relationAeq: forall (y 1 : β ! …y m : β m ), relation (A
t 1 …t n ) over(A : α i -> …α n -> Type) can be declared with the
following command:


Add Parametric Relation (x 1 : T 1 ) …(x n : T k ) :(A t 1 …t n ) (Aeq
t′ 1 …t′ m )
[reflexivity proved by refl]
[symmetry proved by sym]
[transitivity proved by trans]
as id.
after having required the Setoid module with theRequire Setoid
command.

The identifier id gives a unique name to the morphism and it is used
by the command to generate fresh names for automatically provided
lemmas used internally.

Notice that the carrier and relation parameters may refer to the
context of variables introduced at the beginning of the declaration,
but the instances need not be made only of variables. Also notice that
A is *not* required to be a term having the same parameters as Aeq,
although that is often the case in practice (this departs from the
previous implementation).

In case the carrier and relations are not parametric, one can use the
command Add Relation instead, whose syntax is the same except there is
no local context.

The proofs of reflexivity, symmetry and transitivity can be omitted if
the relation is not an equivalence relation. The proofs must be
instances of the corresponding relation definitions: e.g. the proof of
reflexivity must have a type convertible to reflexive (A t 1 …t n )
(Aeq t′ 1 …t′ n ). Each proof may refer to the introduced variables as
well.
Example 6 (Parametric relation) * For Leibniz equality, we may
declare:* *Add Parametric Relation (A : Type) :* * * *A (@eq A)* *
* *[* *reflexivity proved by* * * *@refl_equal A* *]* *
…*
Some tactics (reflexivity, symmetry, transitivity) work only on
relations that respect the expected properties. The remaining tactics
(replace, rewrite and derived tactics such asautorewrite) do not
require any properties over the relation. However, they are able to
replace terms with related ones only in contexts that are syntactic
compositions of parametric morphism instances declared with the
following command.


Add Parametric Morphism (x 1 : T 1 ) …(x k : T k ) : (f t 1 …t n )
with signature sig
as id.
Proof
…
Qed
The command declares f as a parametric morphism of signaturesig. The
identifier id gives a unique name to the morphism and it is used as
the base name of the type class instance definition and as the name of
the lemma that proves the well-definedness of the morphism. The
parameters of the morphism as well as the signature may refer to the
context of variables. The command asks the user to prove interactively
that f respects the relations identified from the signature.
Example 7 * We start the example by assuming a small theory over
homogeneous sets and we declare set equality as a parametric
equivalence relation and union of two sets as a parametric morphism.*
** ** *Coq * *<* * Require Export Setoid.* *

* *Coq * *<* * Require Export Relation* *_* *Definitions.* *

* *Coq * *<* * Set Implicit Arguments.* *

* *Coq * *<* * Parameter set: Type -* *>* * Type.* *

* *Coq * *<* * Parameter empty: forall A, set A.* *

* *Coq * *<* * Parameter eq* *_* *set: forall A, set A -* *>* * set A
-* *>* * Prop.* *

* *Coq * *<* * Parameter union: forall A, set A -* *>* * set A -* *>*
* set A.* *

* *Coq * *<* * Axiom eq* *_* *set* *_* *refl: forall A, reflexive *
*_* * (eq* *_* *set (A:=A)).* *

* *Coq * *<* * Axiom eq* *_* *set* *_* *sym: forall A, symmetric * *_*
* (eq* *_* *set (A:=A)).* *

* *Coq * *<* * Axiom eq* *_* *set* *_* *trans: forall A, transitive *
*_* * (eq* *_* *set (A:=A)).* *

* *Coq * *<* * Axiom empty* *_* *neutral: forall A (S: set A), eq* *_*
*set (union S (empty A)) S.* *

* *Coq * *<* * Axiom union* *_* *compat:* *
* * forall (A : Type),* *
* * forall x x* *'* * : set A, eq* *_* *set x x* *'* * -* *>* *
* * forall y y* *'* * : set A, eq* *_* *set y y* *'* * -* *>* *
* * eq* *_* *set (union x y) (union x* *'* * y* *'* *).* *

* *Coq * *<* * Add Parametric Relation A : (set A) (@eq* *_* *set A)*
*
* * reflexivity proved by (eq* *_* *set* *_* *refl (A:=A))* *
* * symmetry proved by (eq* *_* *set* *_* *sym (A:=A))* *
* * transitivity proved by (eq* *_* *set* *_* *trans (A:=A))* *
* * as eq* *_* *set* *_* *rel.* *

* *Coq * *<* * Add Parametric Morphism A : (@union A) with * *
* * signature (@eq* *_* *set A) ==* *>* * (@eq* *_* *set A) ==* *>* *
(@eq* *_* *set A) as union* *_* *mor.* *

* *Coq * *<* * Proof. exact (@union* *_* *compat A). Qed.* *
* **
It is possible to reduce the burden of specifying parameters using
(maximally inserted) implicit arguments. If A is always set as
maximally implicit in the previous example, one can write:
Coq < Add Parametric Relation A : (set A) eq_set
reflexivity proved by eq_set_refl
symmetry proved by eq_set_sym
transitivity proved by eq_set_trans
as eq_set_rel.

Coq < Add Parametric Morphism A : (@union A) with
signature eq_set ==> eq_set ==> eq_set as union_mor.

Coq < Proof. exact (@union_compat A). Qed.

We proceed now by proving a simple lemma performing a rewrite step and
then applying reflexivity, as we would do working with Leibniz
equality. Both tactic applications are accepted since the required
properties over eq_set andunion can be established from the two
declarations above.
Coq < Goal forall (S: set nat),
eq_set (union (union S empty) S) (union S S).

Coq < Proof. intros. rewrite empty_neutral. reflexivity. Qed.

The tables of relations and morphisms are managed by the type class
instance mechanism. The behavior on section close is to generalize the
instances by the variables of the section (and possibly hypotheses
used in the proofs of instance declarations) but not to export them in
the rest of the development for proof search. One can use theExisting
Instance command to do so outside the section, using the name of the
declared morphism suffixed by _Morphism, or use the Global modifier
for the corresponding class instance declaration (see §27.2.1) at
definition time. When loading a compiled file or importing a module,
all the declarations of this module will be loaded.


27.1.3 Rewriting and non reflexive relations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

To replace only one argument of an n-ary morphism it is necessary to
prove that all the other arguments are related to themselves by the
respective relation instances.
Example 8 * To replace * *(union S empty)* * with * *S* * in* *(union
(union S empty) S) (union S S)* * the rewrite tactic must exploit the
monotony of * *union* * (axiom * *union_compat* * in the previous
example). Applying * *union_compat* * by hand we are left with the
goal * *eq_set (union S S) (union S S)* *.*
When the relations associated to some arguments are not reflexive, the
tactic cannot automatically prove the reflexivity goals, that are left
to the user.

Setoids whose relation are partial equivalence relations (PER) are
useful to deal with partial functions. Let R be a PER. We say that an
element x is defined if R x x. A partial function whose domain
comprises all the defined elements only is declared as a morphism that
respects R. Every time a rewriting step is performed the user must
prove that the argument of the morphism is defined.
Example 9 * Let * *eqO* * be * *fun x y => x = y *∧ * x*≠ * 0* * (the
smaller PER over non zero elements). Division can be declared as a
morphism of signature* *eq ==> eq0 ==> eq* *. Replace * *x* * with *
*y* * in* *div x n = div y n* * opens the additional goal * *eq0 n n*
* that is equivalent to * *n=n *∧ * n*≠ *0* *.*


27.1.4 Rewriting and non symmetric relations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

When the user works up to relations that are not symmetric, it is no
longer the case that any covariant morphism argument is also
contravariant. As a result it is no longer possible to replace a term
with a related one in every context, since the obtained goal implies
the previous one if and only if the replacement has been performed in
a contravariant position. In a similar way, replacement in an
hypothesis can be performed only if the replaced term occurs in a
covariant position.
Example 10 (Covariance and contravariance) * Suppose that division
over real numbers has been defined as a morphism of signature *
*Z.div: Z.lt ++> Z.lt --> Z.lt* * (i.e.* *Z.div* * is increasing in
its first argument, but decreasing on the second one). Let * *<* *
denotes * *Z.lt* *. Under the hypothesis * *H: x < y* * we have* *k <
x / y -> k < x / x* *, but not* *k < y / x -> k < x / x* *. Dually,
under the same hypothesis * *k < x / y -> k < y / y* * holds, but * *k
< y / x -> k < y / y* * does not. Thus, if the current goal is * *k <
x / x* *, it is possible to replace only the second occurrence of *
*x* * (in contravariant position) with * *y* * since the obtained goal
must imply the current one. On the contrary, if * *k < x / x* * is an
hypothesis, it is possible to replace only the first occurrence of*
*x* * (in covariant position) with * *y* * since the current
hypothesis must imply the obtained one.*
Contrary to the previous implementation, no specific error message
will be raised when trying to replace a term that occurs in the wrong
position. It will only fail because the rewriting constraints are not
satisfiable. However it is possible to use the at modifier to specify
which occurrences should be rewritten.

As expected, composing morphisms together propagates the variance
annotations by switching the variance every time a contravariant
position is traversed.
Example 11 * Let us continue the previous example and let us consider
the goal* *x / (x / x) < k* *. The first and third occurrences of *
*x* * are in a contravariant position, while the second one is in
covariant position. More in detail, the second occurrence of * *x* *
occurs covariantly in * *(x / x)* * (since division is covariant in
its first argument), and thus contravariantly in * *x / (x / x)* *
(since division is contravariant in its second argument), and finally
covariantly in* *x / (x / x) < k* * (since * *<* *, as every
transitive relation, is contravariant in its first argument with
respect to the relation itself).*


27.1.5 Rewriting in ambiguous setoid contexts
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

One function can respect several different relations and thus it can
be declared as a morphism having multiple signatures.
Example 12 * Union over homogeneous lists can be given all the
following signatures:* *eq ==> eq ==> eq* * (* *eq* * being the
equality over ordered lists)* *set_eq ==> set_eq ==> set_eq* * (*
*set_eq* * being the equality over unordered lists up to duplicates),*
*multiset_eq ==> multiset_eq ==> multiset_eq* * (* *multiset_eq* *
being the equality over unordered lists).*
To declare multiple signatures for a morphism, repeat the Add Morphism
command.

When morphisms have multiple signatures it can be the case that a
rewrite request is ambiguous, since it is unclear what relations
should be used to perform the rewriting. Contrary to the previous
implementation, the tactic will always choose the first possible
solution to the set of constraints generated by a rewrite and will not
try to find *all* possible solutions to warn the user about.


27.2 Commands and tactics
-------------------------


27.2.1 First class setoids and morphisms
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~



The implementation is based on a first-class representation of
properties of relations and morphisms as type classes. That is, the
various combinations of properties on relations and morphisms are
represented as records and instances of theses classes are put in a
hint database. For example, the declaration:
Add Parametric Relation (x 1 : T 1 ) …(x n : T k ) :(A t 1 …t n ) (Aeq
t′ 1 …t′ m )
[reflexivity proved by refl]
[symmetry proved by sym]
[transitivity proved by trans]
as id.
is equivalent to an instance declaration:
Instance (x 1 : T 1 ) …(x n : T k ) =>id : @Equivalence (A t 1 …t n )
(Aeqt′ 1 …t′ m ) :=
[Equivalence_Reflexive := refl]
[Equivalence_Symmetric := sym]
[Equivalence_Transitive := trans].
The declaration itself amounts to the definition of an object of the
record type Coq.Classes.RelationClasses.Equivalence and a hint added
to the typeclass_instances hint database. Morphism declarations are
also instances of a type class defined inClasses.Morphisms. See the
documentation on type classes `20`_ and the theories files in Classes
for further explanations.

One can inform the rewrite tactic about morphisms and relations just
by using the typeclass mechanism to declare them using Instance and
Context vernacular commands. Any object of type Proper (the type of
morphism declarations) in the local context will also be automatically
used by the rewriting tactic to solve constraints.

Other representations of first class setoids and morphisms can also be
handled by encoding them as records. In the following example, the
projections of the setoid relation and of the morphism function can be
registered as parametric relations and morphisms.
Example 13 (First class setoids) ** *Coq * *<* * Require Import
Relation* *_* *Definitions Setoid.* *

* *Coq * *<* * Record Setoid: Type :=* *
* * { car:Type;* *
* * eq:car-* *>* *car-* *>* *Prop;* *
* * refl: reflexive * *_* * eq;* *
* * sym: symmetric * *_* * eq;* *
* * trans: transitive * *_* * eq* *
* * }.* *

* *Coq * *<* * Add Parametric Relation (s : Setoid) : (@car s) (@eq
s)* *
* * reflexivity proved by (refl s)* *
* * symmetry proved by (sym s)* *
* * transitivity proved by (trans s) as eq* *_* *rel.* *

* *Coq * *<* * Record Morphism (S1 S2:Setoid): Type :=* *
* * { f:car S1 -* *>* *car S2;* *
* * compat: forall (x1 x2: car S1), eq S1 x1 x2 -* *>* * eq S2 (f x1)
(f x2) }.* *

* *Coq * *<* * Add Parametric Morphism (S1 S2 : Setoid) (M : Morphism
S1 S2) :* *
* * (@f S1 S2 M) with signature (@eq S1 ==* *>* * @eq S2) as apply*
*_* *mor.* *

* *Coq * *<* * Proof. apply (compat S1 S2 M). Qed.* *

* *Coq * *<* * Lemma test: forall (S1 S2:Setoid) (m: Morphism S1 S2)*
*
* * (x y: car S1), eq S1 x y -* *>* * eq S2 (f * *_* * * *_* * m x) (f
* *_* * * *_* * m y).* *

* *Coq * *<* * Proof. intros. rewrite H. reflexivity. Qed.* *
*


27.2.2 Tactics enabled on user provided relations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The following tactics, all prefixed by setoid_, deal with arbitrary
registered relations and morphisms. Moreover, all the corresponding
unprefixed tactics (i.e. reflexivity, symmetry, transitivity,replace,
rewrite) have been extended to fall back to their prefixed
counterparts when the relation involved is not Leibniz equality.
Notice, however, that using the prefixed tactics it is possible to
pass additional arguments such asusing relation.


setoid_reflexivity

setoid_symmetry [in ident]

setoid_transitivity

setoid_rewrite [orientation] term [at occs] [in ident]

setoid_replace term with term [in ident] [using relation term] [by
tactic]


The using relation arguments cannot be passed to the unprefixed form.
The latter argument tells the tactic what parametric relation should
be used to replace the first tactic argument with the second one. If
omitted, it defaults to the DefaultRelation instance on the type of
the objects. By default, it means the most recent Equivalence instance
in the environment, but it can be customized by declaring
newDefaultRelation instances. As Leibniz equality is a declared
equivalence, it will fall back to it if no other relation is declared
on a given type.

Every derived tactic that is based on the unprefixed forms of the
tactics considered above will also work up to user defined relations.
For instance, it is possible to register hints for autorewrite that
are not proof of Leibniz equalities. In particular it is possible to
exploitautorewrite to simulate normalization in a term rewriting
system up to user defined equalities.


27.2.3 Printing relations and morphisms
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The Print Instances command can be used to show the list of currently
registered Reflexive (using Print Instances Reflexive),Symmetric or
Transitive relations,Equivalences, PreOrders, PERs, and Morphisms
(implemented as Proper instances). When the rewriting tactics refuse
to replace a term in a context because the latter is not a composition
of morphisms, the Print Instances commands can be useful to understand
what additional morphisms should be registered.


27.2.4 Deprecated syntax and backward incompatibilities
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Due to backward compatibility reasons, the following syntax for the
declaration of setoids and morphisms is also accepted.


Add Setoid A Aeq ST as ident
where Aeq is a congruence relation without parameters,A is its carrier
and ST is an object of type(Setoid_Theory A Aeq) (i.e. a record
packing together the reflexivity, symmetry and transitivity lemmas).
Notice that the syntax is not completely backward compatible since the
identifier was not required.


Add Morphism f:ident.
Proof.
…
Qed.
The latter command also is restricted to the declaration of morphisms
without parameters. It is not fully backward compatible since the
property the user is asked to prove is slightly different: for n-ary
morphisms the hypotheses of the property are permuted; moreover, when
the morphism returns a proposition, the property is now stated using a
bi-implication in place of a simple implication. In practice, porting
an old development to the new semantics is usually quite simple.

Notice that several limitations of the old implementation have been
lifted. In particular, it is now possible to declare several relations
with the same carrier and several signatures for the same morphism.
Moreover, it is now also possible to declare several morphisms having
the same signature. Finally, the replace and rewrite tactics can be
used to replace terms in contexts that were refused by the old
implementation. As discussed in the next section, the semantics of the
new setoid_rewrite command differs slightly from the old one and
rewrite.


27.3 Extensions
---------------


27.3.1 Rewriting under binders
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Warning: Due to compatibility issues, this feature is enabled only
when calling the setoid_rewrite tactics directly and not rewrite.

To be able to rewrite under binding constructs, one must declare
morphisms with respect to pointwise (setoid) equivalence of functions.
Example of such morphisms are the standard all and ex combinators for
universal and existential quantification respectively. They are
declared as morphisms in the Classes.Morphisms_Prop module. For
example, to declare that universal quantification is a morphism for
logical equivalence:
Coq < Instance all_iff_morphism (A : Type) :
Proper (pointwise_relation A iff ==> iff) (@all A).

Coq < Proof. simpl_relation.
1 subgoal

A : Type
============================
Proper (pointwise_relation A iff ==> iff) (all (A:=A))
1 subgoal

A : Type
x, y : A -> Prop
H : pointwise_relation A iff x y
============================
all x <-> all y

One then has to show that if two predicates are equivalent at every
point, their universal quantifications are equivalent. Once we have
declared such a morphism, it will be used by the setoid rewriting
tactic each time we try to rewrite under an all application (products
in Prop are implicitly translated to such applications).

Indeed, when rewriting under a lambda, binding variable x, say fromP x
to Q x using the relation iff, the tactic will generate a proof of
pointwise_relation A iff (fun x => P x) (fun x => Q x) from the proof
of iff (P x) (Q x) and a constraint of the form Proper
(pointwise_relation A iff ==> ?) m will be generated for the
surrounding morphism m.

Hence, one can add higher-order combinators as morphisms by providing
signatures using pointwise extension for the relations on the
functional arguments (or whatever subrelation of the pointwise
extension). For example, one could declare the map combinator on lists
as a morphism:
Coq < Instance map_morphism `{Equivalence A eqA, Equivalence B eqB} :
Proper ((eqA ==> eqB) ==> list_equiv eqA ==> list_equiv eqB) (@map A
B).

where list_equiv implements an equivalence on lists parameterized by
an equivalence on the elements.

Note that when one does rewriting with a lemma under a binder using
setoid_rewrite, the application of the lemma may capture the bound
variable, as the semantics are different from rewrite where the lemma
is first matched on the whole term. With the newsetoid_rewrite,
matching is done on each subterm separately and in its local
environment, and all matches are rewritten *simultaneously* by
default. The semantics of the previoussetoid_rewrite implementation
can almost be recovered using the at 1 modifier.


27.3.2 Sub-relations
~~~~~~~~~~~~~~~~~~~~

Sub-relations can be used to specify that one relation is included in
another, so that morphisms signatures for one can be used for the
other. If a signature mentions a relation R on the left of an
arrow==>, then the signature also applies for any relation S that is
smaller than R, and the inverse applies on the right of an arrow. One
can then declare only a few morphisms instances that generate the
complete set of signatures for a particular constant. By default, the
only declared subrelation is iff, which is a subrelation of impl and
inverse impl (the dual of implication). That’s why we can declare only
two morphisms for conjunction:Proper (impl ==> impl ==> impl) and and
Proper (iff ==> iff ==> iff) and. This is sufficient to satisfy any
rewriting constraints arising from a rewrite using iff,impl or inverse
impl through and.

Sub-relations are implemented in Classes.Morphisms and are a prime
example of a mostly user-space extension of the algorithm.


27.3.3 Constant unfolding
~~~~~~~~~~~~~~~~~~~~~~~~~

The resolution tactic is based on type classes and hence regards user-
defined constants as transparent by default. This may slow down the
resolution due to a lot of unifications (all the declared Proper
instances are tried at each node of the search tree). To speed it up,
declare your constant as rigid for proof search using the command
Typeclasses Opaque (see §`20.6.7`_).


27.4 Strategies for rewriting
-----------------------------


27.4.1 Definitions
~~~~~~~~~~~~~~~~~~

The generalized rewriting tactic is based on a set of strategies that
can be combined to obtain custom rewriting procedures. Its set of
strategies is based on Elan’s rewriting strategies [`102`_]. Rewriting
strategies are applied using the tactic rewrite_strat s where s is a
strategy expression. Strategies are defined inductively as described
by the following grammar:
s, t, u ::= ( s ) strategy | c lemma | <- c lemma, right-to-left |
fail failure | id identity | refl reflexivity | progress s progress |
try s failure catch | s ; u composition | choice s t left-biased
choice | repeat s iteration (+) | any s iteration (*) | subterm s one
subterm | subterms s all subterms | innermost s innermost first |
outermost s outermost first | bottomup s bottom-up | topdown s top-
down | hints hintdb apply hint | terms c … c any of the terms | eval
redexpr apply reduction | fold c fold expression
Actually a few of these are defined in term of the others using a
primitive fixpoint operator:
try s = choice s id any s = fix u. try (s ; u) repeat s = s ; any s
bottomup s = fix bu. (choice (progress (subterms bu)) s) ; try bu
topdown s = fix td. (choice s (progress (subterms td))) ; try td
innermost s = fix i. (choice (subterm i) s) outermost s = fix o.
(choice s (subterm o))
The basic control strategy semantics are straightforward: strategies
are applied to subterms of the term to rewrite, starting from the root
of the term. The lemma strategies unify the left-hand-side of the
lemma with the current subterm and on success rewrite it to the right-
hand-side. Composition can be used to continue rewriting on the
current subterm. The fail strategy always fails while the identity
strategy succeeds without making progress. The reflexivity strategy
succeeds, making progress using a reflexivity proof of rewriting.
Progress tests progress of the argument strategy and fails if no
progress was made, while try always succeeds, catching failures.
Choice is left-biased: it will launch the first strategy and fall back
on the second one in case of failure. One can iterate a strategy at
least 1 time using repeat and at least 0 times usingany.

The subterm and subterms strategies apply their argument strategy s to
respectively one or all subterms of the current term under
consideration, left-to-right. subterm stops at the first subterm for
which s made progress. The composite strategiesinnermost and outermost
perform a single innermost our outermost rewrite using their argument
strategy. Their counterpartsbottomup and topdown perform as many
rewritings as possible, starting from the bottom or the top of the
term.

Hint databases created for autorewrite can also be used
byrewrite_strat using the hints strategy that applies any of the
lemmas at the current subterm. The terms strategy takes the lemma
names directly as arguments. The eval strategy expects a reduction
expression (see §`8.7`_) and succeeds if it reduces the subterm under
consideration. The fold strategy takes a term c and tries to *unify*
it to the current subterm, converting it to c on success, it is
stronger than the tactic fold.


27.4.2 Usage
~~~~~~~~~~~~



rewrite_strat s [in ident]:

Rewrite using the strategy s in hypothesis ident or the conclusion.


Error messages:


#. Nothing to rewrite. If the strategy failed.
#. No progress made. If the strategy succeeded but made no progress.
#. Unable to satisfy the rewriting constraints. If the strategy
   succeeded and made progress but the corresponding rewriting
   constraints are not satisfied.


The setoid_rewrite c tactic is basically equivalent to rewrite_strat
(outermost c).



:1: Nicolas Tabareau helped with the gluing.




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
.. _20.6.7: :///home/steck/type-classes.html#TypeclassesTransparency
.. _Cover: :///home/steck/index.html
.. _Errors: :///home/steck/error-index.html
.. _102: :///home/steck/biblio.html#Luttik97specificationof
.. _Table of contents: :///home/steck/toc.html
.. _Community: :///community
.. _27.4  Strategies for rewriting: :///home/steck/setoid.html#sec866
.. _27.3  Extensions: :///home/steck/setoid.html#sec862
.. _Commands: :///home/steck/command-index.html
.. _xhtml valid: http://validator.w3.org/
.. _Tactics: :///home/steck/tactic-index.html
.. _27.2  Commands and tactics: :///home/steck/setoid.html#sec857
.. _General: :///home/steck/general-index.html
.. _27.1  Introduction to generalized rewriting: :///home/steck/setoid.html#sec851
.. _Options: :///home/steck/option-index.html
.. _8.7: :///home/steck/tactics.html#Conversion-tactics
.. _The Coq Proof Assistant: :///
.. _Documentation: :///documentation
.. _webmaster: mailto:coq-www_@_inria.fr
.. _20: :///home/steck/type-classes.html#typeclasses



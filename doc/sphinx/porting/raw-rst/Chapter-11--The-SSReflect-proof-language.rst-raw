

+ `Home`_
+ `About Coq`_
+ `Get Coq`_
+ `Documentation`_
+ `Community`_

` `_ `The Coq Proof Assistant`_


Chapter 11 The SSReflect proof language
=======================================


+ `11.1 Introduction`_
+ `11.2 Usage`_
+ `11.3 Gallina extensions`_
+ `11.4 Definitions`_
+ `11.5 Basic tactics`_
+ `11.6 Control flow`_
+ `11.7 Rewriting`_
+ `11.8 Contextual patterns`_
+ `11.9 Views and reflection`_
+ `11.10 SSReflect searching tool`_
+ `11.11 Synopsis and Index`_


Georges Gonthier, Assia Mahboubi, Enrico Tassi




11.1 Introduction
-----------------



This chapter describes a set of tactics known as SSReflect originally
designed to provide support for the so-called *small scale reflection*
proof methodology. Despite the original purpose this set of tactic is
of general interest and is available in Coq starting from version 8.7.

SSReflect was developed independently of the tactics described in
Chapter `8`_. Indeed the scope of the tactics part ofSSReflect largely
overlaps with the standard set of tactics. Eventually the overlap will
be reduced in future releases of Coq.

Proofs written in SSReflect typically look quite different from the
ones written using only tactics as per Chapter `8`_. We try to
summarise here the most “visible” ones in order to help the reader
already accustomed to the tactics described in Chapter `8`_ to read
this chapter.

The first difference between the tactics described in this chapter and
the tactics described in Chapter `8`_ is the way hypotheses are
managed (we call this *bookkeeping*). In Chapter `8`_ the most common
approach is to avoid moving explicitly hypotheses back and forth
between the context and the conclusion of the goal. On the contrary in
SSReflect all bookkeeping is performed on the conclusion of the goal,
using for that purpose a couple of syntactic constructions behaving
similar to tacticals (and often named as such in this chapter). The :
tactical moves hypotheses from the context to the conclusion, while =>
moves hypotheses from the conclusion to the context, and in moves back
and forth an hypothesis from the context to the conclusion for the
time of applying an action to it.

While naming hypotheses is commonly done by means of an as clause in
the basic model of Chapter `8`_, it is here to=> that this task is
devoted. As tactics leave new assumptions in the conclusion, and are
often followed by=> to explicitly name them. While generalizing the
goal is normally not explicitly needed in Chapter `8`_, it is an
explicit operation performed by :.

Beside the difference of bookkeeping model, this chapter includes
specific tactics which have no explicit counterpart in Chapter `8`_
such as tactics to mix forward steps and generalizations as generally
have or without loss.

SSReflect adopts the point of view that rewriting, definition
expansion and partial evaluation participate all to a same concept of
rewriting a goal in a larger sense. As such, all these functionalities
are provided by the rewrite tactic.

SSReflect includes a little language of patterns to select subterms in
tactics or tacticals where it matters. Its most notable application is
in the rewrite tactic, where patterns are used to specify where the
rewriting step has to take place.

Finally, SSReflect supports so-called reflection steps, typically
allowing to switch back and forth between the computational view and
logical view of a concept.

To conclude it is worth mentioning that SSReflect tactics can be mixed
with non SSReflect tactics in the same proof, or in the same Ltac
expression. The few exceptions to this statement are described in
section 11.2.2.


Acknowledgments
~~~~~~~~~~~~~~~

The authors would like to thank Frédéric Blanqui, François Pottier and
Laurence Rideau for their comments and suggestions.


11.2 Usage
----------


11.2.1 Getting started
~~~~~~~~~~~~~~~~~~~~~~

To be available, the tactics presented in this manual need the
following minimal set of libraries to loaded: ssreflect.v, ssrfun.v
and ssrbool.v. Moreover, these tactics come with a methodology
specific to the authors of Ssreflect and which requires a few options
to be set in a different way than in their default way. All in all,
this corresponds to working in the following context:
From Coq Require Import ssreflect ssrfun ssrbool. Set Implicit
Arguments. Unset Strict Implicit. Unset Printing Implicit Defensive.


11.2.2 Compatibility issues
~~~~~~~~~~~~~~~~~~~~~~~~~~~

Requiring the above modules creates an environment which is mostly
compatible with the rest of Coq, up to a few discrepancies:


+ New keywords (is) might clash with variable, constant, tactic or
  tactical names, or with quasi-keywords in tactic or vernacular
  notations.
+ New tactic(al)s names (last, done, have,suffices, suff,without loss,
  wlog, congr, unlock) might clash with user tactic names.
+ Identifiers with both leading and trailing _, such as _x_, are
  reserved by SSReflect and cannot appear in scripts.
+ The extensions to the rewrite tactic are partly incompatible with
  those available in current versions of Coq; in particular:rewrite ..
  in (type of k) or rewrite .. in * or any other variant of rewrite will
  not work, and the SSReflect syntax and semantics for occurrence
  selection and rule chaining is different.Use an explicit rewrite
  direction (rewrite <- … or rewrite -> …) to access the Coq rewrite
  tactic.
+ New symbols (//, /=, //=) might clash with adjacent existing symbols
  (e.g., ’//’) instead of ’/”/’). This can be avoided by inserting white
  spaces.
+ New constant and theorem names might clash with the user theory.
  This can be avoided by not importing all of SSReflect: From Coq
  Require ssreflect. Import ssreflect.SsrSyntax. Note that the full
  syntax of SSReflect’s rewrite and reserved identifiers are enabled
  only if the ssreflect module has been required and ifSsrSyntax has
  been imported. Thus a file that requires (without importing)ssreflect
  and imports SsrSyntax, can be required and imported without
  automatically enabling SSReflect’s extended rewrite syntax and
  reserved identifiers.
+ Some user notations (in particular, defining an infix ’;’) might
  interfere with the "open term", parenthesis free, syntax of tactics
  such as have, set and pose.
+ The generalization of if statements to non-Boolean conditions is
  turned off by SSReflect, because it is mostly subsumed byCoercion to
  bool of the sumXXX types (declared inssrfun.v) and the if term is
  pattern then term else term construct (see11.3.2). To use the
  generalized form, turn off the SSReflect Boolean if notation using the
  command: Close Scope boolean_if_scope.
+ The following two options can be unset to disable the incompatible
  rewrite syntax and allow reserved identifiers to appear in scripts.
  Unset SsrRewrite. Unset SsrIdents.



11.3 Gallina extensions
-----------------------

Small-scale reflection makes an extensive use of the programming
subset of Gallina, Coq’s logical specification language. This subset
is quite suited to the description of functions on representations,
because it closely follows the well-established design of the ML
programming language. The SSReflect extension provides three additions
to Gallina, for pattern assignment, pattern testing, and polymorphism;
these mitigate minor but annoying discrepancies between Gallina and
ML.


11.3.1 Pattern assignment
~~~~~~~~~~~~~~~~~~~~~~~~~

The SSReflect extension provides the following construct for
irrefutable pattern matching, that is, destructuring assignment:

let: pattern := term 1 in term 2

Note the colon ‘:’ after the let keyword, which avoids any ambiguity
with a function definition or Coq’s basic destructuring let. The let:
construct differs from the latter in that


+ The pattern can be nested (deep pattern matching), in particular,
  this allows expression of the form: let: exist (x, y) p_xy := Hp in
  ...
+ The destructured constructor is explicitly given in the pattern, and
  is used for type inference, e.g., Let f u := let: (m, n) := u in m +
  n. using a colon let:, infers f : nat * nat -> nat, whereas Let f u :=
  let (m, n) := u in m + n. with a usual let, requires an extra type
  annotation.


The let: construct is just (more legible) notation for the primitive
Gallina expression
match term 1 with pattern => term 2 end
The SSReflect destructuring assignment supports all the dependent
match annotations; the full syntax is
let: pattern 1 as ident in pattern 2 := term 1 return term 2 in term 3
where pattern 2 is a *type* pattern and term 1 andterm 2 are types.

When the as and return are both present, then ident is bound in both
the type term 2 and the expression term 3 ; variables in the optional
type pattern pattern 2 are bound only in the type term 2 , and other
variables in pattern 1 are bound only in the expression term 3 ,
however.


11.3.2 Pattern conditional
~~~~~~~~~~~~~~~~~~~~~~~~~~

The following construct can be used for a refutable pattern matching,
that is, pattern testing:
if term 1 is pattern 1 then term 2 else term 3
Although this construct is not strictly ML (it does exits in variants
such as the pattern calculus or the ρ-calculus), it turns out to be
very convenient for writing functions on representations, because most
such functions manipulate simple datatypes such as Peano integers,
options, lists, or binary trees, and the pattern conditional above is
almost always the right construct for analyzing such simple types. For
example, the null andall list function(al)s can be defined as follows:
Variable d: Set. Fixpoint null (s : list d) := if s is nil then true
else false. Variable a : d -> bool. Fixpoint all (s : list d) : bool
:= if s is cons x s' then a x && all s' else true.
The pattern conditional also provides a notation for destructuring
assignment with a refutable pattern, adapted to the pure functional
setting of Gallina, which lacks a
Match_Failure exception.

Like let: above, the if…is construct is just (more legible) notation
for the primitive Gallina expression:
match term 1 with pattern => term 2 | _ => term 2 end
Similarly, it will always be displayed as the expansion of this form
in terms of primitive match expressions (where the default expression
term 3 may be replicated).

Explicit pattern testing also largely subsumes the generalization of
the if construct to all binary datatypes; compare:
if term is inl _ then term l else term r
and:
if term then term l else term r
The latter appears to be marginally shorter, but it is quite
ambiguous, and indeed often requires an explicit annotation term :
{_}+{_} to type-check, which evens the character count.

Therefore, SSReflect restricts by default the condition of a plain if
construct to the standard bool type; this avoids spurious type
annotations, e.g., in:
Definition orb b1 b2 := if b1 then true else b2.
As pointed out in section 11.2.2, this restriction can be removed with
the command:
Close Scope boolean_if_scope.
Like let: above, the if term is patternelse term construct supports
the dependent match annotations:
if term 1 is pattern 1 as ident in pattern 2 return term 2 then term 3
else term 4
As in let: the variable ident (and those in the type pattern pattern 2
) are bound in term 2 ; ident is also bound in term 3 (but not in term
4 ), while the variables in pattern 1 are bound only in term 3 .

Another variant allows to treat the else case first:
if term 1 isn’t pattern 1 then term 2 else term 3
Note that pattern 1 eventually binds variables in term 3 and not term
2 .


11.3.3 Parametric polymorphism
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~



Unlike ML, polymorphism in core Gallina is explicit: the type
parameters of polymorphic functions must be declared explicitly, and
supplied at each point of use. However, Coq provides two features to
suppress redundant parameters:


+ Sections are used to provide (possibly implicit) parameters for a
  set of definitions.
+ Implicit arguments declarations are used to tell Coq to use type
  inference to deduce some parameters from the context at each point of
  call.


The combination of these features provides a fairly good emulation of
ML-style polymorphism, but unfortunately this emulation breaks down
for higher-order programming. Implicit arguments are indeed not
inferred at all points of use, but only at points of call, leading to
expressions such as
Definition all_null (s : list T) := all (@null T) s.
Unfortunately, such higher-order expressions are quite frequent in
representation functions, especially those which use Coq’sStructures
to emulate Haskell type classes.

Therefore, SSReflect provides a variant of Coq’s implicit argument
declaration, which causes Coq to fill in some implicit parameters at
each point of use, e.g., the above definition can be written:
Definition all_null (s : list d) := all null s.
Better yet, it can be omitted entirely, since all_null s isn’t much of
an improvement over all null s.

The syntax of the new declaration is
Prenex Implicits ident + .
Let us denote 1 … c n the list of identifiers given to aPrenex
Implicits command. The command checks that each c i is the name of a
functional constant, whose implicit arguments are prenex, i.e., the
first n i > 0 arguments of c i are implicit; then it assignsMaximal
Implicit status to these arguments.

As these prenex implicit arguments are ubiquitous and have often large
display strings, it is strongly recommended to change the default
display settings of Coq so that they are not printed (except after
aSet Printing All command). All SSReflect library files thus start
with the incantation
Set Implicit Arguments. Unset Strict Implicit. Unset Printing Implicit
Defensive.


11.3.4 Anonymous arguments
~~~~~~~~~~~~~~~~~~~~~~~~~~

When in a definition, the type of a certain argument is mandatory, but
not its name, one usually use “arrow” abstractions for prenex
arguments, or the (_ : term) syntax for inner arguments. In SSReflect,
the latter can be replaced by the open syntax ‘of term’ or
(equivalently) ‘term’, which are both syntactically equivalent to a (_
: term) expression.

For instance, the usual two-contrsuctor polymorphic type list, i.e.
the one of the standard List library, can be defined by the following
declaration:
Inductive list (A : Type) : Type := nil | cons of A & list A.


11.3.5 Wildcards
~~~~~~~~~~~~~~~~



The terms passed as arguments to SSReflect tactics can contain
*holes*, materialized by wildcards_. Since SSReflect allows a more
powerful form of type inference for these arguments, it enhances the
possibilities of using such wildcards. These holes are in particular
used as a convenient shorthand for abstractions, especially in local
definitions or type expressions.

Wildcards may be interpreted as abstractions (see for example
sections11.4.1 and 11.6.6), or their content can be inferred from the
whole context of the goal (see for example section 11.4.2).


11.4 Definitions
----------------


11.4.1 Definitions
~~~~~~~~~~~~~~~~~~



The pose tactic allows to add a defined constant to a proof context.
SSReflect generalizes this tactic in several ways. In particular, the
SSReflect pose tactic supports *open syntax*: the body of the
definition does not need surrounding parentheses. For instance:
pose t := x + y.
is a valid tactic expression.

The pose tactic is also improved for the local definition of higher
order terms. Local definitions of functions can use the same syntax as
global ones. The tactic:
pose f x y := x + y.
adds to the context the defined constant:
f := fun x y : nat => x + y : nat -> nat -> nat
The SSReflect pose tactic also supports (co)fixpoints, by providing
the local counterpart of theFixpoint f := … and CoFixpoint f := …
constructs. For instance, the following tactic:
pose fix f (x y : nat) {struct x} : nat := if x is S p then S (f p y)
else 0.
defines a local fixpoint f, which mimics the standard plus operation
on natural numbers.

Similarly, local cofixpoints can be defined by a tactic of the form:
pose cofix f (arg : T) ...
The possibility to include wildcards in the body of the definitions
offers a smooth way of defining local abstractions. The type of
“holes” is guessed by type inference, and the holes are abstracted.
For instance the tactic:
pose f := _ + 1.
is shorthand for:
pose f n := n + 1.
When the local definition of a function involves both arguments and
holes, hole abstractions appear first. For instance, the tactic:
pose f x := x + _.
is shorthand for:
pose f n x := x + n.
The interaction of the pose tactic with the interpretation of implicit
arguments results in a powerful and concise syntax for local
definitions involving dependent types. For instance, the tactic:
pose f x y := (x, y).
adds to the context the local definition:
pose f (Tx Ty : Type) (x : Tx) (y : Ty) := (x, y).
The generalization of wildcards makes the use of the pose tactic
resemble ML-like definitions of polymorphic functions.


11.4.2 Abbreviations
~~~~~~~~~~~~~~~~~~~~



The SSReflect set tactic performs abbreviations: it introduces a
defined constant for a subterm appearing in the goal and/or in the
context.

SSReflect extends the set tactic by supplying:


+ an open syntax, similarly to the pose tactic;
+ a more aggressive matching algorithm;
+ an improved interpretation of wildcards, taking advantage of the
  matching algorithm;
+ an improved occurrence selection mechanism allowing to abstract only
  selected occurrences of a term.


The general syntax of this tactic is
set ident [: term 1 ] := [occ-switch] term 2 occ-switch ::= {[+|-]
natural * }
where:


+ ident is a fresh identifier chosen by the user.
+ term 1 is an optional type annotation. The type annotation term 1
  can be given in open syntax (no surrounding parentheses). If no occ-
  switch (described hereafter) is present, it is also the case for term
  2 . On the other hand, in presence of occ-switch, parentheses
  surrounding term 2 are mandatory.
+ In the occurrence switch occ-switch, if the first element of the
  list is a natural, this element should be a number, and not an Ltac
  variable. The empty list {} is not interpreted as a valid occurrence
  switch.


The tactic:
set t := f _.
transforms the goal f x + f x = f x into t + t = t, addingt := f x to
the context, and the tactic:
set t := {2}(f _).
transforms it into f x + t = f x, adding t := f x to the context.

The type annotation term 1 may contain wildcards, which will be filled
with the appropriate value by the matching process.

The tactic first tries to find a subterm of the goal matchingterm 2
(and its type term 1 ), and stops at the first subterm it finds. Then
the occurrences of this subterm selected by the optional occ-switch
are replaced by ident and a definition ident := term is added to the
context. If no occ-switch is present, then all the occurrences are
abstracted.


Matching
````````

The matching algorithm compares a pattern term with a subterm of the
goal by comparing their heads and then pairwise unifying their
arguments (modulo conversion). Head symbols match under the following
conditions:


+ If the head of term is a constant, then it should be syntactically
  equal to the head symbol of the subterm.
+ If this head is a projection of a canonical structure, then
  canonical structure equations are used for the matching.
+ If the head of term is *not* a constant, the subterm should have the
  same structure (λ abstraction,let…in structure …).
+ If the head of term is a hole, the subterm should have at least as
  many arguments as term. For instance the tactic: set t := _ x.
  transforms the goal `x` ` + ` `y` ` = ` `z` into t y = z and addst :=
  plus x : nat -> nat to the context.
+ In the special case where term is of the form(let f := t 0 in f) t 1
  … t n , then the pattern term is treated as (_ t 1 … t n ). For each
  subterm in the goal having the form (A u 1 … u n′ ) with n′ ≥ n, the
  matching algorithm successively tries to find the largest partial
  application (A u 1 … u i′ ) convertible to the headt 0 of term. For
  instance the following tactic: set t := (let g y z := y.+1 + z in g)
  2. transforms the goal (let f x y z := x + y + z in f 1) 2 3 = 6. into
  t 3 = 6 and adds the local definition of t to the context.


Moreover:


+ Multiple holes in term are treated as independent placeholders. For
  instance, the tactic: set t := _ + _. transforms the goal x + y = z
  into t = z and pushest := x + y : nat in the context.
+ The type of the subterm matched should fit the type (possibly casted
  by some type annotations) of the patternterm.
+ The replacement of the subterm found by the instantiated pattern
  should not capture variables, hence the following script: Goal forall
  x : nat, x + 1 = 0. set u := _ + 1. raises an error message, since x
  is bound in the goal.
+ Typeclass inference should fill in any residual hole, but matching
  should never assign a value to a global existential variable.



Occurrence selection
````````````````````



SSReflect provides a generic syntax for the selection of occurrences
by their position indexes. These *occurrence switches* are shared by
allSSReflect tactics which require control on subterm selection like
rewriting, generalization, …

An *occurrence switch* can be:


+ A list { natural * } of occurrences affected by the tactic. For
  instance, the tactic: set x := {1 3}(f 2). transforms the goal f 2 + f
  8 = f 2 + f 2 intox + f 8 = f 2 + x, and adds the abbreviationx := f 2
  in the context. Notice that some occurrences of a given term may be
  hidden to the user, for example because of a notation. The vernacular
  Set Printing All command displays all these hidden occurrences and
  should be used to find the correct coding of the occurrences to be
  selected 1 . For instance, the following script: Notation "a < b":=
  (le (S a) b). Goal forall x y, x < y -> S x < S y. intros x y; set t
  := S x. generates the goalt <= y -> t < S y since x < y is now a
  notation forS x <= y.
+ A list {natural + }. This is equivalent to{ natural + } but the list
  should start with a number, and not with an Ltac variable.
+ A list {natural * } of occurrences *not* to be affected by the
  tactic. For instance, the tactic: set x := {-2}(f 2). behaves like set
  x := {1 3}(f 2). on the goal `f` ` 2 + ` `f` ` 8 = ` `f` ` 2 + ` `f` `
  2` which has three occurrences of the the term f 2
+ In particular, the switch {+} selects *all* the occurrences. This
  switch is useful to turn off the default behavior of a tactic which
  automatically clears some assumptions (see section 11.5.3 for
  instance).
+ The switch {-} imposes that *no* occurrences of the term should be
  affected by the tactic. The tactic: set x := {-}(f 2). leaves the goal
  unchanged and adds the definition x := f 2 to the context. This kind
  of tactic may be used to take advantage of the power of the matching
  algorithm in a local definition, instead of copying large terms by
  hand.


It is important to remember that matching *precedes* occurrence
selection, hence the tactic:
set a := {2}(_ + _).
transforms the goal x + y = x + y + z into x + y = a + z and fails on
the goal
(x + y) + (z + z) = z + z with the error message:
User error: only 1 < 2 occurrence of (x + y + (z + z))


11.4.3 Localization
~~~~~~~~~~~~~~~~~~~



It is possible to define an abbreviation for a term appearing in the
context of a goal thanks to the in tactical.

A tactic of the form:
set x := term in fact 1 ...fact n .
introduces a defined constant called x in the context, and folds it in
the facts fact 1 … fact n The body of x is the first subterm matching
term infact 1 … fact n .

A tactic of the form:
set x := term in fact 1 ...fact n *.
matches term and then folds x similarly infact 1 … fact n , but also
folds x in the goal.

A goal `x` ` + ` `t` ` = 4`, whose context contains Hx : x = 3, is
left unchanged by the tactic:
set z := 3 in Hx.
but the context is extended with the definition z := 3 and Hx
becomesHx : x = z. On the same goal and context, the tactic:
set z := 3 in Hx *.
will moreover change the goal into `x` ` + ` `t` ` = ` `S` ` ` `z`.
Indeed, remember that 4 is just a notation for (S 3).

The use of the in tactical is not limited to the localization of
abbreviations: for a complete description of the in tactical, see
section 11.5.1.


11.5 Basic tactics
------------------



A sizable fraction of proof scripts consists of steps that do not
"prove" anything new, but instead perform menial bookkeeping tasks
such as selecting the names of constants and assumptions or splitting
conjuncts. Although they are logically trivial, bookkeeping steps are
extremely important because they define the structure of the data-flow
of a proof script. This is especially true for reflection-based
proofs, which often involve large numbers of constants and
assumptions. Good bookkeeping consists in always explicitly declaring
(i.e., naming) all new constants and assumptions in the script, and
systematically pruning irrelevant constants and assumptions in the
context. This is essential in the context of an interactive
development environment (IDE), because it facilitates navigating the
proof, allowing to instantly "jump back" to the point at which a
questionable assumption was added, and to find relevant assumptions by
browsing the pruned context. While novice or casual Coq users may find
the automatic name selection feature convenient, the usage of such a
feature severely undermines the readability and maintainability of
proof scripts, much like automatic variable declaration in programming
languages. The SSReflect tactics are therefore designed to support
precise bookkeeping and to eliminate name generation heuristics. The
bookkeeping features of SSReflect are implemented as tacticals (or
pseudo-tacticals), shared across most SSReflect tactics, and thus form
the foundation of the SSReflect proof language.


11.5.1 Bookkeeping
~~~~~~~~~~~~~~~~~~



During the course of a proof Coq always present the user with a
*sequent* whose general form is
c i : T i … d j := e j : T j … F k : P k … forall (x ℓ : T ℓ ) …, let
y m := b m in … in P n -> … -> C
The *goal* to be proved appears below the double line; above the line
is the *context* of the sequent, a set of declarations of *constants*
c i , *defined constants* d i , and *facts* F k that can be used to
prove the goal (usually, T i ,T j : Type and P k : Prop). The various
kinds of declarations can come in any order. The top part of the
context consists of declarations produced by the Section
commandsVariable, Let, and Hypothesis. This *section context* is never
affected by the SSReflect tactics: they only operate on the lower part
— the *proof context*. As in the figure above, the goal often
decomposes into a series of (universally) quantified *variables*(x ℓ :
T ℓ ), local *definitions*let y m := b m in, and *assumptions*P n ->,
and a *conclusion* C (as in the context, variables, definitions, and
assumptions can appear in any order). The conclusion is what actually
needs to be proved — the rest of the goal can be seen as a part of the
proof context that happens to be “below the line”.

However, although they are logically equivalent, there are fundamental
differences between constants and facts on the one hand, and variables
and assumptions on the others. Constants and facts are *unordered*,
but *named* explicitly in the proof text; variables and assumptions
are *ordered*, but *unnamed*: the display names of variables may
change at any time because of α-conversion.

Similarly, basic deductive steps such as apply can only operate on the
goal because the Gallina terms that control their action (e.g., the
type of the lemma used by apply) only provide unnamed bound variables.
2 Since the proof script can only refer directly to the context, it
must constantly shift declarations from the goal to the context and
conversely in between deductive steps.

In SSReflect these moves are performed by two *tacticals* ‘=>’ and
‘:’, so that the bookkeeping required by a deductive step can be
directly associated to that step, and that tactics in an SSReflect
script correspond to actual logical steps in the proof rather than
merely shuffle facts. Still, some isolated bookkeeping is unavoidable,
such as naming variables and assumptions at the beginning of a
proof.SSReflect provides a specific move tactic for this purpose.

Now move does essentially nothing: it is mostly a placeholder for ‘=>’
and ‘:’. The ‘=>’ tactical moves variables, local definitions, and
assumptions to the context, while the ‘:’ tactical moves facts and
constants to the goal. For example, the proof of 3
Lemma subnK : forall m n, n <= m -> m - n + n = m.
might start with
move=> m n le_n_m.
where move does nothing, but `=> ` `m` ` ` `n` ` ` `le_m_n` changes
the variables and assumption of the goal in the constants m n : nat
and the fact `le_n_m` ` : ` `n` ` <= ` `m`, thus exposing the
conclusion
m - n + n = m.

The ‘:’ tactical is the converse of ‘=>’: it removes facts and
constants from the context by turning them into variables and
assumptions. Thus
move: m le_n_m.
turns back m and `le_m_n` into a variable and an assumption, removing
them from the proof context, and changing the goal to
forall m, n <= m -> m - n + n = m.
which can be proved by induction on n using elim: n.

Because they are tacticals, ‘:’ and ‘=>’ can be combined, as in
move: m le_n_m => p le_n_p.
simultaneously renames `m` and `le_m_n` into `p` and `le_n_p`,
respectively, by first turning them into unnamed variables, then
turning these variables back into constants and facts.

Furthermore, SSReflect redefines the basic Coq tactics case,elim, and
apply so that they can take better advantage of ’:’ and ‘=>’. In there
SSReflect variants, these tactic operate on the first variable or
constant of the goal and they do not use or change the proof context.
The ‘:’ tactical is used to operate on an element in the context. For
instance the proof of subnK could continue with
elim: n.
instead of elim n; this has the advantage of removing n from the
context. Better yet, this elim can be combined with previous move and
with the branching version of the => tactical (described in 11.5.4),
to encapsulate the inductive step in a single command:
elim: n m le_n_m => [|n IHn] m => [_ | lt_n_m].
which breaks down the proof into two subgoals,
m - 0 + 0 = m
given m : nat, and
m - S n + S n = m
given m n : nat, `lt_n_m` ` : ` `S` ` ` `n` ` <= ` `m`, and
IHn : forall m, n <= m -> m - n + n = m.
The ’:’ and ‘=>’ tacticals can be explained very simply if one views
the goal as a stack of variables and assumptions piled on a
conclusion:


+ tactic : a b c pushes the context constants a, b, c as goal
  variables *before* performing tactic.
+ tactic => a b c pops the top three goal variables as context
  constants a, b, c, *after* tactic has been performed.


These pushes and pops do not need to balance out as in the examples
above, so
move: m le_n_m => p.
would rename m into p, but leave an extra assumption n <= p in the
goal.

Basic tactics like apply and elim can also be used without the ’:’
tactical: for example we can directly start a proof of subnK by
induction on the top variable m with
elim=> [|m IHm] n le_n.
The general form of the localization tactical in is also best
explained in terms of the goal stack:
tactic in a H1 H2 *.
is basically equivalent to
move: a H1 H2; tactic => a H1 H2.
with two differences: the in tactical will preserve the body of a ifa
is a defined constant, and if the ‘*’ is omitted it will use a
temporary abbreviation to hide the statement of the goal from
/*tactic*/.

The general form of the in tactical can be used directly with the
move, case and elim tactics, so that one can write
elim: n => [|n IHn] in m le_n_m *.
instead of
elim: n m le_n_m => [|n IHn] m le_n_m.
This is quite useful for inductive proofs that involve many facts.

See section 11.6.5 for the general syntax and presentation of the in
tactical.


11.5.2 The defective tactics
~~~~~~~~~~~~~~~~~~~~~~~~~~~~



In this section we briefly present the three basic tactics performing
context manipulations and the main backward chaining tool.


The move tactic.
````````````````



The move tactic, in its defective form, behaves like the primitive hnf
Coq tactic. For example, such a defective:
move.
exposes the first assumption in the goal, i.e. its changes the
goalFalse into False -> False.

More precisely, the move tactic inspects the goal and does nothing
(idtac) if an introduction step is possible, i.e. if the goal is a
product or a let…in, and performs hnf otherwise.

Of course this tactic is most often used in combination with the
bookkeeping tacticals (see section 11.5.4 and11.5.3). These
combinations mostly subsume the intros,generalize, revert, rename,
clear andpattern tactics.


The case tactic.
````````````````



The case tactic performs *primitive case analysis* on (co)inductive
types; specifically, it destructs the top variable or assumption of
the goal, exposing its constructor(s) and its arguments, as well as
setting the value of its type family indices if it belongs to a type
family (see section 11.5.6).

The SSReflect case tactic has a special behavior on equalities. If the
top assumption of the goal is an equality, the case tactic “destructs”
it as a set of equalities between the constructor arguments of its
left and right hand sides, as per the tactic injection. For example,
case changes the goal
(x, y) = (1, 2) -> G.
into
x = 1 -> y = 2 -> G.
Note also that the case of SSReflect performs False elimination, even
if no branch is generated by this case operation. Hence the command:
case.
on a goal of the form False -> G will succeed and prove the goal.


The elim tactic.
````````````````



The elim tactic performs inductive elimination on inductive types. The
defective:
elim.
tactic performs inductive elimination on a goal whose top assumption
has an inductive type. For example on goal of the form:
forall n : nat, m <= n
in a context containing m : nat, the
elim.
tactic produces two goals,
m <= 0
on one hand and
forall n : nat, m <= n -> m <= S n
on the other hand.


The apply tactic.
`````````````````



The apply tactic is the main backward chaining tactic of the proof
system. It takes as argument any/*term*/ and applies it to the goal.
Assumptions in the type of /*term*/ that don’t directly match the goal
may generate one or more subgoals.

In fact the SSReflect tactic:
apply.
is a synonym for:
intro top; first [refine top | refine (top _) | refine (top _ _) |
...]; clear top.
where top is fresh name, and the sequence of refine tactics tries to
catch the appropriate number of wildcards to be inserted. Note that
this use of the refine tactic implies that the tactic tries to match
the goal up to expansion of constants and evaluation of subterms.

SSReflect’s apply has a special behaviour on goals containing
existential metavariables of sort Prop. Consider the following
example:
Goal (forall y, 1 < y -> y < 2 -> exists x : { n | n < 3 }, proj1_sig
x > 0). move=> y y_gt1 y_lt2; apply: (ex_intro _ (exist _ y _)). by
apply: gt_trans _ y_lt2. by move=> y_lt3; apply: lt_trans y_gt1.
Note that the last _ of the tactic apply: (ex_intro _ (exist _ y _))
represents a proof that y < 3. Instead of generating the following
goal
0 < (n:=3) (m:=y) ?54
the system tries to prove y < 3 calling the trivial tactic. If it
succeeds, let’s say because the context containsH : y < 3, then the
system generates the following goal:
0 < proj1_sig (exist (fun n => n < 3) y H
Otherwise the missing proof is considered to be irrelevant, and is
thus discharged generating the following goals:
y < 3 forall H : y < 3, proj1_sig (exist (fun n => n < 3) y H)
Last, the user can replace the trivial tactic by defining an Ltac
expression named ssrautoprop.


11.5.3 Discharge
~~~~~~~~~~~~~~~~



The general syntax of the discharging tactical ‘:’ is:
tactic [ident] : d-item 1 … d-item n [clear-switch]
where n > 0, and d-item and clear-switch are defined as



d-item ::= [occ-switch | clear-switch] term clear-switch ::= { ident 1
… ident m }



with the following requirements:


+ tactic must be one of the four basic tactics described in 11.5.2,
  i.e., move, case, elim or apply, the exact tactic (section 11.6.2),
  the congr tactic (section 11.7.4), or the application of the *view*
  tactical ‘/’ (section 11.9.2) to one of move, case, or elim.
+ The optional ident specifies *equation generation* (section 11.5.5),
  and is only allowed if tactic is move, case or elim, or the
  application of the view tactical ‘/’ (section 11.9.2) to case or elim.
+ An occ-switch selects occurrences of term, as in 11.4.2; occ-switch
  is not allowed iftactic is apply or exact.
+ A clear item clear-switch specifies facts and constants to be
  deleted from the proof context (as per the clear tactic).


The ‘:’ tactical first *discharges* all the d-items, right to left,
and then performs tactic, i.e., for each d-item, starting with d-item
n :


#. The SSReflect matching algorithm described in section 11.4.2 is
   used to find occurrences of term in the goal, after filling any holes
   ‘_’ in term; however if tactic is apply or exact a different matching
   algorithm, described below, is used 4 .
#. These occurrences are replaced by a new variable; in particular, if
   term is a fact, this adds an assumption to the goal.
#. If term is *exactly* the name of a constant or fact in the proof
   context, it is deleted from the context, unless there is an occ-
   switch.


Finally, tactic is performed just after d-item 1 has been generalized
— that is, between steps 2 and 3 for d-item 1 . The names listed in
the final clear-switch (if it is present) are cleared first, before
d-item n is discharged.

Switches affect the discharging of a d-item as follows:


+ An occ-switch restricts generalization (step 2) to a specific subset
  of the occurrences of term, as per11.4.2, and prevents clearing (step
  3).
+ All the names specified by a clear-switch are deleted from the
  context in step 3, possibly in addition to term.


For example, the tactic:
move: n {2}n (refl_equal n).

+ first generalizes (refl_equal n : n = n);
+ then generalizes the second occurrence of n.
+ finally generalizes all the other occurrences of n, and clears n
  from the proof context (assuming n is a proof constant).


Therefore this tactic changes any goal G into
forall n n0 : nat, n = n0 -> G.
where the name n0 is picked by the Coq display function, and assuming
n appeared only in G.

Finally, note that a discharge operation generalizes defined constants
as variables, and not as local definitions. To override this behavior,
prefix the name of the local definition with a @, like in move: @n.

This is in contrast with the behavior of the in tactical (see
section11.6.5), which preserves local definitions by default.


Clear rules
```````````

The clear step will fail if term is a proof constant that appears in
other facts; in that case either the facts should be cleared
explicitly with a clear-switch, or the clear step should be disabled.
The latter can be done by adding an occ-switch or simply by putting
parentheses around term: both
move: (n).
and
move: {+}n.
generalize n without clearing n from the proof context.

The clear step will also fail if the clear-switch contains aident that
is not in the *proof* context. Note that SSReflect never clears a
section constant.

If tactic is move or case and an equation ident is given, then clear
(step 3) for d-item 1 is suppressed (see section 11.5.5).


Matching for apply and exact
````````````````````````````



The matching algorithm for d-items of the SSReflect apply andexact
tactics exploits the type of d-item 1 to interpret wildcards in the
other d-item and to determine which occurrences of these should be
generalized. Therefore, occur switches are not needed for apply and
exact.

Indeed, the SSReflect tactic apply: H x is equivalent to
refine (@H _ ... _ x); clear H x
with an appropriate number of wildcards between H and x.

Note that this means that matching for apply and exact has much more
context to interpret wildcards; in particular it can accommodate the
‘_’ d-item, which would always be rejected after ‘move:’. For example,
the tactic
apply: trans_equal (Hfg _) _.
transforms the goal f a = g b, whose context contains(Hfg : forall x,
f x = g x), into g a = g b. This tactic is equivalent (see section
11.5.1) to:
refine (trans_equal (Hfg _) _).
and this is a common idiom for applying transitivity on the left hand
side of an equation.


The abstract tactic
```````````````````



The abstract tactic assigns an abstract constant previously introduced
with the [: name ] intro pattern (see section 11.5.4, page ??). In a
goal like the following:
m : nat abs : <hidden> n : nat ============= m < 5 + n
The tactic abstract: abs n first generalizes the goal with respect ton
(that is not visible to the abstract constant abs) and then assigns
abs. The resulting goal is:
m : nat n : nat ============= m < 5 + n
Once this subgoal is closed, all other goals having abs in their
context see the type assigned to abs. In this case:
m : nat abs : forall n, m < 5 + n
For a more detailed example the user should refer to section 11.6.6,
page ??.


11.5.4 Introduction
~~~~~~~~~~~~~~~~~~~



The application of a tactic to a given goal can generate (quantified)
variables, assumptions, or definitions, which the user may want to
*introduce* as new facts, constants or defined constants,
respectively. If the tactic splits the goal into several subgoals,
each of them may require the introduction of different constants and
facts. Furthermore it is very common to immediately decompose or
rewrite with an assumption instead of adding it to the context, as the
goal can often be simplified and even proved after this.

All these operations are performed by the introduction tactical ‘=>’,
whose general syntax is
tactic => i-item 1 … i-item n
where tactic can be any tactic, n > 0 and



i-item ::= i-pattern | s-item | clear-switch | /term s-item ::= /= |
// | //= i-pattern ::= ident | _ | ? | * | [occ-switch]-> | [occ-
switch]<- | [ i-item 1 * | … | i-item m * ] | - | [: ident + ]



The ‘=>’ tactical first executes tactic, then thei-items, left to
right, i.e., starting from i-item 1 . Ans-item specifies a
simplification operation; a clear switch specifies context pruning as
in 11.5.3. Thei-patterns can be seen as a variant of *intro patterns*
`8.3.2`_: each performs an introduction operation, i.e., pops some
variables or assumptions from the goal.

An s-item can simplify the set of subgoals or the subgoal themselves:


+ // removes all the “trivial” subgoals that can be resolved by the
  SSReflect tactic done described in 11.6.2, i.e., it executes try done.
+ /= simplifies the goal by performing partial evaluation, as per the
  tactic simpl. 5
+ //= combines both kinds of simplification; it is equivalent to /=
  //, i.e., simpl; try done.


When an s-item bears a clear-switch, then the clear-switch is executed
*after* the s-item, e.g., `{` `IHn` `}//` will solve some subgoals,
possibly using the fact `IHn`, and will erase `IHn` from the context
of the remaining subgoals.

The last entry in the i-item grammar rule, /term, represents a view
(see section 11.9). If i-item k+1 is a view i-item, the view is
applied to the assumption in top position once i-item 1 … i-item k
have been performed.

The view is applied to the top assumption.

SSReflect supports the following i-patterns:


+ ident pops the top variable, assumption, or local definition into a
  new constant, fact, or defined constant ident, respectively. Note that
  defined constants cannot be introduced when δ-expansion is required to
  expose the top variable or assumption.
+ ? pops the top variable into an anonymous constant or fact, whose
  name is picked by the tactic interpreter.SSReflect only generates
  names that cannot appear later in the user script. 6
+ _ pops the top variable into an anonymous constant that will be
  deleted from the proof context of all the subgoals produced by the =>
  tactical. They should thus never be displayed, except in an error
  message if the constant is still actually used in the goal or context
  after the last i-item has been executed (s-items can erase goals or
  terms where the constant appears).
+ * pops all the remaining apparent variables/assumptions as anonymous
  constants/facts. Unlike ? and move the *i-item does not expand
  definitions in the goal to expose quantifiers, so it may be useful to
  repeat a move=> * tactic, e.g., on the goal forall a b : bool, a <> b
  a first move=> * adds only _a_ : bool and _b_ : bool to the context;
  it takes a second move=> * to add_Hyp_ : _a_ = _b_.
+ [occ-switch]-> (resp. [occ-switch]<-) pops the top assumption (which
  should be a rewritable proposition) into an anonymous fact, rewrites
  (resp. rewrites right to left) the goal with this fact (using the
  SSReflect rewrite tactic described in section 11.7, and honoring the
  optional occurrence selector), and finally deletes the anonymous fact
  from the context.
+ [ i-item 1 * | … | i-item m * ], when it is the very *first*
  i-pattern after tactic => tactical *and* tactic is not a move, is a
  *branching*i-pattern. It executes the sequence i-item i * on the i th
  subgoal produced by tactic. The execution of tactic should thus
  generate exactly m subgoals, unless the […] i-pattern comes after an
  initial// or //= s-item that closes some of the goals produced
  bytactic, in which case exactly m subgoals should remain after thes-
  item, or we have the trivial branching i-pattern [], which always does
  nothing, regardless of the number of remaining subgoals.
+ [ i-item 1 * | … | i-item m * ], when it is *not* the first
  i-pattern or when tactic is amove, is a *destructing* i-pattern. It
  starts by destructing the top variable, using the SSReflect case
  tactic described in 11.5.2. It then behaves as the corresponding
  branching i-pattern, executing the sequencei-item i * in the i th
  subgoal generated by the case analysis; unless we have the trivial
  destructing i-pattern[], the latter should generate exactly m
  subgoals, i.e., the top variable should have an inductive type with
  exactly m constructors. 7 While it is good style to use the i-item i *
  to pop the variables and assumptions corresponding to each
  constructor, this is not enforced by SSReflect.
+ - does nothing, but counts as an intro pattern. It can also be used
  to force the interpretation of[ i-item 1 * | … | i-item m * ] as a
  case analysis like in move=> -[H1 H2]. It can also be used to indicate
  explicitly the link between a view and a name like inmove=> /eqP-H1.
  Last, it can serve as a separator between views. Section 11.9.9
  explains in which respect the tactic move=> /v1/v2 differs from the
  tacticmove=> /v1-/v2.
+ [: ident + ] introduces in the context an abstract constant for each
  ident. Its type has to be fixed later on by using the abstract tactic
  (see page ??). Before then the type displayed is <hidden>.


Note that SSReflect does not support the syntax(ipat,…,ipat) for
destructing intro-patterns.

Clears are deferred until the end of the intro pattern. For example,
given the goal:
x, y : nat ================== 0 < x = true -> (0 < x) && (y < 2) =
true
the tactic move=> {x} -> successfully rewrites the goal and deletes x
and the anonymous equation. The goal is thus turned into:
y : nat ================== true && (y < 2) = true
If the cleared names are reused in the same intro pattern, a renaming
is performed behind the scenes.

Facts mentioned in a clear switch must be valid names in the proof
context (excluding the section context).

The rules for interpreting branching and destructing i-pattern are
motivated by the fact that it would be pointless to have a branching
pattern if tactic is a move, and in most of the remaining casestactic
is case or elim, which implies destruction. The rules above imply that
move=> [a b]. case=> [a b]. case=> a b.
are all equivalent, so which one to use is a matter of style;move
should be used for casual decomposition, such as splitting a pair, and
case should be used for actual decompositions, in particular for type
families (see 11.5.6) and proof by contradiction.

The trivial branching i-pattern can be used to force the branching
interpretation, e.g.,
case=> [] [a b] c. move=> [[a b] c]. case; case=> a b c.
are all equivalent.


11.5.5 Generation of equations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~



The generation of named equations option stores the definition of a
new constant as an equation. The tactic:
move En: (size l) => n.
where l is a list, replaces size l by n in the goal and adds the fact
En : size l = n to the context. This is quite different from:
pose n := (size l).
which generates a definition n := (size l). It is not possible to
generalize or rewrite such a definition; on the other hand, it is
automatically expanded during computation, whereas expanding the
equation En requires explicit rewriting.

The use of this equation name generation option with a case or anelim
tactic changes the status of the first i-item, in order to deal with
the possible parameters of the constants introduced.

On the goal a <> b where a, b are natural numbers, the tactic:
case E : a => [|n].
generates two subgoals. The equation E : a = 0 (resp. E : a = S n, and
the constant n : nat) has been added to the context of the goal 0 <> b
(resp. S n <> b).

If the user does not provide a branching i-item as first i-item, or if
the i-item does not provide enough names for the arguments of a
constructor, then the constants generated are introduced under fresh
SSReflect names. For instance, on the goal a <> b, the tactic:
case E : a => H.
also generates two subgoals, both requiring a proof of False. The
hypotheses E : a = 0 andH : 0 = b (resp. E : a = S _n_ andH : S _n_ =
b) have been added to the context of the first subgoal (resp. the
second subgoal).

Combining the generation of named equations mechanism with thecase
tactic strengthens the power of a case analysis. On the other hand,
when combined with the elim tactic, this feature is mostly useful for
debug purposes, to trace the values of decomposed parameters and
pinpoint failing branches.


11.5.6 Type families
~~~~~~~~~~~~~~~~~~~~



When the top assumption of a goal has an inductive type, two specific
operations are possible: the case analysis performed by thecase
tactic, and the application of an induction principle, performed by
the elim tactic. When this top assumption has an inductive type, which
is moreover an instance of a type family, Coq may need help from the
user to specify which occurrences of the parameters of the type should
be substituted.

A specific / switch indicates the type family parameters of the type
of a d-item immediately following this / switch, using the syntax:
[ case | elim ]: d-item + / d-item *
The d-items on the right side of the / switch are discharged as
described in section 11.5.3. The case analysis or elimination will be
done on the type of the top assumption after these discharge
operations.

Every d-item preceding the / is interpreted as arguments of this type,
which should be an instance of an inductive type family. These terms
are not actually generalized, but rather selected for substitution.
Occurrence switches can be used to restrict the substitution. If a
term is left completely implicit (e.g. writing just _), then a pattern
is inferred looking at the type of the top assumption. This allows for
the compact syntaxcase: {2}_ / eqP, were _ is interpreted as (_ == _).
Moreover if the d-items list is too short, it is padded with an
initial sequence of _ of the right length.

Here is a small example on lists. We define first a function which
adds an element at the end of a given list.
Require Import List. Section LastCases. Variable A : Type. Fixpoint
add_last(a : A)(l : list A): list A := match l with |nil => a :: nil
|hd :: tl => hd :: (add_last a tl) end.
Then we define an inductive predicate for case analysis on lists
according to their last element:
Inductive last_spec : list A -> Type := | LastSeq0 : last_spec nil |
LastAdd s x : last_spec (add_last x s). Theorem lastP : forall l :
list A, last_spec l.
Applied to the goal:
Goal forall l : list A, (length l) * 2 = length (app l l).
the command:
move=> l; case: (lastP l).
generates two subgoals:
length nil * 2 = length (nil ++ nil)
and
forall (s : list A) (x : A), length (add_last x s) * 2 = length
(add_last x s ++ add_last x s)
both having l : list A in their context.

Applied to the same goal, the command:
move=> l; case: l / (lastP l).
generates the same subgoals but l has been cleared from both contexts.

Again applied to the same goal, the command:
move=> l; case: {1 3}l / (lastP l).
generates the subgoals `length` ` ` `l` ` * 2 = ` `length` ` (` `nil`
` ++ ` `l` `)` and `forall` ` (` `s` ` : ` `list` ` ` `A` `) (` `x` `
: ` `A` `), ` `length` ` ` `l` ` * 2 = ` `length` ` (` `add_last` ` `
`x` ` ` `s` `++` `l` `)` where the selected occurrences on the left of
the / switch have been substituted with l instead of being affected by
the case analysis.

The equation name generation feature combined with a type family /
switch generates an equation for the *first* dependent d-item
specified by the user. Again starting with the above goal, the
command:
move=> l; case E: {1 3}l / (lastP l)=>[|s x].
adds E : l = nil and E : l = add_last x s, respectively, to the
context of the two subgoals it generates.

There must be at least one *d-item* to the left of the / switch; this
prevents any confusion with the view feature. However, the d-items to
the right of the / are optional, and if they are omitted the first
assumption provides the instance of the type family.

The equation always refers to the first *d-item* in the actual tactic
call, before any padding with initial _s. Thus, if an inductive type
has two family parameters, it is possible to haveSSReflect generate an
equation for the second one by omitting the pattern for the first;
note however that this will fail if the type of the second parameter
depends on the value of the first parameter.


11.6 Control flow
-----------------


11.6.1 Indentation and bullets
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~



A linear development of Coq scripts gives little information on the
structure of the proof. In addition, replaying a proof after some
changes in the statement to be proved will usually not display
information to distinguish between the various branches of case
analysis for instance.

To help the user in this organization of the proof script at
development time, SSReflect provides some bullets to highlight the
structure of branching proofs. The available bullets are -,+ and *.
Combined with tabulation, this lets us highlight four nested levels of
branching; the most we have ever needed is three. Indeed, the use of
“simpl and closing” switches, of terminators (see above section
11.6.2) and selectors (see section 11.6.3) is powerful enough to avoid
most of the time more than two levels of indentation.

Here is a fragment of such a structured script:
case E1: (abezoutn _ _) => [[| k1] [| k2]]. - rewrite !muln0 !gexpn0
mulg1 => H1. move/eqP: (sym_equal F0); rewrite -H1 orderg1 eqn_mul1.
by case/andP; move/eqP. - rewrite muln0 gexpn0 mulg1 => H1. have F1: t
%| t * S k2.+1 - 1. apply: (@dvdn_trans (orderg x)); first by rewrite
F0; exact: dvdn_mull. rewrite orderg_dvd; apply/eqP; apply: (mulgI x).
rewrite -{1}(gexpn1 x) mulg1 gexpn_add leq_add_sub //. by move: P1;
case t. rewrite dvdn_subr in F1; last by exact: dvdn_mulr. + rewrite
H1 F0 -{2}(muln1 (p ^ l)); congr (_ * _). by apply/eqP; rewrite
-dvdn1. + by move: P1; case: (t) => [| [| s1]]. - rewrite muln0 gexpn0
mul1g => H1. ...


11.6.2 Terminators
~~~~~~~~~~~~~~~~~~



To further structure scripts, SSReflect supplies *terminating*
tacticals to explicitly close off tactics. When replaying scripts, we
then have the nice property that an error immediately occurs when a
closed tactic fails to prove its subgoal.

It is hence recommended practice that the proof of any subgoal should
end with a tactic which *fails if it does not solve the current goal*,
like discriminate, contradiction or assumption.

In fact, SSReflect provides a generic tactical which turns any tactic
into a closing one (similar to now). Its general syntax is:
by tactic.
The Ltac expression:
by [tactic 1 | [tactic 2 | ...].
is equivalent to:
[by tactic 1 | by tactic 2 | ...].
and this form should be preferred to the former.

In the script provided as example in section 11.6.1, the paragraph
corresponding to each sub-case ends with a tactic line prefixed with a
by, like in:
by apply/eqP; rewrite -dvdn1.
The by tactical is implemented using the user-defined, and extensible
done tactic. This done tactic tries to solve the current goal by some
trivial means and fails if it doesn’t succeed. Indeed, the tactic
expression:
by tactic.
is equivalent to:
tactic; done.
Conversely, the tactic
by [ ].
is equivalent to:
done.
The default implementation of the done tactic, in the ssreflect.v
file, is:
Ltac done := trivial; hnf; intros; solve [ do ![solve [trivial |
apply: sym_equal; trivial] | discriminate | contradiction | split] |
case not_locked_false_eq_true; assumption | match goal with H : ~ _ |-
_ => solve [case H; trivial] end ].
The lemma |*not_locked_false_eq_true*| is needed to discriminate
*locked* boolean predicates (see section 11.7.3). The iterator
tactical do is presented in section11.6.4. This tactic can be
customized by the user, for instance to include anauto tactic.

A natural and common way of closing a goal is to apply a lemma which
is the exact one needed for the goal to be solved. The defective form
of the tactic:
exact.
is equivalent to:
do [done | by move=> top; apply top].
where top is a fresh name affected to the top assumption of the goal.
This applied form is supported by the : discharge tactical, and the
tactic:
exact: MyLemma.
is equivalent to:
by apply: MyLemma.
(see section 11.5.3 for the documentation of the apply: combination).

Warning The list of tactics, possibly chained by semi-columns, that
follows a by keyword is considered as a parenthesized block applied to
the current goal. Hence for example if the tactic:
by rewrite my_lemma1.
succeeds, then the tactic:
by rewrite my_lemma1; apply my_lemma2.
usually fails since it is equivalent to:
by (rewrite my_lemma1; apply my_lemma2).


11.6.3 Selectors
~~~~~~~~~~~~~~~~



When composing tactics, the two tacticals first andlast let the user
restrict the application of a tactic to only one of the subgoals
generated by the previous tactic. This covers the frequent cases where
a tactic generates two subgoals one of which can be easily disposed
of.

This is an other powerful way of linearization of scripts, since it
happens very often that a trivial subgoal can be solved in a less than
one line tactic. For instance, the tactic:
tactic 1 ; last by tactic 2 .
tries to solve the last subgoal generated by tactic 1 using thetactic
2 , and fails if it does not succeeds. Its analogous
tactic 1 ; first by tactic 2 .
tries to solve the first subgoal generated by tactic 1 using the
tactic tactic 2 , and fails if it does not succeeds.

SSReflect also offers an extension of this facility, by supplying
tactics to *permute* the subgoals generated by a tactic. The tactic:
tactic; last first.
inverts the order of the subgoals generated by tactic. It is
equivalent to:
tactic; first last.
More generally, the tactic:
tactic; last natural first.
where natural is a Coq numeral, or and Ltac variable denoting a Coq
numeral, having the value k. It rotates the n subgoals G 1 , …, G n
generated by tactic. The first subgoal becomesG n + 1 − k and the
circular order of subgoals remains unchanged.

Conversely, the tactic:

tactic; first natural last.

rotates the n subgoals G 1 , …, G n generated by tactic in order that
the first subgoal becomes G k .

Finally, the tactics last and first combine with the branching syntax
of Ltac: if the tactic tactic 0 generates n subgoals on a given goal,
then the tactic

tactic 0 ; last natural [tactic 1 |…|tactic m ] || tactic m+1 .

where natural denotes the integer k as above, applies tactic 1 to then
−k + 1-th goal, … tactic m to the n −k + 2 − m-th goal and tactic m+1
to the others.

For instance, the script:
Inductive test : nat -> Prop := C1 : forall n, test n | C2 : forall n,
test n | C3 : forall n, test n | C4 : forall n, test n. Goal forall n,
test n -> True. move=> n t; case: t; last 2 [move=> k| move=> l];
idtac.
creates a goal with four subgoals, the first and the last beingnat ->
True, the second and the third being True with respectively k : nat
and l : nat in their context.


11.6.4 Iteration
~~~~~~~~~~~~~~~~



SSReflect offers an accurate control on the repetition of tactics,
thanks to the do tactical, whose general syntax is:
do [mult] [ tactic 1 | … | tactic n ]
where mult is a *multiplier*.

Brackets can only be omitted if a single tactic is given *and* a
multiplier is present.

A tactic of the form:
do [ tactic 1 | … | tactic n ].
is equivalent to the standard Ltac expression:
first [ tactic 1 | … | tactic n ].
The optional multiplier mult specifies how many times the action of
tactic should be repeated on the current subgoal.

There are four kinds of multipliers:


+ n!: the step tactic is repeated exactly n times (where n is a
  positive integer argument).
+ !: the step tactic is repeated as many times as possible, and done
  at least once.
+ ?: the step tactic is repeated as many times as possible,
  optionally.
+ n?: the step tactic is repeated up to n times, optionally.


For instance, the tactic:
tactic `; ` `do` ` 1?` `rewrite` ` ` `mult_comm` `.`
rewrites at most one time the lemma mult_com in all the subgoals
generated by tactic , whereas the tactic:
tactic `; ` `do` ` 2!` `rewrite` ` ` `mult_comm` `.`
rewrites exactly two times the lemma mult_com in all the subgoals
generated by tactic, and fails if this rewrite is not possible in some
subgoal.

Note that the combination of multipliers and rewrite is so often used
that multipliers are in fact integrated to the syntax of the
SSReflectrewrite tactic, see section 11.7.


11.6.5 Localization
~~~~~~~~~~~~~~~~~~~



In sections 11.4.3 and 11.5.1, we have already presented the
*localization* tactical in, whose general syntax is:
tactic in ident + [*]
where ident + is a non empty list of fact names in the context. On the
left side of in, tactic can bemove, case, elim, rewrite, set, or any
tactic formed with the general iteration tactical do (see section
11.6.4).

The operation described by tactic is performed in the facts listed in
ident + and in the goal if a * ends the list.

The in tactical successively:


+ generalizes the selected hypotheses, possibly “protecting” the goal
  if * is not present,
+ performs tactic, on the obtained goal,
+ reintroduces the generalized facts, under the same names.


This defective form of the do tactical is useful to avoid clashes
between standard Ltac in and the SSReflect tactical in. For example,
in the following script:
Ltac mytac H := rewrite H. Goal forall x y, x = y -> y = 3 -> x + y =
6. move=> x y H1 H2. do [mytac H2] in H1 *.
the last tactic rewrites the hypothesis H2 : y = 3 both inH1 : x = y
and in the goal x + y = 6.

By default in keeps the body of local definitions. To erase the body
of a local definition during the generalization phase, the name of the
local definition must be written between parentheses, like in rewrite
H in H1 (def_n) H2.

From SSReflect 1.5 the grammar for the in tactical has been extended
to the following one:
tactic in [ clear-switch | [@]ident |(ident) | ([@]ident := c-pattern)
] + [*]
In its simplest form the last option lets one rename hypotheses that
can’t be cleared (like section variables). For example (y := x)
generalizes over x and reintroduces the generalized variable under the
name y (and does not clear x).
For a more precise description the ([@]ident := c-pattern) item refer
to the “Advanced generalization” paragraph at page ??.


11.6.6 Structure
~~~~~~~~~~~~~~~~



Forward reasoning structures the script by explicitly specifying some
assumptions to be added to the proof context. It is closely associated
with the declarative style of proof, since an extensive use of these
highlighted statements make the script closer to a (very detailed)
text book proof.

Forward chaining tactics allow to state an intermediate lemma and
start a piece of script dedicated to the proof of this statement. The
use of closing tactics (see section 11.6.2) and of indentation makes
syntactically explicit the portion of the script building the proof of
the intermediate statement.


The have tactic.
````````````````



The main SSReflect forward reasoning tactic is the have tactic. It can
be use in two modes: one starts a new (sub)proof for an intermediate
result in the main proof, and the other provides explicitly a proof
term for this intermediate step.

In the first mode, the syntax of have in its defective form is:

have: term.

This tactic supports open syntax for term. Applied to a goal G, it
generates a first subgoal requiring a proof of term in the context of
G. The second generated subgoal is of the form term -> G, where term
becomes the new top assumption, instead of being introduced with a
fresh name. At the proof-term level, the have tactic creates a β
redex, and introduces the lemma under a fresh name, automatically
chosen.

Like in the case of the pose tactic (see section 11.4.1), the types of
the holes are abstracted in term. For instance, the tactic:
have: _ * 0 = 0.
is equivalent to:
have: forall n : nat, n * 0 = 0.
The have tactic also enjoys the same abstraction mechanism as thepose
tactic for the non-inferred implicit arguments. For instance, the
tactic:
have: forall x y, (x, y) = (x, y + 0).
opens a new subgoal to prove that:

forall (T : Type) (x : T) (y : nat), (x, y) = (x, y + 0)

The behavior of the defective have tactic makes it possible to
generalize it in the following general construction:
have i-item * [i-pattern] [s-item | binder + ] [: term 1 ] [:= term 2
| by tactic]
Open syntax is supported for term 1 and term 2 . For the description
ofi-items and clear switches see section 11.5.4. The first mode of the
have tactic, which opens a sub-proof for an intermediate result, uses
tactics of the form:
have clear-switch i-item : term by tactic.
which behave like:

have: term ; first by tactic. move=> clear-switch i-item.
Note that the clear-switch *precedes* thei-item, which allows to reuse
a name of the context, possibly used by the proof of the assumption,
to introduce the new assumption itself.

The by feature is especially convenient when the proof script of the
statement is very short, basically when it fits in one line like in:
have H : forall x y, x + y = y + x by move=> x y; rewrite addnC.
The possibility of using i-items supplies a very concise syntax for
the further use of the intermediate step. For instance,
have -> : forall x, x * a = a.
on a goal G, opens a new subgoal asking for a proof offorall x, x * a
= a, and a second subgoal in which the lemmaforall x, x * a = a has
been rewritten in the goal G. Note that in this last subgoal, the
intermediate result does not appear in the context. Note that, thanks
to the deferred execution of clears, the following idiom is supported
(assuming x occurs in the goal only):
have {x} -> : x = y
An other frequent use of the intro patterns combined with have is the
destruction of existential assumptions like in the tactic:
have [x Px]: exists x : nat, x > 0.
which opens a new subgoal asking for a proof of exists x : nat, x > 0
and a second subgoal in which the witness is introduced under the name
x : nat, and its property under the name Px : x > 0.

An alternative use of the have tactic is to provide the explicit proof
term for the intermediate lemma, using tactics of the form:
have [ident] := term.
This tactic creates a new assumption of type the type ofterm. If the
optional ident is present, this assumption is introduced under the
name ident. Note that the body of the constant is lost for the user.

Again, non inferred implicit arguments and explicit holes are
abstracted. For instance, the tactic:
have H := forall x, (x, x) = (x, x).
adds to the context H : Type -> Prop. This is a schematic example but
the feature is specially useful when the proof term to give involves
for instance a lemma with some hidden implicit arguments.

After the i-pattern, a list of binders is allowed. For example, if
Pos_to_P is a lemma that proves thatP holds for any positive, the
following command:
have H x (y : nat) : 2 * x + y = x + x + y by auto.
will put in the context H : forall x, 2 * x = x + x. A proof term
provided after := can mention these bound variables (that are
automatically introduced with the given names). Since the i-pattern
can be omitted, to avoid ambiguity, bound variables can be surrounded
with parentheses even if no type is specified:
have (x) : 2 * x = x + x by auto.
The i-items and s-item can be used to interpret the asserted
hypothesis with views (see section 11.9) or simplify the resulting
goals.

The have tactic also supports a suff modifier which allows for
asserting that a given statement implies the current goal without
copying the goal itself. For example, given a goal G the tactichave
suff H : P results in the following two goals:
|- P -> G H : P -> G |- G
Note that H is introduced in the second goal. The suff modifier is not
compatible with the presence of a list of binders.


Generating let in context entries with have
```````````````````````````````````````````



Since SSReflect 1.5 the have tactic supports a “transparent” modifier
to generate let in context entries: the @ symbol in front of the
context entry name. For example:
have @i : 'I_n by apply: (Sub m); auto.
generates the following two context entry:
i := Sub m proof_produced_by_auto : 'I_n
Note that the sub-term produced by auto is in general huge and
uninteresting, and hence one may want to hide it.

For this purpose the [: name ] intro pattern and the tacticabstract
(see page ??) are provided. Example:
have [:blurb] @i : 'I_n by apply: (Sub m); abstract: blurb; auto.
generates the following two context entries:
blurb : (m < n) (*1*) i := Sub m blurb : 'I_n
The type of blurb can be cleaned up by its annotations by just
simplifying it. The annotations are there for technical reasons only.

When intro patterns for abstract constants are used in conjunction
with have and an explicit term, they must be used as follows:
have [:blurb] @i : 'I_n := Sub m blurb. by auto.
In this case the abstract constant blurb is assigned by using it in
the term that follows := and its corresponding goal is left to be
solved. Goals corresponding to intro patterns for abstract constants
are opened in the order in which the abstract constants are declared
(not in the “order” in which they are used in the term).

Note that abstract constants do respect scopes. Hence, if a variable
is declared after their introduction, it has to be properly
generalized (i.e. explicitly passed to the abstract constant when one
makes use of it). For example any of the following two lines:
have [:blurb] @i k : 'I_(n+k) by apply: (Sub m); abstract: blurb k;
auto. have [:blurb] @i k : 'I_(n+k) := apply: Sub m (blurb k); first
by auto.
generates the following context:
blurb : (forall k, m < n+k) (*1*) i := fun k => Sub m (blurb k) :
forall k, 'I_(n+k)
Last, notice that the use of intro patterns for abstract constants is
orthogonal to the transparent flag @ for have.


The have tactic and type classes resolution
```````````````````````````````````````````



Since SSReflect 1.5 the have tactic behaves as follows with respect to
type classes inference.


+ have foo : ty. Full inference for ty. The first subgoal demands a
  proof of such instantiated statement.
+ have foo : ty := . No inference for ty. Unresolved instances are
  quantified in ty. The first subgoal demands a proof of such quantified
  statement. Note that no proof term follows :=, hence two subgoals are
  generated.
+ have foo : ty := t. No inference for ty and t.
+ have foo := t. No inference for t. Unresolved instances are
  quantified in the (inferred) type of t and abstracted in t.


The behavior of SSReflect 1.4 and below (never resolve type classes)
can be restored with the option Set SsrHave NoTCResolution.


Variants: the suff and wlog tactics.
````````````````````````````````````



As it is often the case in mathematical textbooks, forward reasoning
may be used in slightly different variants. One of these variants is
to show that the intermediate step L easily implies the initial goal
G. By easily we mean here that the proof of L ⇒ G is shorter than the
one of L itself. This kind of reasoning step usually starts with: “It
suffices to show that …”.

This is such a frequent way of reasoning that SSReflect has a variant
of thehave tactic called suffices (whose abridged name issuff). The
have and suff tactics are equivalent and have the same syntax but:


+ the order of the generated subgoals is inversed
+ but the optional clear item is still performed in the *second*
  branch. This means that the tactic: suff {H} H : forall x : nat, x >=
  0. fails if the context of the current goal indeed contains an
  assumption named H.


The rationale of this clearing policy is to make possible “trivial”
refinements of an assumption, without changing its name in the main
branch of the reasoning.

The have modifier can follow the suff tactic. For example, given a
goal G the tacticsuff have H : P results in the following two goals:
H : P |- G |- (P -> G) -> G
Note that, in contrast with have suff, the name H has been introduced
in the first goal.

Another useful construct is reduction, showing that a particular case
is in fact general enough to prove a general property. This kind of
reasoning step usually starts with: “Without loss of generality, we
can suppose that …”. Formally, this corresponds to the proof of a goal
G by introducing a cut wlog_statement -> G. Hence the user shall
provide a proof for both (wlog_statement -> G) -> G andwlog_statement
-> G. However, such cuts are usually rather painful to perform by
hand, because the statementwlog_statement is tedious to write by hand,
and somtimes even to read.

SSReflect implements this kind of reasoning step through the without
loss tactic, whose short name is wlog. It offers support to describe
the shape of the cut statements, by providing the simplifying
hypothesis and by pointing at the elements of the initial goals which
should be generalized. The general syntax of without loss is:
wlog [suff] [clear-switch] [i-item] : [ident 1 … ident n ] / term
where ident 1 … ident n are identifiers for constants in the context
of the goal. Open syntax is supported for term.

In its defective form:
wlog: / term.
on a goal G, it creates two subgoals: a first one to prove the
formula(term -> G) -> G and a second one to prove the formulaterm ->
G.

:browse confirm wa If the optional list ident 1 … ident n is present
on the left side of /, these constants are generalized in the
premise(term -> G) of the first subgoal. By default the body of local
definitions is erased. This behavior can be inhibited prefixing the
name of the local definition with the @ character.

In the second subgoal, the tactic:
move=> clear-switch i-item.
is performed if at least one of these optional switches is present in
the wlog tactic.

The wlog tactic is specially useful when a symmetry argument
simplifies a proof. Here is an example showing the beginning of the
proof that quotient and reminder of natural number euclidean division
are unique.
Lemma quo_rem_unicity: forall d q1 q2 r1 r2, q1*d + r1 = q2*d + r2 ->
r1 < d -> r2 < d -> (q1, r1) = (q2, r2). move=> d q1 q2 r1 r2. wlog:
q1 q2 r1 r2 / q1 <= q2. by case (le_gt_dec q1 q2)=> H; last symmetry;
eauto with arith.
The wlog suff variant is simpler, since it cutswlog_statement instead
of wlog_statement -> G. It thus opens the goals wlog_statement -> G
and wlog_statement.

In its simplest form the generally have :... tactic is equivalent to
wlog suff :... followed by last first. When the have tactic is used
with the generally (or gen) modifier it accepts an extra identifier
followed by a comma before the usual intro pattern. The identifier
will name the new hypothesis in its more general form, while the intro
pattern will be used to process its instance. For example:
Lemma simple n (ngt0 : 0 < n ) : P n. gen have ltnV, /andP[nge0 neq0]
: n ngt0 / (0 <= n) && (n != 0).
The first subgoal will be
n : nat ngt0 : 0 < n ==================== (0 <= n) && (n != 0)
while the second one will be
n : nat ltnV : forall n, 0 < n -> (0 <= n) && (n != 0) nge0 : 0 <= n
neqn0 : n != 0 ==================== P n


Advanced generalization
+++++++++++++++++++++++

The complete syntax for the items on the left hand side of the /
separator is the following one:
clear-switch | [@] ident | ([@]ident := c-pattern)
Clear operations are intertwined with generalization operations. This
helps in particular avoiding dependency issues while generalizing some
facts.

If an ident is prefixed with the @ prefix mark, then a let-in redex is
created, which keeps track if its body (if any). The syntax
(ident:=c-pattern) allows to generalize an arbitrary term using a
given name. Note that its simplest form (x := y) is just a renaming of
y into x. In particular, this can be useful in order to simulate the
generalization of a section variable, otherwise not allowed. Indeed
renaming does not require the original variable to be cleared.

The syntax (@x := y) generates a let-in abstraction but with the
following caveat: x will not bind y, but its body, whenever y can be
unfolded. This cover the case of both local and global definitions, as
illustrated in the following example:
Section Test. Variable x : nat. Definition addx z := z + x. Lemma test
: x <= addx x. wlog H : (y := x) (@twoy := addx x) / twoy = 2 * y.
The first subgoal is:
(forall y : nat, let twoy := y + y in twoy = 2 * y -> y <= twoy) -> x
<= addx x
To avoid unfolding the term captured by the pattern add x one can use
the pattern id (addx x), that would produce the following first
subgoal:
(forall y : nat, let twoy := addx y in twoy = 2 * y -> y <= twoy) -> x
<= addx x


11.7 Rewriting
--------------



The generalized use of reflection implies that most of the
intermediate results handled are properties of effectively computable
functions. The most efficient mean of establishing such results are
computation and simplification of expressions involving such
functions, i.e., rewriting. SSReflect therefore includes an
extendedrewrite tactic, that unifies and combines most of the
rewriting functionalities.


11.7.1 An extended rewrite tactic
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The main features of the rewrite tactic are:


+ It can perform an entire series of such operations in any subset of
  the goal and/or context;
+ It allows to perform rewriting, simplifications, folding/unfolding
  of definitions, closing of goals;
+ Several rewriting operations can be chained in a single tactic;
+ Control over the occurrence at which rewriting is to be performed is
  significantly enhanced.


The general form of an SSReflect rewrite tactic is:
rewrite rstep + .
The combination of a rewrite tactic with the in tactical (see section
11.4.3) performs rewriting in both the context and the goal.

A rewrite step rstep has the general form:
[r-prefix]r-item
where:





r-prefix ::= [-] [mult] [occ-switch | clear-switch] [[r-pattern]]
r-pattern ::= term | in [ident in] term | [term in | term as ] ident
in term r-item ::= [/]term | s-item



An r-prefix contains annotations to qualify where and how the rewrite
operation should be performed:


+ The optional initial - indicates the direction of the rewriting of
  r-item: if present the direction is right-to-left and it is left-to-
  right otherwise.
+ The multiplier mult (see section 11.6.4) specifies if and how the
  rewrite operation should be repeated.
+ A rewrite operation matches the occurrences of a *rewrite pattern*,
  and replaces these occurrences by an other term, according to the
  given r-item. The optional *redex switch* [r-pattern], which should
  always be surrounded by brackets, gives explicitly this rewrite
  pattern. In its simplest form, it is a regular term. If no explicit
  redex switch is present the rewrite pattern to be matched is inferred
  from ther-item.
+ This optional term, or the r-item, may be preceded by an occurrence
  switch (see section 11.6.3) or a clear item (see section 11.5.3),
  these two possibilities being exclusive. An occurrence switch selects
  the occurrences of the rewrite pattern which should be affected by the
  rewrite operation.


An r-item can be:


+ A *simplification r-item*, represented by as-item (see section
  11.5.4). Simplification operations are intertwined with the possible
  other rewrite operations specified by the list of r-items.
+ A *folding/unfolding r-item*. The tactic:rewrite /termunfolds the
  head constant of term in every occurrence of the first matching of
  term in the goal. In particular, ifmy_def is a (local or global)
  defined constant, the tactic: rewrite /my_def. is analogous to: unfold
  my_def. Conversely: rewrite -/my_def. is equivalent to: fold my_def.
  When an unfold r-item is combined with a redex pattern, a conversion
  operation is performed. A tactic of the form: rewrite -[term 1 ]/term
  2 . is equivalent to: change term 1 with term 2 . If term 2 is a
  single constant and term 1 head symbol is not term 2 , then the head
  symbol of term 1 is repeatedly unfolded until term 2 appears.
  Definition double x := x + x. Definition ddouble x := double (double
  x). Lemma ex1 x : ddouble x = 4 * x. rewrite [ddouble _]/double. The
  resulting goal is: double x + double x = 4 * x *Warning* The SSReflect
  terms containing holes are *not* typed as abstractions in this
  context. Hence the following script: Definition f := fun x y => x + y.
  Goal forall x y, x + y = f y x. move=> x y. rewrite -[f y]/(y + _).
  raises the error message

::

       User error: fold pattern (y + _) does not match redex (f y)

  but the script obtained by replacing the last line with: rewrite -[f y
  x]/(y + _). is valid.
+ A term, which can be:

    + A term whose type has the form: forall (x 1 : A 1 )…(x n : A n ), eq
      term 1 term 2 where eq is the Leibniz equality or a registered setoid
      equality.
    + A list of terms (t 1 ,…,t n ), each t i having a type of the form:
      forall (x 1 : A 1 )…(x n : A n ), eq term 1 term 2 whereeq is the
      Leibniz equality or a registered setoid equality. The tactic: rewrite
      r-prefix(t 1 ,…,t n ). is equivalent to: do [rewrite r-prefix t 1 | …
      | rewrite r-prefix t n ].
    + An anonymous rewrite lemma(_ : term), where term has again the form:
      forall (x 1 : A 1 )…(x n : A n ), eq term 1 term 2 The tactic: rewrite
      (_ : term) is in fact synonym of: cutrewrite (term).




11.7.2 Remarks and examples
~~~~~~~~~~~~~~~~~~~~~~~~~~~




Rewrite redex selection
```````````````````````

The general strategy of SSReflect is to grasp as many redexes as
possible and to let the user select the ones to be rewritten thanks to
the improved syntax for the control of rewriting.

This may be a source of incompatibilities between the two rewrite
tactics.

In a rewrite tactic of the form:

rewrite occ-switch[term 1 ]term 2 .

term 1 is the explicit rewrite redex andterm 2 is the rewrite rule.
This execution of this tactic unfolds as follows:


+ First term 1 and term 2 are βι normalized. Thenterm 2 is put in head
  normal form if the Leibniz equality constructor eq is not the head
  symbol. This may involve ζ reductions.
+ Then, the matching algorithm (see section 11.4.2) determines the
  first subterm of the goal matching the rewrite pattern. The rewrite
  pattern is given by term 1 , if an explicit redex pattern switch is
  provided, or by the type of term 2 otherwise. However, matching skips
  over matches that would lead to trivial rewrites. All the occurrences
  of this subterm in the goal are candidates for rewriting.
+ Then only the occurrences coded by occ-switch (see again section
  11.4.2) are finally selected for rewriting.
+ The left hand side of term 2 is unified with the subterm found by
  the matching algorithm, and if this succeeds, all the selected
  occurrences in the goal are replaced by the right hand side ofterm 2 .
+ Finally the goal is βι normalized.


In the case term 2 is a list of terms, the first top-down (in the
goal) left-to-right (in the list) matching rule gets selected.


Chained rewrite steps
`````````````````````

The possibility to chain rewrite operations in a single tactic makes
scripts more compact and gathers in a single command line a bunch of
surgical operations which would be described by a one sentence in a
pen and paper proof.

Performing rewrite and simplification operations in a single tactic
enhances significantly the concision of scripts. For instance the
tactic:
rewrite /my_def {2}[f _]/= my_eq //=.
unfolds my_def in the goal, simplifies the second occurrence of the
first subterm matching pattern [f _], rewrites my_eq, simplifies the
whole goal and closes trivial goals.

Here are some concrete examples of chained rewrite operations, in the
proof of basic results on natural numbers arithmetic:
Lemma addnS : forall m n, m + n.+1 = (m + n).+1. Proof. by move=> m n;
elim: m. Qed. Lemma addSnnS : forall m n, m.+1 + n = m + n.+1. Proof.
move=> *; rewrite addnS; apply addSn. Qed. Lemma addnCA : forall m n
p, m + (n + p) = n + (m + p). Proof. by move=> m n; elim: m => [|m
Hrec] p; rewrite ?addSnnS -?addnS. Qed. Lemma addnC : forall m n, m +
n = n + m. Proof. by move=> m n; rewrite -{1}[n]addn0 addnCA addn0.
Qed.
Note the use of the ? switch for parallel rewrite operations in the
proof of |*addnCA*|.


Explicit redex switches are matched first
`````````````````````````````````````````

If an r-prefix involves a *redex switch*, the first step is to find a
subterm matching this redex pattern, independently from the left hand
side t1 of the equality the user wants to rewrite.

For instance, if `H` ` : ` `forall` ` ` `t` ` ` `u` `, ` `t` ` + ` `u`
` = ` `u` ` + ` `t` is in the context of a goal `x` ` + ` `y` ` = `
`y` ` + ` `x`, the tactic:
rewrite [y + _]H.
transforms the goal into `x` ` + ` `y` ` = ` `x` ` + ` `y`.

Note that if this first pattern matching is not compatible with the
*r-item*, the rewrite fails, even if the goal contains a correct redex
matching both the redex switch and the left hand side of the equality.
For instance, if `H` ` : ` `forall` ` ` `t` ` ` `u` `, ` `t` ` + ` `u`
` * 0 = ` `t` is in the context of a goal `x` ` + ` `y` ` * 4 + 2 * 0
= ` `x` ` + 2 * 0`, then tactic:
rewrite [x + _]H.
raises the error message:

::

      User error: rewrite rule H doesn't match redex (x + y * 4)


while the tactic:
rewrite (H _ 2).
transforms the goal into `x` ` + ` `y` ` * 4 = ` `x` ` + 2 * 0`.


Occurrence switches and redex switches
``````````````````````````````````````

The tactic:
rewrite {2}[_ + y + 0](_: forall z, z + 0 = z).
transforms the goal:
x + y + 0 = x + y + y + 0 + 0 + (x + y + 0)
into:
x + y + 0 = x + y + y + 0 + 0 + (x + y)
and generates a second subgoal:
forall z : nat, z + 0 = z
The second subgoal is generated by the use of an anonymous lemma in
the rewrite tactic. The effect of the tactic on the initial goal is to
rewrite this lemma at the second occurrence of the first matching `x`
` + ` `y` ` + 0` of the explicit rewrite redex `_` ` + ` `y` ` + 0`.


Occurrence selection and repetition
```````````````````````````````````

Occurrence selection has priority over repetition switches. This means
the repetition of a rewrite tactic specified by a multiplier will
perform matching each time an elementary rewrite operation is
performed. Repeated rewrite tactics apply to every subgoal generated
by the previous tactic, including the previous instances of the
repetition. For example:
Goal forall x y z : nat, x + 1 = x + y + 1. move=> x y z.
creates a goal x + 1 = x + y + 1, which is turned into z = z by the
additional tactic:
rewrite 2!(_ : _ + 1 = z).
In fact, this last tactic generates *three* subgoals, respectively x +
y + 1 = z, z = z and x + 1 = z. Indeed, the second rewrite operation
specified with the 2! multiplier applies to the two subgoals generated
by the first rewrite.


Multi-rule rewriting
````````````````````

The rewrite tactic can be provided a *tuple* of rewrite rules, or more
generally a tree of such rules, since this tuple can feature arbitrary
inner parentheses. We call *multirule* such a generalized rewrite
rule. This feature is of special interest when it is combined with
multiplier switches, which makes the rewrite tactic iterates the
rewrite operations prescribed by the rules on the current goal. For
instance, let us define two triples multi1 andmulti2 as:
Variables (a b c : nat). Hypothesis eqab : a = b. Hypothesis eqac : a
= c.
Executing the tactic:
rewrite (eqab, eqac)
on the goal:
========= a = a
turns it into b = b, as rule eqab is the first to apply among the ones
gathered in the tuple passed to the rewrite tactic. This multirule
(eqab, eqac) is actually a Coq term and we can name it with a
definition:
Definition multi1 := (eqab, eqac).
In this case, the tactic rewrite multi1 is a synonym for(eqab, eqac).
More precisely, a multirule rewrites the first subterm to which one of
the rules applies in a left-to-right traversal of the goal, with the
first rule from the multirule tree in left-to-right order. Matching is
performed according to the algorithm described in Section 11.4.2, but
literal matches have priority. For instance if we add a definition and
a new multirule to our context:
Definition d := a. Hypotheses eqd0 : d = 0. Definition multi2 :=
(eqab, eqd0).
then executing the tactic:
rewrite multi2.
on the goal:
========= d = b
turns it into 0 = b, as rule eqd0 applies without unfolding the
definition of d. For repeated rewrites the selection process is
repeated anew. For instance, if we define:
Hypothesis eq_adda_b : forall x, x + a = b. Hypothesis eq_adda_c :
forall x, x + a = c. Hypothesis eqb0 : b = 0. Definition multi3 :=
(eq_adda_b, eq_adda_c, eqb0).
then executing the tactic:
rewrite 2!multi3.
on the goal:
========= 1 + a = 12 + a
turns it into 0 = 12 + a: it uses eq_adda_b then eqb0 on the left-hand
side only. Now executing the tactic rewrite !multi3 turns the same
goal into 0 = 0.

The grouping of rules inside a multirule does not affect the selection
strategy but can make it easier to include one rule set in another or
to (universally) quantify over the parameters of a subset of rules (as
there is special code that will omit unnecessary quantifiers for rules
that can be syntactically extracted). It is also possible to reverse
the direction of a rule subset, using a special dedicated syntax: the
tactic rewrite (= multi1) is equivalent torewrite multi1_rev with:
Hypothesis eqba : b = a. Hypothesis eqca : c = a. Definition
multi1_rev := (eqba, eqca).
except that the constants eqba, eqab, mult1_rev have not been created.

Rewriting with multirules is useful to implement simplification or
transformation procedures, to be applied on terms of small to medium
size. For instance the library `ssrnat` provides two implementations
for arithmetic operations on natural numbers: an elementary one and a
tail recursive version, less inefficient but also less convenient for
reasoning purposes. The library also provides one lemma per such
operation, stating that both versions return the same values when
applied to the same arguments:
Lemma addE : add =2 addn. Lemma doubleE : double =1 doublen. Lemma
add_mulE n m s : add_mul n m s = addn (muln n m) s. Lemma mulE : mul
=2 muln. Lemma mul_expE m n p : mul_exp m n p = muln (expn m n) p.
Lemma expE : exp =2 expn. Lemma oddE : odd =1 oddn.
The operation on the left hand side of each lemma is the efficient
version, and the corresponding naive implementation is on the right
hand side. In order to reason conveniently on expressions involving
the efficient operations, we gather all these rules in the definition
|*trecE*|:
Definition trecE := (addE, (doubleE, oddE), (mulE, add_mulE, (expE,
mul_expE))).
The tactic:
rewrite !trecE.
restores the naive versions of each operation in a goal involving the
efficient ones, e.g. for the purpose of a correctness proof.


Wildcards vs abstractions
`````````````````````````

The rewrite tactic supports r-items containing holes. For example in
the tactic (1):
rewrite (_ : _ * 0 = 0).
the term _ * 0 = 0 is interpreted as forall n : nat, n * 0 = 0. Anyway
this tactic is *not* equivalent to the tactic (2):
rewrite (_ : forall x, x * 0 = 0).
The tactic (1) transforms the goal `(` `y` ` * 0) + ` `y` ` * (` `z` `
* 0) = 0` into y * (z * 0) = 0 and generates a new subgoal to prove
the statement y * 0 = 0, which is the *instance* of the
forall x, x * 0 = 0 rewrite rule that has been used to perform the
rewriting. On the other hand, tactic (2) performs the same rewriting
on the current goal but generates a subgoal to prove forall x, x * 0 =
0.


When SSReflect rewrite fails on standard Coq licit rewrite
``````````````````````````````````````````````````````````

In a few cases, the SSReflect rewrite tactic fails rewriting some
redexes which standard Coq successfully rewrites. There are two main
cases:


+ SSReflect never accepts to rewrite indeterminate patterns like:
  Lemma foo : forall x : unit, x = tt. SSReflect will however accept the
  ηζ expansion of this rule: Lemma fubar : forall x : unit, (let u := x
  in u) = tt.
+ In standard Coq, suppose that we work in the following context:
  Variable g : nat -> nat. Definition f := g. then rewriting H : forall
  x, f x = 0 in the goalg 3 + g 3 = g 6 succeeds and transforms the goal
  into 0 + 0 = g 6.This rewriting is not possible in SSReflect because
  there is no occurrence of the head symbol f of the rewrite rule in the
  goal. Rewriting with H first requires unfolding the occurrences off
  where the substitution is to be performed (here there is a single such
  occurrence), using tactic rewrite /f (for a global replacement of f by
  g) or rewrite pattern/f, for a finer selection.



Existential metavariables and rewriting
```````````````````````````````````````

The rewrite tactic will not instantiate existing existential
metavariables when matching a redex pattern.

If a rewrite rule generates a goal with new existential metavariables,
these will be generalized as for apply (see page ??) and corresponding
new goals will be generated. For example, consider the following
script:
Lemma ex3 (x : 'I_2) y (le_1 : y < 1) (E : val x = y) : Some x = insub
y. rewrite insubT ?(leq_trans le_1)// => le_2.
Since insubT has the following type:
forall T P (sT : subType P) (x : T) (Px : P x), insub x = Some (Sub x
Px)
and since the implicit argument corresponding to the Px abstraction is
not supplied by the user, the resulting goal should be Some x = Some
(Sub y ? Px ). Instead, SSReflect rewrite tactic generates the two
following goals:
y < 2 forall Hyp0 : y < 2, Some x = Some (Sub y Hyp0)
The script closes the former with ?(leq_trans le_1)//, then it
introduces the new generalization naming it le_2.
x : 'I_2 y : nat le_1 : y < 1 E : val x = y le_2 : y < 2
============================ Some x = Some (Sub y le_2)
As a temporary limitation, this behavior is available only if the
rewriting rule is stated using Leibniz equality (as opposed to setoid
relations). It will be extended to other rewriting relations in the
future.


11.7.3 Locking, unlocking
~~~~~~~~~~~~~~~~~~~~~~~~~



As program proofs tend to generate large goals, it is important to be
able to control the partial evaluation performed by the simplification
operations that are performed by the tactics. These evaluations can
for example come from a /= simplification switch, or from rewrite
steps which may expand large terms while performing conversion. We
definitely want to avoid repeating large subterms of the goal in the
proof script. We do this by “clamping down” selected function symbols
in the goal, which prevents them from being considered in
simplification or rewriting steps. This clamping is accomplished by
using the occurrence switches (see section11.4.2) together with “term
tagging” operations.

SSReflect provides two levels of tagging.

The first one uses auxiliary definitions to introduce a provably equal
copy of any term t. However this copy is (on purpose) *not
convertible* to t in the Coq system 8 . The job is done by the
following construction:
Lemma master_key : unit. Proof. exact tt. Qed. Definition locked A :=
let: tt := master_key in fun x : A => x. Lemma lock : forall A x, x =
locked x :> A.
Note that the definition of |*master_key*| is explicitly opaque. The
equation t = locked t given by the lock lemma can be used for
selective rewriting, blocking on the fly the reduction in the term t.
For example the script:
Require Import List. Variable A : Type. Fixpoint my_has (p : A ->
bool)(l : list A){struct l} : bool:= match l with |nil => false |cons
x l => p x || (my_has p l) end. Goal forall a x y l, a x = true ->
my_has a ( x :: y :: l) = true. move=> a x y l Hax.
where `||` denotes the boolean disjunction, results in a goalmy_has a
( x :: y :: l) = true. The tactic:
rewrite {2}[cons]lock /= -lock.
turns it into a x || my_has a (y :: l) = true. Let us now start by
reducing the initial goal without blocking reduction. The script:
Goal forall a x y l, a x = true -> my_has a ( x :: y :: l) = true.
move=> a x y l Hax /=.
creates a goal (a x) || (a y) || (my_has a l) = true. Now the tactic:
rewrite {1}[orb]lock orbC -lock.
where orbC states the commutativity of orb, changes the goal into
(a x) || (my_has a l) || (a y) = true: only the arguments of the
second disjunction where permuted.

It is sometimes desirable to globally prevent a definition from being
expanded by simplification; this is done by adding locked in the
definition.

For instance, the function |*fgraph_of_fun*| maps a function whose
domain and codomain are finite types to a concrete representation of
its (finite) graph. Whatever implementation of this transformation we
may use, we want it to be hidden to simplifications and tactics, to
avoid the collapse of the graph object:
Definition fgraph_of_fun := locked (fun (d1 :finType) (d2 :eqType) (f
: d1 -> d2) => Fgraph (size_maps f _)).
We provide a special tactic unlock for unfolding such definitions
while removing “locks”, e.g., the tactic:

unlock occ-switchfgraph_of_fun.

replaces the occurrence(s) of fgraph_of_fun coded by the occ-switch
with (Fgraph (size_maps _ _)) in the goal.

We found that it was usually preferable to prevent the expansion of
some functions by the partial evaluation switch “/=”, unless this
allowed the evaluation of a condition. This is possible thanks to an
other mechanism of term tagging, resting on the following *Notation*:
Notation "'nosimpl' t" := (let: tt := tt in t).
The term (nosimpl t) simplifies to t *except* in a definition. More
precisely, given:
Definition foo := (nosimpl bar).
the term foo (or (foo t’)) will *not* be expanded by the *simpl*
tactic unless it is in a forcing context (e.g., inmatch foo t’ with …
end, foo t’ will be reduced if this allowsmatch to be reduced). Note
that nosimpl bar is simply notation for a term that reduces to bar;
hence unfold foo will replacefoo by bar, and fold foo will replace bar
byfoo.

*Warning* The nosimpl trick only works if no reduction is apparent in
t; in particular, the declaration:
Definition foo x := nosimpl (bar x).
will usually not work. Anyway, the common practice is to tag only the
function, and to use the following definition, which blocks the
reduction as expected:
Definition foo x := nosimpl bar x.
A standard example making this technique shine is the case of
arithmetic operations. We define for instance:
Definition addn := nosimpl plus.
The operation addn behaves exactly like plus, except that(addn (S n)
m) will not simplify spontaneously to (S (addn n m)) (the two terms,
however, are inter-convertible). In addition, the unfolding step:
rewrite /addn
will replace addn directly with plus, so the nosimpl form is
essentially invisible.


11.7.4 Congruence
~~~~~~~~~~~~~~~~~



Because of the way matching interferes with type families parameters,
the tactic:
apply: my_congr_property.
will generally fail to perform congruence simplification, even on
rather simple cases. We therefore provide a more robust alternative in
which the function is supplied:
congr [int] term
This tactic:


+ checks that the goal is a Leibniz equality
+ matches both sides of this equality with “term applied to some
  arguments”, inferring the right number of arguments from the goal and
  the type of term. This may expand some definitions or fixpoints.
+ generates the subgoals corresponding to pairwise equalities of the
  arguments present in the goal.


The goal can be a non dependent product P -> Q. In that case, the
system asserts the equation P = Q, uses it to solve the goal, and
calls the congr tactic on the remaining goalP = Q. This can be useful
for instance to perform a transitivity step, like in the following
situation:
x, y, z : nat =============== x = y -> x = z
the tactic congr (_ = _) turns this goal into:
x, y, z : nat =============== y = z
which can also be obtained starting from:
x, y, z : nat h : x = y =============== x = z
and using the tactic congr (_ = _): h.

The optional int forces the number of arguments for which the tactic
should generate equality proof obligations.

This tactic supports equalities between applications with dependent
arguments. Yet dependent arguments should have exactly the same
parameters on both sides, and these parameters should appear as first
arguments.

The following script:
Definition f n := match n with 0 => plus | S _ => mult end. Definition
g (n m : nat) := plus. Goal forall x y, f 0 x y = g 1 1 x y. by move=>
x y; congr plus. Qed.
shows that the congr tactic matches plus with f 0 on the left hand
side and g 1 1 on the right hand side, and solves the goal.

The script:
Goal forall n m, m <= n -> S m + (S n - S m) = S n. move=> n m Hnm;
congr S; rewrite -/plus.
generates the subgoal m + (S n - S m) = n. The tacticrewrite -/plus
folds back the expansion of plus which was necessary for matching both
sides of the equality with an application of S.

Like most SSReflect arguments, term can contain wildcards. The script:
Goal forall x y, x + (y * (y + x - x)) = x * 1 + (y + 0) * y. move=> x
y; congr ( _ + (_ * _)).
generates three subgoals, respectively x = x * 1, y = y + 0 and y + x
- x = y.


11.8 Contextual patterns
------------------------



The simple form of patterns used so far, terms possibly containing
wild cards, often require an additional occ-switch to be specified.
While this may work pretty fine for small goals, the use of
polymorphic functions and dependent types may lead to an invisible
duplication of functions arguments. These copies usually end up in
types hidden by the implicit arguments machinery or by user defined
notations. In these situations computing the right occurrence numbers
is very tedious because they must be counted on the goal as printed
after setting the Printing All flag. Moreover the resulting script is
not really informative for the reader, since it refers to occurrence
numbers he cannot easily see.

Contextual patterns mitigate these issues allowing to specify
occurrences according to the context they occur in.


11.8.1 Syntax
~~~~~~~~~~~~~

The following table summarizes the full syntax ofc-pattern and the
corresponding subterm(s) identified by the pattern. In the third
column we use s.m.r. for “the subterms matching the redex” specified
in the second column.
c-pattern redex subterms affected term term all occurrences of term
ident in term subterm of term selected by ident all the subterms
identified by ident in all the occurrences of term term 1 in ident in
term 2 term 1 in all s.m.r. in all the subterms identified by ident in
all the occurrences of term 2 term 1 as ident in term 2 term 1 in all
the subterms identified by ident in all the occurrences of term 2
[term 1 /ident]
The rewrite tactic supports two more patterns obtained prefixing the
first two with in. The intended meaning is that the pattern identifies
all subterms of the specified context. Therewrite tactic will infer a
pattern for the redex looking at the rule used for rewriting.
r-pattern redex subterms affected in term inferred from rule in all
s.m.r. in all occurrences of term in ident in term inferred from rule
in all s.m.r. in all the subterms identified by ident in all the
occurrences of term
The first c-pattern is the simplest form matching any context but
selecting a specific redex and has been described in the previous
sections. We have seen so far that the possibility of selecting a
redex using a term with holes is already a powerful mean of redex
selection. Similarly, any terms provided by the user in the more
complex forms of c-patterns presented in the tables above can contain
holes.

For a quick glance at what can be expressed with the lastr-pattern
consider the goal a = b and the tactic
rewrite [in X in _ = X]rule.
It rewrites all occurrences of the left hand side of rule insideb only
(a, and the hidden type of the equality, are ignored). Note that the
variant rewrite [X in _ = X]rule would have rewritten b exactly (i.e.,
it would only work if b and the left hand side of rule can be
unified).


11.8.2 Matching contextual patterns
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The c-patterns and r-patterns involvingterms with holes are matched
against the goal in order to find a closed instantiation. This
matching proceeds as follows:
c-pattern instantiation order and place for term i and redex term term
is matched against the goal, redex is unified with the instantiation
of term ident in term term is matched against the goal, redex is
unified with the subterm of the instantiation of term identified by
ident term 1 in ident in term 2 term 2 is matched against the goal,
term 1 is matched against the subterm of the instantiation of term 1
identified by ident, redex is unified with the instantiation of term 1
term 1 as ident in term 2 term 2 [term 1 /ident] is matched against
the goal, redex is unified with the instantiation of term 1
In the following patterns, the redex is intended to be inferred from
the rewrite rule.
r-pattern instantiation order and place for term i and redex in ident
in term term is matched against the goal, the redex is matched against
the subterm of the instantiation of term identified by ident in term
term is matched against the goal, redex is matched against the
instantiation of term


11.8.3 Examples
~~~~~~~~~~~~~~~


Contextual pattern in set and the : tactical
````````````````````````````````````````````

As already mentioned in section 11.4.2 the set tactic takes as an
argument a term in open syntax. This term is interpreted as the
simplest for of c-pattern. To void confusion in the grammar, open
syntax is supported only for the simplest form of patterns, while
parentheses are required around more complex patterns.
set t := (X in _ = X). set t := (a + _ in X in _ = X).
Given the goal a + b + 1 = b + (a + 1) the first tactic captures b +
(a + 1), while the latter a + 1.

Since the user may define an infix notation for in the former tactic
may result ambiguous. The disambiguation rule implemented is to prefer
patterns over simple terms, but to interpret a pattern with double
parentheses as a simple term. For example the following tactic would
capture any occurrence of the term ‘a in A’.
set t := ((a in A)).
Contextual pattern can also be used as arguments of the : tactical.
For example:
elim: n (n in _ = n) (refl_equal n).


Contextual patterns in rewrite
``````````````````````````````

As a more comprehensive example consider the following goal:
(x.+1 + y) + f (x.+1 + y) (z + (x + y).+1) = 0
The tactic rewrite [in f _ _]addSn turns it into:
(x.+1 + y) + f (x + y).+1 (z + (x + y).+1) = 0
since the simplification rule addSn is applied only under the f
symbol. Then we simplify also the first addition and expand 0 into
0+0.
rewrite addSn -[X in _ = X]addn0.
obtaining:
(x + y).+1 + f (x + y).+1 (z + (x + y).+1) = 0 + 0
Note that the right hand side of addn0 is undetermined, but the
rewrite pattern specifies the redex explicitly. The right hand side
ofaddn0 is unified with the term identified by X, 0 here.

The following pattern does not specify a redex, since it identifies an
entire region, hence the rewrite rule has to be instantiated
explicitly. Thus the tactic:
rewrite -{2}[in X in _ = X](addn0 0).
changes the goal as follows:
(x + y).+1 + f (x + y).+1 (z + (x + y).+1) = 0 + (0 + 0)
The following tactic is quite tricky:
rewrite [_.+1 in X in f _ X](addnC x.+1).
and the resulting goals is:
(x + y).+1 + f (x + y).+1 (z + (y + x.+1)) = 0 + (0 + 0)
The explicit redex _.+1 is important since its head constant S differs
from the head constant inferred from(addnC x.+1) (that is addn,
denoted + here). Moreover, the pattern f _ X is important to rule out
the first occurrence of (x + y).+1. Last, only the subterms of f _ X
identified by X are rewritten, thus the first argument of f is skipped
too. Also note the pattern _.+1 is interpreted in the context
identified by X, thus it gets instantiated to (y + x).+1 and not (x +
y).+1.

The last rewrite pattern allows to specify exactly the shape of the
term identified by X, that is thus unified with the left hand side of
the rewrite rule.
rewrite [x.+1 + y as X in f X _]addnC.
The resulting goal is:
(x + y).+1 + f (y + x.+1) (z + (y + x.+1)) = 0 + (0 + 0)


11.8.4 Patterns for recurrent contexts
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The user can define shortcuts for recurrent contexts corresponding to
theident in term part. The notation scope identified with %pattern
provides a special notation ‘(X in t)’ the user must adopt to define
context shortcuts.

The following example is taken from ssreflect.v where theLHS and RHS
shortcuts are defined.
Notation RHS := (X in _ = X)%pattern. Notation LHS := (X in X =
_)%pattern.
Shortcuts defined this way can be freely used in place of the trailing
ident in term part of any contextual pattern. Some examples follow:
set rhs := RHS. rewrite [in RHS]rule. case: (a + _ in RHS).


11.9 Views and reflection
-------------------------



The bookkeeping facilities presented in section 11.5 are crafted to
ease simultaneous introductions and generalizations of facts and
casing, naming … operations. It also a common practice to make a stack
operation immediately followed by an *interpretation* of the fact
being pushed, that is, to apply a lemma to this fact before passing it
to a tactic for decomposition, application and so on.

SSReflect provides a convenient, unified syntax to combine these
interpretation operations with the proof stack operations. This *view
mechanism* relies on the combination of the / view switch with
bookkeeping tactics and tacticals.


11.9.1 Interpreting eliminations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~



The view syntax combined with the elim tactic specifies an elimination
scheme to be used instead of the default, generated, one. Hence the
SSReflect tactic:
elim/V.
is a synonym for:
intro top; elim top using V; clear top.
where top is a fresh name and V any second-order lemma.

Since an elimination view supports the two bookkeeping tacticals of
discharge and introduction (see section 11.5), the SSReflect tactic:
elim/V: x => y.
is a synonym for:
elim x using V; clear x; intro y.
where x is a variable in the context, y a fresh name and V any second
order lemma; SSReflect relaxes the syntactic restrictions of the Coq
elim. The first pattern following : can be a _ wildcard if the
conclusion of the view V specifies a pattern for its last argument
(e.g., if V is a functional induction lemma generated by the Function
command).

The elimination view mechanism is compatible with the equation name
generation (see section 11.5.5).

The following script illustrate a toy example of this feature. Let us
define a function adding an element at the end of a list:
Require Import List. Variable d : Type. Fixpoint add_last(s : list d)
(z : d) {struct s} : list d := match s with | nil => z :: nil | cons x
s' => cons x (add_last s' z) end.
One can define an alternative, reversed, induction principle on
inductively defined lists, by proving the following lemma:
Lemma last_ind_list : forall (P : list d -> Type), P nil -> (forall (s
: list d) (x : d), P s -> P (add_last s x)) -> forall s : list d, P s.
Then the combination of elimination views with equation names result
in a concise syntax for reasoning inductively using the user defined
elimination scheme. The script:
Goal forall (x : d)(l : list d), l = l. move=> x l. elim/last_ind_list
E : l=> [| u v]; last first.
generates two subgoals: the first one to prove nil = nil in a context
featuring E : l = nil and the second to proveadd_last u v = add_last u
v, in a context containingE : l = add_last u v.

User provided eliminators (potentially generated with theFunction
Coq’s command) can be combined with the type family switches described
in section 11.5.6. Consider an eliminatorfoo_ind of type:

foo_ind : forall …, forall x : T, P p 1 … p m

and consider the tactic

elim/foo_ind: e 1 … / e n

The elim/ tactic distinguishes two cases:

:truncated eliminator: when x does not occur in P p 1 … p m and the
  type of e n unifies with T and e n is not _. In that case, e n is
  passed to the eliminator as the last argument (x in foo_ind) and e n−1
  … e 1 are used as patterns to select in the goal the occurrences that
  will be bound by the predicate P, thus it must be possible to unify
  the sub-term of the goal matched by e n−1 with p m , the one matched
  bye n−2 with p m−1 and so on.
:regular eliminator: in all the other cases. Here it must be possible
  to unify the term matched bye n with p m , the one matched bye n−1
  with p m−1 and so on. Note that standard eliminators have the shape
  …forall x, P … x, thuse n is the pattern identifying the eliminated
  term, as expected.


As explained in section 11.5.6, the initial prefix ofe i can be
omitted.

Here an example of a regular, but non trivial, eliminator:
Function plus (m n : nat) {struct n} : nat := match n with 0 => m | S
p => S (plus m p) end.
The type of plus_ind is
plus_ind : forall (m : nat) (P : nat -> nat -> Prop), (forall n : nat,
n = 0 -> P 0 m) -> (forall n p : nat, n = p.+1 -> P p (plus m p) -> P
p.+1 (plus m p).+1) -> forall n : nat, P n (plus m n)
Consider the following goal
Lemma exF x y z: plus (plus x y) z = plus x (plus y z).
The following tactics are all valid and perform the same elimination
on that goal.
elim/plus_ind: z / (plus _ z). elim/plus_ind: {z}(plus _ z).
elim/plus_ind: {z}_. elim/plus_ind: z / _.
In the two latter examples, being the user provided pattern a
wildcard, the pattern inferred from the type of the eliminator is used
instead. For both cases it is (plus _ _) and matches the subterm plus
(plus x y) z thus instantiating the latter _ with z. Note that the
tacticelim/plus_ind: y / _ would have resulted in an error, since y
and z do no unify but the type of the eliminator requires the second
argument ofP to be the same as the second argument of plus in the
second argument of P.

Here an example of a truncated eliminator. Consider the goal
p : nat_eqType n : nat n_gt0 : 0 < n pr_p : prime p =================
p %| \prod_(i <- prime_decomp n | i \in prime_decomp n) i.1 ^ i.2 ->
exists2 x : nat * nat, x \in prime_decomp n & p = x.1
and the tactic
elim/big_prop: _ => [| u v IHu IHv | [q e] /=].
where the type of the eliminator is
big_prop: forall (R : Type) (Pb : R -> Type) (idx : R) (op1 : R -> R
-> R), Pb idx -> (forall x y : R, Pb x -> Pb y -> Pb (op1 x y)) ->
forall (I : Type) (r : seq I) (P : pred I) (F : I -> R), (forall i :
I, P i -> Pb (F i)) -> Pb (\big[op1/idx]_(i <- r | P i) F i)
Since the pattern for the argument of Pb is not specified, the
inferred one is used instead: (
big[_/_]_(i <- _ | _ i) _ i), and after the introductions, the
following goals are generated.
subgoal 1 is: p %| 1 -> exists2 x : nat * nat, x \in prime_decomp n &
p = x.1 subgoal 2 is: p %| u * v -> exists2 x : nat * nat, x \in
prime_decomp n & p = x.1 subgoal 3 is: (q, e) \in prime_decomp n -> p
%| q ^ e -> exists2 x : nat * nat, x \in prime_decomp n & p = x.1
Note that the pattern matching algorithm instantiated all the
variables occurring in the pattern.


11.9.2 Interpreting assumptions
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~



Interpreting an assumption in the context of a proof is applying it a
correspondence lemma before generalizing, and/or decomposing it. For
instance, with the extensive use of boolean reflection (see section
11.9.4), it is quite frequent to need to decompose the logical
interpretation of (the boolean expression of) a fact, rather than the
fact itself. This can be achieved by a combination of move : _ => _
switches, like in the following script, where || is a notation for the
boolean disjunction:
Variables P Q : bool -> Prop. Hypothesis P2Q : forall a b, P (a || b)
-> Q a. Goal forall a, P (a || a) -> True. move=> a HPa; move:
{HPa}(P2Q _ _ HPa) => HQa.
which transforms the hypothesis HPn : P n which has been introduced
from the initial statement into HQn : Q n. This operation is so common
that the tactic shell has specific syntax for it. The following
scripts:
Goal forall a, P (a || a) -> True. move=> a HPa; move/P2Q: HPa => HQa.
or more directly:
Goal forall a, P (a || a) -> True. move=> a; move/P2Q=> HQa.
are equivalent to the former one. The former script shows how to
interpret a fact (already in the context), thanks to the discharge
tactical (see section 11.5.3) and the latter, how to interpret the top
assumption of a goal. Note that the number of wildcards to be inserted
to find the correct application of the view lemma to the hypothesis
has been automatically inferred.

The view mechanism is compatible with the case tactic and with the
equation name generation mechanism (see section 11.5.5):
Variables P Q: bool -> Prop. Hypothesis Q2P : forall a b, Q (a || b)
-> P a \/ P b. Goal forall a b, Q (a || b) -> True. move=> a b;
case/Q2P=> [HPa | HPb].
creates two new subgoals whose contexts no more containHQ : Q (a || b)
but respectively HPa : P a andHPb : P b. This view tactic performs:
move=> a b HQ; case: {HQ}(Q2P _ _ HQ) => [HPa | HPb].
The term on the right of the / view switch is called a *view lemma*.
Any SSReflect term coercing to a product type can be used as a view
lemma.

The examples we have given so far explicitly provide the direction of
the translation to be performed. In fact, view lemmas need not to be
oriented. The view mechanism is able to detect which application is
relevant for the current goal. For instance, the script:
Variables P Q: bool -> Prop. Hypothesis PQequiv : forall a b, P (a ||
b) <-> Q a. Goal forall a b, P (a || b) -> True. move=> a b;
move/PQequiv=> HQab.
has the same behavior as the first example above.

The view mechanism can insert automatically a *view hint* to transform
the double implication into the expected simple implication. The last
script is in fact equivalent to:
Goal forall a b, P (a || b) -> True. move=> a b; move/(iffLR (PQequiv
_ _)).
where:
Lemma iffLR : forall P Q, (P <-> Q) -> P -> Q.


Specializing assumptions
````````````````````````



The special case when the *head symbol* of the view lemma is a
wildcard is used to interpret an assumption by *specializing* it. The
view mechanism hence offers the possibility to apply a higher-order
assumption to some given arguments.

For example, the script:
Goal forall z, (forall x y, x + y = z -> z = x) -> z = 0. move=> z;
move/(_ 0 z).
changes the goal into:
(0 + z = z -> z = 0) -> z = 0


11.9.3 Interpreting goals
~~~~~~~~~~~~~~~~~~~~~~~~~



In a similar way, it is also often convenient to interpret a goal by
changing it into an equivalent proposition. The view mechanism of
SSReflect has a special syntax apply/ for combining simultaneous goal
interpretation operations and bookkeeping steps in a single tactic.

With the hypotheses of section 11.9.2, the following script, where
`~~` denotes the boolean negation:
Goal forall a, P ((~~ a) || a). move=> a; apply/PQequiv.
transforms the goal into Q ( a), and is equivalent to:
Goal forall a, P ((~~ a) || a). move=> a; apply: (iffRL (PQequiv _
_)).
where iffLR is the analogous of iffRL for the converse implication.

Any SSReflect term whose type coerces to a double implication can be
used as a view for goal interpretation.

Note that the goal interpretation view mechanism supports bothapply
and exact tactics. As expected, a goal interpretation view command
exact/term should solve the current goal or it will fail.

*Warning* Goal interpretation view tactics are *not* compatible with
the bookkeeping tactical => since this would be redundant with the
apply: term => _ construction.


11.9.4 Boolean reflection
~~~~~~~~~~~~~~~~~~~~~~~~~

In the Calculus of Inductive Construction, there is an obvious
distinction between logical propositions and boolean values. On the
one hand, logical propositions are objects of *sort* Prop which is the
carrier of intuitionistic reasoning. Logical connectives in Prop are
*types*, which give precise information on the structure of their
proofs; this information is automatically exploited by Coq tactics.
For example, Coq knows that a proof of `A` ` \/ ` `B` is either a
proof of A or a proof of B. The tactics left and right change the goal
`A` ` \/ ` `B` to A and B, respectively; dualy, the tactic case
reduces the goal `A` ` \/ ` `B` ` => ` `G` to two subgoals A => G and
B => G.

On the other hand, bool is an inductive *datatype* with two
constructors true and false. Logical connectives on bool are
*computable functions*, defined by their truth tables, using case
analysis:
Definition (b1 || b2) := if b1 then true else b2.
Properties of such connectives are also established using case
analysis: the tactic by case: b solves the goal
b || ~~ b = true
by replacing b first by true and then by false; in either case, the
resulting subgoal reduces by computation to the trivialtrue = true.

Thus, Prop and bool are truly complementary: the former supports
robust natural deduction, the latter allows brute-force
evaluation.SSReflect supplies a generic mechanism to have the best of
the two worlds and move freely from a propositional version of a
decidable predicate to its boolean version.

First, booleans are injected into propositions using the coercion
mechanism:
Coercion is_true (b : bool) := b = true.
This allows any boolean formula b to be used in a context where Coq
would expect a proposition, e.g., after Lemma … : . It is then
interpreted as (is_true b), i.e., the proposition b = true. Coercions
are elided by the pretty-printer, so they are essentially transparent
to the user.


11.9.5 The reflect predicate
~~~~~~~~~~~~~~~~~~~~~~~~~~~~



To get all the benefits of the boolean reflection, it is in fact
convenient to introduce the following inductive predicatereflect to
relate propositions and booleans:
Inductive reflect (P: Prop): bool -> Type := | Reflect_true: P =>
reflect P true | Reflect_false: ~P => reflect P false.
The statement (reflect P b) asserts that (is_true b) and P are
logically equivalent propositions.

For instance, the following lemma:
Lemma andP: forall b1 b2, reflect (b1 /\ b2) (b1 && b2).
relates the boolean conjunction to the logical one `/\`. Note that in
andP, b1 and b2 are two boolean variables and the proposition `b1` `
/\ ` `b2` hides two coercions. The conjunction of b1 and b2 can then
be viewed as `b1` ` /\ ` `b2` or as b1b2.

Expressing logical equivalences through this family of inductive types
makes possible to take benefit from *rewritable equations* associated
to the case analysis of Coq’s inductive types.

Since the equivalence predicate is defined in Coq as:
Definition iff (A B:Prop) := (A -> B) /\ (B -> A).
where /
is a notation for and:
Inductive and (A B:Prop) : Prop := conj : A -> B -> and A B
This make case analysis very different according to the way an
equivalence property has been defined.

For instance, if we have proved the lemma:
Lemma andE: forall b1 b2, (b1 /\ b2) <-> (b1 && b2).
let us compare the respective behaviours of andE and andP on a goal:
Goal forall b1 b2, if (b1 && b2) then b1 else ~~(b1||b2).
The command:
move=> b1 b2; case (@andE b1 b2).
generates a single subgoal:
(b1 && b2 -> b1 /\ b2) -> (b1 /\ b2 -> b1 && b2) -> if b1 && b2 then
b1 else ~~ (b1 || b2)
while the command:
move=> b1 b2; case (@andP b1 b2).
generates two subgoals, respectively `b1` ` /\ ` `b2` ` -> ` `b1` and
`~ (` `b1` ` /\ ` `b2` `) -> ~~ (` `b1` ` || ` `b2` `)`.

Expressing reflection relation through the reflect predicate is hence
a very convenient way to deal with classical reasoning, by case
analysis. Using the reflect predicate allows moreover to program rich
specifications inside its two constructors, which will be
automatically taken into account during destruction. This
formalisation style gives far more efficient specifications than
quantified (double) implications.

A naming convention in SSReflect is to postfix the name of view lemmas
with P. For example, orP relates || and `\/`, negP relates `~~` and
`~`.

The view mechanism is compatible with reflect predicates.

For example, the script
Goal forall a b : bool, a -> b -> a /\\ b. move=> a b Ha Hb;
apply/andP.
changes the goal `a` ` /\ ` `b` to ab (see section 11.9.3).

Conversely, the script
Goal forall a b : bool, a /\ b -> a. move=> a b; move/andP.
changes the goal `a` ` /\ ` `b` ` -> ` `a` into ab -> a (see
section11.9.2).

The same tactics can also be used to perform the converse operation,
changing a boolean conjunction into a logical one. The view mechanism
guesses the direction of the transformation to be used i.e., the
constructor of the reflect predicate which should be chosen.


11.9.6 General mechanism for interpreting goals and assumptions
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


Specializing assumptions
````````````````````````



The SSReflect tactic:

move/(_ term 1 … term n )

is equivalent to the tactic:

intro top; generalize (top term 1 … term n ); clear top.

where top is a fresh name for introducing the top assumption of the
current goal.


Interpreting assumptions
````````````````````````

The general form of an assumption view tactic is:
[move | case] / term 0
The term term 0 , called the *view lemma* can be:


+ a (term coercible to a) function;
+ a (possibly quantified) implication;
+ a (possibly quantified) double implication;
+ a (possibly quantified) instance of the reflect predicate (see
  section 11.9.5).


Let top be the top assumption in the goal.

There are three steps in the behaviour of an assumption view tactic:


+ It first introduces `top`.
+ If the type of term 0 is neither a double implication nor an
  instance of the reflect predicate, then the tactic automatically
  generalises a term of the form: (term 0 term 1 … term n ) where the
  terms term 1 … term n instantiate the possible quantified variables of
  term 0 , in order for(term 0 term 1 … term n top) to be well typed.
+ If the type of term 0 is an equivalence, or an instance of the
  reflect predicate, it generalises a term of the form: (term vh (term 0
  term 1 … term n )) where the term term vh inserted is called an
  *assumption interpretation view hint*.
+ It finally clears top.


For a case/term 0 tactic, the generalisation step is replaced by a
case analysis step.

*View hints* are declared by the user (see section11.9.8) and are
stored in the Hint View database. The proof engine automatically
detects from the shape of the top assumption top and of the view lemma
term 0 provided to the tactic the appropriate view hint in the
database to be inserted.

If term 0 is a double implication, then the view hint A will be one of
the defined view hints for implication. These hints are by default the
ones present in the file ssreflect.v:
Lemma iffLR : forall P Q, (P <-> Q) -> P -> Q.
which transforms a double implication into the left-to-right one, or:
Lemma iffRL : forall P Q, (P <-> Q) -> Q -> P.
which produces the converse implication. In both cases, the two
firstProp arguments are implicit.

If term 0 is an instance of the reflect predicate, then A will be one
of the defined view hints for the reflect predicate, which are by
default the ones present in the file ssrbool.v. These hints are not
only used for choosing the appropriate direction of the translation,
but they also allow complex transformation, involving negations. For
instance the hint:
Lemma introN : forall (P : Prop) (b : bool), reflect P b -> ~ P -> ~~
b.
makes the following script:
Goal forall a b : bool, a -> b -> ~~ (a && b). move=> a b Ha Hb.
apply/andP.
transforms the goal into (a / b). In fact 9 this last script does not
exactly use the hint introN, but the more general hint:
Lemma introNTF : forall (P : Prop) (b c : bool), reflect P b -> (if c
then ~ P else P) -> ~~ b = c
The lemma ` `introN`` is an instantiation of introNF usingc := true.

Note that views, being part of i-pattern, can be used to interpret
assertions too. For example the following script asserts a && b but
actually used its propositional interpretation.
Lemma test (a b : bool) (pab : b && a) : b. have /andP [pa ->] : (a &&
b) by rewrite andbC.


Interpreting goals
``````````````````



A goal interpretation view tactic of the form:
apply/ term 0
applied to a goal top is interpreted in the following way:


+ If the type of term 0 is not an instance of thereflect predicate,
  nor an equivalence, then the term term 0 is applied to the current
  goal top, possibly inserting implicit arguments.
+ If the type of term 0 is an instance of the reflect predicate or an
  equivalence, then a *goal interpretation view hint* can possibly be
  inserted, which corresponds to the application of a term(term vh (term
  0 _ … _)) to the current goal, possibly inserting implicit arguments.


Like assumption interpretation view hints, goal interpretation ones
are user defined lemmas stored (see section 11.9.8) in theHint View
database bridging the possible gap between the type of term 0 and the
type of the goal.


11.9.7 Interpreting equivalences
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~



Equivalent boolean propositions are simply *equal* boolean terms. A
special construction helps the user to prove boolean equalities by
considering them as logical double implications (between their coerced
versions), while performing at the same time logical operations on
both sides.

The syntax of double views is:
apply/ term l / term r
The term term l is the view lemma applied to the left hand side of the
equality, term r is the one applied to the right hand side.

In this context, the identity view:
Lemma idP : reflect b1 b1.
is useful, for example the tactic:
apply/idP/idP.
transforms the goal `~~ (` `b1` ` || ` `b2` `)= ` `b3` into two
subgoals, respectively `~~ (` `b1` ` || ` `b2` `) -> ` `b3` and
`b3` ` -> ~~ (` `b1` ` || ` `b2` `).`

The same goal can be decomposed in several ways, and the user may
choose the most convenient interpretation. For instance, the tactic:
apply/norP/idP.
applied on the same goal `~~ (` `b1` ` || ` `b2` `) = ` `b3` generates
the subgoals `~~ ` `b1` ` /\ ~~ ` `b2` ` -> ` `b3` and
`b3` ` -> ~~ ` `b1` ` /\ ~~ ` `b2`.


11.9.8 Declaring new Hint Views
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~



The database of hints for the view mechanism is extensible via a
dedicated vernacular command. As library ssrbool.v already declares a
corpus of hints, this feature is probably useful only for users who
define their own logical connectives. Users can declare their own
hints following the syntax used in ssrbool.v:
Hint View for tactic / ident [|natural]
where tactic∈ {move, apply}, ident is the name of the lemma to be
declared as a hint, and natural a natural number. If `move` is used as
tactic, the hint is declared for assumption interpretation tactics,
`apply` declares hints for goal interpretations. Goal interpretation
view hints are declared for both simple views and left hand side
views. The optional natural number natural is the number of implicit
arguments to be considered for the declared hint view lemma
name_of_the_lemma.

The command:
Hint View for apply// ident[|natural].
with a double slash `//`, declares hint views for right hand sides of
double views.

See the files ssreflect.v and ssrbool.v for examples.


11.9.9 Multiple views
~~~~~~~~~~~~~~~~~~~~~



The hypotheses and the goal can be interpreted applying multiple views
in sequence. Both move and apply can be followed by an arbitrary
number of /term i . The main difference between the following two
tactics
apply/v1/v2/v3. apply/v1; apply/v2; apply/v3.
is that the former applies all the views to the principal goal.
Applying a view with hypotheses generates new goals, and the second
line would apply the view v2 to all the goals generated by apply/v1.
Note that the NO-OP intro pattern - can be used to separate two views,
making the two following examples equivalent:
move=> /v1; move=> /v2. move=> /v1-/v2.
The tactic move can be used together with the in tactical to pass a
given hypothesis to a lemma. For example, ifP2Q : P -> Q and Q2R : Q
-> R, the following tactic turns the hypothesis p : P into P : R.
move/P2Q/Q2R in p.
If the list of views is of length two, Hint Views for interpreting
equivalences are indeed taken into account, otherwise only singleHint
Views are used.


11.10 SSReflect searching tool
------------------------------



SSReflect proposes an extension of the Search command. Its syntax is:
Search [pattern] [[] [string[%key] | pattern]] * [in [[] name ] + ]
where name is the name of an open module. This command search returns
the list of lemmas:


+ whose *conclusion* contains a subterm matching the optional first
  pattern. A - reverses the test, producing the list of lemmas whose
  conclusion does not contain any subterm matching the pattern;
+ whose name contains the given string. A - prefix reverses the test,
  producing the list of lemmas whose name does not contain the string. A
  string that contains symbols or is followed by a scope key, is
  interpreted as the constant whose notation involves that string (e.g.,
  `+` for `addn`), if this is unambiguous; otherwise the diagnostic
  includes the output of theLocate vernacular command.
+ whose statement, including assumptions and types, contains a subterm
  matching the next patterns. If a pattern is prefixed by-, the test is
  reversed;
+ contained in the given list of modules, except the ones in the
  modules prefixed by a -.


Note that:


+ As for regular terms, patterns can feature scope indications. For
  instance, the command: Search _ (_ + _)%N. lists all the lemmas whose
  statement (conclusion or hypotheses) involve an application of the
  binary operation denoted by the infix+ symbol in the N scope (which is
  SSReflect scope for natural numbers).
+ Patterns with holes should be surrounded by parentheses.
+ Search always volunteers the expansion of the notation, avoiding the
  need to execute Locate independently. Moreover, a string fragment
  looks for any notation that contains fragment as a substring. If the
  `ssrbool` library is imported, the command: Search "~~". answers :
  "~~" is part of notation (~~ _) In bool_scope, (~~ b) denotes negb b
  negbT forall b : bool, b = false -> ~~ b contra forall c b : bool, (c
  -> b) -> ~~ b -> ~~ c introN forall (P : Prop) (b : bool), reflect P b
  -> ~ P -> ~~ b
+ A diagnostic is issued if there are different matching notations; it
  is an error if all matches are partial.
+ Similarly, a diagnostic warns about multiple interpretations, and
  signals an error if there is no default one.
+ The command Search in M. is a way of obtaining the complete
  signature of the module `M`.
+ Strings and pattern indications can be interleaved, but the first
  indication has a special status if it is a pattern, and only filters
  the conclusion of lemmas:

    + The command : Search (_ =1 _) "bij". lists all the lemmas whose
      conclusion features a ’=1’ and whose name contains the string `bij`.
    + The command : Search "bij" (_ =1 _). lists all the lemmas whose
      statement, including hypotheses, features a ’=1’ and whose name
      contains the string `bij`.




11.11 Synopsis and Index
------------------------


Parameters
~~~~~~~~~~



d-tactic one of theelim, case, congr, apply, exact and move SSReflect
tactics fix-body standard Coq fix_body ident standard Coq identifier
int integer literal key notation scope name module name natural int or
Ltac variable denoting a standard Coq numeral 1 pattern synonym for
term string standard Coq string tactic standard Coq tactic or
SSReflect tactic term Gallina term, possibly containing wildcards



:1: The name of this Ltac variable should not be the name of a tactic
  which can be followed by a bracket `[`, like `do`, ` ` `have`,…




Items and switches
~~~~~~~~~~~~~~~~~~





binder ident | ( ident [: term ] ) binder p. ?? clear-switch { ident +
} clear switch p. ?? c-pattern [term in | term as] ident in term
context pattern p. ?? d-item [occ-switch | clear-switch] [term |
(c-pattern)] discharge item p. ?? gen-item [@]ident | (ident) |
([@]ident := c-pattern) generalization item p. ?? i-pattern ident | _
| ? | * | [occ-switch]-> | [occ-switch]<- | intro pattern p. ?? [
i-item * | … | i-item * ] | - | [: ident + ] i-item clear-switch |
s-item | i-pattern | /term intro item p. ?? int-mult [natural] mult-
mark multiplier p. ?? occ-switch { [+ | -] natural * } occur. switch
p. ?? mult [natural] mult-mark multiplier p. ?? mult-mark ? | !
multiplier mark p. ?? r-item [/] term | s-item rewrite item p. ??
r-prefix [-] [int-mult] [occ-switch | clear-switch] [[r-pattern]]
rewrite prefix p. ?? r-pattern term | c-pattern | in [ident in] term
rewrite pattern p. ?? r-step [r-prefix]r-item rewrite step p. ??
s-item /= | // | //= simplify switch p. ??





Tactics
~~~~~~~

*Note*: without loss and suffices are synonyms for wlog andsuff
respectively.





move idtac or hnf p. ?? apply application p. ?? exact abstract p. ??,
?? elim induction p. ?? case case analysis p. ?? rewrite rstep +
rewrite p. ?? have i-item * [i-pattern] [s-item | binder + ] [: term]
:= term forward p. ?? have i-item * [i-pattern] [s-item| binder + ] :
term [by tactic] chaining have suff [clear-switch] [i-pattern] [:
term] := term have suff [clear-switch] [i-pattern] : term [by tactic]
gen have [ident,] [i-pattern] : gen-item + / term [by tactic] wlog
[suff] [i-item] : [gen-item| clear-switch] * / term specializing p. ??
suff i-item * [i-pattern] [binder + ] : term [by tactic] backchaining
p. ?? suff [have] [clear-switch] [i-pattern] : term [by tactic] pose
ident := term local definition p. ?? pose ident binder + := term local
function definition pose fix fix-body local fix definition pose cofix
fix-body local cofix definition set ident [: term] := [occ-switch]
[term| (c-pattern)] abbreviation p. ?? unlock [r-prefix]ident] *
unlock p. ?? congr [natural] term congruence p. ??





Tacticals
~~~~~~~~~





d-tactic [ident] : d-item + [clear-switch] discharge p. ?? tactic =>
i-item + introduction p. ?? tactic in [gen-item | clear-switch] + [*]
localization p. ?? do [mult] [ tactic | … | tactic ] iteration p. ??
do mult tactic tactic ; first [natural] [tactic | … | tactic] selector
p. ?? tactic ; last [natural] [tactic | … | tactic] tactic ; first
[natural] last subgoals p. ?? tactic ; last [natural] first rotation
by [ tactic | … | tactic ] closing p. ?? by [] by tactic





Commands
~~~~~~~~





`Hint` ` ` `View` ` ` `for` [ `move` | `apply`] / ident [| natural]
view hint declaration p. ?? `Hint` ` ` `View` ` ` `for` ` ` `apply`
`//` ident [|natural] right hand side double p. ?? view hint
declaration `Prenex` ` ` `Implicits` ident + prenex implicits decl. p.
??






:1: Unfortunately, even after a call to the Set Printing All command,
  some occurrences are still not displayed to the user, essentially the
  ones possibly hidden in the predicate of a dependent match structure.
:2: Thus scripts that depend on bound variable names, e.g., via intros
  or with, are inherently fragile.
:3: The name subnK reads as “right cancellation rule for nat
  subtraction”.
:4: Also, a slightly different variant may be used for the firstd-item
  of case and elim; see section 11.5.6.
:5: Except /= does not expand the local definitions created by the
  SSReflect in tactical.
:6: SSReflect reserves all identifiers of the form “_x_”, which is
  used for such generated names.
:7: More precisely, it should have a quantified inductive type with a
  assumptions and m − a constructors.
:8: This is an implementation feature: there is not such obstruction
  in the metatheory
:9: The current state of the proof shall be displayed by the Show
  Proof command of Coq proof mode.




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
.. _11.7  Rewriting: :///home/steck/ssreflect.html#sec561
.. _Cover: :///home/steck/index.html
.. _Errors: :///home/steck/error-index.html
.. _Table of contents: :///home/steck/toc.html
.. _Community: :///community
.. _11.9  Views and reflection: :///home/steck/ssreflect.html#sec582
.. _8.3.2: :///home/steck/tactics.html#intros-pattern
.. _11.5  Basic tactics: :///home/steck/ssreflect.html#sec535
.. _Tactics: :///home/steck/tactic-index.html
.. _11.1  Introduction: :///home/steck/ssreflect.html#sec518
.. _Commands: :///home/steck/command-index.html
.. _11.8  Contextual patterns: :///home/steck/ssreflect.html#sec575
.. _xhtml valid: http://validator.w3.org/
.. _ searching tool: :///home/steck/ssreflect.html#sec596
.. _11.11  Synopsis and Index: :///home/steck/ssreflect.html#sec597
.. _11.6  Control flow: :///home/steck/ssreflect.html#sec549
.. _General: :///home/steck/general-index.html
.. _11.4  Definitions: :///home/steck/ssreflect.html#sec529
.. _Options: :///home/steck/option-index.html
.. _11.2  Usage: :///home/steck/ssreflect.html#sec520
.. _11.3  Gallina extensions: :///home/steck/ssreflect.html#sec523
.. _The Coq Proof Assistant: :///
.. _Documentation: :///documentation
.. _8: :///home/steck/tactics.html#Tactics
.. _webmaster: mailto:coq-www_@_inria.fr



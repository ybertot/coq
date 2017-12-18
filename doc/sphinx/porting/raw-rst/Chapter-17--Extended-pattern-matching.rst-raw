

+ `Home`_
+ `About Coq`_
+ `Get Coq`_
+ `Documentation`_
+ `Community`_

` `_ `The Coq Proof Assistant`_


Chapter 17 Extended pattern-matching
====================================


+ `17.1 Patterns`_
+ `17.2 About patterns of parametric types`_
+ `17.3 Matching objects of dependent types`_
+ `17.4 Using pattern matching to write proofs`_
+ `17.5 Pattern-matching on inductive objects involving local
  definitions`_
+ `17.6 Pattern-matching and coercions`_
+ `17.7 When does the expansion strategy fail ?`_


Cristina Cornes and Hugo Herbelin





This section describes the full form of pattern-matching in Coq terms.


17.1 Patterns
-------------

The full syntax of match is presented in Figures `1.1`_ and `1.2`_.
Identifiers in patterns are either constructor names or variables. Any
identifier that is not the constructor of an inductive or co-inductive
type is considered to be a variable. A variable name cannot occur more
than once in a given pattern. It is recommended to start variable
names by a lowercase letter.

If a pattern has the form (c x) where c is a constructor symbol and x
is a linear vector of (distinct) variables, it is called *simple*: it
is the kind of pattern recognized by the basic version of match. On
the opposite, if it is a variable x or has the form (c p) with p not
only made of variables, the pattern is called *nested*.

A variable pattern matches any value, and the identifier is bound to
that value. The pattern “_” (called “don’t care” or “wildcard” symbol)
also matches any value, but does not bind anything. It may occur an
arbitrary number of times in a pattern. Alias patterns written
(pattern asidentifier) are also accepted. This pattern matches the
same values as pattern does and identifier is bound to the matched
value. A pattern of the form pattern|pattern is called disjunctive. A
list of patterns separated with commas is also considered as a pattern
and is called *multiple pattern*. However multiple patterns can only
occur at the root of pattern-matching equations. Disjunctions of
*multiple pattern* are allowed though.

Since extended match expressions are compiled into the primitive ones,
the expressiveness of the theory remains the same. Once the stage of
parsing has finished only simple patterns remain. Re-nesting of
pattern is performed at printing time. An easy way to see the result
of the expansion is to toggle off the nesting performed at printing
(use here Set Printing Matching), then by printing the term with Print
if the term is a constant, or using the commandCheck.

The extended match still accepts an optional *elimination predicate*
given after the keyword return. Given a pattern matching expression,
if all the right-hand-sides of => ( *rhs* in short) have the same
type, then this type can be sometimes synthesized, and so we can omit
the return part. Otherwise the predicate after return has to be
provided, like for the basicmatch.

Let us illustrate through examples the different aspects of extended
pattern matching. Consider for example the function that computes the
maximum of two natural numbers. We can write it in primitive syntax
by:
Coq < Fixpoint max (n m:nat) {struct m} : nat :=
match n with
| O => m
| S n' => match m with
| O => S n'
| S m' => S (max n' m')
end
end.
max is defined
max is recursively defined (decreasing on 2nd argument)



Multiple patterns
+++++++++++++++++

Using multiple patterns in the definition of max lets us write:
Coq < Fixpoint max (n m:nat) {struct m} : nat :=
match n, m with
| O, _ => m
| S n', O => S n'
| S n', S m' => S (max n' m')
end.
max is defined
max is recursively defined (decreasing on 2nd argument)

which will be compiled into the previous form.

The pattern-matching compilation strategy examines patterns from left
to right. A match expression is generated only when there is at least
one constructor in the column of patterns. E.g. the following example
does not build a match expression.
Coq < Check (fun x:nat => match x return nat with
| y => y
end).
fun x : nat => x
: nat -> nat



Aliasing subpatterns
++++++++++++++++++++

We can also use “as ident” to associate a name to a sub-pattern:
Coq < Fixpoint max (n m:nat) {struct n} : nat :=
match n, m with
| O, _ => m
| S n' as p, O => p
| S n', S m' => S (max n' m')
end.
max is defined
max is recursively defined (decreasing on 1st argument)



Nested patterns
+++++++++++++++

Here is now an example of nested patterns:
Coq < Fixpoint even (n:nat) : bool :=
match n with
| O => true
| S O => false
| S (S n') => even n'
end.
even is defined
even is recursively defined (decreasing on 1st argument)

This is compiled into:
Coq < Unset Printing Matching.

Coq < Print even.
even =
fix even (n : nat) : bool :=
match n with
| 0 => true
| S n0 => match n0 with
| 0 => false
| S n' => even n'
end
end
: nat -> bool
Argument scope is [nat_scope]

In the previous examples patterns do not conflict with, but sometimes
it is comfortable to write patterns that admit a non trivial
superposition. Consider the boolean function lef that given two
natural numbers yields true if the first one is less or equal than the
second one and false otherwise. We can write it as follows:
Coq < Fixpoint lef (n m:nat) {struct m} : bool :=
match n, m with
| O, x => true
| x, O => false
| S n, S m => lef n m
end.
lef is defined
lef is recursively defined (decreasing on 2nd argument)

Note that the first and the second multiple pattern superpose because
the couple of values O O matches both. Thus, what is the result of the
function on those values? To eliminate ambiguity we use the *textual
priority rule*: we consider patterns ordered from top to bottom, then
a value is matched by the pattern at the ith row if and only if it is
not matched by some pattern of a previous row. Thus in the example,O O
is matched by the first pattern, and so (lef O O) yields true.

Another way to write this function is:
Coq < Fixpoint lef (n m:nat) {struct m} : bool :=
match n, m with
| O, x => true
| S n, S m => lef n m
| _, _ => false
end.
lef is defined
lef is recursively defined (decreasing on 2nd argument)

Here the last pattern superposes with the first two. Because of the
priority rule, the last pattern will be used only for values that do
not match neither the first nor the second one.

Terms with useless patterns are not accepted by the system. Here is an
example:
Coq < Fail Check (fun x:nat =>
match x with
| O => true
| S _ => false
| x => true
end).
The command has indeed failed with message:
This clause is redundant.



Disjunctive patterns
++++++++++++++++++++

Multiple patterns that share the same right-hand-side can be
factorized using the notation mult_pattern | … | mult_pattern. For
instance,max can be rewritten as follows:
Coq < Fixpoint max (n m:nat) {struct m} : nat :=
match n, m with
| S n', S m' => S (max n' m')
| 0, p | p, 0 => p
end.
max is defined
max is recursively defined (decreasing on 2nd argument)

Similarly, factorization of (non necessary multiple) patterns that
share the same variables is possible by using the notationpattern | …
| pattern. Here is an example:
Coq < Definition filter_2_4 (n:nat) : nat :=
match n with
| 2 as m | 4 as m => m
| _ => 0
end.
filter_2_4 is defined

Here is another example using disjunctive subpatterns.
Coq < Definition filter_some_square_corners (p:nat*nat) : nat*nat :=
match p with
| ((2 as m | 4 as m), (3 as n | 5 as n)) => (m,n)
| _ => (0,0)
end.
filter_some_square_corners is defined



17.2 About patterns of parametric types
---------------------------------------


Parameters in patterns
++++++++++++++++++++++

When matching objects of a parametric type, parameters do not bind in
patterns. They must be substituted by “_”. Consider for example the
type of polymorphic lists:
Coq < Inductive List (A:Set) : Set :=
| nil : List A
| cons : A -> List A -> List A.
List is defined
List_rect is defined
List_ind is defined
List_rec is defined

We can check the function *tail*:
Coq < Check
(fun l:List nat =>
match l with
| nil _ => nil nat
| cons _ _ l' => l'
end).
fun l : List nat =>
match l with
| nil _ => nil nat
| cons _ _ l' => l'
end
: List nat -> List nat

When we use parameters in patterns there is an error message:
Coq < Fail Check
(fun l:List nat =>
match l with
| nil A => nil nat
| cons A _ l' => l'
end).
The command has indeed failed with message:
The parameters do not bind in patterns; they must be replaced by '_'.



Implicit arguments in patterns
++++++++++++++++++++++++++++++

By default, implicit arguments are omitted in patterns. So we write:
Coq < Arguments nil [A].

Coq < Arguments cons [A] _ _.

Coq < Check
(fun l:List nat =>
match l with
| nil => nil
| cons _ l' => l'
end).
fun l : List nat => match l with
| nil => nil
| cons _ l' => l'
end
: List nat -> List nat

But the possibility to use all the arguments is given by “@” implicit
explicitations (as for terms `2.7.11`_).
Coq < Check
(fun l:List nat =>
match l with
| @nil _ => @nil nat
| @cons _ _ l' => l'
end).
fun l : List nat => match l with
| nil => nil
| cons _ l' => l'
end
: List nat -> List nat



17.3 Matching objects of dependent types
----------------------------------------

The previous examples illustrate pattern matching on objects of non-
dependent types, but we can also use the expansion strategy to
destructure objects of dependent type. Consider the type listn of
lists of a certain length:
Coq < Inductive listn : nat -> Set :=
| niln : listn 0
| consn : forall n:nat, nat -> listn n -> listn (S n).
listn is defined
listn_rect is defined
listn_ind is defined
listn_rec is defined



17.3.1 Understanding dependencies in patterns
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

We can define the function length over listn by:
Coq < Definition length (n:nat) (l:listn n) := n.
length is defined

Just for illustrating pattern matching, we can define it by case
analysis:
Coq < Definition length (n:nat) (l:listn n) :=
match l with
| niln => 0
| consn n _ _ => S n
end.
length is defined

We can understand the meaning of this definition using the same
notions of usual pattern matching.


17.3.2 When the elimination predicate must be provided
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


Dependent pattern matching
++++++++++++++++++++++++++

The examples given so far do not need an explicit elimination
predicate because all the rhs have the same type and the strategy
succeeds to synthesize it. Unfortunately when dealing with dependent
patterns it often happens that we need to write cases where the type
of the rhs are different instances of the elimination predicate. The
function concat for listn is an example where the branches have
different type and we need to provide the elimination predicate:
Coq < Fixpoint concat (n:nat) (l:listn n) (m:nat) (l':listn m) {struct
l} :
listn (n + m) :=
match l in listn n return listn (n + m) with
| niln => l'
| consn n' a y => consn (n' + m) a (concat n' y m l')
end.
concat is defined
concat is recursively defined (decreasing on 2nd argument)

The elimination predicate is fun (n:nat) (l:listn n) => listn (n+m).
In general if m has type (I q 1 … q r t 1 … t s ) whereq 1 , …, q r
are parameters, the elimination predicate should be of the form :fun y
1 … y s x:(I q 1 … q r y 1 …y s ) => Q.

In the concrete syntax, it should be written :
match m as x in (I _ … _ y 1 … y s ) return Q with … end
The variables which appear in the in and as clause are new and bounded
in the property Q in the return clause. The parameters of the
inductive definitions should not be mentioned and are replaced by _.


Multiple dependent pattern matching
+++++++++++++++++++++++++++++++++++

Recall that a list of patterns is also a pattern. So, when we
destructure several terms at the same time and the branches have
different types we need to provide the elimination predicate for this
multiple pattern. It is done using the same scheme, each term may be
associated to an as and in clause in order to introduce a dependent
product.

For example, an equivalent definition for concat (even though the
matching on the second term is trivial) would have been:
Coq < Fixpoint concat (n:nat) (l:listn n) (m:nat) (l':listn m) {struct
l} :
listn (n + m) :=
match l in listn n, l' return listn (n + m) with
| niln, x => x
| consn n' a y, x => consn (n' + m) a (concat n' y m x)
end.
concat is defined
concat is recursively defined (decreasing on 2nd argument)

Even without real matching over the second term, this construction can
be used to keep types linked. If a and b are two listn of the same
length, by writing
Coq < Check (fun n (a b: listn n) => match a,b with
|niln,b0 => tt
|consn n' a y, bS => tt
end).
fun (n : nat) (a _ : listn n) =>
match a with
| niln => tt
| consn n' _ _ => tt
end
: forall n : nat, listn n -> listn n -> unit

I have a copy of b in type listn 0 resp listn (S n’).


Patterns in in
++++++++++++++



If the type of the matched term is more precise than an inductive
applied to variables, arguments of the inductive in the in branch can
be more complicated patterns than a variable.

Moreover, constructors whose type do not follow the same pattern will
become impossible branches. In an impossible branch, you can answer
anything but False_rect unit has the advantage to be subterm of
anything.

To be concrete: the tail function can be written:
Coq < Definition tail n (v: listn (S n)) :=
match v in listn (S m) return listn m with
| niln => False_rect unit
| consn n' a y => y
end.
tail is defined

and tail n v will be subterm of v.


17.4 Using pattern matching to write proofs
-------------------------------------------

In all the previous examples the elimination predicate does not depend
on the object(s) matched. But it may depend and the typical case is
when we write a proof by induction or a function that yields an object
of dependent type. An example of proof using match in given in Section
`8.2.3`_.

For example, we can write the function buildlist that given a natural
numbern builds a list of length n containing zeros as follows:
Coq < Fixpoint buildlist (n:nat) : listn n :=
match n return listn n with
| O => niln
| S n => consn n 0 (buildlist n)
end.
buildlist is defined
buildlist is recursively defined (decreasing on 1st argument)

We can also use multiple patterns. Consider the following definition
of the predicate less-equalLe:
Coq < Inductive LE : nat -> nat -> Prop :=
| LEO : forall n:nat, LE 0 n
| LES : forall n m:nat, LE n m -> LE (S n) (S m).
LE is defined
LE_ind is defined

We can use multiple patterns to write the proof of the lemmaforall (n
m:nat), (LE n m) `\/`(LE m n):
Coq < Fixpoint dec (n m:nat) {struct n} : LE n m \/ LE m n :=
match n, m return LE n m \/ LE m n with
| O, x => or_introl (LE x 0) (LEO x)
| x, O => or_intror (LE x 0) (LEO x)
| S n as n', S m as m' =>
match dec n m with
| or_introl h => or_introl (LE m' n') (LES n m h)
| or_intror h => or_intror (LE n' m') (LES m n h)
end
end.
dec is defined
dec is recursively defined (decreasing on 1st argument)

In the example of dec, the first match is dependent while the second
is not.

The user can also use match in combination with the tacticrefine (see
Section `8.2.3`_) to build incomplete proofs beginning with a match
construction.


17.5 Pattern-matching on inductive objects involving local definitions
----------------------------------------------------------------------

If local definitions occur in the type of a constructor, then there
are two ways to match on this constructor. Either the local
definitions are skipped and matching is done only on the true
arguments of the constructors, or the bindings for local definitions
can also be caught in the matching.

Example.
Coq < Inductive list : nat -> Set :=
| nil : list 0
| cons : forall n:nat, let m := (2 * n) in list m -> list (S (S m)).

In the next example, the local definition is not caught.
Coq < Fixpoint length n (l:list n) {struct l} : nat :=
match l with
| nil => 0
| cons n l0 => S (length (2 * n) l0)
end.
length is defined
length is recursively defined (decreasing on 2nd argument)

But in this example, it is.
Coq < Fixpoint length' n (l:list n) {struct l} : nat :=
match l with
| nil => 0
| @cons _ m l0 => S (length' m l0)
end.
length' is defined
length' is recursively defined (decreasing on 2nd argument)


Remark: for a given matching clause, either none of the local
definitions or all of them can be caught.


Remark: you can only catch let bindings in mode where you bind all
variables and so you have to use @ syntax.


Remark: this feature is incoherent with the fact that parameters
cannot be caught and consequently is somehow hidden. For example,
there is no mention of it in error messages.


17.6 Pattern-matching and coercions
-----------------------------------

If a mismatch occurs between the expected type of a pattern and its
actual type, a coercion made from constructors is sought. If such a
coercion can be found, it is automatically inserted around the
pattern.

Example:
Coq < Inductive I : Set :=
| C1 : nat -> I
| C2 : I -> I.
I is defined
I_rect is defined
I_ind is defined
I_rec is defined

Coq < Coercion C1 : nat >-> I.
C1 is now a coercion

Coq < Check (fun x => match x with
| C2 O => 0
| _ => 0
end).
fun x : I =>
match x with
| C1 _ => 0
| C2 (C1 0) => 0
| C2 (C1 (S _)) => 0
| C2 (C2 _) => 0
end
: I -> nat



17.7 When does the expansion strategy fail ?
--------------------------------------------

The strategy works very like in ML languages when treating patterns of
non-dependent type. But there are new cases of failure that are due to
the presence of dependencies.

The error messages of the current implementation may be sometimes
confusing. When the tactic fails because patterns are somehow
incorrect then error messages refer to the initial expression. But the
strategy may succeed to build an expression whose sub-expressions are
well typed when the whole expression is not. In this situation the
message makes reference to the expanded expression. We encourage
users, when they have patterns with the same outer constructor in
different equations, to name the variable patterns in the same
positions with the same name. E.g. to write (cons n O x) => e1 and
(cons n _ x) => e2 instead of(cons n O x) => e1 and(cons n’ _ x’) =>
e2. This helps to maintain certain name correspondence between the
generated expression and the original.

Here is a summary of the error messages corresponding to each
situation:


Error messages:


#. The constructor ident expects num argumentsThe variable ident is
   bound several times in pattern termFound a constructor of inductive
   type term while a constructor of term is expectedPatterns are
   incorrect (because constructors are not applied to the correct number
   of the arguments, because they are not linear or they are wrongly
   typed).
#. Non exhaustive pattern-matchingThe pattern matching is not
   exhaustive.
#. The elimination predicate term should be of arity num (for non
   dependent case) or num (for dependent case)The elimination predicate
   provided to match has not the expected arity.
#. Unable to infer a match predicate Either there is a type
   incompatibility or the problem involves dependenciesThere is a type
   mismatch between the different branches. The user should provide an
   elimination predicate.




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


.. _17.3  Matching objects of dependent types: :///home/steck/cases.html#sec728
.. _Get Coq: :///download
.. _1.2: :///home/steck/gallina.html#term-syntax-aux
.. _17.1  Patterns: :///home/steck/cases.html#sec720
.. _About Coq: :///about-coq
.. _17.2  About patterns of parametric types: :///home/steck/cases.html#sec725
.. _Commands: :///home/steck/command-index.html
.. _CSS valid: http://jigsaw.w3.org/css-validator/
.. _Cover: :///home/steck/index.html
.. _Errors: :///home/steck/error-index.html
.. _8.2.3: :///home/steck/tactics.html#refine
.. _Table of contents: :///home/steck/toc.html
.. _Community: :///community
.. _1.1: :///home/steck/gallina.html#term-syntax
.. _17.6  Pattern-matching and coercions: :///home/steck/cases.html#sec736
.. _17.7  When does the expansion strategy fail ?: :///home/steck/cases.html#sec737
.. _17.4  Using pattern matching to write proofs: :///home/steck/cases.html#sec734
.. _17.5  Pattern-matching on inductive objects involving local
definitions: :///home/steck/cases.html#sec735
.. _2.7.11: :///home/steck/gallina-ext.html#Implicits-explicitation
.. _xhtml valid: http://validator.w3.org/
.. _Tactics: :///home/steck/tactic-index.html
.. _General: :///home/steck/general-index.html
.. _Options: :///home/steck/option-index.html
.. _The Coq Proof Assistant: :///
.. _8.2.3: :///home/steck/tactics.html#refine-example
.. _Documentation: :///documentation
.. _webmaster: mailto:coq-www_@_inria.fr



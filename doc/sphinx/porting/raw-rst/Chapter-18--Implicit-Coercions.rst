

+ `Home`_
+ `About Coq`_
+ `Get Coq`_
+ `Documentation`_
+ `Community`_

` `_ `The Coq Proof Assistant`_


Chapter 18 Implicit Coercions
=============================


+ `18.1 General Presentation`_
+ `18.2 Classes`_
+ `18.3 Coercions`_
+ `18.4 Identity Coercions`_
+ `18.5 Inheritance Graph`_
+ `18.6 Declaration of Coercions`_
+ `18.7 Displaying Available Coercions`_
+ `18.8 Activating the Printing of Coercions`_
+ `18.9 Classes as Records`_
+ `18.10 Coercions and Sections`_
+ `18.11 Coercions and Modules`_
+ `18.12 Examples`_


Amokrane Saïbi






18.1 General Presentation
-------------------------

This section describes the inheritance mechanism of Coq. In Coq with
inheritance, we are not interested in adding any expressive power to
our theory, but only convenience. Given a term, possibly not typable,
we are interested in the problem of determining if it can be well
typed modulo insertion of appropriate coercions. We allow to write:


+ f a where f:forall x:A, B and a:A′ when A′ can be seen in some sense
  as a subtype of A.
+ x:A when A is not a type, but can be seen in a certain sense as a
  type: set, group, category etc.
+ f a when f is not a function, but can be seen in a certain sense as
  a function: bijection, functor, any structure morphism etc.



18.2 Classes
------------

A class with n parameters is any defined name with a typeforall (x 1
:A 1 )..(x n :A n ), s where s is a sort. Thus a class with parameters
is considered as a single class and not as a family of classes. An
object of a class C is any term of type C t 1 .. t n . In addition to
these user-classes, we have two abstract classes:


+ Sortclass, the class of sorts; its objects are the terms whose type
  is a sort.
+ Funclass, the class of functions; its objects are all the terms with
  a functional type, i.e. of form forall x:A, B.


Formally, the syntax of a classes is defined on Figure 18.1.



class ::= qualid | Sortclass | Funclass Figure 18.1: Syntax of classes





18.3 Coercions
--------------

A name f can be declared as a coercion between a source user-classC
with n parameters and a target class D if one of these conditions
holds:


+ D is a user-class, then the type of f must have the formforall (x 1
  : A 1 )..(x n : A n )(y: C x 1 ..x n ), D u 1 ..u m where m is the
  number of parameters of D.
+ D is Funclass, then the type of f must have the formforall (x 1 : A
  1 )..(x n : A n )(y: C x 1 ..x n )(x:A), B.
+ D is Sortclass, then the type of f must have the formforall (x 1 : A
  1 )..(x n : A n )(y: C x 1 ..x n ), s with s a sort.


We then write f:C >-> D. The restriction on the type of coercions is
called *the uniform inheritance condition*. Remark that the abstract
classes Funclass and Sortclass cannot be source classes.

To coerce an object t:C t 1 ..t n of C towards D, we have to apply the
coercion f to it; the obtained term f t 1 ..t n t is then an object of
D.


18.4 Identity Coercions
-----------------------



Identity coercions are special cases of coercions used to go around
the uniform inheritance condition. Let C and D be two classes with
respectively n and m parameters andf:forall (x 1 :T 1 )..(x k :T k
)(y:C u 1 ..u n ), D v 1 ..v m a function which does not verify the
uniform inheritance condition. To declare f as coercion, one has first
to declare a subclass C′ of C:
C′ := fun (x 1 :T 1 )..(x k :T k ) => C u 1 ..u n
We then define an *identity coercion* between C′ and C:
Id_C′_C := fun (x 1 :T 1 )..(x k :T k )(y:C′ x 1 ..x k ) => (y:C u 1
..u n )
We can now declare f as coercion from C′ to D, since we can “cast” its
type asforall (x 1 :T 1 )..(x k :T k )(y:C′ x 1 ..x k ),D v 1 ..v m .
The identity coercions have a special status: to coerce an object t:C′
t 1 ..t k of C′ towards C, we does not have to insert explicitly
Id_C′_C since Id_C′_C t 1 ..t k t is convertible with t. However we
“rewrite” the type of t to become an object of C; in this case, it
becomes C u 1 * ..u k * where each u i * is the result of the
substitution in u i of the variables x j by t j .


18.5 Inheritance Graph
----------------------

Coercions form an inheritance graph with classes as nodes. We call
*coercion path* an ordered list of coercions between two nodes of the
graph. A class C is said to be a subclass of D if there is a coercion
path in the graph from C to D; we also say that C inherits from D. Our
mechanism supports multiple inheritance since a class may inherit from
several classes, contrary to simple inheritance where a class inherits
from at most one class. However there must be at most one path between
two classes. If this is not the case, only the *oldest* one is valid
and the others are ignored. So the order of declaration of coercions
is important.

We extend notations for coercions to coercion paths. For instance [f 1
;..;f k ]:C >-> D is the coercion path composed by the coercions f 1
..f k . The application of a coercion path to a term consists of the
successive application of its coercions.


18.6 Declaration of Coercions
-----------------------------


18.6.1 Coercion qualid : class 1 >-> class 2 .
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~



Declares the construction denoted by qualid as a coercion betweenclass
1 and class 2 .


Error messages:


#. qualid not declared
#. qualid is already a coercion
#. Funclass cannot be a source class
#. Sortclass cannot be a source class
#. qualid is not a function
#. Cannot find the source class of qualid
#. Cannot recognize class 1 as a source class of qualid
#. qualid does not respect the uniform inheritance condition
#. Found target class class instead of class 2


When the coercion qualid is added to the inheritance graph, non valid
coercion paths are ignored; they are signaled by a warning.
Warning :


#. Ambiguous paths: [f 1 1 ;..;f n 1 1 ] : C 1 >->D 1 … [f 1 m ;..;f n
   m m ] : C m >->D m



Variants:


#. Local Coercion qualid : class 1 >-> class 2 . Declares the
   construction denoted by qualid as a coercion local to the current
   section.
#. Coercion ident := term This defines ident just like Definition
   ident :=term, and then declares ident as a coercion between it source
   and its target.
#. Coercion ident := term : type This defines ident just like
   Definition ident : type := term, and then declares ident as a coercion
   between it source and its target.
#. Local Coercion ident := term This defines ident just like Let ident
   :=term, and then declares ident as a coercion between it source and
   its target.
#. Assumptions can be declared as coercions at declaration time. This
   extends the grammar of assumptions from Figure `1.3`_ as follows:
   assumption ::= assumption_keyword assums . assums ::= simple_assums |
   ( simple_assums) … ( simple_assums) simple_assums ::= ident … ident
   :[>] term If the extra > is present before the type of some
   assumptions, these assumptions are declared as coercions.
#. Constructors of inductive types can be declared as coercions at
   definition time of the inductive type. This extends and modifies the
   grammar of inductive types from Figure `1.3`_ as follows: inductive
   ::= Inductive ind_body with … with ind_body . | CoInductive ind_body
   with … with ind_body . ind_body ::= ident [binders] : term := [[|]
   constructor | … | constructor] constructor ::= ident [binders] [:[>]
   term] Especially, if the extra > is present in a constructor
   declaration, this constructor is declared as a coercion.



18.6.2 Identity Coercion ident:class 1 >-> class 2 .
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~



We check that class 1 is a constant with a value of the formfun (x 1
:T 1 )..(x n :T n ) => (class 2 t 1 ..t m ) where m is the number of
parameters of class 2 . Then we define an identity function with the
typeforall (x 1 :T 1 )..(x n :T n )(y:class 1 x 1 ..x n ),class 2 t 1
..t m , and we declare it as an identity coercion between class 1 and
class 2 .


Error messages:


#. class 1 must be a transparent constant



Variants:


#. Local Identity Coercion ident:ident 1 >-> ident 2 . Idem but
   locally to the current section.
#. SubClass ident := type. If type is a classident’ applied to some
   arguments then ident is defined and an identity coercion of name
   Id_ident_ident’ is declared. Otherwise said, this is an abbreviation
   for Definition ident := type. followed byIdentity Coercion
   Id_ident_ident’:ident >-> ident’.
#. Local SubClass ident := type. Same as before but locally to the
   current section.



18.7 Displaying Available Coercions
-----------------------------------


18.7.1 Print Classes.
~~~~~~~~~~~~~~~~~~~~~

Print the list of declared classes in the current context.


18.7.2 Print Coercions.
~~~~~~~~~~~~~~~~~~~~~~~

Print the list of declared coercions in the current context.


18.7.3 Print Graph.
~~~~~~~~~~~~~~~~~~~

Print the list of valid coercion paths in the current context.


18.7.4 Print Coercion Paths class 1 class 2 .
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Print the list of valid coercion paths from class 1 to class 2 .


18.8 Activating the Printing of Coercions
-----------------------------------------


18.8.1 Set Printing Coercions.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~



This command forces all the coercions to be printed. Conversely, to
skip the printing of coercions, useUnset Printing Coercions. By
default, coercions are not printed.


18.8.2 Add Printing Coercion qualid.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~



This command forces coercion denoted by qualid to be printed. To skip
the printing of coercion qualid, useRemove Printing Coercion qualid.
By default, a coercion is never printed.


18.9 Classes as Records
-----------------------

We allow the definition of *Structures with Inheritance* (or classes
as records) by extending the existing Record macro (see Section
`2.1`_). Its new syntax is:
Record [>] ident [binders] : sort := [ident 0 ] `{` ident 1 [:|:>]
term 1 ; ... ident n [:|:>] term n `}`.
The identifier ident is the name of the defined record and sort is its
type. The identifier ident 0 is the name of its constructor. The
identifiers ident 1 , .., ident n are the names of its fields and term
1 , .., term n their respective types. The alternative [:|:>] is “:”
or “:>”. If ident i :>term i , then ident i is automatically declared
as coercion from ident to the class ofterm i . Remark that ident i
always verifies the uniform inheritance condition. If the optional “>”
before ident is present, then ident 0 (or the default name Build_ident
if ident 0 is omitted) is automatically declared as a coercion from
the class of term n to ident (this may fail if the uniform inheritance
condition is not satisfied).


Remark: The keyword Structure is a synonym of Record.


18.10 Coercions and Sections
----------------------------

The inheritance mechanism is compatible with the section mechanism.
The global classes and coercions defined inside a section are
redefined after its closing, using their new value and new type. The
classes and coercions which are local to the section are simply
forgotten. Coercions with a local source class or a local target
class, and coercions which do not verify the uniform inheritance
condition any longer are also forgotten.


18.11 Coercions and Modules
---------------------------



From Coq version 8.3, the coercions present in a module are activated
only when the module is explicitly imported. Formerly, the coercions
were activated as soon as the module was required, whatever it was
imported or not.

To recover the behavior of the versions of Coq prior to 8.3, use the
following command:



::

    Set Automatic Coercions Import.


To cancel the effect of the option, use instead:

::

    Unset Automatic Coercions Import.



18.12 Examples
--------------

There are three situations:


+ f a is ill-typed where f:forall x:A,B and a:A′. If there is a
  coercion path between A′ and A, f a is transformed intof a′ where a′
  is the result of the application of this coercion path to a.We first
  give an example of coercion between atomic inductive types Coq <
  Definition bool_in_nat (b:bool) := if b then 0 else 1. bool_in_nat is
  defined Coq < Coercion bool_in_nat : bool >-> nat. bool_in_nat is now
  a coercion Coq < Check (0 = true). 0 = true : Prop Coq < Set Printing
  Coercions. Coq < Check (0 = true). 0 = bool_in_nat true : Prop
  Warning: “ `Check true=O.`” fails. This is “normal” behaviour of
  coercions. To validate `true=O`, the coercion is searched from `nat`
  to `bool`. There is none.We give an example of coercion between
  classes with parameters. Coq < Parameters (C : nat -> Set) (D : nat ->
  bool -> Set) (E : bool -> Set). C is declared D is declared E is
  declared Coq < Parameter f : forall n:nat, C n -> D (S n) true. f is
  declared Coq < Coercion f : C >-> D. f is now a coercion Coq <
  Parameter g : forall (n:nat) (b:bool), D n b -> E b. g is declared Coq
  < Coercion g : D >-> E. g is now a coercion Coq < Parameter c : C 0. c
  is declared Coq < Parameter T : E true -> nat. T is declared Coq <
  Check (T c). T c : nat Coq < Set Printing Coercions. Coq < Check (T
  c). T (g 1 true (f 0 c)) : nat We give now an example using identity
  coercions. Coq < Definition D' (b:bool) := D 1 b. D' is defined Coq <
  Identity Coercion IdD'D : D' >-> D. Coq < Print IdD'D. IdD'D = (fun (b
  : bool) (x : D' b) => x) : forall b : bool, D' b -> D 1 b : forall b :
  bool, D' b -> D 1 b Argument scopes are [bool_scope _] IdD'D is a
  coercion Coq < Parameter d' : D' true. d' is declared Coq < Check (T
  d'). T d' : nat Coq < Set Printing Coercions. Coq < Check (T d'). T (g
  1 true d') : nat In the case of functional arguments, we use the
  monotonic rule of sub-typing. Approximatively, to coerce t:forall x:A,
  B towardsforall x:A′,B′, one have to coerce A′ towards A and B
  towardsB′. An example is given below: Coq < Parameters (A B : Set) (h
  : A -> B). A is declared B is declared h is declared Coq < Coercion h
  : A >-> B. h is now a coercion Coq < Parameter U : (A -> E true) ->
  nat. U is declared Coq < Parameter t : B -> C 0. t is declared Coq <
  Check (U t). U (fun x : A => t x) : nat Coq < Set Printing Coercions.
  Coq < Check (U t). U (fun x : A => g 1 true (f 0 (t (h x)))) : nat
  Remark the changes in the result following the modification of the
  previous example. Coq < Parameter U' : (C 0 -> B) -> nat. U' is
  declared Coq < Parameter t' : E true -> A. t' is declared Coq < Check
  (U' t'). U' (fun x : C 0 => t' x) : nat Coq < Set Printing Coercions.
  Coq < Check (U' t'). U' (fun x : C 0 => h (t' (g 1 true (f 0 x)))) :
  nat
+ An assumption x:A when A is not a type, is ill-typed. It is replaced
  by x:A′ where A′ is the result of the application to A of the coercion
  path between the class of A and Sortclass if it exists. This case
  occurs in the abstractionfun x:A => t, universal quantification forall
  x:A, B, global variables and parameters of (co-)inductive definitions
  and functions. In forall x:A, B, such a coercion path may be applied
  to B also if necessary. Coq < Parameter Graph : Type. Graph is
  declared Coq < Parameter Node : Graph -> Type. Node is declared Coq <
  Coercion Node : Graph >-> Sortclass. Node is now a coercion Coq <
  Parameter G : Graph. G is declared Coq < Parameter Arrows : G -> G ->
  Type. Arrows is declared Coq < Check Arrows. Arrows : G -> G -> Type
  Coq < Parameter fg : G -> G. fg is declared Coq < Check fg. fg : G ->
  G Coq < Set Printing Coercions. Coq < Check fg. fg : Node G -> Node G
+ f a is ill-typed because f:A is not a function. The termf is
  replaced by the term obtained by applying to f the coercion path
  between A and Funclass if it exists. Coq < Parameter bij : Set -> Set
  -> Set. bij is declared Coq < Parameter ap : forall A B:Set, bij A B
  -> A -> B. ap is declared Coq < Coercion ap : bij >-> Funclass. ap is
  now a coercion Coq < Parameter b : bij nat nat. b is declared Coq <
  Check (b 0). b 0 : nat Coq < Set Printing Coercions. Coq < Check (b
  0). ap nat nat b 0 : nat Let us see the resulting graph of this
  session. Coq < Print Graph. [bool_in_nat] : bool >-> nat [f] : C >-> D
  [f; g] : C >-> E [g] : D >-> E [IdD'D] : D' >-> D [IdD'D; g] : D' >->
  E [h] : A >-> B [Node] : Graph >-> Sortclass [ap] : bij >-> Funclass




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
.. _1.3: :///home/steck/gallina.html#sentences-syntax
.. _Cover: :///home/steck/index.html
.. _Errors: :///home/steck/error-index.html
.. _Table of contents: :///home/steck/toc.html
.. _Community: :///community
.. _18.5  Inheritance Graph: :///home/steck/coercions.html#sec743
.. _18.4  Identity Coercions: :///home/steck/coercions.html#sec742
.. _18.3  Coercions: :///home/steck/coercions.html#sec741
.. _18.2  Classes: :///home/steck/coercions.html#sec740
.. _18.7  Displaying Available Coercions: :///home/steck/coercions.html#sec747
.. _18.6  Declaration of Coercions: :///home/steck/coercions.html#sec744
.. _Commands: :///home/steck/command-index.html
.. _2.1: :///home/steck/gallina-ext.html#Record
.. _CSS valid: http://jigsaw.w3.org/css-validator/
.. _xhtml valid: http://validator.w3.org/
.. _Tactics: :///home/steck/tactic-index.html
.. _webmaster: mailto:coq-www_@_inria.fr
.. _General: :///home/steck/general-index.html
.. _Options: :///home/steck/option-index.html
.. _The Coq Proof Assistant: :///
.. _18.12  Examples: :///home/steck/coercions.html#sec758
.. _Documentation: :///documentation
.. _18.8  Activating the Printing of Coercions: :///home/steck/coercions.html#sec752
.. _18.1  General Presentation: :///home/steck/coercions.html#sec739
.. _18.9  Classes as Records: :///home/steck/coercions.html#sec755
.. _18.10  Coercions and Sections: :///home/steck/coercions.html#sec756
.. _18.11  Coercions and Modules: :///home/steck/coercions.html#sec757



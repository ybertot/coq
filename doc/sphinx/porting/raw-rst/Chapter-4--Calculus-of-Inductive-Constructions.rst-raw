

+ `Home`_
+ `About Coq`_
+ `Get Coq`_
+ `Documentation`_
+ `Community`_

` `_ `The Coq Proof Assistant`_


Chapter 4 Calculus of Inductive Constructions
=============================================


+ `4.1 The terms`_
+ `4.2 Typing rules`_
+ `4.3 Conversion rules`_
+ `4.4 Subtyping rules`_
+ `4.5 Inductive definitions`_
+ `4.6 Admissible rules for global environments`_
+ `4.7 Co-inductive types`_
+ `4.8 The Calculus of Inductive Construction with impredicative Set`_


The underlying formal language of Coq is a *Calculus of Inductive
Constructions* (Cic) whose inference rules are presented in this
chapter. The history of this formalism as well as pointers to related
work are provided in a separate chapter; see *Credits*.


4.1 The terms
-------------

The expressions of the Cic are *terms* and all terms have a *type*.
There are types for functions (or programs), there are atomic types
(especially datatypes)... but also types for proofs and types for the
types themselves. Especially, any object handled in the formalism must
belong to a type. For instance, universal quantification is relative
to a type and takes the form “for all x of type T, P”. The expression
“x of type T” is written “x:T”. Informally, “x:T” can be thought as“x
belongs to T”.

The types of types are *sorts*. Types and sorts are themselves terms
so that terms, types and sorts are all components of a common
syntactic language of terms which is described in Section 4.1.2 but,
first, we describe sorts.


4.1.1 Sorts
~~~~~~~~~~~

All sorts have a type and there is an infinite well-founded typing
hierarchy of sorts whose base sorts are Prop and Set.

The sort Prop intends to be the type of logical propositions. IfM is a
logical proposition then it denotes the class of terms representing
proofs of M. An object m belonging to M witnesses the fact that M is
provable. An object of type Prop is called a proposition.

The sort Set intends to be the type of small sets. This includes data
types such as booleans and naturals, but also products, subsets, and
function types over these data types.

Prop and Set themselves can be manipulated as ordinary terms.
Consequently they also have a type. Because assuming simply that Set
has type Set leads to an inconsistent theory [`25`_], the language of
Cic has infinitely many sorts. There are, in addition to Set and Prop
a hierarchy of universes Type(i) for any integer i.

Like Set, all of the sorts Type(i) contain small sets such as
booleans, natural numbers, as well as products, subsets and function
types over small sets. But, unlike Set, they also contain large sets,
namely the sorts Set and Type(j) for j<i, and all products, subsets
and function types over these sorts.

Formally, we call S the set of sorts which is defined by:
S ≡ {Prop,Set,Type(i) | i ∈ ℕ}
Their properties, such as:Prop:Type(1), Set:Type(1), and
Type(i):Type(i+1), are defined in Section 4.4.

The user does not have to mention explicitly the index i when
referring to the universe Type(i). One only writes Type. The system
itself generates for each instance of Type a new index for the
universe and checks that the constraints between these indexes can be
solved. From the user point of view we consequently have Type:Type. We
shall make precise in the typing rules the constraints between the
indexes.


Implementation issues
+++++++++++++++++++++

In practice, the Type hierarchy is implemented using *algebraic
universes*. An algebraic universe u is either a variable (a qualified
identifier with a number) or a successor of an algebraic universe (an
expression u+1), or an upper bound of algebraic universes (an
expression max(u 1 ,...,u n )), or the base universe (the expression
0) which corresponds, in the arity of template polymorphic inductive
types (see Section 4.5.2), to the predicative sort Set. A graph of
constraints between the universe variables is maintained globally. To
ensure the existence of a mapping of the universes to the positive
integers, the graph of constraints must remain acyclic. Typing
expressions that violate the acyclicity of the graph of constraints
results in a Universe inconsistency error (see also Section `2.10`_).


4.1.2 Terms
~~~~~~~~~~~



Terms are built from sorts, variables, constants, abstractions,
applications, local definitions, and products. From a syntactic point
of view, types cannot be distinguished from terms, except that they
cannot start by an abstraction or a constructor. More precisely the
language of the *Calculus of Inductive Constructions* is built from
the following rules.


#. the sorts Set, Prop, Type(i) are terms.
#. variables, hereafter ranged over by letters x, y, etc., are terms
#. constants, hereafter ranged over by letters c, d, etc., are terms.
#. if x is a variable and T, U are terms then ∀ x:T,U (forall x:T, U
   in Coq concrete syntax) is a term. If x occurs in U, ∀ x:T,U reads as
   “for all x of type T, U”. As U depends on x, one says that ∀ x:T,U is
   a *dependent product*. If x does not occur in U then ∀ x:T,U reads as
   “if T then U”. A *non dependent product* can be written: T → U.
#. if x is a variable and T, u are terms then λ x:T . u (fun x:T => u
   in Coq concrete syntax) is a term. This is a notation for the
   λ-abstraction of λ-calculus [`8`_]. The term λ x:T . u is a function
   which maps elements of T to the expression u.
#. if t and u are terms then (t u) is a term (t u in Coq concrete
   syntax). The term (t u) reads as “t applied to u”.
#. if x is a variable, and t, T and u are terms thenlet x:=t:T in u is
   a term which denotes the term u where the variable x is locally bound
   to t of type T. This stands for the common “let-in” construction of
   functional programs such as ML or Scheme.



Free variables.
+++++++++++++++

The notion of free variables is defined as usual. In the expressions λ
x:T. U and ∀ x:T, U the occurrences of x in U are bound.


Substitution.
+++++++++++++

The notion of substituting a term t to free occurrences of a variable
x in a term u is defined as usual. The resulting term is written
u{x/t}.


The logical vs programming readings.
++++++++++++++++++++++++++++++++++++

The constructions of the Cic can be used to express both logical and
programming notions, accordingly to the Curry-Howard correspondence
between proofs and programs, and between propositions and types
[`38`_, `81`_, `39`_].

For instance, let us assume that nat is the type of natural numbers
with zero element written 0 and that True is the always true
proposition. Then → is used both to denote nat→nat which is the type
of functions from nat to nat, to denote True→True which is an
implicative proposition, to denote nat →Prop which is the type of
unary predicates over the natural numbers, etc.

Let us assume that mult is a function of type nat→nat→nat and eqnat a
predicate of type nat→nat→ Prop. The λ-abstraction can serve to build
“ordinary” functions as in λ x:nat.(mult x x) (i.e. fun x:nat => mult
x x in Coq notation) but may build also predicates over the natural
numbers. For instance λ x:nat.(eqnat x 0) (i.e. fun x:nat => eqnat x 0
in Coq notation) will represent the predicate of one variable x which
asserts the equality of x with 0. This predicate has type nat → Prop
and it can be applied to any expression of type nat, say t, to give an
object P t of type Prop, namely a proposition.

Furthermore forall x:nat, P x will represent the type of functions
which associate to each natural number n an object of type (P n) and
consequently represent the type of proofs of the formula “∀ x. P(x)”.


4.2 Typing rules
----------------

As objects of type theory, terms are subjected to *type discipline*.
The well typing of a term depends on a global environment and a local
context.


Local context.
++++++++++++++

A *local context* is an ordered list of *local declarations* of names
which we call *variables*. The declaration of some variable x is
either a *local assumption*, written x:T (T is a type) or a *local
definition*, written x:=t:T. We use brackets to write local contexts.
A typical example is [x:T;y:=u:U;z:V]. Notice that the variables
declared in a local context must be distinct. If Γ declares some x, we
write x ∈ Γ. By writing (x:T) ∈ Γ we mean that either x:T is an
assumption in Γ or that there exists some t such that x:=t:T is a
definition in Γ. If Γ defines somex:=t:T, we also write (x:=t:T) ∈ Γ.
For the rest of the chapter, the Γ::(y:T) denotes the local context Γ
enriched with the local assumption y:T. Similarly, Γ::(y:=t:T) denotes
the local context Γ enriched with the local definition (y:=t:T). The
notation [] denotes the empty local context. By Γ 1 ; Γ 2 we mean
concatenation of the local context Γ 1 and the local context Γ 2 .


Global environment.
+++++++++++++++++++

A *global environment* is an ordered list of *global declarations*.
Global declarations are either *global assumptions* or *global
definitions*, but also declarations of inductive objects. Inductive
objects themselves declare both inductive or coinductive types and
constructors (see Section 4.5).

A *global assumption* will be represented in the global environment as
(c:T) which assumes the name c to be of some type T. A *global
definition* will be represented in the global environment as c:=t:T
which defines the name c to have value t and type T. We shall call
such names *constants*. For the rest of the chapter, the E;c:T denotes
the global environmentE enriched with the global assumption c:T.
Similarly, E;c:=t:T denotes the global environmentE enriched with the
global definition (c:=t:T).

The rules for inductive definitions (see Section4.5) have to be
considered as assumption rules to which the following definitions
apply: if the name c is declared in E, we write c ∈ E and if c:T or
c:=t:T is declared in E, we write (c : T) ∈ E.


Typing rules.
+++++++++++++

In the following, we define simultaneously two judgments. The first
one E[Γ] ⊢ t : T means the term t is well-typed and has type T in the
global environment E and local context Γ. The second judgment WF(E)[Γ]
means that the global environment E is well-formed and the local
context Γ is a valid local context in this global environment.

A term t is well typed in a global environment E iff there exists a
local context Γ and a term T such that the judgment E[Γ] ⊢ t : T can
be derived from the following rules.

:W-Empty: WF([])[]
:W-Local-Assum: E[Γ] ⊢ T : s s ∈ S x ∉Γ WF(E)[Γ::(x:T)]
:W-Local-Def: E[Γ] ⊢ t : T x ∉Γ WF(E)[Γ::(x:=t:T)]
:W-Global-Assum: E[] ⊢ T : s s ∈ S c ∉ E WF(E;c:T)[]
:W-Global-Def: E[] ⊢ t : T c ∉ E WF(E;c:=t:T)[]
:Ax-Prop: WF(E)[Γ] E[Γ] ⊢ Prop : Type(1)
:Ax-Set: WF(E)[Γ] E[Γ] ⊢ Set : Type(1)
:Ax-Type: WF(E)[Γ] E[Γ] ⊢ Type(i) : Type(i+1)
:Var: WF(E)[Γ] (x:T) ∈ Γ or (x:=t:T) ∈ Γ for some t E[Γ] ⊢ x : T
:Const: WF(E)[Γ] (c:T) ∈ E or (c:=t:T) ∈ E for some t E[Γ] ⊢ c : T
:Prod-Prop: E[Γ] ⊢ T : s s ∈ S E[Γ::(x:T)] ⊢ U : Prop E[Γ] ⊢ ∀ x:T,U :
  Prop
:Prod-Set: E[Γ] ⊢ T : s s ∈{Prop, Set} E[Γ::(x:T)] ⊢ U : Set E[Γ] ⊢ ∀
  x:T,U : Set
:Prod-Type: E[Γ] ⊢ T : Type(i) E[Γ::(x:T)] ⊢ U : Type(i) E[Γ] ⊢ ∀
  x:T,U : Type(i)
:Lam: E[Γ] ⊢ ∀ x:T,U : s E[Γ::(x:T)] ⊢ t : U E[Γ] ⊢ λ x:T. t : ∀ x:T,
  U
:App: E[Γ] ⊢ t : ∀ x:U,T E[Γ] ⊢ u : U E[Γ] ⊢ (t u) : T{x/u}
:Let: E[Γ] ⊢ t : T E[Γ::(x:=t:T)] ⊢ u : U E[Γ] ⊢ let x:=t:T in u :
  U{x/t}



Remark: Prod 1 and Prod 2 typing-rules make sense if we consider the
semantic difference between Prop and Set:


+ All values of a type that has a sort Set are extractable.
+ No values of a type that has a sort Prop are extractable.



Remark: We may have let x:=t:T in u well-typed without having ((λ x:T.
u) t) well-typed (whereT is a type of t). This is because the value t
associated to x may be used in a conversion rule (see Section 4.3).


4.3 Conversion rules
--------------------

In Cic, there is an internal reduction mechanism. In particular, it
can decide if two programs are *intentionally* equal (one says
*convertible*). Convertibility is described in this section.


β-reduction.
++++++++++++

We want to be able to identify some terms as we can identify the
application of a function to a given argument with its result. For
instance the identity function over a given type T can be written λ
x:T. x. In any global environment E and local context Γ, we want to
identify any object a (of type T) with the application ((λ x:T. x) a).
We define for this a *reduction* (or a *conversion*) rule we call β:
E[Γ] ⊢ ((λ x:T. t) u) ▷ β t{x/u}
We say that t{x/u} is the β *-contraction* of ((λ x:T. t) u) and,
conversely, that ((λ x:T. t) u) is the β *-expansion* of t{x/u}.

According to β-reduction, terms of the *Calculus of Inductive
Constructions* enjoy some fundamental properties such as confluence,
strong normalization, subject reduction. These results are
theoretically of great importance but we will not detail them here and
refer the interested reader to [`24`_].


ι-reduction.
++++++++++++

A specific conversion rule is associated to the inductive objects in
the global environment. We shall give later on (see Section 4.5.3) the
precise rules but it just says that a destructor applied to an object
built from a constructor behaves as expected. This reduction is called
ι-reduction and is more precisely studied in [`126`_, `145`_].


δ-reduction.
++++++++++++

We may have variables defined in local contexts or constants defined
in the global environment. It is legal to identify such a reference
with its value, that is to expand (or unfold) it into its value. This
reduction is called δ-reduction and shows as follows.
E[Γ] ⊢ x ▷ δ t if (x:=t:T) ∈ Γ E[Γ] ⊢ c ▷ δ t if (c:=t:T) ∈ E


ζ-reduction.
++++++++++++

Coq allows also to remove local definitions occurring in terms by
replacing the defined variable by its value. The declaration being
destroyed, this reduction differs from δ-reduction. It is called
ζ-reduction and shows as follows.
E[Γ] ⊢ let x:=u in t ▷ ζ t{x/u}


η-expansion.
++++++++++++

Another important concept is η-expansion. It is legal to identify any
term t of functional type ∀ x:T, U with its so-called η-expansion λ
x:T. (t x) for x an arbitrary variable name fresh in t.


Remark: We deliberately do not define η-reduction:
λ x:T. (t x) ⋫ η t
This is because, in general, the type of t need not to be convertible
to the type of λ x:T. (t x). E.g., if we take f such that:
f : ∀ x:Type(2),Type(1)
then
λ x:Type(1),(f x) : ∀ x:Type(1),Type(1)
We could not allow
λ x:Type(1),(f x) ⋫ η f
because the type of the reduced term ∀ x:Type(2),Type(1) would not be
convertible to the type of the original term ∀ x:Type(1),Type(1).


Convertibility.
+++++++++++++++

Let us write E[Γ] ⊢ t ▷ u for the contextual closure of the relation t
reduces to u in the global environment E and local context Γ with one
of the previous reduction β, ι, δ or ζ.

We say that two terms t 1 and t 2 are βιδζη *-convertible*, or simply
*convertible*, or *equivalent*, in the global environment E and local
context Γ iff there exist terms u 1 and u 2 such thatE[Γ] ⊢ t 1 ▷ … ▷
u 1 andE[Γ] ⊢ t 2 ▷ … ▷ u 2 and eitheru 1 and u 2 are identical, or
they are convertible up to η-expansion, i.e. u 1 is λ x:T. u′ 1 and u
2 x is recursively convertible to u′ 1 , or, symmetrically, u 2 is
λx:T. u′ 2 and u 1 x is recursively convertible to u′ 2 . We then
write E[Γ] ⊢ t 1 = βδιζη t 2 .

Apart from this we consider two instances of polymorphic and
cumulative (see Chapter `29`_) inductive types (see below) convertible
E[Γ] ⊢ t w 1 … w m = βδιζη t w 1 ′ … w m ′ if we have subtypings (see
below) in both directions, i.e.,E[Γ] ⊢ t w 1 … w m ≤ βδιζη t w 1 ′ … w
m ′ and E[Γ] ⊢ t w 1 ′ … w m ′ ≤ βδιζη t w 1 … w m . Furthermore, we
consider E[Γ] ⊢ c v 1 … v m = βδιζη c′ v 1 ′ … v m ′ convertible if
E[Γ] ⊢ v i = βδιζη v i ′ and we have that c and c′ are the same
constructors of different instances the same inductive types
(differing only in universe levels) such that E[Γ] ⊢ c v 1 … v m : t w
1 … w m and E[Γ] ⊢ c′ v 1 ′ … v m ′ : t′ w 1 ′ … w m ′ and we have
E[Γ] ⊢ t w 1 … w m = βδιζη t w 1 ′ … w m ′.

The convertibility relation allows introducing a new typing rule which
says that two convertible well-formed types have the same inhabitants.


4.4 Subtyping rules
-------------------

At the moment, we did not take into account one rule between universes
which says that any term in a universe of index i is also a term in
the universe of index i+1 (this is the *cumulativity* rule ofCic).
This property extends the equivalence relation of convertibility into
a *subtyping* relation inductively defined by:


#. if E[Γ] ⊢ t = βδιζη u then E[Γ] ⊢ t ≤ βδιζη u,
#. if i ≤ j then E[Γ] ⊢ Type(i) ≤ βδιζη Type(j),
#. for any i, E[Γ] ⊢ Set ≤ βδιζη Type(i),
#. E[Γ] ⊢ Prop ≤ βδιζη Set, hence, by transitivity,E[Γ] ⊢ Prop ≤ βδιζη
   Type(i), for any i
#. if E[Γ] ⊢ T = βδιζη U and E[Γ::(x:T)] ⊢ T′ ≤ βδιζη U′ then E[Γ] ⊢ ∀
   x:T, T′ ≤ βδιζη ∀ x:U, U′.
#. if Ind[p](Γ I := Γ C ) is a universe polymorphic and cumulative
   (see Chapter `29`_) inductive type (see below) and (t : ∀Γ P ,∀Γ
   Arr(t) , S)∈Γ I and (t′ : ∀Γ P ′,∀Γ Arr(t) ′, S′)∈Γ I are two
   different instances of *the same* inductive type (differing only in
   universe levels) with constructors [c 1 : ∀Γ P ,∀ T 1,1 … T 1,n 1 ,t v
   1,1 … v 1,m ; …; c k : ∀Γ P ,∀ T k, 1 … T k,n k ,t v n,1 … v n,m ] and
   [c 1 : ∀Γ P ′,∀ T 1,1 ′ … T 1,n 1 ′,t′ v 1,1 ′ … v 1,m ′; …; c k : ∀Γ
   P ′,∀ T k, 1 ′ … T k,n k ′,t v n,1 ′… v n,m ′] respectively then E[Γ]
   ⊢ t w 1 … w m ≤ βδιζη t w 1 ′ … w m ′ (notice that t and t′ are both
   fully applied, i.e., they have a sort as a type) if E[Γ] ⊢ w i = βδιζη
   w i ′ for 1 ≤ i ≤ m and we have E[Γ] ⊢ T i,j ≤ βδιζη T i,j ′ and E[Γ]
   ⊢ A i ≤ βδιζη A i ′ where Γ Arr(t) = [a 1 : A 1 ; a 1 : A l ] and Γ
   Arr(t) = [a 1 : A 1 ′; a 1 : A l ′].


The conversion rule up to subtyping is now exactly:

:Conv: E[Γ] ⊢ U : s E[Γ] ⊢ t : T E[Γ] ⊢ T ≤ βδιζη U E[Γ] ⊢ t : U



Normal form.
++++++++++++

A term which cannot be any more reduced is said to be in *normal
form*. There are several ways (or strategies) to apply the reduction
rules. Among them, we have to mention the *head reduction* which will
play an important role (see Chapter `8`_). Any term can be written as
λ x 1 :T 1 . … λ x k :T k . (t 0 t 1 … t n ) wheret 0 is not an
application. We say then that t 0 is the *head of *t. If we assume
that t 0 is λ x:T. u 0 then one step of β-head reduction of t is:
λ x 1 :T 1 . … λ x k :T k . (λ x:T. u 0 t 1 … t n ) ▷ λ (x 1 :T 1 )…(x
k :T k ). (u 0 {x/t 1 } t 2 … t n )
Iterating the process of head reduction until the head of the reduced
term is no more an abstraction leads to the β *-head normal form* of
t:
t ▷ … ▷ λ x 1 :T 1 . …λ x k :T k . (v u 1 … u m )
where v is not an abstraction (nor an application). Note that the head
normal form must not be confused with the normal form since someu i
can be reducible. Similar notions of head-normal forms involving δ, ι
and ζ reductions or any combination of those can also be defined.


4.5 Inductive Definitions
-------------------------

Formally, we can represent any *inductive definition* as Ind[p](Γ I :=
Γ C ) where:


+ Γ I determines the names and types of inductive types;
+ Γ C determines the names and types of constructors of these
  inductive types;
+ p determines the number of parameters of these inductive types.


These inductive definitions, together with global assumptions and
global definitions, then form the global environment. Additionally,
for any p there always exists Γ P =[a 1 :A 1 ;…;a p :A p ] such that
each T in (t:T)∈Γ I ∪Γ C can be written as: ∀Γ P , T ′ where Γ P is
called the *context of parameters*. Furthermore, we must have that
each T in (t:T)∈Γ I can be written as: ∀Γ P ,∀Γ Arr(t) , S where Γ
Arr(t) is called the *Arity* of the inductive type t and S is called
the sort of the inductive type t.


Examples
++++++++

The declaration for parameterized lists is:

::

    
      
        Ind
        [1]
        ⎛
    ⎝
        [ list : Set → Set ]
        :=
        ⎡
    ⎣
        
          
            
              nil
              :=
              ∀A : Set, list A
            
            
              cons
              :=
              ∀A : Set, A → list A → list A
            
          
        
        ⎤
    ⎦
        ⎞
    ⎠
      

which corresponds to the result of the Coq declaration:
Coq < Inductive list (A:Set) : Set :=
| nil : list A
| cons : A -> list A -> list A.

The declaration for a mutual inductive definition of tree and forest
is:

::

    
      
        Ind
        [1]
        ⎛
    ⎜
    ⎝
        ⎡
    ⎣
        
          
            
              tree
              :
              Set
            
            
              forest
              :
              Set
            
          
        
        ⎤
    ⎦
        :=
        ⎡
    ⎢
    ⎣
        
          
            
              node
              :
              forest → tree
            
            
              emptyf
              :
              forest
            
            
              consf
              :
              tree → forest → forest
            
          
        
        ⎤
    ⎥
    ⎦
        ⎞
    ⎟
    ⎠
      

which corresponds to the result of the Coq declaration:
Coq < Inductive tree : Set :=
node : forest -> tree
with forest : Set :=
| emptyf : forest
| consf : tree -> forest -> forest.

The declaration for a mutual inductive definition of even and odd is:

::

    
      
        Ind
        [1]
        ⎛
    ⎜
    ⎝
        ⎡
    ⎣
        
          
            
              even
              :
              nat → Prop
            
            
              odd
              :
              nat → Prop
            
          
        
        ⎤
    ⎦
        :=
        ⎡
    ⎢
    ⎣
        
          
            
              even_O
              :
              even O
            
            
              even_S
              :
              ∀n : nat, odd n → even (S n)
            
            
              odd_S
              :
              ∀n : nat, even n → odd (S n)
            
          
        
        ⎤
    ⎥
    ⎦
        ⎞
    ⎟
    ⎠
      

which corresponds to the result of the Coq declaration:
Coq < Inductive even : nat -> Prop :=
| even_O : even 0
| even_S : forall n, odd n -> even (S n)
with odd : nat -> Prop :=
| odd_S : forall n, even n -> odd (S n).



4.5.1 Types of inductive objects
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

We have to give the type of constants in a global environment E which
contains an inductive declaration.

:Ind: WF(E)[Γ] Ind[p](Γ I := Γ C ) ∈ E (a:A)∈Γ I E[Γ] ⊢ a : A
:Constr: WF(E)[Γ] Ind[p](Γ I := Γ C ) ∈ E (c:C)∈Γ C E[Γ] ⊢ c : C



4.5.2 Well-formed inductive definitions
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

We cannot accept any inductive declaration because some of them lead
to inconsistent systems. We restrict ourselves to definitions which
satisfy a syntactic criterion of positivity. Before giving the formal
rules, we need a few definitions:


Definition
++++++++++

A type T is an *arity of sort *s if it converts to the sort s or to a
product ∀ x:T,U with U an arity of sort s.


Examples
++++++++

A→ Set is an arity of sort Set. ∀ A:Prop,A→ Prop is an arity of sort
Prop.


Definition
++++++++++

A type T is an *arity* if there is a s∈ S such that T is an arity of
sort s.


Examples
++++++++

A→ Set and ∀ A:Prop,A→ Prop are arities.


Definition
++++++++++

We say that T is a *type of constructor of *I in one of the following
two cases:


+ T is (I t 1 … t n )
+ T is ∀ x:U,T ′ where T ′ is also a type of constructor of I



Examples
++++++++

nat and nat→nat are types of constructors of nat.
∀ A:Type,list A and ∀ A:Type,A→list A→list A are constructors of list.


Definition
++++++++++

The type of constructor T will be said to *satisfy the positivity
condition* for a constant X in the following cases:


+ T=(X t 1 … t n ) and X does not occur free in any t i
+ T=∀ x:U,V and X occurs only strictly positively in U and the type V
  satisfies the positivity condition for X


The constant X *occurs strictly positively* in T in the following
cases:


+ X does not occur in T
+ T converts to (X t 1 … t n ) and X does not occur in any of t i
+ T converts to ∀ x:U,V and X does not occur in type U but occurs
  strictly positively in type V
+ T converts to (I a 1 … a m t 1 … t p ) whereI is the name of an
  inductive declaration of the formInd[m](I:A := c 1 :∀ p 1 :P 1 ,… ∀p m
  :P m ,C 1 ;…;c n :∀ p 1 :P 1 ,… ∀p m :P m ,C n ) (in particular, it is
  not mutually defined and it has m parameters) and X does not occur in
  any of the t i , and the (instantiated) types of constructor C i {p j
  /a j } j=1… m of I satisfy the nested positivity condition for X


The type of constructor T of I *satisfies the nested positivity
condition* for a constant X in the following cases:


+ T=(I b 1 … b m u 1 … u p ), I is an inductive definition with m
  parameters and X does not occur in any u i
+ T=∀ x:U,V and X occurs only strictly positively in U and the type V
  satisfies the nested positivity condition for X


For instance, if one considers the type

::

    Inductive tree (A:Type) : Type :=
     | leaf : list A
     | node : A -> (nat -> tree A) -> tree A




::

    
    Then every instantiated constructor of list A satisfies the nested positivity condition for list
      │
      ├─ concerning type list A of constructor nil:
      │    Type list A of constructor nil satisfies the positivity condition for list
      │    because list does not appear in any (real) arguments of the type of that constructor
      │    (primarily because list does not have any (real) arguments) ... (bullet 1)
      │
      ╰─ concerning type ∀ A → list A → list A of constructor cons:
           Type ∀ A : Type, A → list A → list A of constructor cons
           satisfies the positivity condition for list because:
           │
           ├─ list occurs only strictly positively in Type ... (bullet 3)
           │
           ├─ list occurs only strictly positively in A ... (bullet 3)
           │
           ├─ list occurs only strictly positively in list A ... (bullet 4)
           │
           ╰─ list satisfies the positivity condition for list A ... (bullet 1)




Correctness rules.
++++++++++++++++++

We shall now describe the rules allowing the introduction of a new
inductive definition.

:W-Ind: Let E be a global environment and Γ P ,Γ I ,Γ C are contexts
such that Γ I is [I 1 :∀ Γ P ,A 1 ;…;I k :∀ Γ P ,A k ] and Γ C is [c 1
:∀ Γ P ,C 1 ;…;c n :∀ Γ P ,C n ]. (E[Γ P ] ⊢ A j : s′ j ) j=1… k (E[Γ
I ;Γ P ] ⊢ C i : s q i ) i=1… n WF(E;Ind[p](Γ I := Γ C ))[Γ] provided
that the following side conditions hold:

    + k>0 and all of I j and c i are distinct names for j=1… k and i=1… n,
    + p is the number of parameters of Ind(Γ I := Γ C ) and Γ P is the
      context of parameters,
    + for j=1… k we have that A j is an arity of sort s j and I j ∉ E,
    + for i=1… n we have that C i is a type of constructor ofI q i which
      satisfies the positivity condition for I 1 … I k and c i ∉ Γ ∪ E.



One can remark that there is a constraint between the sort of the
arity of the inductive type and the sort of the type of its
constructors which will always be satisfied for the impredicative
sortProp but may fail to define inductive definition on sort Set and
generate constraints between universes for inductive definitions in
the Type hierarchy.


Examples.
+++++++++

It is well known that existential quantifier can be encoded as an
inductive definition. The following declaration introduces the second-
order existential quantifier ∃ X.P(X).
Coq < Inductive exProp (P:Prop->Prop) : Prop :=
exP_intro : forall X:Prop, P X -> exProp P.

The same definition on Set is not allowed and fails:
Coq < Fail Inductive exSet (P:Set->Prop) : Set :=
exS_intro : forall X:Set, P X -> exSet P.
The command has indeed failed with message:
Large non-propositional inductive types must be in Type.

It is possible to declare the same inductive definition in the
universe Type. The exType inductive definition has type (Type i
→Prop)→Type j with the constraint that the parameter X of exT_intro
has type Type k with k<j and k≤ i.
Coq < Inductive exType (P:Type->Prop) : Type :=
exT_intro : forall X:Type, P X -> exType P.



Template polymorphism.
++++++++++++++++++++++



Inductive types declared in Type are polymorphic over their arguments
in Type. If A is an arity of some sort and s is a sort, we write A /s
for the arity obtained from A by replacing its sort with s.
Especially, if A is well-typed in some global environment and local
context, then A /s is typable by typability of all products in the
Calculus of Inductive Constructions. The following typing rule is
added to the theory.

:Ind-Family: Let Ind[p](Γ I := Γ C ) be an inductive definition. Let Γ
P = [p 1 :P 1 ;…;p p :P p ] be its context of parameters, Γ I = [I 1
:∀ Γ P ,A 1 ;…;I k :∀ Γ P ,A k ] its context of definitions and Γ C =
[c 1 :∀ Γ P ,C 1 ;…;c n :∀ Γ P ,C n ] its context of constructors,
with c i a constructor of I q i .Let m ≤ p be the length of the
longest prefix of parameters such that the m first arguments of all
occurrences of all I j in all C k (even the occurrences in the
hypotheses of C k ) are exactly applied to p 1 … p m (m is the number
of *recursively uniform parameters* and the p−m remaining parameters
are the *recursively non-uniform parameters*). Let q 1 , …, q r , with
0≤ r≤ m, be a (possibly) partial instantiation of the recursively
uniform parameters of Γ P . We have: ⎧ ⎪ ⎨ ⎪ ⎩ Ind[p](Γ I := Γ C ) ∈ E
(E[] ⊢ q l : P′ l ) l=1… r (E[] ⊢ P′ l ≤ βδιζη P l {p u /q u } u=1…
l−1 ) l=1… r 1 ≤ j ≤ k E[] ⊢ I j q 1 … q r :∀ [p r+1 :P r+1 ;…;p p :P
p ], (A j ) /s j provided that the following side conditions hold:

    + Γ P′ is the context obtained from Γ P by replacing each P l that is
      an arity with P′ l for 1≤ l ≤ r (notice thatP l arity implies P′ l
      arity since E[] ⊢ P′ l ≤ βδιζη P l {p u /q u } u=1… l−1 );
    + there are sorts s i , for 1 ≤ i ≤ k such that, for Γ I′ = [I 1 :∀ Γ
      P′ ,(A 1 ) /s 1 ;…;I k :∀ Γ P′ ,(A k ) /s k ] we have (E[Γ I′ ;Γ P′ ]
      ⊢ C i : s q i ) i=1… n ;
    + the sorts s i are such that all eliminations, to Prop, Set
      andType(j), are allowed (see Section 4.5.3).



Notice that if I j q 1 … q r is typable using the rules Ind-Const and
App, then it is typable using the rule Ind-Family. Conversely, the
extended theory is not stronger than the theory without Ind-Family. We
get an equiconsistency result by mapping each Ind[p](Γ I := Γ C )
occurring into a given derivation into as many different inductive
types and constructors as the number of different (partial)
replacements of sorts, needed for this derivation, in the parameters
that are arities (this is possible because Ind[p](Γ I := Γ C ) well-
formed implies that Ind[p](Γ I′ := Γ C′ ) is well-formed and has the
same allowed eliminations, where Γ I′ is defined as above and Γ C′ =
[c 1 :∀ Γ P′ ,C 1 ;…;c n :∀ Γ P′ ,C n ]). That is, the changes in the
types of each partial instanceq 1 … q r can be characterized by the
ordered sets of arity sorts among the types of parameters, and to each
signature is associated a new inductive definition with fresh names.
Conversion is preserved as any (partial) instance I j q 1 … q r orC i
q 1 … q r is mapped to the names chosen in the specific instance of
Ind[p](Γ I := Γ C ).

In practice, the rule Ind-Family is used by Coq only when all the
inductive types of the inductive definition are declared with an arity
whose sort is in the Type hierarchy. Then, the polymorphism is over
the parameters whose type is an arity of sort in the Type hierarchy.
The sort s j are chosen canonically so that each s j is minimal with
respect to the hierarchy Prop⊂Set p ⊂Type where Set p is predicative
Set. More precisely, an empty or small singleton inductive definition
(i.e. an inductive definition of which all inductive types are
singleton – see paragraph 4.5.3) is set inProp, a small non-singleton
inductive type is set in Set (even in case Set is impredicative – see
Section 4.8), and otherwise in the Type hierarchy.

Note that the side-condition about allowed elimination sorts in the
rule Ind-Family is just to avoid to recompute the allowed elimination
sorts at each instance of a pattern-matching (see section 4.5.3). As
an example, let us consider the following definition:
Coq < Inductive option (A:Type) : Type :=
| None : option A
| Some : A -> option A.

As the definition is set in the Type hierarchy, it is used
polymorphically over its parameters whose types are arities of a sort
in the Type hierarchy. Here, the parameter A has this property, hence,
if option is applied to a type in Set, the result is in Set. Note that
if option is applied to a type in Prop, then, the result is not set in
Prop but in Set still. This is because option is not a singleton type
(see section 4.5.3) and it would lose the elimination to Set andType
if set in Prop.
Coq < Check (fun A:Set => option A).
fun A : Set => option A
: Set -> Set

Coq < Check (fun A:Prop => option A).
fun A : Prop => option A
: Prop -> Set

Here is another example.
Coq < Inductive prod (A B:Type) : Type := pair : A -> B -> prod A B.

As prod is a singleton type, it will be in Prop if applied twice to
propositions, in Set if applied twice to at least one type in Set and
none in Type, and in Type otherwise. In all cases, the three kind of
eliminations schemes are allowed.
Coq < Check (fun A:Set => prod A).
fun A : Set => prod A
: Set -> Type -> Type

Coq < Check (fun A:Prop => prod A A).
fun A : Prop => prod A A
: Prop -> Prop

Coq < Check (fun (A:Prop) (B:Set) => prod A B).
fun (A : Prop) (B : Set) => prod A B
: Prop -> Set -> Set

Coq < Check (fun (A:Type) (B:Prop) => prod A B).
fun (A : Type) (B : Prop) => prod A B
: Type -> Prop -> Type


Remark: Template polymorphism used to be called “sort-polymorphism of
inductive types” before universe polymorphism (see Chapter `29`_) was
introduced.


4.5.3 Destructors
~~~~~~~~~~~~~~~~~

The specification of inductive definitions with arities and
constructors is quite natural. But we still have to say how to use an
object in an inductive type.

This problem is rather delicate. There are actually several different
ways to do that. Some of them are logically equivalent but not always
equivalent from the computational point of view or from the user point
of view.

From the computational point of view, we want to be able to define a
function whose domain is an inductively defined type by using a
combination of case analysis over the possible constructors of the
object and recursion.

Because we need to keep a consistent theory and also we prefer to keep
a strongly normalizing reduction, we cannot accept any sort of
recursion (even terminating). So the basic idea is to restrict
ourselves to primitive recursive functions and functionals.

For instance, assuming a parameter A:Set exists in the local context,
we want to build a function length of type list A→ nat which computes
the length of the list, so such that (length (nil A)) = O and (length
(cons A a l)) = (S (length l)). We want these equalities to be
recognized implicitly and taken into account in the conversion rule.

From the logical point of view, we have built a type family by giving
a set of constructors. We want to capture the fact that we do not have
any other way to build an object in this type. So when trying to prove
a property about an object m in an inductive definition it is enough
to enumerate all the cases where m starts with a different
constructor.

In case the inductive definition is effectively a recursive one, we
want to capture the extra property that we have built the smallest
fixed point of this recursive equation. This says that we are only
manipulating finite objects. This analysis provides induction
principles. For instance, in order to prove ∀ l:list A,(has_length A l
(length l)) it is enough to prove:


+ (has_length A (nil A) (length (nil A)))
+ ∀ a:A, ∀ l:list A, (has_length A l (length l)) → → (has_length A
  (cons A a l) (length (cons A a l)))


which given the conversion equalities satisfied by length is the same
as proving:


+ (has_length A (nil A) O)
+ ∀ a:A, ∀ l:list A, (has_length A l (length l)) → → (has_length A
  (cons A a l) (S (length l)))


One conceptually simple way to do that, following the basic scheme
proposed by Martin-Löf in his Intuitionistic Type Theory, is to
introduce for each inductive definition an elimination operator. At
the logical level it is a proof of the usual induction principle and
at the computational level it implements a generic operator for doing
primitive recursion over the structure.

But this operator is rather tedious to implement and use. We choose in
this version of Coq to factorize the operator for primitive recursion
into two more primitive operations as was first suggested by Th.
Coquand in [`28`_]. One is the definition by pattern-matching. The
second one is a definition by guarded fixpoints.


The match…with …end construction.
`````````````````````````````````

The basic idea of this operator is that we have an objectm in an
inductive type I and we want to prove a property which possibly
depends on m. For this, it is enough to prove the property for m = (c
i u 1 … u p i ) for each constructor of I. The Coq term for this proof
will be written:
match m with (c 1 x 11 ... x 1p 1 ) ⇒ f 1 | … | (c n x n1 ... x np n )
⇒ f n end
In this expression, ifm eventually happens to evaluate to (c i u 1 … u
p i ) then the expression will behave as specified in its i-th branch
and it will reduce to f i where the x i1 …x ip i are replaced by the u
1 … u p i according to the ι-reduction.

Actually, for type-checking a match…with…end expression we also need
to know the predicate P to be proved by case analysis. In the general
case where I is an inductively definedn-ary relation, P is a predicate
over n+1 arguments: the n first ones correspond to the arguments of I
(parameters excluded), and the last one corresponds to object m. Coq
can sometimes infer this predicate but sometimes not. The concrete
syntax for describing this predicate uses the as…in…return
construction. For instance, let us assume that I is an unary predicate
with one parameter and one argument. The predicate is made explicit
using the syntax:
match m as x in I `_` a return P with (c 1 x 11 ... x 1p 1 ) ⇒ f 1 | …
| (c n x n1 ... x np n ) ⇒ f n end
The as part can be omitted if either the result type does not depend
on m (non-dependent elimination) or m is a variable (in this case, m
can occur in P where it is considered a bound variable). The in part
can be omitted if the result type does not depend on the arguments
ofI. Note that the arguments of I corresponding to parameters *must*
be `_`, because the result type is not generalized to all possible
values of the parameters. The other arguments of I (sometimes called
indices in the literature) have to be variables (a above) and these
variables can occur in P. The expression after in must be seen as an
*inductive type pattern*. Notice that expansion of implicit arguments
and notations apply to this pattern. For the purpose of presenting the
inference rules, we use a more compact notation:
case(m,(λ a x . P), λ x 11 ... x 1p 1 . f 1 | … | λ x n1 ...x np n . f
n )


Allowed elimination sorts.
++++++++++++++++++++++++++



An important question for building the typing rule for match is what
can be the type of λ a x . P with respect to the type of m. Ifm:I
andI:A and λ a x . P : B then by [I:A|B] we mean that one can use λ a
x . P with m in the above match-construct.


Notations.
++++++++++

The [I:A|B] is defined as the smallest relation satisfying the
following rules: We write [I|B] for [I:A|B] where A is the type ofI.

The case of inductive definitions in sorts Set or Type is simple.
There is no restriction on the sort of the predicate to be eliminated.

:Prod: [(I x):A′|B′] [I:∀ x:A, A′|∀ x:A, B′]
:Set & Type: s 1 ∈ {Set,Type(j)} s 2 ∈ S [I:s 1 |I→ s 2 ]


The case of Inductive definitions of sort Prop is a bit more
complicated, because of our interpretation of this sort. The only
harmless allowed elimination, is the one when predicate P is also of
sort Prop.

:Prop: [I:Prop|I→Prop]


Prop is the type of logical propositions, the proofs of propertiesP in
Prop could not be used for computation and are consequently ignored by
the extraction mechanism. Assume A and B are two propositions, and the
logical disjunctionA∨ B is defined inductively by:
Coq < Inductive or (A B:Prop) : Prop :=
or_introl : A -> or A B | or_intror : B -> or A B.

The following definition which computes a boolean value by case over
the proof of or A B is not accepted:
Coq < Fail Definition choice (A B: Prop) (x:or A B) :=
match x with or_introl _ _ a => true | or_intror _ _ b => false end.
The command has indeed failed with message:
Incorrect elimination of "x" in the inductive type "or":
the return type has sort "Set" while it should be "Prop".
Elimination of an inductive object of sort Prop
is not allowed on a predicate in sort Set
because proofs can be eliminated only to build proofs.

From the computational point of view, the structure of the proof of(or
A B) in this term is needed for computing the boolean value.

In general, if I has type Prop then P cannot have type I→Set, because
it will mean to build an informative proof of type (P m) doing a case
analysis over a non-computational object that will disappear in the
extracted program. But the other way is safe with respect to our
interpretation we can have I a computational object and P a non-
computational one, it just corresponds to proving a logical property
of a computational object.

In the same spirit, elimination on P of type I→Type cannot be allowed
because it trivially implies the elimination on P of type I→ Set by
cumulativity. It also implies that there are two proofs of the same
property which are provably different, contradicting the proof-
irrelevance property which is sometimes a useful axiom:
Coq < Axiom proof_irrelevance : forall (P : Prop) (x y : P), x=y.
proof_irrelevance is declared

The elimination of an inductive definition of type Prop on a predicate
P of type I→ Type leads to a paradox when applied to impredicative
inductive definition like the second-order existential quantifier
exProp defined above, because it give access to the two projections on
this type.


Empty and singleton elimination
+++++++++++++++++++++++++++++++

There are special inductive definitions in Prop for which more
eliminations are allowed.

:Prop-extended: I is an empty or singleton definition s ∈ S [I:Prop|I→
  s]


A *singleton definition* has only one constructor and all the
arguments of this constructor have type Prop. In that case, there is a
canonical way to interpret the informative extraction on an object in
that type, such that the elimination on any sort s is legal. Typical
examples are the conjunction of non-informative propositions and the
equality. If there is an hypothesis h:a=b in the local context, it can
be used for rewriting not only in logical propositions but also in any
type.
Coq < Print eq_rec.
eq_rec =
fun (A : Type) (x : A) (P : A -> Set) => eq_rect x P
: forall (A : Type) (x : A) (P : A -> Set),
P x -> forall y : A, x = y -> P y
Argument A is implicit
Argument scopes are [type_scope _ function_scope _ _ _]

Coq < Extraction eq_rec.
(** val eq_rec : 'a1 -> 'a2 -> 'a1 -> 'a2 **)
let eq_rec _ f _ =
f

An empty definition has no constructors, in that case also,
elimination on any sort is allowed.


Type of branches.
+++++++++++++++++

Let c be a term of type C, we assume C is a type of constructor for an
inductive type I. Let P be a term that represents the property to be
proved. We assume r is the number of parameters and p is the number of
arguments.

We define a new type {c:C} P which represents the type of the branch
corresponding to the c:C constructor.
{c:(I p 1 … p r t 1 … t p )} P ≡ (P t 1 … t p c) {c:∀ x:T,C} P ≡ ∀
x:T,{(c x):C} P
We write {c} P for {c:C} P with C the type of c.


Example.
++++++++

The following term in concrete syntax:

::

    match t as l return P' with
    | nil _ => t1
    | cons _ hd tl => t2
    end


can be represented in abstract syntax as
case(t,P,f 1 | f 2 )
where
P = λ l . P ′ f 1 = t 1 f 2 = λ (hd:nat) . λ (tl:list nat) . t 2
According to the definition:

{(nil nat)} P ≡ {(nil nat) : (list nat)} P ≡ (P (nil nat))

{(cons nat)} P ≡{(cons nat) : (nat→list nat→list nat)} P ≡
≡∀ n:nat, {(cons nat n) : list nat→list nat)} P ≡
≡∀ n:nat, ∀ l:list nat, {(cons nat n l) : list nat)} P ≡
≡∀ n:nat, ∀ l:list nat,(P (cons nat n l)).

Given some P, then {(nil nat)} P represents the expected type of f 1 ,
and {(cons nat)} P represents the expected type of f 2 .


Typing rule.
++++++++++++

Our very general destructor for inductive definition enjoys the
following typing rule

:match: E[Γ] ⊢ c : (I q 1 … q r t 1 … t s ) E[Γ] ⊢ P : B [(I q 1 … q r
  )|B] (E[Γ] ⊢ f i : {(c p i q 1 … q r )} P ) i=1… l E[Γ] ⊢ case(c,P,f 1
  |… |f l ) : (P t 1 … t s c) provided I is an inductive type in a
  definitionInd[r](Γ I := Γ C ) with Γ C = [c 1 :C 1 ;…;c n :C n ] and c
  p 1 … c p l are the only constructors of I.



Example.
++++++++

Below is a typing rule for the term shown in the previous example:
E[Γ] ⊢ t : (list nat) E[Γ] ⊢ P : B [(list nat)|B] E[Γ] ⊢ f 1 : {(nil
nat)} P E[Γ] ⊢ f 2 : {(cons nat)} P E[Γ] ⊢ case(t,P,f 1 |f 2 ) : (P t)


Definition of ι-reduction.
++++++++++++++++++++++++++

We still have to define the ι-reduction in the general case.

A ι-redex is a term of the following form:
case((c p i q 1 … q r a 1 … a m ),P,f 1 |… |f l )
with c p i the i-th constructor of the inductive type I with r
parameters.

The ι-contraction of this term is (f i a 1 … a m ) leading to the
general reduction rule:
case((c p i q 1 … q r a 1 … a m ),P,f 1 |… |f n ) ▷ ι (f i a 1 … a m )


4.5.4 Fixpoint definitions
~~~~~~~~~~~~~~~~~~~~~~~~~~

The second operator for elimination is fixpoint definition. This
fixpoint may involve several mutually recursive definitions. The basic
concrete syntax for a recursive set of mutually recursive declarations
is (with Γ i contexts):
fix f 1 (Γ 1 ) :A 1 :=t 1 with … with f n (Γ n ) :A n :=t n
The terms are obtained by projections from this set of declarations
and are written
fix f 1 (Γ 1 ) :A 1 :=t 1 with … with f n (Γ n ) :A n :=t n for f i
In the inference rules, we represent such a term by
Fix f i {f 1 :A 1 ′:=t 1 ′ … f n :A n ′:=t n ′}
with t i ′ (resp. A i ′) representing the term t i abstracted (resp.
generalized) with respect to the bindings in the context Γ i , namelyt
i ′=λ Γ i . t i and A i ′=∀ Γ i , A i .


Typing rule
```````````

The typing rule is the expected one for a fixpoint.

:Fix: (E[Γ] ⊢ A i : s i ) i=1… n (E[Γ,f 1 :A 1 ,…,f n :A n ] ⊢ t i : A
  i ) i=1… n E[Γ] ⊢ Fix f i {f 1 :A 1 :=t 1 … f n :A n :=t n } : A i


Any fixpoint definition cannot be accepted because non-normalizing
terms allow proofs of absurdity. The basic scheme of recursion that
should be allowed is the one needed for defining primitive recursive
functionals. In that case the fixpoint enjoys a special syntactic
restriction, namely one of the arguments belongs to an inductive type,
the function starts with a case analysis and recursive calls are done
on variables coming from patterns and representing subterms. For
instance in the case of natural numbers, a proof of the induction
principle of type
∀ P:nat→Prop, (P O)→(∀ n:nat, (P n)→(P (S n)))→ ∀ n:nat, (P n)
can be represented by the term:
λ P:nat→Prop. λ f:(P O). λ g:(∀ n:nat, (P n)→(P (S n))) . Fix h{h:∀
n:nat, (P n):=λ n:nat. case(n,P,f | λp:nat. (g p (h p)))}
Before accepting a fixpoint definition as being correctly typed, we
check that the definition is “guarded”. A precise analysis of this
notion can be found in [`67`_]. The first stage is to precise on which
argument the fixpoint will be decreasing. The type of this argument
should be an inductive definition. For doing this, the syntax of
fixpoints is extended and becomes
Fix f i {f 1 /k 1 :A 1 :=t 1 … f n /k n :A n :=t n }
where k i are positive integers. Each k i represents the index of
pararameter of f i , on which f i is decreasing. Each A i should be a
type (reducible to a term) starting with at leastk i products ∀ y 1 :B
1 ,… ∀ y k i :B k i , A′ i and B k i an is unductive type.

Now in the definition t i , if f j occurs then it should be applied to
at least k j arguments and the k j -th argument should be
syntactically recognized as structurally smaller than y k i

The definition of being structurally smaller is a bit technical. One
needs first to define the notion of *recursive arguments of a
constructor*. For an inductive definition Ind[r](Γ I := Γ C ), if the
type of a constructor c has the form ∀ p 1 :P 1 ,… ∀ p r :P r , ∀ x 1
:T 1 , … ∀ x r :T r , (I j p 1 … p r t 1 … t s ), then the recursive
arguments will correspond to T i in which one of the I l occurs.

The main rules for being structurally smaller are the following:
Given a variable y of type an inductive definition in a declaration
Ind[r](Γ I := Γ C ) where Γ I is [I 1 :A 1 ;…;I k :A k ], and Γ C is
[c 1 :C 1 ;…;c n :C n ]. The terms structurally smaller than y are:


+ (t u) and λ x:u . t when t is structurally smaller than y.
+ case(c,P,f 1 … f n ) when each f i is structurally smaller than y.
  If c is y or is structurally smaller than y, its type is an inductive
  definition I p part of the inductive declaration corresponding to y.
  Each f i corresponds to a type of constructor C q ≡ ∀ p 1 :P 1 ,…,∀ p
  r :P r , ∀ y 1 :B 1 , … ∀ y k :B k , (I a 1 … a k ) and can
  consequently be written λ y 1 :B′ 1 . … λ y k :B′ k . g i . (B′ i is
  obtained from B i by substituting parameters variables) the variables
  y j occurring in g i corresponding to recursive arguments B i (the
  ones in which one of the I l occurs) are structurally smaller than y.


The following definitions are correct, we enter them using theFixpoint
command as described in Section `1.3.4`_ and show the internal
representation.
Coq < Fixpoint plus (n m:nat) {struct n} : nat :=
match n with
| O => m
| S p => S (plus p m)
end.
plus is defined
plus is recursively defined (decreasing on 1st argument)

Coq < Print plus.
plus =
fix plus (n m : nat) {struct n} : nat :=
match n with
| 0 => m
| S p => S (plus p m)
end
: nat -> nat -> nat
Argument scopes are [nat_scope nat_scope]

Coq < Fixpoint lgth (A:Set) (l:list A) {struct l} : nat :=
match l with
| nil _ => O
| cons _ a l' => S (lgth A l')
end.
lgth is defined
lgth is recursively defined (decreasing on 2nd argument)

Coq < Print lgth.
lgth =
fix lgth (A : Set) (l : list A) {struct l} : nat :=
match l with
| nil _ => 0
| cons _ _ l' => S (lgth A l')
end
: forall A : Set, list A -> nat
Argument scopes are [type_scope _]

Coq < Fixpoint sizet (t:tree) : nat := let (f) := t in S (sizef f)
with sizef (f:forest) : nat :=
match f with
| emptyf => O
| consf t f => plus (sizet t) (sizef f)
end.
sizet is defined
sizef is defined
sizet, sizef are recursively defined (decreasing respectively on 1st,
1st arguments)

Coq < Print sizet.
sizet =
fix sizet (t : tree) : nat := let (f) := t in S (sizef f)
with sizef (f : forest) : nat :=
match f with
| emptyf => 0
| consf t f0 => plus (sizet t) (sizef f0)
end
for sizet
: tree -> nat



Reduction rule
``````````````

Let F be the set of declarations: f 1 /k 1 :A 1 :=t 1 …f n /k n :A n
:=t n . The reduction for fixpoints is:
(Fix f i {F} a 1 …a k i ) ▷ ι t i {(f k /Fix f k {F}) k=1… n } a 1 … a
k i
when a k i starts with a constructor. This last restriction is needed
in order to keep strong normalization and corresponds to the reduction
for primitive recursive operators. The following reductions are now
possible:
plus (S (S O)) (S O) ▷ ι S (plus (S O) (S O)) ▷ ι S (S (plus O (S O)))
▷ ι S (S (S O))


Mutual induction
````````````````

The principles of mutual induction can be automatically generated
using the Scheme command described in Section `13.1`_.


4.6 Admissible rules for global environments
--------------------------------------------

From the original rules of the type system, one can show the
admissibility of rules which change the local context of definition of
objects in the global environment. We show here the admissible rules
that are used used in the discharge mechanism at the end of a section.


Abstraction.
++++++++++++

One can modify a global declaration by generalizing it over a
previously assumed constant c. For doing that, we need to modify the
reference to the global declaration in the subsequent global
environment and local context by explicitly applying this constant to
the constant c′.

Below, if Γ is a context of the form [y 1 :A 1 ;…;y n :A n ], we write
∀x:U,Γ{c/x} to mean [y 1 :∀ x:U,A 1 {c/x};…;y n :∀ x:U,A n {c/x}]
andE{|Γ|/|Γ|c}. to mean the parallel substitutionE{y 1 /(y 1 c)}…{y n
/(y n c)}.


First abstracting property:
+++++++++++++++++++++++++++
WF(E;c:U;E′;c′:=t:T;E″)[Γ] WF(E;c:U;E′;c′:=λ x:U. t{c/x}:∀
x:U,T{c/x};E″{c′/(c′ c)})[Γ{c/(c c′)}] WF(E;c:U;E′;c′:T;E″)[Γ]
WF(E;c:U;E′;c′:∀ x:U,T{c/x};E″{c′/(c′ c)})[Γ{c/(c c′)}]
WF(E;c:U;E′;Ind[p](Γ I := Γ C );E″)[Γ] WF (E;c:U;E′;Ind[p+1](∀ x:U,Γ I
{c/x} := ∀ x:U,Γ C {c/x});E″{|Γ I ,Γ C |/|Γ I ,Γ C | c}) [Γ{|Γ I ,Γ C
|/|Γ I ,Γ C | c}]
One can similarly modify a global declaration by generalizing it over
a previously defined constant c′. Below, if Γ is a context of the form
[y 1 :A 1 ;…;y n :A n ], we write Γ{c/u} to mean [y 1 :A 1 {c/u};…;y n
:A n {c/u}].


Second abstracting property:
++++++++++++++++++++++++++++
WF(E;c:=u:U;E′;c′:=t:T;E″)[Γ] WF(E;c:=u:U;E′;c′:=(let x:=u:U in
t{c/x}):T{c/u};E″)[Γ] WF(E;c:=u:U;E′;c′:T;E″)[Γ]
WF(E;c:=u:U;E′;c′:T{c/u};E″)[Γ] WF(E;c:=u:U;E′;Ind[p](Γ I := Γ C
);E″)[Γ] WF(E;c:=u:U;E′;Ind[p](Γ I {c/u} := Γ C {c/u});E″)[Γ]


Pruning the local context.
++++++++++++++++++++++++++

If one abstracts or substitutes constants with the above rules then it
may happen that some declared or defined constant does not occur any
more in the subsequent global environment and in the local context.
One can consequently derive the following property.


First pruning property:
+++++++++++++++++++++++
WF(E;c:U;E′)[Γ] c does not occur in E′ and Γ WF(E;E′)[Γ]


Second pruning property:
++++++++++++++++++++++++
WF(E;c:=u:U;E′)[Γ] c does not occur in E′ and Γ WF(E;E′)[Γ]


4.7 Co-inductive types
----------------------

The implementation contains also co-inductive definitions, which are
types inhabited by infinite objects. More information on co-inductive
definitions can be found in [`68`_, `70`_, `71`_].


4.8 The Calculus of Inductive Construction with impredicative Set
-----------------------------------------------------------------

Coq can be used as a type-checker for the Calculus of Inductive
Constructions with an impredicative sort Set by using the compiler
option -impredicative-set. For example, using the ordinary coqtop
command, the following is rejected.
Coq < Fail Definition id: Set := forall X:Set,X->X.
The command has indeed failed with message:
The term "forall X : Set, X -> X" has type "Type"
while it is expected to have type "Set".

while it will type-check, if one uses instead the coqtop
-impredicative-set command.

The major change in the theory concerns the rule for product formation
in the sort Set, which is extended to a domain in any sort:

:Prod: E[Γ] ⊢ T : s s ∈ S E[Γ::(x:T)] ⊢ U : Set E[Γ] ⊢ ∀ x:T,U : Set


This extension has consequences on the inductive definitions which are
allowed. In the impredicative system, one can build so-called *large
inductive definitions* like the example of second-order existential
quantifier (exSet).

There should be restrictions on the eliminations which can be
performed on such definitions. The eliminations rules in the
impredicative system for sort Set become:

:Set: s ∈ {Prop, Set} [I:Set|I→ s] I is a small inductive definition s
  ∈ {Type(i)} [I:Set|I→ s]




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
.. _4.5  Inductive definitions: :///home/steck/cic.html#Cic-inductive-definitions
.. _About Coq: :///about-coq
.. _Commands: :///home/steck/command-index.html
.. _CSS valid: http://jigsaw.w3.org/css-validator/
.. _126: :///home/steck/biblio.html#Moh93
.. _Cover: :///home/steck/index.html
.. _General: :///home/steck/general-index.html
.. _Table of contents: :///home/steck/toc.html
.. _Community: :///community
.. _13.1: :///home/steck/schemes.html#Scheme
.. _28: :///home/steck/biblio.html#Coq92
.. _4.1  The terms: :///home/steck/cic.html#Terms
.. _2.10: :///home/steck/gallina-ext.html#PrintingUniverses
.. _Set: :///home/steck/cic.html#impredicativity
.. _145: :///home/steck/biblio.html#Wer94
.. _4.7  Co-inductive types: :///home/steck/cic.html#sec222
.. _8: :///home/steck/biblio.html#Bar81
.. _29: :///home/steck/universes.html#Universes-full
.. _4.2  Typing rules: :///home/steck/cic.html#Typed-terms
.. _4.4  Subtyping rules: :///home/steck/cic.html#subtyping-rules
.. _71: :///home/steck/biblio.html#GimCas05
.. _4.3  Conversion rules: :///home/steck/cic.html#conv-rules
.. _25: :///home/steck/biblio.html#Coq86
.. _24: :///home/steck/biblio.html#Coq85
.. _xhtml valid: http://validator.w3.org/
.. _Tactics: :///home/steck/tactic-index.html
.. _70: :///home/steck/biblio.html#Gim98
.. _81: :///home/steck/biblio.html#How80
.. _Options: :///home/steck/option-index.html
.. _68: :///home/steck/biblio.html#Gimenez95b
.. _The Coq Proof Assistant: :///
.. _38: :///home/steck/biblio.html#Cur58
.. _4.6  Admissible rules for global environments: :///home/steck/cic.html#sec215
.. _Errors: :///home/steck/error-index.html
.. _Documentation: :///documentation
.. _67: :///home/steck/biblio.html#Gim94
.. _8: :///home/steck/tactics.html#Tactics
.. _webmaster: mailto:coq-www_@_inria.fr
.. _39: :///home/steck/biblio.html#Bru72



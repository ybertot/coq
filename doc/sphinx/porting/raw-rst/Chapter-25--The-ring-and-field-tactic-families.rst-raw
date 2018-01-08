

+ `Home`_
+ `About Coq`_
+ `Get Coq`_
+ `Documentation`_
+ `Community`_

` `_ `The Coq Proof Assistant`_


Chapter 25 The ring and field tactic families
=============================================


+ `25.1 What does this tactic do?`_
+ `25.2 The variables map`_
+ `25.3 Is it automatic?`_
+ `25.4 Concrete usage in Coq`_
+ `25.5 Adding a ring structure`_
+ `25.6 How does it work?`_
+ `25.7 Dealing with fields `_
+ `25.8 Adding a new field structure`_
+ `25.9 History of ring`_
+ `25.10 Discussion`_


Bruno Barras, Benjamin Grégoire, Assia Mahboubi, Laurent Théry 1



This chapter presents the tactics dedicated to deal with ring and
field equations.


25.1 What does this tactic do?
------------------------------

ring does associative-commutative rewriting in ring and semi-ring
structures. Assume you have two binary functions ⊕ and ⊗ that are
associative and commutative, with ⊕ distributive on ⊗, and two
constants 0 and 1 that are unities for ⊕ and ⊗. A polynomial is an
expression built on variables V 0 , V 1 , … and constants by
application of ⊕ and ⊗.

Let an ordered product be a product of variables V i 1 ⊗ … ⊗ V i n
verifying i 1 ≤ i 2 ≤ … ≤i n . Let a monomial be the product of a
constant and an ordered product. We can order the monomials by the
lexicographic order on products of variables. Let a canonical sum be
an ordered sum of monomials that are all different, i.e. each monomial
in the sum is strictly less than the following monomial according to
the lexicographic order. It is an easy theorem to show that every
polynomial is equivalent (modulo the ring properties) to exactly one
canonical sum. This canonical sum is called the normal form of the
polynomial. In fact, the actual representation shares monomials with
same prefixes. So what does ring? It normalizes polynomials over any
ring or semi-ring structure. The basic use ofring is to simplify ring
expressions, so that the user does not have to deal manually with the
theorems of associativity and commutativity.


Examples:


#. In the ring of integers, the normal form of x (3 + yx + 25(1 − z))
   + zx is 28x + (−24)xz + xxy.


ring is also able to compute a normal form modulo monomial equalities.
For example, under the hypothesis that 2x 2 = yz+1, the normal form of
2(x + 1)x − x − zy is x+1.


25.2 The variables map
----------------------

It is frequent to have an expression built with + and ×, but rarely on
variables only. Let us associate a number to each subterm of a ring
expression in the Gallina language. For example in the ringnat,
consider the expression:


::

    (plus (mult (plus (f (5)) x) x)
          (mult (if b then (4) else (f (3))) (2)))


As a ring expression, it has 3 subterms. Give each subterm a number in
an arbitrary order:
0 ↦ `if b then (4) else (f (3))` 1 ↦ `(f (5))` 2 ↦ `x`
Then normalize the “abstract” polynomial
((V 1 ⊗ V 2 ) ⊕ V 2 ) ⊕ (V 0 ⊗ 2)
In our example the normal form is:
(2 ⊗ V 0 ) ⊕ (V 1 ⊗ V 2 ) ⊕ (V 2 ⊗ V 2 )
Then substitute the variables by their values in the variables map to
get the concrete normal polynomial:


::

    (plus (mult (2) (if b then (4) else (f (3)))) 
          (plus (mult (f (5)) x) (mult x x))) 




25.3 Is it automatic?
---------------------

Yes, building the variables map and doing the substitution after
normalizing is automatically done by the tactic. So you can just
forget this paragraph and use the tactic according to your intuition.


25.4 Concrete usage in Coq
--------------------------

The ring tactic solves equations upon polynomial expressions of a ring
(or semi-ring) structure. It proceeds by normalizing both hand sides
of the equation (w.r.t. associativity, commutativity and
distributivity, constant propagation, rewriting of monomials) and
comparing syntactically the results.

ring_simplify applies the normalization procedure described above to
the terms given. The tactic then replaces all occurrences of the terms
given in the conclusion of the goal by their normal forms. If no term
is given, then the conclusion should be an equation and both hand
sides are normalized. The tactic can also be applied in a hypothesis.

The tactic must be loaded by Require Import Ring. The ring structures
must be declared with the Add Ring command (see below). The ring of
booleans is predefined; if one wants to use the tactic on nat one must
first require the moduleArithRing (exported by Arith); for Z, do
Require Import ZArithRing or simply Require Import ZArith; for N, do
Require Import NArithRing or Require Import NArith.


Example:
Coq < Require Import ZArith.

Coq < Open Scope Z_scope.

Coq < Goal forall a b c:Z,
(a + b + c)^2 =
a * a + b^2 + c * c + 2 * a * b + 2 * a * c + 2 * b * c.
1 subgoal

============================
forall a b c : Z,
(a + b + c) ^ 2 = a * a + b ^ 2 + c * c + 2 * a * b + 2 * a * c + 2 *
b * c

Coq < intros; ring.
No more subgoals.
Coq < Goal forall a b:Z, 2*a*b = 30 ->
(a+b)^2 = a^2 + b^2 + 30.
1 subgoal

============================
forall a b : Z, 2 * a * b = 30 -> (a + b) ^ 2 = a ^ 2 + b ^ 2 + 30

Coq < intros a b H; ring [H].
No more subgoals.


Variants:


#. ring [term 1 … term n ] decides the equality of two terms modulo
   ring operations and rewriting of the equalities defined by term 1 …
   term n . Each of term 1 … term n has to be a proof of some equality m
   = p, where m is a monomial (after “abstraction”),p a polynomial and =
   the corresponding equality of the ring structure.
#. ring_simplify [term 1 … term n ] t 1 … t m in ident performs the
   simplification in the hypothesis named ident.



Warning: ring_simplify term 1 ; ring_simplify term 2 is not equivalent
to ring_simplify term 1 term 2 . In the latter case the variables map
is shared between the two terms, and common subterm t of term 1 and
term 2 will have the same associated variable number. So the first
alternative should be avoided for terms belonging to the same ring
theory.


Error messages:


#. not a valid ring equation The conclusion of the goal is not
   provable in the corresponding ring theory.
#. arguments of ring_simplify do not have all the same
   typering_simplify cannot simplify terms of several rings at the same
   time. Invoke the tactic once per ring structure.
#. cannot find a declared ring structure over term No ring has been
   declared for the type of the terms to be simplified. Use Add Ring
   first.
#. cannot find a declared ring structure for equalityterm Same as
   above is the case of the ring tactic.



25.5 Adding a ring structure
----------------------------

Declaring a new ring consists in proving that a ring signature (a
carrier set, an equality, and ring operations: Ring_theory.ring_theory
and Ring_theory.semi_ring_theory) satisfies the ring axioms. Semi-
rings (rings without + inverse) are also supported. The equality can
be either Leibniz equality, or any relation declared as a setoid (see
`27.2.2`_). The definition of ring and semi-rings (see module
Ring_theory) is:

::

    Record ring_theory : Prop := mk_rt {
      Radd_0_l    : forall x, 0 + x == x;
      Radd_sym    : forall x y, x + y == y + x;
      Radd_assoc  : forall x y z, x + (y + z) == (x + y) + z;
      Rmul_1_l    : forall x, 1 * x == x;
      Rmul_sym    : forall x y, x * y == y * x;
      Rmul_assoc  : forall x y z, x * (y * z) == (x * y) * z;
      Rdistr_l    : forall x y z, (x + y) * z == (x * z) + (y * z);
      Rsub_def    : forall x y, x - y == x + -y;
      Ropp_def    : forall x, x + (- x) == 0
    }.
    
    Record semi_ring_theory : Prop := mk_srt {
      SRadd_0_l   : forall n, 0 + n == n;
      SRadd_sym   : forall n m, n + m == m + n ;
      SRadd_assoc : forall n m p, n + (m + p) == (n + m) + p;
      SRmul_1_l   : forall n, 1*n == n;
      SRmul_0_l   : forall n, 0*n == 0;
      SRmul_sym   : forall n m, n*m == m*n;
      SRmul_assoc : forall n m p, n*(m*p) == (n*m)*p;
      SRdistr_l   : forall n m p, (n + m)*p == n*p + m*p
    }.


This implementation of ring also features a notion of constant that
can be parameterized. This can be used to improve the handling of
closed expressions when operations are effective. It consists in
introducing a type of *coefficients* and an implementation of the ring
operations, and a morphism from the coefficient type to the ring
carrier type. The morphism needs not be injective, nor surjective.

As an example, one can consider the real numbers. The set of
coefficients could be the rational numbers, upon which the ring
operations can be implemented. The fact that there exists a morphism
is defined by the following properties:

::

    Record ring_morph : Prop := mkmorph {
      morph0    : [cO] == 0;
      morph1    : [cI] == 1;
      morph_add : forall x y, [x +! y] == [x]+[y];
      morph_sub : forall x y, [x -! y] == [x]-[y];
      morph_mul : forall x y, [x *! y] == [x]*[y];
      morph_opp : forall x, [-!x] == -[x];
      morph_eq  : forall x y, x?=!y = true -> [x] == [y]
    }.
    
    Record semi_morph : Prop := mkRmorph {
      Smorph0 : [cO] == 0;
      Smorph1 : [cI] == 1;
      Smorph_add : forall x y, [x +! y] == [x]+[y];
      Smorph_mul : forall x y, [x *! y] == [x]*[y];
      Smorph_eq  : forall x y, x?=!y = true -> [x] == [y]
    }.


where c0 and cI denote the 0 and 1 of the coefficient set,+!, *!, -!
are the implementations of the ring operations, == is the equality of
the coefficients, ?+! is an implementation of this equality, and [x]
is a notation for the image of x by the ring morphism.

Since Z is an initial ring (and N is an initial semi-ring), it can
always be considered as a set of coefficients. There are basically
three kinds of (semi-)rings:

:abstract rings: to be used when operations are not effective. The set
  of coefficients is Z (or N for semi-rings).
:computational rings: to be used when operations are effective. The
  set of coefficients is the ring itself. The user only has to provide
  an implementation for the equality.
:customized ring: for other cases. The user has to provide the
  coefficient set and the morphism.


This implementation of ring can also recognize simple power
expressions as ring expressions. A power function is specified by the
following property:

::

    Section POWER.
      Variable Cpow : Set.
      Variable Cp_phi : N -> Cpow.
      Variable rpow : R -> Cpow -> R.
    
      Record power_theory : Prop := mkpow_th {
        rpow_pow_N : forall r n, req (rpow r (Cp_phi n)) (pow_N rI rmul r n)
      }.
    
    End POWER.


The syntax for adding a new ring is Add Ring name : ring (mod 1 ,…,mod
2 ). The name is not relevant. It is just used for error messages. The
term ring is a proof that the ring signature satisfies the (semi-)ring
axioms. The optional list of modifiers is used to tailor the behavior
of the tactic. The following list describes their syntax and effects:

:abstract: declares the ring as abstract. This is the default.
:decidable term: declares the ring as computational. The expression
  term is the correctness proof of an equality test ?=! (which should be
  evaluable). Its type should be of the form forall x y, x?=!y = true →
  x == y.
:morphism term: declares the ring as a customized one. The expression
  term is a proof that there exists a morphism between a set of
  coefficient and the ring carrier (see Ring_theory.ring_morph and
  Ring_theory.semi_morph).
:setoid term 1 term 2 : forces the use of given setoid. The expression
  term 1 is a proof that the equality is indeed a setoid (see
  Setoid.Setoid_Theory), and term 2 a proof that the ring operations are
  morphisms (see Ring_theory.ring_eq_ext andRing_theory.sring_eq_ext).
  This modifier needs not be used if the setoid and morphisms have been
  declared.
:constants [ L tac : ] specifies a tactic expression that, given a
  term, returns either an object of the coefficient set that is mapped
  to the expression via the morphism, or returns
  InitialRing.NotConstant. The default behavior is to map only 0 and 1
  to their counterpart in the coefficient set. This is generally not
  desirable for non trivial computational rings.
:preprocess [ L tac : ] specifies a tactic that is applied as a
  preliminary step for ring and ring_simplify. It can be used to
  transform a goal so that it is better recognized. For instance, S n
  can be changed to plus 1 n.
:postprocess [ L tac : ] specifies a tactic that is applied as a final
  step for ring_simplify. For instance, it can be used to undo
  modifications of the preprocessor.
:power_tac term [ L tac : ] allows ring and ring_simplify to recognize
  power expressions with a constant positive integer exponent (example:
  x 2 ). The term term is a proof that a given power function satisfies
  the specification of a power function (term has to be a proof of
  Ring_theory.power_theory) and L tac specifies a tactic expression
  that, given a term, “abstracts” it into an object of type N whose
  interpretation via Cp_phi (the evaluation function of power
  coefficient) is the original term, or returns InitialRing.NotConstant
  if not a constant coefficient (i.e. L tac is the inverse function of
  Cp_phi). See files plugins/setoid_ring/ZArithRing.v
  andplugins/setoid_ring/RealField.v for examples. By default the tactic
  does not recognize power expressions as ring expressions.
:sign term: allows ring_simplify to use a minus operation when
  outputting its normal form, i.e writing x − y instead of x + (−y). The
  term term is a proof that a given sign function indicates expressions
  that are signed (term has to be a proof of Ring_theory.get_sign). See
  plugins/setoid_ring/InitialRing.v for examples of sign function.
:div term: allows ring and ring_simplify to use monomials with
  coefficient other than 1 in the rewriting. The term term is a proof
  that a given division function satisfies the specification of an
  euclidean division function (term has to be a proof of
  Ring_theory.div_theory). For example, this function is called when
  trying to rewrite 7x by 2x = z to tell that 7 = 3 * 2 + 1. See
  plugins/setoid_ring/InitialRing.v for examples of div function.



Error messages:


#. bad ring structure The proof of the ring structure provided is not
   of the expected type.
#. bad lemma for decidability of equality The equality function
   provided in the case of a computational ring has not the expected
   type.
#. ring operation should be declared as a morphism A setoid associated
   to the carrier of the ring structure as been found, but the ring
   operation should be declared as morphism. See `27.2.2`_.



25.6 How does it work?
----------------------

The code of ring is a good example of tactic written usingreflection.
What is reflection? Basically, it is writingCoq tactics in Coq, rather
than in Objective Caml. From the philosophical point of view, it is
using the ability of the Calculus of Constructions to speak and reason
about itself. For the ring tactic we used Coq as a programming
language and also as a proof environment to build a tactic and to
prove it correctness.

The interested reader is strongly advised to have a look at the
fileRing_polynom.v. Here a type for polynomials is defined:


::

    Inductive PExpr : Type :=
      | PEc : C -> PExpr
      | PEX : positive -> PExpr
      | PEadd : PExpr -> PExpr -> PExpr
      | PEsub : PExpr -> PExpr -> PExpr
      | PEmul : PExpr -> PExpr -> PExpr
      | PEopp : PExpr -> PExpr
      | PEpow : PExpr -> N -> PExpr.


Polynomials in normal form are defined as:


::

    Inductive Pol : Type :=
      | Pc : C -> Pol 
      | Pinj : positive -> Pol -> Pol                   
      | PX : Pol -> positive -> Pol -> Pol.


where Pinj n P denotes P in which V i is replaced byV i+n , and PX P n
Q denotes P ⊗ V 1 n ⊕ Q′,Q′ being Q where V i is replaced by V i+1 .

Variables maps are represented by list of ring elements, and two
interpretation functions, one that maps a variables map and a
polynomial to an element of the concrete ring, and the second one that
does the same for normal forms:


::

    Definition PEeval : list R -> PExpr -> R := [...].
    Definition Pphi_dev : list R -> Pol -> R := [...].


A function to normalize polynomials is defined, and the big theorem is
its correctness w.r.t interpretation, that is:


::

    Definition norm : PExpr -> Pol := [...].
    Lemma Pphi_dev_ok :
       forall l pe npe, norm pe = npe -> PEeval l pe == Pphi_dev l npe.


So now, what is the scheme for a normalization proof? Let p be the
polynomial expression that the user wants to normalize. First a little
piece of ML code guesses the type of p, the ring theory T to use, an
abstract polynomial ap and a variables map v such that p is βδι-
equivalent to `(PEeval v ap)`. Then we replace it by `(Pphi_dev v
(norm ap))`, using the main correctness theorem and we reduce it to a
concrete expressionp’, which is the concrete normal form ofp. This is
summarized in this diagram:
p → βδι (PEeval v ap) = (by the main correctness theorem) p’ ← βδι
(Pphi_dev v (norm ap))
The user do not see the right part of the diagram. From outside, the
tactic behaves like a βδι simplification extended with AC rewriting
rules. Basically, the proof is only the application of the main
correctness theorem to well-chosen arguments.


25.7 Dealing with fields
------------------------

The field tactic is an extension of the ring to deal with rational
expression. Given a rational expression F=0. It first reduces the
expression F to a common denominator N/D= 0 where N and D are two ring
expressions. For example, if we take F = (1 − 1/x) x − x + 1, this
gives N= (x −1) x − x 2 + x and D= x. It then calls ring to solve N=0.
Note that field also generates non-zero conditions for all the
denominators it encounters in the reduction. In our example, it
generates the condition x ≠ 0. These conditions appear as one subgoal
which is a conjunction if there are several denominators. Non-zero
conditions are always polynomial expressions. For example when
reducing the expression 1/(1 + 1/x), two side conditions are
generated: x≠ 0 and x + 1 ≠ 0. Factorized expressions are broken since
a field is an integral domain, and when the equality test on
coefficients is complete w.r.t. the equality of the target field,
constants can be proven different from zero automatically.

The tactic must be loaded by Require Import Field. New field
structures can be declared to the system with the Add Field command
(see below). The field of real numbers is defined in moduleRealField
(in textttplugins/setoid_ring). It is exported by module Rbase, so
that requiring Rbase orReals is enough to use the field tactics on
real numbers. Rational numbers in canonical form are also declared as
a field in module Qcanon.


Example:
Coq < Require Import Reals.

Coq < Open Scope R_scope.

Coq < Goal forall x, x <> 0 ->
(1 - 1/x) * x - x + 1 = 0.
1 subgoal

============================
forall x : R, x <> 0 -> (1 - 1 / x) * x - x + 1 = 0

Coq < intros; field; auto.
No more subgoals.
Coq < Goal forall x y, y <> 0 -> y = x -> x/y = 1.
1 subgoal

============================
forall x y : R, y <> 0 -> y = x -> x / y = 1

Coq < intros x y H H1; field [H1]; auto.
No more subgoals.


Variants:


#. field [term 1 … term n ] decides the equality of two terms modulo
   field operations and rewriting of the equalities defined by term 1 …
   term n . Each of term 1 … term n has to be a proof of some equality m
   = p, where m is a monomial (after “abstraction”),p a polynomial and =
   the corresponding equality of the field structure. Beware that
   rewriting works with the equality m=p only if p is a polynomial since
   rewriting is handled by the underlying ring tactic.
#. field_simplify performs the simplification in the conclusion of the
   goal, F 1 = F 2 becomes N 1 /D 1 = N 2 /D 2 . A normalization step
   (the same as the one for rings) is then applied to N 1 , D 1 , N 2
   andD 2 . This way, polynomials remain in factorized form during the
   fraction simplifications. This yields smaller expressions when
   reducing to the same denominator since common factors can be canceled.
#. field_simplify [term 1 … term n ] performs the simplification in
   the conclusion of the goal using the equalities defined by term 1 …
   term n .
#. field_simplify [term 1 … term n ] t 1 …t m performs the
   simplification in the terms t 1 …t m of the conclusion of the goal
   using the equalities defined by term 1 … term n .
#. field_simplify in H performs the simplification in the assumption
   H.
#. field_simplify [term 1 … term n ] in H performs the simplification
   in the assumption H using the equalities defined by term 1 … term n .
#. field_simplify [term 1 … term n ] t 1 …t m in H performs the
   simplification in the terms t 1 …t n of the assumption H using the
   equalities defined by term 1 … term m .
#. field_simplify_eq performs the simplification in the conclusion of
   the goal removing the denominator. F 1 = F 2 becomes N 1 D 2 = N 2 D 1
   .
#. field_simplify_eq [term 1 … term n ] performs the simplification in
   the conclusion of the goal using the equalities defined by term 1 …
   term n .
#. field_simplify_eq in H performs the simplification in the
   assumption H.
#. field_simplify_eq [term 1 … term n ] in H performs the
   simplification in the assumption H using the equalities defined by
   term 1 … term n .



25.8 Adding a new field structure
---------------------------------

Declaring a new field consists in proving that a field signature (a
carrier set, an equality, and field operations:
Field_theory.field_theory and Field_theory.semi_field_theory)
satisfies the field axioms. Semi-fields (fields without + inverse) are
also supported. The equality can be either Leibniz equality, or any
relation declared as a setoid (see `27.2.2`_). The definition of
fields and semi-fields is:

::

    Record field_theory : Prop := mk_field {
      F_R : ring_theory rO rI radd rmul rsub ropp req;
      F_1_neq_0 : ~ 1 == 0;
      Fdiv_def : forall p q, p / q == p * / q;
      Finv_l : forall p, ~ p == 0 ->  / p * p == 1
    }.
    
    Record semi_field_theory : Prop := mk_sfield {
      SF_SR : semi_ring_theory rO rI radd rmul req;
      SF_1_neq_0 : ~ 1 == 0;
      SFdiv_def : forall p q, p / q == p * / q;
      SFinv_l : forall p, ~ p == 0 ->  / p * p == 1
    }.


The result of the normalization process is a fraction represented by
the following type:

::

    Record linear : Type := mk_linear {
      num : PExpr C;
      denum : PExpr C;
      condition : list (PExpr C)
    }.


where num and denum are the numerator and denominator;condition is a
list of expressions that have appeared as a denominator during the
normalization process. These expressions must be proven different from
zero for the correctness of the algorithm.

The syntax for adding a new field is Add Field name : field (mod 1
,…,mod 2 ). The name is not relevant. It is just used for error
messages. field is a proof that the field signature satisfies the
(semi-)field axioms. The optional list of modifiers is used to tailor
the behavior of the tactic. Since field tactics are built upon ring
tactics, all modifiers of the Add Ring apply. There is only one
specific modifier:

:completeness term: allows the field tactic to prove automatically
  that the image of non-zero coefficients are mapped to non-zero
  elements of the field. termis a proof of forall x y, [x] == [y] ->
  x?=!y = true, which is the completeness of equality on coefficients
  w.r.t. the field equality.



25.9 History of ring
--------------------

First Samuel Boutin designed the tactic ACDSimpl. This tactic did lot
of rewriting. But the proofs terms generated by rewriting were too big
for Coq’s type-checker. Let us see why:
Coq < Goal forall x y z:Z, x + 3 + y + y * z = x + 3 + y + z * y.
1 subgoal

============================
forall x y z : Z, x + 3 + y + y * z = x + 3 + y + z * y

Coq < intros; rewrite (Z.mul_comm y z); reflexivity.

Coq < Save toto.

Coq < Print toto.
toto =
fun x y z : Z =>
eq_ind_r (fun z0 : Z => x + 3 + y + z0 = x + 3 + y + z * y) eq_refl
(Z.mul_comm y z)
: forall x y z : Z, x + 3 + y + y * z = x + 3 + y + z * y
Argument scopes are [Z_scope Z_scope Z_scope]

At each step of rewriting, the whole context is duplicated in the
proof term. Then, a tactic that does hundreds of rewriting generates
huge proof terms. Since ACDSimpl was too slow, Samuel Boutin rewrote
it using reflection (see his article in TACS’97 [`19`_]). Later, the
stuff was rewritten by Patrick Loiseleur: the new tactic does not any
more require ACDSimpl to compile and it makes use of βδι-reduction not
only to replace the rewriting steps, but also to achieve the
interleaving of computation and reasoning (see 25.10). He also wrote a
few ML code for the Add Ring command, that allow to register new rings
dynamically.

Proofs terms generated by ring are quite small, they are linear in the
number of ⊕ and ⊗ operations in the normalized terms. Type-checking
those terms requires some time because it makes a large use of the
conversion rule, but memory requirements are much smaller.


25.10 Discussion
----------------



Efficiency is not the only motivation to use reflection here. ring
also deals with constants, it rewrites for example the expression 34 +
2*x −x + 12 to the expected result x + 46. For the tactic ACDSimpl,
the only constants were 0 and 1. So the expression 34 + 2*(x − 1) + 12
is interpreted as V 0 ⊕ V 1 ⊗ (V 2 ⊖ 1) ⊕ V 3 , with the variables
mapping {V 0 ↦ 34; V 1 ↦ 2; V 2 ↦ x; V 3 ↦ 12 }. Then it is rewritten
to 34 − x + 2*x + 12, very far from the expected result. Here
rewriting is not sufficient: you have to do some kind of reduction
(some kind of computation) to achieve the normalization.

The tactic ring is not only faster than a classical one: using
reflection, we get for free integration of computation and reasoning
that would be very complex to implement in the classic fashion.

Is it the ultimate way to write tactics? The answer is: yes and no.
The ring tactic uses intensively the conversion rule ofCic, that is
replaces proof by computation the most as it is possible. It can be
useful in all situations where a classical tactic generates huge proof
terms. Symbolic Processing and Tautologies are in that case. But there
are also tactics like auto orlinear that do many complex computations,
using side-effects and backtracking, and generate a small proof term.
Clearly, it would be significantly less efficient to replace them by
tactics using reflection.

Another idea suggested by Benjamin Werner: reflection could be used to
couple an external tool (a rewriting program or a model checker)
withCoq. We define (in Coq) a type of terms, a type of *traces*, and
prove a correction theorem that states that *replaying traces* is safe
w.r.t some interpretation. Then we let the external tool do every
computation (using side-effects, backtracking, exception, or others
features that are not available in pure lambda calculus) to produce
the trace: now we can check in Coq that the trace has the expected
semantic by applying the correction lemma.



:1: based on previous work from Patrick Loiseleur and Samuel Boutin




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
.. _27.2.2: :///home/steck/setoid.html#setoidtactics
.. _Table of contents: :///home/steck/toc.html
.. _Community: :///community
.. _25.10  Discussion: :///home/steck/ring.html#sec846
.. _25.8  Adding a new field structure
: :///home/steck/ring.html#sec844
.. _ring: :///home/steck/ring.html#sec845
.. _25.6  How does it work?: :///home/steck/ring.html#sec842
.. _25.7  Dealing with fields


: :///home/steck/ring.html#sec843
.. _
: :///home/steck/ring.html#sec840
.. _25.5  Adding a ring structure
: :///home/steck/ring.html#sec841
.. _Commands: :///home/steck/command-index.html
.. _xhtml valid: http://validator.w3.org/
.. _Tactics: :///home/steck/tactic-index.html
.. _General: :///home/steck/general-index.html
.. _Options: :///home/steck/option-index.html
.. _The Coq Proof Assistant: :///
.. _25.1  What does this tactic do?: :///home/steck/ring.html#sec837
.. _Documentation: :///documentation
.. _19: :///home/steck/biblio.html#Bou97
.. _25.3  Is it automatic?: :///home/steck/ring.html#sec839
.. _25.2  The variables map: :///home/steck/ring.html#sec838
.. _webmaster: mailto:coq-www_@_inria.fr



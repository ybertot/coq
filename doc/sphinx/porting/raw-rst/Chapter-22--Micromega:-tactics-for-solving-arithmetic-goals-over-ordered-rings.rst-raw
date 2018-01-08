

+ `Home`_
+ `About Coq`_
+ `Get Coq`_
+ `Documentation`_
+ `Community`_

` `_ `The Coq Proof Assistant`_


Chapter 22 Micromega: tactics for solving arithmetic goals over
ordered rings
=============


+ `22.1 Short description of the tactics`_
+ `22.2 *Positivstellensatz* refutations`_
+ `22.3 lra: a decision procedure for linear real and rational
  arithmetic`_
+ `22.4 lia: a tactic for linear integer arithmetic`_
+ `22.5 nra: a proof procedure for non-linear arithmetic`_
+ `22.6 nia: a proof procedure for non-linear integer arithmetic`_
+ `22.7 psatz: a proof procedure for non-linear arithmetic`_


Frédéric Besson and Evgeny Makarov




22.1 Short description of the tactics
-------------------------------------

The Psatz module (Require Import Psatz.) gives access to several
tactics for solving arithmetic goals over Z, Q, andR: 1 . It also
possible to get the tactics for integers by a Require Import Lia,
rationals Require Import Lqa and reals Require Import Lra.


+ lia is a decision procedure for linear integer arithmetic (see
  Section 22.4);
+ nia is an incomplete proof procedure for integer non-linear
  arithmetic (see Section 22.6);
+ lra is a decision procedure for linear (real or rational) arithmetic
  (see Section 22.3);
+ nra is an incomplete proof procedure for non-linear (real or
  rational) arithmetic (see Section 22.5);
+ psatz D n where D is Z or Q or R, andn is an optional integer
  limiting the proof search depth is is an incomplete proof procedure
  for non-linear arithmetic. It is based on John Harrison’s HOL Light
  driver to the external prover csdp 2 . Note that the csdp driver is
  generating a *proof cache* which makes it possible to rerun scripts
  even without csdp (see Section 22.7).


The tactics solve propositional formulas parameterized by atomic
arithmetic expressions interpreted over a domain D ∈ {ℤ, ℚ, ℝ }. The
syntax of the formulas is the following:
F ::= A ∣ P ∣ True ∣ False ∣ F 1 ∧ F 2 ∣ F 1 ∨ F 2 ∣ F 1 ↔ F 2 ∣ F 1 →
F 2 ∣ ¬ F A ::= p 1 = p 2 ∣ p 1 > p 2 ∣ p 1 < p 2 ∣ p 1 ≥ p 2 ∣ p 1 ≤
p 2 p ::= c ∣ x ∣ −p ∣ p 1 − p 2 ∣ p 1 + p 2 ∣ p 1 × p 2 ∣ p `^` n
where c is a numeric constant, x∈ D is a numeric variable, the
operators −, +, × are respectively subtraction, addition, product, p
`^`n is exponentiation by a constant n, P is an arbitrary proposition.
For Q, equality is not Leibniz equality = but the equality of
rationals ==.

For Z (resp. Q ), c ranges over integer constants (resp. rational
constants). For R, the tactic recognizes as real constants the
following expressions:

::

    c ::= R0 | R1 | Rmul(c,c) | Rplus(c,c) | Rminus(c,c) | IZR z | IQR q
        | Rdiv(c,c) | Rinv c


where z is a constant in Z and q is a constant in Q. This includes
integer constants written using the decimal notation *i.e.,* c%R.


22.2 *Positivstellensatz* refutations
-------------------------------------



The name psatz is an abbreviation for *positivstellensatz* – literally
positivity theorem – which generalizes Hilbert’s *nullstellensatz*. It
relies on the notion of Cone. Given a (finite) set of polynomials S,
Cone(S) is inductively defined as the smallest set of polynomials
closed under the following rules:
p ∈ S p ∈ Cone(S) p 2 ∈ Cone(S) p 1 ∈ Cone(S) p 2 ∈ Cone(S) ⑅ ∈ {+,*}
p 1 ⑅ p 2 ∈ Cone(S)
The following theorem provides a proof principle for checking that a
set of polynomial inequalities does not have solutions. 3
Theorem 1 ** * Let *S * be a set of polynomials.
If *−1 * belongs to *Cone(S) * then the conjunction*∧ p ∈ S p≥ 0 * is
unsatisfiable.*
A proof based on this theorem is called a *positivstellensatz*
refutation. The tactics work as follows. Formulas are normalized into
conjunctive normal form ∧ i C i whereC i has the general form (∧ j∈ S
i p j ⑅ 0) → False) and ⑅ ∈ {>,≥,=} for D∈ {ℚ,ℝ} and ⑅ ∈ {≥, =} for ℤ.
For each conjunct C i , the tactic calls a oracle which searches for
−1 within the cone. Upon success, the oracle returns a *cone
expression* that is normalized by the ring tactic (see chapter `25`_)
and checked to be −1.


22.3 lra: a decision procedure for linear real and rational arithmetic
----------------------------------------------------------------------

The lra tactic is searching for *linear* refutations using Fourier
elimination. 4 As a result, this tactic explores a subset of the Cone
defined as
LinCone(S) = ⎧
⎪
⎨
⎪
⎩ ∑ p ∈ S α p × p ⎪
⎪
⎪
⎪ α p are positive constants ⎫
⎪
⎬
⎪
⎭ .
The deductive power of lra is the combined deductive power of
ring_simplify and fourier. There is also an overlap with the field
tactic *e*.g., x = 10 * x / 10 is solved by lra.


22.4 lia: a tactic for linear integer arithmetic
------------------------------------------------



The tactic lia offers an alternative to the omega and romega tactic
(see Chapter `21`_). Roughly speaking, the deductive power of lia is
the combined deductive power of ring_simplify and omega. However, it
solves linear goals that omega and romega do not solve, such as the
following so-called *omega nightmare* [`130`_].
Coq < Goal forall x y,
27 <= 11 * x + 13 * y <= 45 ->
-10 <= 7 * x - 9 * y <= 4 -> False.

The estimation of the relative efficiency of lia *vs* omega and romega
is under evaluation.


High level view of lia.
+++++++++++++++++++++++

Over ℝ, *positivstellensatz* refutations are a complete proof
principle. 5 However, this is not the case over ℤ. Actually,
*positivstellensatz* refutations are not even sufficient to decide
linear *integer* arithmetic. The canonical example is 2 * x = 1 ->
False which is a theorem of ℤ but not a theorem of ℝ. To remedy this
weakness, the lia tactic is using recursively a combination of:


+ linear *positivstellensatz* refutations;
+ cutting plane proofs;
+ case split.



Cutting plane proofs
++++++++++++++++++++

are a way to take into account the discreetness of ℤ by rounding up
(rational) constants up-to the closest integer.
Theorem 2 * Let *p * be an integer and *c * a rational constant.* p ≥
c ⇒ p ≥ ⌈ c ⌉ **
For instance, from 2 x = 1 we can deduce


+ x ≥ 1/2 which cut plane is x ≥ ⌈ 1/2 ⌉ = 1;
+ x ≤ 1/2 which cut plane is x ≤ ⌊ 1/2 ⌋ = 0.


By combining these two facts (in normal form) x − 1 ≥ 0 and −x ≥ 0, we
conclude by exhibiting a *positivstellensatz* refutation: −1 ≡ x−1 +
−x ∈ Cone({x−1,x}).

Cutting plane proofs and linear *positivstellensatz* refutations are a
complete proof principle for integer linear arithmetic.


Case split
++++++++++

enumerates over the possible values of an expression.
Theorem 3 * Let *p * be an integer and *c 1 * and *c 2 * integer
constants.* c 1 ≤ p ≤ c 2 ⇒ ∨ x ∈ [c 1 ,c 2 ] p = x **
Our current oracle tries to find an expression e with a small range [c
1 ,c 2 ]. We generate c 2 − c 1 subgoals which contexts are enriched
with an equation e = i for i ∈ [c 1 ,c 2 ] and recursively search for
a proof.


22.5 nra: a proof procedure for non-linear arithmetic
-----------------------------------------------------

The nra tactic is an *e*xperimental proof procedure for non-linear
arithmetic. The tactic performs a limited amount of non-linear
reasoning before running the linear prover of lra. This pre-processing
does the following:


+ If the context contains an arithmetic expression of the form e[x 2 ]
  where x is a monomial, the context is enriched with x 2 ≥ 0;
+ For all pairs of hypotheses e 1 ≥ 0, e 2 ≥ 0, the context is
  enriched with e 1 × e 2 ≥ 0.


After this pre-processing, the linear prover of lra searches for a
proof by abstracting monomials by variables.


22.6 nia: a proof procedure for non-linear integer arithmetic
-------------------------------------------------------------

The nia tactic is a proof procedure for non-linear integer arithmetic.
It performs a pre-processing similar to nra. The obtained goal is
solved using the linear integer prover lia.


22.7 psatz: a proof procedure for non-linear arithmetic
-------------------------------------------------------

The psatz tactic explores the Cone by increasing degrees – hence the
depth parameter n. In theory, such a proof search is complete – if the
goal is provable the search eventually stops. Unfortunately, the
external oracle is using numeric (approximate) optimization techniques
that might miss a refutation.

To illustrate the working of the tactic, consider we wish to prove the
following Coq goal.
Coq < Goal forall x, -x^2 >= 0 -> x - 1 >= 0 -> False.

Such a goal is solved by intro x; psatz Z 2. The oracle returns the
cone expression 2 × (x−1) + (x−1) × (x−1) + −x 2 (polynomial
hypotheses are printed in bold). By construction, this expression
belongs to Cone({−x 2 ,x −1}). Moreover, by running ring we obtain −1.
By Theorem 1, the goal is valid.



:1: Support for nat and N is obtained by pre-processing the goal with
  the zify tactic.
:2: Sources and binaries can be found at`https://projects.coin-
  or.org/Csdp`_
:3: Variants deal with equalities and strict inequalities.
:4: More efficient linear programming techniques could equally be
  employed.
:5: In practice, the oracle might fail to produce such a refutation.




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
.. _22.1  Short description of the tactics: :///home/steck/micromega.html#sec803
.. _About Coq: :///about-coq
.. _: a decision procedure for linear real and rational arithmetic: :///home/steck/micromega.html#sec805
.. _ refutations: :///home/steck/micromega.html#sec804
.. _https://projects.coin-or.org/Csdp: https://projects.coin-or.org/Csdp
.. _: a tactic for linear integer arithmetic: :///home/steck/micromega.html#sec806
.. _Cover: :///home/steck/index.html
.. _Errors: :///home/steck/error-index.html
.. _Table of contents: :///home/steck/toc.html
.. _Community: :///community
.. _21: :///home/steck/omega.html#OmegaChapter
.. _Commands: :///home/steck/command-index.html
.. _130: :///home/steck/biblio.html#TheOmegaPaper
.. _: a proof procedure for non-linear arithmetic: :///home/steck/micromega.html#sec812
.. _: a proof procedure for non-linear arithmetic: :///home/steck/micromega.html#sec810
.. _: a proof procedure for non-linear integer arithmetic: :///home/steck/micromega.html#sec811
.. _CSS valid: http://jigsaw.w3.org/css-validator/
.. _xhtml valid: http://validator.w3.org/
.. _Tactics: :///home/steck/tactic-index.html
.. _General: :///home/steck/general-index.html
.. _Options: :///home/steck/option-index.html
.. _The Coq Proof Assistant: :///
.. _25: :///home/steck/ring.html#ring
.. _Documentation: :///documentation
.. _webmaster: mailto:coq-www_@_inria.fr



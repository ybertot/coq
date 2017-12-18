

+ `Home`_
+ `About Coq`_
+ `Get Coq`_
+ `Documentation`_
+ `Community`_

` `_ `The Coq Proof Assistant`_


Chapter 21 Omega: a solver of quantifier-free problems in Presburger
Arithmetic
==========


+ `21.1 Description of omega`_
+ `21.2 Using omega`_
+ `21.3 Technical data`_
+ `21.4 Bugs`_


Pierre Crégut




21.1 Description of omega
-------------------------



omega solves a goal in Presburger arithmetic, i.e. a universally
quantified formula made of equations and inequations. Equations may be
specified either on the type `nat` of natural numbers or on the type
`Z` of binary-encoded integer numbers. Formulas on `nat` are
automatically injected into `Z`. The procedure may use any hypothesis
of the current proof session to solve the goal.

Multiplication is handled by omega but only goals where at least one
of the two multiplicands of products is a constant are solvable. This
is the restriction meant by “Presburger arithmetic”.

If the tactic cannot solve the goal, it fails with an error message.
In any case, the computation eventually stops.


21.1.1 Arithmetical goals recognized by omega
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

omega applied only to quantifier-free formulas built from the
connectors
`/\, \/, ~, ->`
on atomic formulas. Atomic formulas are built from the predicates
`=, le, lt, gt, ge`
on `nat` or from the predicates
`=, <, <=, >, >=`
on `Z`. In expressions of type `nat`, omega recognizes
`plus, minus, mult, pred, S, O`
and in expressions of type `Z`, omega recognizes
`+, -, *, Z.succ`, and constants.
All expressions of type `nat` or `Z` not built on these operators are
considered abstractly as if they were arbitrary variables of type
`nat` or `Z`.


21.1.2 Messages from omega
~~~~~~~~~~~~~~~~~~~~~~~~~~



When omega does not solve the goal, one of the following errors is
generated:


Error messages:


#. omega can’t solve this systemThis may happen if your goal is not
   quantifier-free (if it is universally quantified, try intros first; if
   it contains existentials quantifiers too, omega is not strong enough
   to solve your goal). This may happen also if your goal contains
   arithmetical operators unknown from omega. Finally, your goal may be
   really wrong!
#. omega: Not a quantifier-free goalIf your goal is universally
   quantified, you should first apply intro as many time as needed.
#. omega: Unrecognized predicate or connective: ident
#. omega: Unrecognized atomic proposition: prop
#. omega: Can’t solve a goal with proposition variables
#. omega: Unrecognized proposition
#. omega: Can’t solve a goal with non-linear products
#. omega: Can’t solve a goal with equality on type



21.2 Using omega
----------------

The omega tactic does not belong to the core system. It should be
loaded by
Coq < Require Import Omega.

Coq < Open Scope Z_scope.


Example 3:
Coq < Goal forall m n:Z, 1 + 2 * m <> 2 * n.
1 subgoal

============================
forall m n : Z, 1 + 2 * m <> 2 * n

Coq < intros; omega.
No more subgoals.


Example 4:
Coq < Goal forall z:Z, z > 0 -> 2 * z + 1 > z.
1 subgoal

============================
forall z : Z, z > 0 -> 2 * z + 1 > z

Coq < intro; omega.
No more subgoals.



21.3 Technical data
-------------------




21.3.1 Overview of the tactic
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


+ The goal is negated twice and the first negation is introduced as an
  hypothesis.
+ Hypothesis are decomposed in simple equations or inequations.
  Multiple goals may result from this phase.
+ Equations and inequations over `nat` are translated over `Z`,
  multiple goals may result from the translation of substraction.
+ Equations and inequations are normalized.
+ Goals are solved by the OMEGA decision procedure.
+ The script of the solution is replayed.



21.3.2 Overview of the OMEGA decision procedure
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The OMEGA decision procedure involved in the omega tactic uses a small
subset of the decision procedure presented in
"The Omega Test: a fast and practical integer programming algorithm
for dependence analysis", William Pugh, Communication of the ACM ,
1992, p 102-114.
Here is an overview, look at the original paper for more information.


+ Equations and inequations are normalized by division by the GCD of
  their coefficients.
+ Equations are eliminated, using the Banerjee test to get a
  coefficient equal to one.
+ Note that each inequation defines a half space in the space of real
  value of the variables.
+ Inequations are solved by projecting on the hyperspace defined by
  cancelling one of the variable. They are partitioned according to the
  sign of the coefficient of the eliminated variable. Pairs of
  inequations from different classes define a new edge in the
  projection.
+ Redundant inequations are eliminated or merged in new equations that
  can be eliminated by the Banerjee test.
+ The last two steps are iterated until a contradiction is reached
  (success) or there is no more variable to eliminate (failure).


It may happen that there is a real solution and no integer one. The
last steps of the Omega procedure (dark shadow) are not implemented,
so the decision procedure is only partial.


21.4 Bugs
---------


+ The simplification procedure is very dumb and this results in many
  redundant cases to explore.
+ Much too slow.
+ Certainly other bugs! You can report them to
  `https://coq.inria.fr/bugs/`_.




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
.. _Options: :///home/steck/option-index.html
.. _Tactics: :///home/steck/tactic-index.html
.. _About Coq: :///about-coq
.. _Cover: :///home/steck/index.html
.. _CSS valid: http://jigsaw.w3.org/css-validator/
.. _The Coq Proof Assistant: :///
.. _Errors: :///home/steck/error-index.html
.. _General: :///home/steck/general-index.html
.. _21.3  Technical data: :///home/steck/omega.html#sec798
.. _21.4  Bugs: :///home/steck/omega.html#sec801
.. _https://coq.inria.fr/bugs/: https://coq.inria.fr/bugs/
.. _Documentation: :///documentation
.. _xhtml valid: http://validator.w3.org/
.. _Table of contents: :///home/steck/toc.html
.. _Community: :///community
.. _webmaster: mailto:coq-www_@_inria.fr
.. _omega: :///home/steck/omega.html#sec797
.. _omega: :///home/steck/omega.html#sec794



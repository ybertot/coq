

+ `Home`_
+ `About Coq`_
+ `Get Coq`_
+ `Documentation`_
+ `Community`_

` `_ `The Coq Proof Assistant`_


Chapter 10 Detailed examples of tactics
=======================================


+ `10.1 dependent induction`_
+ `10.2 autorewrite`_
+ `10.3 quote`_
+ `10.4 Using the tactical language`_


This chapter presents detailed examples of certain tactics, to
illustrate their behavior.


10.1 dependent induction
------------------------

The tactics dependent induction and dependent destruction are another
solution for inverting inductive predicate instances and potentially
doing induction at the same time. It is based on the BasicElim tactic
of Conor McBride which works by abstracting each argument of an
inductive instance by a variable and constraining it by equalities
afterwards. This way, the usual induction and destruct tactics can be
applied to the abstracted instance and after simplification of the
equalities we get the expected goals.

The abstracting tactic is called generalize_eqs and it takes as
argument an hypothesis to generalize. It uses the JMeq datatype
defined in Coq.Logic.JMeq, hence we need to require it before. For
example, revisiting the first example of the inversion documentation
above:
Coq < Require Import Coq.Logic.JMeq.
Coq < Goal forall n m:nat, Le (S n) m -> P n m.

Coq < intros n m H.

Coq < generalize_eqs H.
1 subgoal

n, m, gen_x : nat
H : Le gen_x m
============================
gen_x = S n -> P n m

The index S n gets abstracted by a variable here, but a corresponding
equality is added under the abstract instance so that no information
is actually lost. The goal is now almost amenable to do induction or
case analysis. One should indeed first move n into the goal to
strengthen it before doing induction, or n will be fixed in the
inductive hypotheses (this does not matter for case analysis). As a
rule of thumb, all the variables that appear inside constructors in
the indices of the hypothesis should be generalized. This is exactly
what the generalize_eqs_vars variant does:
Coq < generalize_eqs_vars H.
1 subgoal

m, gen_x : nat
H : Le gen_x m
============================
forall n : nat, gen_x = S n -> P n m

Coq < induction H.
2 subgoals

n : nat
============================
forall n0 : nat, 0 = S n0 -> P n0 n
subgoal 2 is:
forall n0 : nat, S n = S n0 -> P n0 (S m)

As the hypothesis itself did not appear in the goal, we did not need
to use an heterogeneous equality to relate the new hypothesis to the
old one (which just disappeared here). However, the tactic works just
as well in this case, e.g.:
Coq < Goal forall n m (p : Le (S n) m), Q (S n) m p.
1 subgoal

============================
forall (n m : nat) (p : Le (S n) m), Q (S n) m p

Coq < intros n m p ; generalize_eqs_vars p.
1 subgoal

m, gen_x : nat
p : Le gen_x m
============================
forall (n : nat) (p0 : Le (S n) m),
gen_x = S n -> p ~= p0 -> Q (S n) m p0

One drawback of this approach is that in the branches one will have to
substitute the equalities back into the instance to get the right
assumptions. Sometimes injection of constructors will also be needed
to recover the needed equalities. Also, some subgoals should be
directly solved because of inconsistent contexts arising from the
constraints on indexes. The nice thing is that we can make a tactic
based on discriminate, injection and variants of substitution to
automatically do such simplifications (which may involve the K axiom).
This is what the simplify_dep_elim tactic fromCoq.Program.Equality
does. For example, we might simplify the previous goals considerably:
Coq < induction p ; simplify_dep_elim.
1 subgoal

n, m : nat
p : Le n m
IHp : forall (n0 : nat) (p0 : Le (S n0) m),
n = S n0 -> p ~= p0 -> Q (S n0) m p0
============================
Q (S n) (S m) (LeS n m p)

The higher-order tactic do_depind defined in Coq.Program.Equality
takes a tactic and combines the building blocks we have seen with it:
generalizing by equalities calling the given tactic with the
generalized induction hypothesis as argument and cleaning the subgoals
with respect to equalities. Its most important instantiations
aredependent induction and dependent destruction that do induction or
simply case analysis on the generalized hypothesis. For example we can
redo what we’ve done manually with dependent destruction :
Coq < Require Import Coq.Program.Equality.

Coq < Lemma ex : forall n m:nat, Le (S n) m -> P n m.

Coq < intros n m H.

Coq < dependent destruction H.
1 subgoal

n, m : nat
H : Le n m
============================
P n (S m)

This gives essentially the same result as inversion. Now if the
destructed hypothesis actually appeared in the goal, the tactic would
still be able to invert it, contrary to dependent inversion. Consider
the following example on vectors:
Coq < Require Import Coq.Program.Equality.

Coq < Set Implicit Arguments.

Coq < Variable A : Set.

Coq < Inductive vector : nat -> Type :=
| vnil : vector 0
| vcons : A -> forall n, vector n -> vector (S n).

Coq < Goal forall n, forall v : vector (S n),
exists v' : vector n, exists a : A, v = vcons a v'.

Coq < intros n v.

Coq < dependent destruction v.
1 subgoal

n : nat
a : A
v : vector n
============================
exists (v' : vector n) (a0 : A), vcons a v = vcons a0 v'

In this case, the v variable can be replaced in the goal by the
generalized hypothesis only when it has a type of the form vector (S
n), that is only in the second case of the destruct. The first one is
dismissed because S n <> 0.


10.1.1 A larger example
~~~~~~~~~~~~~~~~~~~~~~~

Let’s see how the technique works with induction on inductive
predicates on a real example. We will develop an example application
to the theory of simply-typed lambda-calculus formalized in a
dependently-typed style:
Coq < Inductive type : Type :=
| base : type
| arrow : type -> type -> type.

Coq < Notation " t --> t' " := (arrow t t') (at level 20, t' at next
level).

Coq < Inductive ctx : Type :=
| empty : ctx
| snoc : ctx -> type -> ctx.

Coq < Notation " G , tau " := (snoc G tau) (at level 20, tau at next
level).

Coq < Fixpoint conc (G D : ctx) : ctx :=
match D with
| empty => G
| snoc D' x => snoc (conc G D') x
end.

Coq < Notation " G ; D " := (conc G D) (at level 20).

Coq < Inductive term : ctx -> type -> Type :=
| ax : forall G tau, term (G, tau) tau
| weak : forall G tau,
term G tau -> forall tau', term (G, tau') tau
| abs : forall G tau tau',
term (G , tau) tau' -> term G (tau --> tau')
| app : forall G tau tau',
term G (tau --> tau') -> term G tau -> term G tau'.

We have defined types and contexts which are snoc-lists of types. We
also have a conc operation that concatenates two contexts. The term
datatype represents in fact the possible typing derivations of the
calculus, which are isomorphic to the well-typed terms, hence the
name. A term is either an application of:


+ the axiom rule to type a reference to the first variable in a
  context,
+ the weakening rule to type an object in a larger context
+ the abstraction or lambda rule to type a function
+ the application to type an application of a function to an argument


Once we have this datatype we want to do proofs on it, like weakening:
Coq < Lemma weakening : forall G D tau, term (G ; D) tau ->
forall tau', term (G , tau' ; D) tau.

The problem here is that we can’t just use induction on the typing
derivation because it will forget about the G ; D constraint appearing
in the instance. A solution would be to rewrite the goal as:
Coq < Lemma weakening' : forall G' tau, term G' tau ->
forall G D, (G ; D) = G' ->
forall tau', term (G, tau' ; D) tau.

With this proper separation of the index from the instance and the
right induction loading (putting G and D after the inducted-on
hypothesis), the proof will go through, but it is a very tedious
process. One is also forced to make a wrapper lemma to get back the
more natural statement. The dependent induction tactic alleviates this
trouble by doing all of this plumbing of generalizing and substituting
back automatically. Indeed we can simply write:
Coq < Require Import Coq.Program.Tactics.

Coq < Lemma weakening : forall G D tau, term (G ; D) tau ->
forall tau', term (G , tau' ; D) tau.

Coq < Proof with simpl in * ; simpl_depind ; auto.

Coq < intros G D tau H. dependent induction H generalizing G D ;
intros.

This call to dependent induction has an additional arguments which is
a list of variables appearing in the instance that should be
generalized in the goal, so that they can vary in the induction
hypotheses. By default, all variables appearing inside constructors
(except in a parameter position) of the instantiated hypothesis will
be generalized automatically but one can always give the list
explicitly.
Coq < Show.
4 subgoals

G0 : ctx
tau : type
G, D : ctx
x : G0, tau = G; D
tau' : type
============================
term ((G, tau'); D) tau
subgoal 2 is:
term ((G, tau'0); D) tau
subgoal 3 is:
term ((G, tau'0); D) (tau –> tau')
subgoal 4 is:
term ((G, tau'0); D) tau'

The simpl_depind tactic includes an automatic tactic that tries to
simplify equalities appearing at the beginning of induction
hypotheses, generally using trivial applications of reflexivity. In
cases where the equality is not between constructor forms though, one
must help the automation by giving some arguments, using the
specialize tactic for example.
Coq < destruct D... apply weak ; apply ax. apply ax.

Coq < destruct D...

Coq < Show.
4 subgoals

G0 : ctx
tau : type
H : term G0 tau
tau' : type
IHterm : forall G D : ctx,
G0 = G; D -> forall tau' : type, term ((G, tau'); D) tau
tau'0 : type
============================
term ((G0, tau'), tau'0) tau
subgoal 2 is:
term (((G, tau'0); D), t) tau
subgoal 3 is:
term ((G, tau'0); D) (tau –> tau')
subgoal 4 is:
term ((G, tau'0); D) tau'

Coq < specialize (IHterm G0 empty eq_refl).
4 subgoals

G0 : ctx
tau : type
H : term G0 tau
tau' : type
IHterm : forall tau' : type, term ((G0, tau'); empty) tau
tau'0 : type
============================
term ((G0, tau'), tau'0) tau
subgoal 2 is:
term (((G, tau'0); D), t) tau
subgoal 3 is:
term ((G, tau'0); D) (tau –> tau')
subgoal 4 is:
term ((G, tau'0); D) tau'

Once the induction hypothesis has been narrowed to the right equality,
it can be used directly.
Coq < apply weak, IHterm.
3 subgoals

tau : type
G, D : ctx
IHterm : forall G0 D0 : ctx,
G; D = G0; D0 ->
forall tau' : type, term ((G0, tau'); D0) tau
H : term (G; D) tau
t, tau'0 : type
============================
term (((G, tau'0); D), t) tau
subgoal 2 is:
term ((G, tau'0); D) (tau –> tau')
subgoal 3 is:
term ((G, tau'0); D) tau'

If there is an easy first-order solution to these equations as in this
subgoal, thespecialize_eqs tactic can be used instead of giving
explicit proof terms:
Coq < specialize_eqs IHterm.
Toplevel input, characters 2-23:
> specialize_eqs IHterm.
> ^^^^^^^^^^^^^^^^^^^^^
Error:
Ltac call to "specialize_eqs (var)" failed.
Specialization not allowed on dependent hypotheses

This concludes our example.
See also: The induction `9`_, case `9`_ and inversion `8.14`_ tactics.


10.2 autorewrite
----------------

Here are two examples of autorewrite use. The first one ( *Ackermann
function*) shows actually a quite basic use where there is no
conditional rewriting. The second one ( *Mac Carthy function*)
involves conditional rewritings and shows how to deal with them using
the optional tactic of theHint Rewrite command.


Example 1: Ackermann function
Coq < Reset Initial.

Coq < Require Import Arith.

Coq < Variable Ack :
nat -> nat -> nat.

Coq < Axiom Ack0 :
forall m:nat, Ack 0 m = S m.

Coq < Axiom Ack1 : forall n:nat, Ack (S n) 0 = Ack n 1.

Coq < Axiom Ack2 : forall n m:nat, Ack (S n) (S m) = Ack n (Ack (S n)
m).
Coq < Hint Rewrite Ack0 Ack1 Ack2 : base0.

Coq < Lemma ResAck0 :
Ack 3 2 = 29.
1 subgoal

============================
Ack 3 2 = 29

Coq < autorewrite with base0 using try reflexivity.
No more subgoals.


Example 2: Mac Carthy function
Coq < Require Import Omega.

Coq < Variable g :
nat -> nat -> nat.

Coq < Axiom g0 :
forall m:nat, g 0 m = m.

Coq < Axiom
g1 :
forall n m:nat,
(n > 0) -> (m > 100) -> g n m = g (pred n) (m - 10).

Coq < Axiom
g2 :
forall n m:nat,
(n > 0) -> (m <= 100) -> g n m = g (S n) (m + 11).
Coq < Hint Rewrite g0 g1 g2 using omega : base1.

Coq < Lemma Resg0 :
g 1 110 = 100.
1 subgoal

============================
g 1 110 = 100

Coq < autorewrite with base1 using reflexivity || simpl.
No more subgoals.
Coq < Lemma Resg1 : g 1 95 = 91.
1 subgoal

============================
g 1 95 = 91

Coq < autorewrite with base1 using reflexivity || simpl.
No more subgoals.



10.3 quote
----------

The tactic quote allows using Barendregt’s so-called 2-level approach
without writing any ML code. Suppose you have a language L of
’abstract terms’ and a type A of ’concrete terms’ and a function f : L
-> A. If L is a simple inductive datatype and f a simple fixpoint,
quote f will replace the head of current goal by a convertible term of
the form (f t). L must have a constructor of type: A -> L.

Here is an example:
Coq < Require Import Quote.

Coq < Parameters A B C : Prop.
A is declared
B is declared
C is declared

Coq < Inductive formula : Type :=
| f_and : formula -> formula -> formula (* binary constructor *)
| f_or : formula -> formula -> formula
| f_not : formula -> formula (* unary constructor *)
| f_true : formula (* 0-ary constructor *)
| f_const : Prop -> formula (* constructor for constants *).
formula is defined
formula_rect is defined
formula_ind is defined
formula_rec is defined

Coq < Fixpoint interp_f (f:
formula) : Prop :=
match f with
| f_and f1 f2 => interp_f f1 /\ interp_f f2
| f_or f1 f2 => interp_f f1 \/ interp_f f2
| f_not f1 => ~ interp_f f1
| f_true => True
| f_const c => c
end.
interp_f is defined
interp_f is recursively defined (decreasing on 1st argument)

Coq < Goal A /\ (A \/ True) /\ ~ B /\ (A <-> A).
1 subgoal

============================
A /\ (A \/ True) /\ ~ B /\ (A <-> A)

Coq < quote interp_f.
1 subgoal

============================
interp_f
(f_and (f_const A)
(f_and (f_or (f_const A) f_true)
(f_and (f_not (f_const B)) (f_const (A <-> A)))))

The algorithm to perform this inversion is: try to match the term with
right-hand sides expression of f. If there is a match, apply the
corresponding left-hand side and call yourself recursively on sub-
terms. If there is no match, we are at a leaf: return the
corresponding constructor (here f_const) applied to the term.


Error messages:


#. quote: not a simple fixpoint Happens when quote is not able to
   perform inversion properly.



10.3.1 Introducing variables map
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The normal use of quote is to make proofs by reflection: one defines a
function simplify : formula -> formula and proves a theorem
simplify_ok: (f:formula)(interp_f (simplify f)) -> (interp_f f). Then,
one can simplify formulas by doing:

::

       quote interp_f.
       apply simplify_ok.
       compute.


But there is a problem with leafs: in the example above one cannot
write a function that implements, for example, the logical
simplifications A ∧ A → A or A ∧ ¬ A → False. This is because the Prop
is impredicative.

It is better to use that type of formulas:
Coq < Inductive formula : Set :=
| f_and : formula -> formula -> formula
| f_or : formula -> formula -> formula
| f_not : formula -> formula
| f_true : formula
| f_atom : index -> formula.
formula is defined
formula_rect is defined
formula_ind is defined
formula_rec is defined

index is defined in module quote. Equality on that type is decidable
so we are able to simplify A ∧ A into A at the abstract level.

When there are variables, there are bindings, and quote provides also
a type (varmap A) of bindings fromindex to any set A, and a
functionvarmap_find to search in such maps. The interpretation
function has now another argument, a variables map:
Coq < Fixpoint interp_f (vm:
varmap Prop) (f:formula) {struct f} : Prop :=
match f with
| f_and f1 f2 => interp_f vm f1 /\ interp_f vm f2
| f_or f1 f2 => interp_f vm f1 \/ interp_f vm f2
| f_not f1 => ~ interp_f vm f1
| f_true => True
| f_atom i => varmap_find True i vm
end.
interp_f is defined
interp_f is recursively defined (decreasing on 2nd argument)

quote handles this second case properly:
Coq < Goal A /\ (B \/ A) /\ (A \/ ~ B).
1 subgoal

============================
A /\ (B \/ A) /\ (A \/ ~ B)

Coq < quote interp_f.
1 subgoal

============================
interp_f
(Node_vm B (Node_vm A (Empty_vm Prop) (Empty_vm Prop)) (Empty_vm
Prop))
(f_and (f_atom (Left_idx End_idx))
(f_and (f_or (f_atom End_idx) (f_atom (Left_idx End_idx)))
(f_or (f_atom (Left_idx End_idx)) (f_not (f_atom End_idx)))))

It builds vm and t such that (f vm t) is convertible with the
conclusion of current goal.


10.3.2 Combining variables and constants
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

One can have both variables and constants in abstracts terms; that is
the case, for example, for the ring tactic (chapter`25`_). Then one
must provide to quote a list of *constructors of constants*. For
example, if the list is[O S] then closed natural numbers will be
considered as constants and other terms as variables.

Example:
Coq < Inductive formula : Type :=
| f_and : formula -> formula -> formula
| f_or : formula -> formula -> formula
| f_not : formula -> formula
| f_true : formula
| f_const : Prop -> formula (* constructor for constants *)
| f_atom : index -> formula.

Coq < Fixpoint interp_f
(vm: (* constructor for variables *)
varmap Prop) (f:formula) {struct f} : Prop :=
match f with
| f_and f1 f2 => interp_f vm f1 /\ interp_f vm f2
| f_or f1 f2 => interp_f vm f1 \/ interp_f vm f2
| f_not f1 => ~ interp_f vm f1
| f_true => True
| f_const c => c
| f_atom i => varmap_find True i vm
end.

Coq < Goal
A /\ (A \/ True) /\ ~ B /\ (C <-> C).
Coq < quote interp_f [ A B ].
1 subgoal

============================
interp_f (Node_vm (C <-> C) (Empty_vm Prop) (Empty_vm Prop))
(f_and (f_const A)
(f_and (f_or (f_const A) f_true)
(f_and (f_not (f_const B)) (f_atom End_idx))))

Coq < Undo.
1 subgoal

============================
A /\ (A \/ True) /\ ~ B /\ (C <-> C)

Coq < quote interp_f [ B C iff ].
1 subgoal

============================
interp_f (Node_vm A (Empty_vm Prop) (Empty_vm Prop))
(f_and (f_atom End_idx)
(f_and (f_or (f_atom End_idx) f_true)
(f_and (f_not (f_const B)) (f_const (C <-> C)))))


Warning: Since function inversion is undecidable in general case,
don’t expect miracles from it!


Variants:


#. quote ident in term using tactictactic must be a functional tactic
   (starting with fun x =>) and will be called with the quoted version of
   term according toident.
#. quote ident [ ident 1 … ident n ] in term using tacticSame as
   above, but will use ident 1 , …, ident n to chose which subterms are
   constants (see above).



See also: comments of source file plugins/quote/quote.ml


See also: the ring tactic (Chapter `25`_)


10.4 Using the tactical language
--------------------------------


10.4.1 About the cardinality of the set of natural numbers
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

A first example which shows how to use the pattern matching over the
proof contexts is the proof that natural numbers have more than two
elements. The proof of such a lemma can be done as follows:
Coq < Lemma card_nat :
~ (exists x : nat, exists y : nat, forall z:nat, x = z \/ y = z).

Coq < Proof.

Coq < red; intros (x, (y, Hy)).

Coq < elim (Hy 0); elim (Hy 1); elim (Hy 2); intros;
match goal with
| [_:(?a = ?b),_:(?a = ?c) |- _ ] =>
cut (b = c); [ discriminate | transitivity a; auto ]
end.

Coq < Qed.

We can notice that all the (very similar) cases coming from the three
eliminations (with three distinct natural numbers) are successfully
solved by a match goal structure and, in particular, with only one
pattern (use of non-linear matching).


10.4.2 Permutation on closed lists
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Another more complex example is the problem of permutation on closed
lists. The aim is to show that a closed list is a permutation of
another one.

First, we define the permutation predicate as shown in table 10.1.



Coq < Section Sort.

Coq < Variable A : Set.

Coq < Inductive permut : list A -> list A -> Prop :=
| permut_refl : forall l, permut l l
| permut_cons :
forall a l0 l1, permut l0 l1 -> permut (a :: l0) (a :: l1)
| permut_append : forall a l, permut (a :: l) (l ++ a :: nil)
| permut_trans :
forall l0 l1 l2, permut l0 l1 -> permut l1 l2 -> permut l0 l2.

Coq < End Sort.
Figure 10.1: Definition of the permutation predicate



A more complex example is the problem of permutation on closed lists.
The aim is to show that a closed list is a permutation of another one.
First, we define the permutation predicate as shown on Figure 10.1.



Coq < Ltac Permut n :=
match goal with
| |- (permut _ ?l ?l) => apply permut_refl
| |- (permut _ (?a :: ?l1) (?a :: ?l2)) =>
let newn := eval compute in (length l1) in
(apply permut_cons; Permut newn)
| |- (permut ?A (?a :: ?l1) ?l2) =>
match eval compute in n with
| 1 => fail
| _ =>
let l1' := constr:(l1 ++ a :: nil) in
(apply (permut_trans A (a :: l1) l1' l2);
[ apply permut_append | compute; Permut (pred n) ])
end
end.
Permut is defined

Coq < Ltac PermutProve :=
match goal with
| |- (permut _ ?l1 ?l2) =>
match eval compute in (length l1 = length l2) with
| (?n = ?n) => Permut n
end
end.
PermutProve is defined
Figure 10.2: Permutation tactic



Next, we can write naturally the tactic and the result can be seen on
Figure 10.2. We can notice that we use two toplevel definitions
PermutProve and Permut. The function to be called is PermutProve which
computes the lengths of the two lists and calls Permut with the length
if the two lists have the same length. Permut works as expected. If
the two lists are equal, it concludes. Otherwise, if the lists have
identical first elements, it applies Permut on the tail of the lists.
Finally, if the lists have different first elements, it puts the first
element of one of the lists (here the second one which appears in the
permut predicate) at the end if that is possible, i.e., if the new
first element has been at this place previously. To verify that all
rotations have been done for a list, we use the length of the list as
an argument for Permut and this length is decremented for each
rotation down to, but not including, 1 because for a list of lengthn,
we can make exactly n−1 rotations to generate at most n distinct
lists. Here, it must be noticed that we use the natural numbers of Coq
for the rotation counter. On Figure `9.1`_, we can see that it is
possible to use usual natural numbers but they are only used as
arguments for primitive tactics and they cannot be handled, in
particular, we cannot make computations with them. So, a natural
choice is to use Coq data structures so that Coq makes the
computations (reductions) by eval compute in and we can get the terms
back by match.

With PermutProve, we can now prove lemmas as follows:
Coq < Lemma permut_ex1 :
permut nat (1 :: 2 :: 3 :: nil) (3 :: 2 :: 1 :: nil).

Coq < Proof. PermutProve. Qed.

Coq < Lemma permut_ex2 :
permut nat
(0 :: 1 :: 2 :: 3 :: 4 :: 5 :: 6 :: 7 :: 8 :: 9 :: nil)
(0 :: 2 :: 4 :: 6 :: 8 :: 9 :: 7 :: 5 :: 3 :: 1 :: nil).

Coq < Proof. PermutProve. Qed.



10.4.3 Deciding intuitionistic propositional logic
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~



Coq < Ltac Axioms :=
match goal with
| |- True => trivial
| _:False |- _ => elimtype False; assumption
| _:?A |- ?A => auto
end.
Axioms is defined
Figure 10.3: Deciding intuitionistic propositions (1)





Coq < Ltac DSimplif :=
repeat
(intros;
match goal with
| id:(~ _) |- _ => red in id
| id:(_ /\ _) |- _ =>
elim id; do 2 intro; clear id
| id:(_ \/ _) |- _ =>
elim id; intro; clear id
| id:(?A /\ ?B -> ?C) |- _ =>
cut (A -> B -> C);
[ intro | intros; apply id; split; assumption ]
| id:(?A \/ ?B -> ?C) |- _ =>
cut (B -> C);
[ cut (A -> C);
[ intros; clear id
| intro; apply id; left; assumption ]
| intro; apply id; right; assumption ]
| id0:(?A -> ?B),id1:?A |- _ =>
cut B; [ intro; clear id0 | apply id0; assumption ]
| |- (_ /\ _) => split
| |- (~ _) => red
end).
DSimplif is defined

Coq < Ltac TautoProp :=
DSimplif;
Axioms ||
match goal with
| id:((?A -> ?B) -> ?C) |- _ =>
cut (B -> C);
[ intro; cut (A -> B);
[ intro; cut C;
[ intro; clear id | apply id; assumption ]
| clear id ]
| intro; apply id; intro; assumption ]; TautoProp
| id:(~ ?A -> ?B) |- _ =>
cut (False -> B);
[ intro; cut (A -> False);
[ intro; cut B;
[ intro; clear id | apply id; assumption ]
| clear id ]
| intro; apply id; red; intro; assumption ]; TautoProp
| |- (_ \/ _) => (left; TautoProp) || (right; TautoProp)
end.
TautoProp is defined
Figure 10.4: Deciding intuitionistic propositions (2)



The pattern matching on goals allows a complete and so a powerful
backtracking when returning tactic values. An interesting application
is the problem of deciding intuitionistic propositional logic.
Considering the contraction-free sequent calculi LJT* of Roy Dyckhoff
([`56`_]), it is quite natural to code such a tactic using the tactic
language as shown on Figures 10.3 and 10.4. The tactic Axioms tries to
conclude using usual axioms. The tactic DSimplif applies all the
reversible rules of Dyckhoff’s system. Finally, the tactic TautoProp
(the main tactic to be called) simplifies with DSimplif, tries to
conclude with Axioms and tries several paths using the backtracking
rules (one of the four Dyckhoff’s rules for the left implication to
get rid of the contraction and the right or).

For example, with TautoProp, we can prove tautologies like those:
Coq < Lemma tauto_ex1 : forall A B:Prop, A /\ B -> A \/ B.

Coq < Proof. TautoProp. Qed.

Coq < Lemma tauto_ex2 :
forall A B:Prop, (~ ~ B -> B) -> (A -> B) -> ~ ~ A -> B.

Coq < Proof. TautoProp. Qed.



10.4.4 Deciding type isomorphisms
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

A more tricky problem is to decide equalities between types and modulo
isomorphisms. Here, we choose to use the isomorphisms of the simply
typed λ-calculus with Cartesian product and unit type (see, for
example, [`45`_]). The axioms of this λ-calculus are given by table
10.5.



Coq < Open Scope type_scope.

Coq < Section Iso_axioms.

Coq < Variables A B C : Set.

Coq < Axiom Com : A * B = B * A.

Coq < Axiom Ass : A * (B * C) = A * B * C.

Coq < Axiom Cur : (A * B -> C) = (A -> B -> C).

Coq < Axiom Dis : (A -> B * C) = (A -> B) * (A -> C).

Coq < Axiom P_unit : A * unit = A.

Coq < Axiom AR_unit : (A -> unit) = unit.

Coq < Axiom AL_unit : (unit -> A) = A.

Coq < Lemma Cons : B = C -> A * B = A * C.

Coq < Proof.

Coq < intro Heq; rewrite Heq; reflexivity.

Coq < Qed.

Coq < End Iso_axioms.
Figure 10.5: Type isomorphism axioms



A more tricky problem is to decide equalities between types and modulo
isomorphisms. Here, we choose to use the isomorphisms of the simply
typed λ-calculus with Cartesian product and unit type (see, for
example, [`45`_]). The axioms of this λ-calculus are given on Figure
10.5.



Coq < Ltac DSimplif trm :=
match trm with
| (?A * ?B * ?C) =>
rewrite <- (Ass A B C); try MainSimplif
| (?A * ?B -> ?C) =>
rewrite (Cur A B C); try MainSimplif
| (?A -> ?B * ?C) =>
rewrite (Dis A B C); try MainSimplif
| (?A * unit) =>
rewrite (P_unit A); try MainSimplif
| (unit * ?B) =>
rewrite (Com unit B); try MainSimplif
| (?A -> unit) =>
rewrite (AR_unit A); try MainSimplif
| (unit -> ?B) =>
rewrite (AL_unit B); try MainSimplif
| (?A * ?B) =>
(DSimplif A; try MainSimplif) || (DSimplif B; try MainSimplif)
| (?A -> ?B) =>
(DSimplif A; try MainSimplif) || (DSimplif B; try MainSimplif)
end
with MainSimplif :=
match goal with
| |- (?A = ?B) => try DSimplif A; try DSimplif B
end.
DSimplif is defined
MainSimplif is defined

Coq < Ltac Length trm :=
match trm with
| (_ * ?B) => let succ := Length B in constr:(S succ)
| _ => constr:(1)
end.
Length is defined

Coq < Ltac assoc := repeat rewrite <- Ass.
assoc is defined
Figure 10.6: Type isomorphism tactic (1)





Coq < Ltac DoCompare n :=
match goal with
| [ |- (?A = ?A) ] => reflexivity
| [ |- (?A * ?B = ?A * ?C) ] =>
apply Cons; let newn := Length B in
DoCompare newn
| [ |- (?A * ?B = ?C) ] =>
match eval compute in n with
| 1 => fail
| _ =>
pattern (A * B) at 1; rewrite Com; assoc; DoCompare (pred n)
end
end.
DoCompare is defined

Coq < Ltac CompareStruct :=
match goal with
| [ |- (?A = ?B) ] =>
let l1 := Length A
with l2 := Length B in
match eval compute in (l1 = l2) with
| (?n = ?n) => DoCompare n
end
end.
CompareStruct is defined

Coq < Ltac IsoProve := MainSimplif; CompareStruct.
IsoProve is defined
Figure 10.7: Type isomorphism tactic (2)



The tactic to judge equalities modulo this axiomatization can be
written as shown on Figures 10.6 and 10.7. The algorithm is quite
simple. Types are reduced using axioms that can be oriented (this done
by MainSimplif). The normal forms are sequences of Cartesian products
without Cartesian product in the left component. These normal forms
are then compared modulo permutation of the components (this is done
by CompareStruct). The main tactic to be called and realizing this
algorithm isIsoProve.

Here are examples of what can be solved by IsoProve.
Coq < Lemma isos_ex1 :
forall A B:Set, A * unit * B = B * (unit * A).

Coq < Proof.

Coq < intros; IsoProve.

Coq < Qed.

Coq < Lemma isos_ex2 :
forall A B C:Set,
(A * unit -> B * (C * unit)) =
(A * unit -> (C -> unit) * C) * (unit -> A -> B).

Coq < Proof.

Coq < intros; IsoProve.

Coq < Qed.



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


.. _9: :///home/steck/tactics.html#case
.. _Get Coq: :///download
.. _About Coq: :///about-coq
.. _CSS valid: http://jigsaw.w3.org/css-validator/
.. _dependent induction: :///home/steck/tactic-examples.html#dependent-induction-example
.. _Cover: :///home/steck/index.html
.. _45: :///home/steck/biblio.html#RC95
.. _Table of contents: :///home/steck/toc.html
.. _Community: :///community
.. _Errors: :///home/steck/error-index.html
.. _Commands: :///home/steck/command-index.html
.. _quote: :///home/steck/tactic-examples.html#quote-examples
.. _autorewrite: :///home/steck/tactic-examples.html#autorewrite-example
.. _9.1: :///home/steck/ltac.html#ltac
.. _10.4  Using the tactical language: :///home/steck/tactic-examples.html#sec512
.. _xhtml valid: http://validator.w3.org/
.. _Tactics: :///home/steck/tactic-index.html
.. _webmaster: mailto:coq-www_@_inria.fr
.. _9: :///home/steck/tactics.html#elim
.. _General: :///home/steck/general-index.html
.. _Options: :///home/steck/option-index.html
.. _The Coq Proof Assistant: :///
.. _56: :///home/steck/biblio.html#Dyc92
.. _25: :///home/steck/ring.html#ring
.. _Documentation: :///documentation
.. _8.14: :///home/steck/tactics.html#inversion





+ `Home`_
+ `About Coq`_
+ `Get Coq`_
+ `Documentation`_
+ `Community`_

` `_ `The Coq Proof Assistant`_


Chapter 9 The tactic language
=============================


+ `9.1 Syntax`_
+ `9.2 Semantics`_
+ `9.3 Tactic toplevel definitions`_
+ `9.4 Debugging L tac tactics`_


This chapter gives a compact documentation of Ltac, the tactic
language available in Coq. We start by giving the syntax, and next, we
present the informal semantics. If you want to know more regarding
this language and especially about its foundations, you can refer to
[`43`_]. Chapter `10`_ is devoted to giving examples of use of this
language on small but also with non-trivial problems.


9.1 Syntax
----------

The syntax of the tactic language is given Figures 9.1 and 9.2. See
Chapter `1`_ for a description of the BNF metasyntax used in these
grammar rules. Various already defined entries will be used in this
chapter: entriesnatural, integer, ident, qualid, term,cpattern and
atomic_tactic represent respectively the natural and integer numbers,
the authorized identificators and qualified names,Coq’s terms and
patterns and all the atomic tactics described in Chapter `8`_. The
syntax of cpattern is the same as that of terms, but it is extended
with pattern matching metavariables. Incpattern, a pattern-matching
metavariable is represented with the syntax ?id where id is an ident.
The notation _ can also be used to denote metavariable whose instance
is irrelevant. In the notation ?id, the identifier allows us to keep
instantiations and to make constraints whereas _ shows that we are not
interested in what will be matched. On the right hand side of pattern-
matching clauses, the named metavariable are used without the question
mark prefix. There is also a special notation for second-order
pattern-matching problems: in an applicative pattern of the form @?id
id 1 …id n , the variable id matches any complex expression with
(possible) dependencies in the variables id 1 …id n and returns a
functional term of the form fun id 1 …id n => term.

The main entry of the grammar is expr. This language is used in proof
mode but it can also be used in toplevel definitions as shown in
Figure 9.3.


Remarks:


#. The infix tacticals “… || …”, “… + …”, and “… ; …” are associative.
#. In tacarg, there is an overlap between qualid as a direct tactic
   argument and qualid as a particular case ofterm. The resolution is
   done by first looking for a reference of the tactic language and if it
   fails, for a reference to a term. To force the resolution as a
   reference of the tactic language, use the form ltac : qualid. To force
   the resolution as a reference to a term, use the syntax (qualid).
#. As shown by the figure, tactical || binds more than the prefix
   tacticals try, repeat, do andabstract which themselves bind more than
   the postfix tactical “… ;[ … ]” which binds more than “… ; …”.For
   instance try repeat tactic 1 ||tactic 2 ;tactic 3 ;[tactic 31
   |…|tactic 3n ];tactic 4 . is understood as (try (repeat (tactic 1 ||
   tactic 2 ))); ((tactic 3 ;[tactic 31 |…|tactic 3n ]);tactic 4 ).




expr ::= expr ; expr | [> expr | … | expr ] | expr ; [ expr | … | expr
] | tacexpr 3 tacexpr 3 ::= do (natural | ident) tacexpr 3 | progress
tacexpr 3 | repeat tacexpr 3 | try tacexpr 3 | once tacexpr 3 |
exactly_once tacexpr 3 | timeout (natural | ident) tacexpr 3 | time
[string] tacexpr 3 | only selector : tacexpr 3 | tacexpr 2 tacexpr 2
::= tacexpr 1 || tacexpr 3 | tacexpr 1 + tacexpr 3 | tryif tacexpr 1
then tacexpr 1 else tacexpr 1 | tacexpr 1 tacexpr 1 ::= fun name …
name => atom | let [rec] let_clause with … with let_clause inatom |
match goal with context_rule | … | context_rule end | match reverse
goal with context_rule | … | context_rule end | match expr with
match_rule | … | match_rule end | lazymatch goal with context_rule | …
| context_rule end | lazymatch reverse goal with context_rule | … |
context_rule end | lazymatch expr with match_rule | … | match_rule end
| multimatch goal with context_rule | … | context_rule end |
multimatch reverse goal with context_rule | … | context_rule end |
multimatch expr with match_rule | … | match_rule end | abstract atom |
abstract atom using ident | first [ expr | … | expr ] | solve [ expr |
… | expr ] | idtac [message_token … message_token] | fail [natural]
[message_token … message_token] | gfail [natural] [message_token …
message_token] | fresh | fresh string| fresh qualid | context ident [
term ] | eval redexpr in term | type of term | external string string
tacarg … tacarg | constr : term | uconstr : term | type_term term |
numgoals | guard test | atomic_tactic | qualid tacarg … tacarg | atom
Figure 9.1: Syntax of the tactic language





atom ::= qualid | () | integer | ( expr ) message_token ::= string |
ident | integer tacarg ::= qualid | () | ltac : atom | term let_clause
::= ident [name … name] := expr context_rule ::= context_hyp , … ,
context_hyp |-cpattern => expr | |- cpattern => expr | _ => expr
context_hyp ::= name : cpattern | name := cpattern [: cpattern]
match_rule ::= cpattern => expr | context [ident] [ cpattern ]=> expr
| appcontext [ident] [ cpattern ]=> expr | _ => expr test ::= integer
= integer | integer < integer | integer <= integer | integer > integer
| integer >= integer selector ::= [ident] | integer | (integer |
integer - integer) , … , (integer | integer - integer)
toplevel_selector ::= selector | all | par Figure 9.2: Syntax of the
tactic language (continued)





top ::= [Local] Ltac ltac_def with … with ltac_def ltac_def ::= ident
[ident … ident] :=expr | qualid [ident … ident] ::=expr Figure 9.3:
Tactic toplevel definitions





9.2 Semantics
-------------



Tactic expressions can only be applied in the context of a proof. The
evaluation yields either a term, an integer or a tactic. Intermediary
results can be terms or integers but the final result must be a tactic
which is then applied to the focused goals.

There is a special case for match goal expressions of which the
clauses evaluate to tactics. Such expressions can only be used as end
result of a tactic expression (never as argument of a non recursive
local definition or of an application).

The rest of this section explains the semantics of every construction
of Ltac.


Sequence
````````

A sequence is an expression of the following form:
expr 1 ; expr 2
The expressions expr 1 and expr 2 are evaluated to v 1 and v 2 which
have to be tactic values. The tactic v 1 is then applied and v 2 is
applied to the goals generated by the application of v 1 . Sequence is
left-associative.


Local application of tactics
````````````````````````````

Different tactics can be applied to the different goals using the
following form:
[ > expr 1 | ... | expr n ]
The expressions expr i are evaluated to v i , for i=0,...,n and all
have to be tactics. The v i is applied to the i-th goal, for =1,...,n.
It fails if the number of focused goals is not exactly n.


Variants:


#. If no tactic is given for the i-th goal, it behaves as if the
   tactic idtac were given. For instance, [ > | auto ] is a shortcut for
   [ > idtac | auto ].
#. [ > expr 1 | ... |expr i | expr .. |expr i+1+j | ... | expr n ]In
   this variant, expr is used for each goal numbered fromi+1 to i+j
   (assuming n is the number of goals).Note that .. is part of the
   syntax, while ... is the meta-symbol used to describe a list of expr
   of arbitrary length. goals numbered from i+1 to i+j.
#. [ > expr 1 | ... |expr i | .. | expr i+1+j | ... | expr n ]In this
   variant, idtac is used for the goals numbered fromi+1 to i+j.
#. [ > expr .. ]In this variant, the tactic expr is applied
   independently to each of the goals, rather than globally. In
   particular, if there are no goal, the tactic is not run at all. A
   tactic which expects multiple goals, such as swap, would act as if a
   single goal is focused.
#. expr ; [ expr 1 | ... | expr n ]This variant of local tactic
   application is paired with a sequence. In this variant, n must be the
   number of goals generated by the application of expr to each of the
   individual goals independently. All the above variants work in this
   form too. Formally, expr ; [ ... ] is equivalent to [ > expr ; [ > ...
   ] .. ]



Goal selectors
``````````````

We can restrict the application of a tactic to a subset of the
currently focused goals with:
toplevel_selector : expr
We can also use selectors as a tactical, which allows to use them
nested in a tactic expression, by using the keyword only:
only selector : expr
When selecting several goals, the tactic expr is applied globally to
all selected goals.


Variants:


#. [ident] : exprIn this variant, expr is applied locally to a goal
   previously named by the user (see `2.11`_).
#. num : exprIn this variant, expr is applied locally to thenum-th
   goal.
#. n 1 -m 1 , …, n k -m k : exprIn this variant, expr is applied
   globally to the subset of goals described by the given ranges. You can
   write a singlen as a shortcut for n-n when specifying multiple ranges.
#. all: exprIn this variant, expr is applied to all focused goals.all:
   can only be used at the toplevel of a tactic expression.
#. par: exprIn this variant, expr is applied to all focused goals in
   parallel. The number of workers can be controlled via the command line
   option -async-proofs-tac-j taking as argument the desired number of
   workers. Limitations: par: only works on goals containing no
   existential variables and expr must either solve the goal completely
   or do nothing (i.e. it cannot make some progress).par: can only be
   used at the toplevel of a tactic expression.



Error message: No such goal


For loop
````````

There is a for loop that repeats a tactic num times:
do num expr
expr is evaluated to v which must be a tactic value. This tactic value
v is applied num times. Supposing num>1, after the first application
of v, v is applied, at least once, to the generated subgoals and so
on. It fails if the application of v fails before the num applications
have been completed.


Repeat loop
```````````

We have a repeat loop with:
repeat expr
expr is evaluated to v. If v denotes a tactic, this tactic is applied
to each focused goal independently. If the application succeeds, the
tactic is applied recursively to all the generated subgoals until it
eventually fails. The recursion stops in a subgoal when the tactic has
failed *to make progress*. The tactic repeatexpr itself never fails.


Error catching
``````````````

We can catch the tactic errors with:
try expr
expr is evaluated to v which must be a tactic value. The tactic value
v is applied to each focused goal independently. If the application of
v fails in a goal, it catches the error and leaves the goal unchanged.
If the level of the exception is positive, then the exception is re-
raised with its level decremented.


Detecting progress
``````````````````

We can check if a tactic made progress with:
progress expr
expr is evaluated to v which must be a tactic value. The tactic value
v is applied to each focued subgoal independently. If the application
ofv to one of the focused subgoal produced subgoals equal to the
initial goals (up to syntactical equality), then an error of level 0
is raised.


Error message: Failed to progress


Backtracking branching
``````````````````````

We can branch with the following structure:
expr 1 + expr 2
expr 1 and expr 2 are evaluated to v 1 andv 2 which must be tactic
values. The tactic value v 1 is applied to each focused goal
independently and if it fails or a later tactic fails, then the proof
backtracks to the current goal and v 2 is applied.

Tactics can be seen as having several successes. When a tactic fails
it asks for more successes of the prior tactics. expr 1 + expr 2 has
all the successes of v 1 followed by all the successes of v 2 .
Algebraically, (expr 1 +expr 2 );expr 3 = (expr 1 ;expr 3 )+ (expr 2
;expr 3 ).

Branching is left-associative.


First tactic to work
````````````````````

Backtracking branching may be too expensive. In this case we may
restrict to a local, left biased, branching and consider the first
tactic to work (i.e. which does not fail) among a panel of tactics:
first [ expr 1 | ... | expr n ]
expr i are evaluated to v i and v i must be tactic values, for
i=1,...,n. Supposing n>1, it applies, in each focused goal
independently, v 1 , if it works, it stops otherwise it tries to apply
v 2 and so on. It fails when there is no applicable tactic. In other
words, first [ expr 1 | ... |expr n ] behaves, in each goal, as the
the first v i to have *at least* one success.


Error message: No applicable tactic


Variant: first expr

This is an Ltac alias that gives a primitive access to the first
tactical as a Ltac definition without going through a parsing rule. It
expects to be given a list of tactics through a Tactic Notation,
allowing to write notations of the following form.


Example:
Tactic Notation "foo" tactic_list(tacs) := first tacs.


Left-biased branching
`````````````````````

Yet another way of branching without backtracking is the following
structure:
expr 1 || expr 2
expr 1 and expr 2 are evaluated to v 1 andv 2 which must be tactic
values. The tactic value v 1 is applied in each subgoal independently
and if it fails *to progress* then v 2 is applied. expr 1 || expr 2 is
equivalent to first [ progress expr 1 | progressexpr 2 ] (except that
if it fails, it fails likev 2 ). Branching is left-associative.


Generalized biased branching
````````````````````````````

The tactic
tryif expr 1 then expr 2 else expr 3
is a generalization of the biased-branching tactics above. The
expression expr 1 is evaluated to v 1 , which is then applied to each
subgoal independently. For each goal where v 1 succeeds at least once,
tacexpr 2 is evaluated to v 2 which is then applied collectively to
the generated subgoals. The v 2 tactic can trigger backtracking points
in v 1 : where v 1 succeeds at least once, tryif expr 1 then expr 2
else expr 3 is equivalent to v 1 ;v 2 . In each of the goals where v 1
does not succeed at least once, expr 3 is evaluated in v 3 which is is
then applied to the goal.


Soft cut
````````

Another way of restricting backtracking is to restrict a tactic to a
single success *a posteriori*:
once expr
expr is evaluated to v which must be a tactic value. The tactic value
v is applied but only its first success is used. If v fails, onceexpr
fails like v. If v has a least one success, onceexpr succeeds once,
but cannot produce more successes.


Checking the successes
``````````````````````

Coq provides an experimental way to check that a tactic has *exactly
one* success:
exactly_once expr
expr is evaluated to v which must be a tactic value. The tactic value
v is applied if it has at most one success. If v fails, exactly_once
expr fails like v. If v has a exactly one success, exactly_once expr
succeeds like v. If v has two or more successes, exactly_once expr
fails.

The experimental status of this tactic pertains to the fact if v
performs side effects, they may occur in a unpredictable way. Indeed,
normally v would only be executed up to the first success until
backtracking is needed, however exactly_once needs to look ahead to
see whether a second success exists, and may run further effects
immediately.


Error message: This tactic has more than one success


Solving
```````

We may consider the first to solve (i.e. which generates no subgoal)
among a panel of tactics:
solve [ expr 1 | ... | expr n ]
expr i are evaluated to v i and v i must be tactic values, for
i=1,...,n. Supposing n>1, it applies v 1 to each goal independently,
if it doesn’t solve the goal then it tries to applyv 2 and so on. It
fails if there is no solving tactic.


Error message: Cannot solve the goal


Variant: solve expr

This is an Ltac alias that gives a primitive access to the solve
tactical. See the first tactical for more information.


Identity
````````

The constant idtac is the identity tactic: it leaves any goal
unchanged but it appears in the proof script.


Variant: idtac message_token … message_token

This prints the given tokens. Strings and integers are printed
literally. If a (term) variable is given, its contents are printed.


Failing
```````

The tactic fail is the always-failing tactic: it does not solve any
goal. It is useful for defining other tacticals since it can be caught
by try, repeat, match goal, or the branching tacticals. The fail
tactic will, however, succeed if all the goals have already been
solved.


Variants:


#. fail n The number n is the failure level. If no level is specified,
   it defaults to 0. The level is used by try, repeat, match goal and the
   branching tacticals. If 0, it makes match goal considering the next
   clause (backtracking). If non zero, the current match goal block,try,
   repeat, or branching command is aborted and the level is decremented.
   In the case of +, a non-zero level skips the first backtrack point,
   even if the call to fail n is not enclosed in a + command, respecting
   the algebraic identity.
#. fail message_token … message_token The given tokens are used for
   printing the failure message.
#. fail n message_token … message_token This is a combination of the
   previous variants.
#. gfail This variant fails even if there are no goals left.
#. gfail message_token … message_token gfail n message_token …
   message_token These variants fail with an error message or an error
   level even if there are no goals left. Be careful however if Coq terms
   have to be printed as part of the failure: term construction always
   forces the tactic into the goals, meaning that if there are no goals
   when it is evaluated, a tactic call like let x:=H in fail 0 x will
   succeed.



Error message: Tactic Failure message (level n).


Timeout
```````

We can force a tactic to stop if it has not finished after a certain
amount of time:
timeout num expr
expr is evaluated to v which must be a tactic value. The tactic value
v is applied normally, except that it is interrupted after num seconds
if it is still running. In this case the outcome is a failure.

Warning: For the moment, timeout is based on elapsed time in seconds,
which is very machine-dependent: a script that works on a quick
machine may fail on a slow one. The converse is even possible if you
combine atimeout with some other tacticals. This tactical is hence
proposed only for convenience during debug or other development
phases, we strongly advise you to not leave any timeout in final
scripts. Note also that this tactical isn’t available on the native
Windows port of Coq.


Timing a tactic
```````````````

A tactic execution can be timed:
time string expr
evaluates expr and displays the time the tactic expression ran,
whether it fails or successes. In case of several successes, the time
for each successive runs is displayed. Time is in seconds and is
machine-dependent. Thestring argument is optional. When provided, it
is used to identify this particular occurrence of time.


Local definitions
`````````````````

Local definitions can be done as follows:
let ident 1 := expr 1
with ident 2 := expr 2
...
with ident n := expr n in
expr
each expr i is evaluated to v i , then, expr is evaluated by
substituting v i to each occurrence of ident i , for i=1,...,n. There
is no dependencies between the expr i and the ident i .

Local definitions can be recursive by using let rec instead oflet. In
this latter case, the definitions are evaluated lazily so that the rec
keyword can be used also in non recursive cases so as to avoid the
eager evaluation of local definitions.


Application
```````````

An application is an expression of the following form:
qualid tacarg 1 ... tacarg n
The reference qualid must be bound to some defined tactic definition
expecting at least n arguments. The expressionsexpr i are evaluated to
v i , for i=1,...,n.


Function construction
`````````````````````

A parameterized tactic can be built anonymously (without resorting to
local definitions) with:
fun ident 1 ... ident n => expr
Indeed, local definitions of functions are a syntactic sugar for
binding a fun tactic to an identifier.


Pattern matching on terms
`````````````````````````

We can carry out pattern matching on terms with:
match expr with
cpattern 1 => expr 1
| cpattern 2 => expr 2
...
| cpattern n => expr n
| _ => expr n+1
end
The expression expr is evaluated and should yield a term which is
matched against cpattern 1 . The matching is non-linear: if a
metavariable occurs more than once, it should match the same
expression every time. It is first-order except on the variables of
the form @?id that occur in head position of an application. For these
variables, the matching is second-order and returns a functional term.

Alternatively, when a metavariable of the form ?id occurs under
binders, say x 1 , …, x n and the expression matches, the metavariable
is instantiated by a term which can then be used in any context which
also binds the variables x 1 , …, x n with same types. This provides
with a primitive form of matching under context which does not require
manipulating a functional term.

If the matching with cpattern 1 succeeds, then expr 1 is evaluated
into some value by substituting the pattern matching instantiations to
the metavariables. If expr 1 evaluates to a tactic and the match
expression is in position to be applied to a goal (e.g. it is not
bound to a variable by a let in), then this tactic is applied. If the
tactic succeeds, the list of resulting subgoals is the result of the
match expression. Ifexpr 1 does not evaluate to a tactic or if the
match expression is not in position to be applied to a goal, then the
result of the evaluation of expr 1 is the result of the match
expression.

If the matching with cpattern 1 fails, or if it succeeds but the
evaluation of expr 1 fails, or if the evaluation ofexpr 1 succeeds but
returns a tactic in execution position whose execution fails, then
cpattern 2 is used and so on. The pattern _ matches any term and
shunts all remaining patterns if any. If all clauses fail (in
particular, there is no pattern _) then a no-matching-clause error is
raised.

Failures in subsequent tactics do not cause backtracking to select new
branches or inside the right-hand side of the selected branch even if
it has backtracking points.


Error messages:


#. No matching clauses for matchNo pattern can be used and, in
   particular, there is no _ pattern.
#. Argument of match does not evaluate to a termThis happens when expr
   does not denote a term.



Variants:


#. Using multimatch instead of match will allow subsequent tactics to
   backtrack into a right-hand side tactic which has backtracking points
   left and trigger the selection of a new matching branch when all the
   backtracking points of the right-hand side have been consumed.The
   syntax match … is, in fact, a shorthand foronce multimatch ….
#. Using lazymatch instead of match will perform the same pattern
   matching procedure but will commit to the first matching branch rather
   than trying a new matching if the right-hand side fails. If the right-
   hand side of the selected branch is a tactic with backtracking points,
   then subsequent failures cause this tactic to backtrack.
#. There is a special form of patterns to match a subterm against the
   pattern: context ident [ cpattern ] It matches any term with a subterm
   matching cpattern. If there is a match, the optional ident is assigned
   the “matched context”, i.e. the initial term where the matched subterm
   is replaced by a hole. The example below will show how to use such
   term contexts.If the evaluation of the right-hand-side of a valid
   match fails, the next matching subterm is tried. If no further subterm
   matches, the next clause is tried. Matching subterms are considered
   top-bottom and from left to right (with respect to the raw printing
   obtained by setting option Printing All, see Section `2.9`_). Coq <
   Ltac f x := match x with context f [S ?X] => idtac X; (* To display
   the evaluation order *) assert (p := eq_refl 1 : X=1); (* To filter
   the case X=1 *) let x:= context f[O] in assert (x=O) (* To observe the
   context *) end. f is defined Coq < Goal True. 1 subgoal
   ============================ True Coq < f (3+4). 2 1 2 subgoals p : 1
   = 1 ============================ 1 + 4 = 0 subgoal 2 is: True
#. For historical reasons, context used to consider n-ary applications
   such as (f 1 2) as a whole, and not as a sequence of unary
   applications ((f 1) 2). Hence context [f ?x] would fail to find a
   matching subterm in (f 1 2): if the pattern was a partial application,
   the matched subterms would have necessarily been applications with
   exactly the same number of arguments. As a workaround, one could use
   the following variant of context: appcontext ident [ cpattern ] This
   syntax is now deprecated, as context behaves as intended. The former
   behavior can be retrieved with the Tactic Compat Context flag.



Pattern matching on goals
`````````````````````````

We can make pattern matching on goals using the following expression:
match goal with | hyp 1,1 ,...,hyp 1,m 1 |-cpattern 1 => expr 1 | hyp
2,1 ,...,hyp 2,m 2 |-cpattern 2 => expr 2 ... | hyp n,1 ,...,hyp n,m n
|-cpattern n => expr n |_ => expr n+1 end
If each hypothesis pattern hyp 1,i , with i=1,...,m 1 is matched (non-
linear first-order unification) by an hypothesis of the goal and if
cpattern 1 is matched by the conclusion of the goal, then expr 1 is
evaluated to v 1 by substituting the pattern matching to the
metavariables and the real hypothesis names bound to the possible
hypothesis names occurring in the hypothesis patterns. If v 1 is a
tactic value, then it is applied to the goal. If this application
fails, then another combination of hypotheses is tried with the same
proof context pattern. If there is no other combination of hypotheses
then the second proof context pattern is tried and so on. If the next
to last proof context pattern fails then expr n+1 is evaluated to v
n+1 and v n+1 is applied. Note also that matching against subterms
(using the context ident [ cpattern ]) is available and is also
subject to yielding several matchings.

Failures in subsequent tactics do not cause backtracking to select new
branches or combinations of hypotheses, or inside the right-hand side
of the selected branch even if it has backtracking points.


Error message: No matching clauses for match goal

No clause succeeds, i.e. all matching patterns, if any, fail at the
application of the right-hand-side.




It is important to know that each hypothesis of the goal can be
matched by at most one hypothesis pattern. The order of matching is
the following: hypothesis patterns are examined from the right to the
left (i.e. hyp i,m i before hyp i,1 ). For each hypothesis pattern,
the goal hypothesis are matched in order (fresher hypothesis first),
but it possible to reverse this order (older first) with the match
reverse goal with variant.


Variant:



Using multimatch instead of match will allow subsequent tactics to
backtrack into a right-hand side tactic which has backtracking points
left and trigger the selection of a new matching branch or combination
of hypotheses when all the backtracking points of the right-hand side
have been consumed.

The syntax match [reverse] goal … is, in fact, a shorthand foronce
multimatch [reverse] goal ….

Using lazymatch instead of match will perform the same pattern
matching procedure but will commit to the first matching branch with
the first matching combination of hypotheses rather than trying a new
matching if the right-hand side fails. If the right-hand side of the
selected branch is a tactic with backtracking points, then subsequent
failures cause this tactic to backtrack.


Filling a term context
``````````````````````

The following expression is not a tactic in the sense that it does not
produce subgoals but generates a term to be used in tactic
expressions:
context ident [ expr ]
ident must denote a context variable bound by a context pattern of a
match expression. This expression evaluates replaces the hole of the
value of ident by the value ofexpr.


Error message: not a context variable


Generating fresh hypothesis names
`````````````````````````````````

Tactics sometimes have to generate new names for hypothesis. Letting
the system decide a name with the intro tactic is not so good since it
is very awkward to retrieve the name the system gave. The following
expression returns an identifier:
fresh component … component
It evaluates to an identifier unbound in the goal. This fresh
identifier is obtained by concatenating the value of thecomponent’s
(each of them is, either an qualid which has to refer to a
(unqualified) name, or directly a name denoted by astring). If the
resulting name is already used, it is padded with a number so that it
becomes fresh. If no component is given, the name is a fresh
derivative of the name H.


Computing in a constr
`````````````````````

Evaluation of a term can be performed with:
eval redexpr in term
where redexpr is a reduction tactic among red, hnf, compute, simpl,
cbv, lazy, unfold,fold, pattern.


Recovering the type of a term
`````````````````````````````



The following returns the type of term:
type of term


Manipulating untyped terms
``````````````````````````

The terms built in Ltac are well-typed by default. It may not be
appropriate for building large terms using a recursive Ltac function:
the term has to be entirely type checked at each step, resulting in
potentially very slow behavior. It is possible to build untyped terms
using Ltac with the syntax
uconstr : term
An untyped term, in Ltac, can contain references to hypotheses or to
Ltac variables containing typed or untyped terms. An untyped term can
be type-checked using the function type_term whose argument is parsed
as an untyped term and returns a well-typed term which can be used in
tactics.
type_term term
Untyped terms built using uconstr : can also be used as arguments to
the refine tactic `8.2.3`_. In that case the untyped term is type
checked against the conclusion of the goal, and the holes which are
not solved by the typing procedure are turned into new subgoals.


Counting the goals
``````````````````

The number of goals under focus can be recovered using the numgoals
function. Combined with the guard command below, it can be used to
branch over the number of goals produced by previous tactics.
Coq < Ltac pr_numgoals := let n := numgoals in idtac "There are" n
"goals".

Coq < Goal True /\ True /\ True.

Coq < split;[|split].

Coq < all:pr_numgoals.
There are 3 goals
3 subgoals

============================
True
subgoal 2 is:
True
subgoal 3 is:
True



Testing boolean expressions
```````````````````````````

The guard tactic tests a boolean expression, and fails if the
expression evaluates to false. If the expression evaluates to true, it
succeeds without affecting the proof.
guard test
The accepted tests are simple integer comparisons.
Coq < Goal True /\ True /\ True.

Coq < split;[|split].

Coq < all:let n:= numgoals in guard n<4.
3 subgoals

============================
True
subgoal 2 is:
True
subgoal 3 is:
True

Coq < Fail all:let n:= numgoals in guard n=2.
The command has indeed failed with message:
Ltac call to "guard (test)" failed.
Condition not satisfied: 3=2
3 subgoals

============================
True
subgoal 2 is:
True
subgoal 3 is:
True


Error messages:


#. Condition not satisfied



Proving a subgoal as a separate lemma
`````````````````````````````````````

From the outside “abstract expr” is the same assolve expr. Internally
it saves an auxiliary lemma calledident_subproofn where ident is the
name of the current goal and n is chosen so that this is a fresh name.
Such auxiliary lemma is inlined in the final proof term unless the
proof is ended with “Qed exporting”. In such case the lemma is
preserved. The syntax “Qed exporting ident 1 , ..., ident n ” is also
supported. In such case the system checks that the names given by the
user actually exist when the proof is ended.

This tactical is useful with tactics such as omega ordiscriminate that
generate huge proof terms. With that tool the user can avoid the
explosion at time of the Save command without having to cut manually
the proof in smaller lemmas.

It may be useful to generate lemmas minimal w.r.t. the assumptions
they depend on. This can be obtained thanks to the option below.
Set Shrink Abstract
*Deprecated since 8.7*

When set (default), all lemmas generated through abstract expr and
transparent_abstract expr are quantified only over the variables that
appear in the term constructed by expr.


Variants:


#. abstract expr using ident. Give explicitly the name of the
   auxiliary lemma. Use this feature at your own risk; explicitly named
   and reused subterms don’t play well with asynchronous proofs.
#. transparent_abstract expr. Save the subproof in a transparent lemma
   rather than an opaque one. Use this feature at your own risk; building
   computationally relevant terms with tactics is fragile.
#. transparent_abstract expr using ident. Give explicitly the name of
   the auxiliary transparent lemma. Use this feature at your own risk;
   building computationally relevant terms with tactics is fragile, and
   explicitly named and reused subterms don’t play well with asynchronous
   proofs.



Error message: Proof is not complete


9.3 Tactic toplevel definitions
-------------------------------


9.3.1 Defining L tac functions
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Basically, L tac toplevel definitions are made as follows:
Ltac ident ident 1 ... ident n :=expr
This defines a new L tac function that can be used in any tactic
script or new L tac toplevel definition.


Remark: The preceding definition can equivalently be written:
Ltac ident := fun ident 1 ... ident n => expr
Recursive and mutual recursive function definitions are also possible
with the syntax:
Ltac ident 1 ident 1,1 ...ident 1,m 1 := expr 1
with ident 2 ident 2,1 ... ident 2,m 2 :=expr 2
...
with ident n ident n,1 ... ident n,m n :=expr n

It is also possible to *redefine* an existing user-defined tactic
using the syntax:
Ltac qualid ident 1 ... ident n ::=expr
A previous definition of qualid must exist in the environment. The new
definition will always be used instead of the old one and it goes
across module boundaries.

If preceded by the keyword Local the tactic definition will not be
exported outside the current module.


9.3.2 Printing L tac tactics
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Defined L tac functions can be displayed using the command
Print Ltac qualid.
The command Print Ltac Signatures displays a list of all user-defined
tactics, with their arguments.


9.4 Debugging L tac tactics
---------------------------


9.4.1 Info trace
~~~~~~~~~~~~~~~~

It is possible to print the trace of the path eventually taken by an L
tac script. That is, the list of executed tactics, discarding all the
branches which have failed. To that end the Info command can be used
with the following syntax.
Info num expr.
The number num is the unfolding level of tactics in the trace. At
level 0, the trace contains a sequence of tactics in the actual
script, at level 1, the trace will be the concatenation of the traces
of these tactics, etc…
Coq < Ltac t x := exists x; reflexivity.

Coq < Goal exists n, n=0.

Coq < Info 0 t 1||t 0.
t <constr:(0)>
No more subgoals.

Coq < Undo.

Coq < Info 1 t 1||t 0.
exists 0;reflexivity
No more subgoals.

The trace produced by Info tries its best to be a reparsable L tac
script, but this goal is not achievable in all generality. So some of
the output traces will contain oddities.

As an additional help for debugging, the trace produced by Info
contains (in comments) the messages produced by the idtac tacticals
9.2 at the right possition in the script. In particular, the calls to
idtac in branches which failed are not printed.

An alternative to the Info command is to use the Info Level option as
follows:
Set Info Level num.
This will automatically print the same trace as Info num at each
tactic call. The unfolding level can be overridden by a call to the
Info command. And this option can be turned off with:
Unset Info Level num.
The current value for the Info Level option can be checked using the
Test Info Level command.


9.4.2 Interactive debugger
~~~~~~~~~~~~~~~~~~~~~~~~~~

The L tac interpreter comes with a step-by-step debugger. The debugger
can be activated using the command
Set Ltac Debug.
and deactivated using the command
Unset Ltac Debug.
To know if the debugger is on, use the command Test Ltac Debug. When
the debugger is activated, it stops at every step of the evaluation of
the current L tac expression and it prints information on what it is
doing. The debugger stops, prompting for a command which can be one of
the following:



simple newline: go to the next step h: get help x: exit current
evaluation s: continue current evaluation without stopping r n:
advance n steps further r string: advance up to the next call to
“idtac string”
A non-interactive mode for the debugger is available via the command
Set Ltac Batch Debug.
This option has the effect of presenting a newline at every prompt,
when the debugger is on. The debug log thus created, which does not
require user input to generate when this option is set, can then be
run through external tools such as diff.


9.4.3 Profiling L tac tactics
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

It is possible to measure the time spent in invocations of primitive
tactics as well as tactics defined in L tac and their inner
invocations. The primary use is the development of complex tactics,
which can sometimes be so slow as to impede interactive usage. The
reasons for the performence degradation can be intricate, like a
slowly performing L tac match or a sub-tactic whose performance only
degrades in certain situations. The profiler generates a call tree and
indicates the time spent in a tactic depending its calling context.
Thus it allows to locate the part of a tactic definition that contains
the performance bug.
Set Ltac Profiling.
Enables the profiler
Unset Ltac Profiling.
Disables the profiler
Show Ltac Profile.
Prints the profile
Show Ltac Profile string.
Prints a profile for all tactics that start with string. Append a
period (.) to the string if you only want exactly that name.
Reset Ltac Profile.
Resets the profile, that is, deletes all accumulated information. Note
that backtracking across a Reset Ltac Profile will not restore the
information.
Coq < Require Import Coq.omega.Omega.

Coq < Ltac mytauto := tauto.

Coq < Ltac tac := intros; repeat split; omega || mytauto.

Coq < Notation max x y := (x + (y - x)) (only parsing).

Coq < Goal forall x y z A B C D E F G H I J K L M N O P Q R S T U V W
X Y Z,
max x (max y z) = max (max x y) z /\ max x (max y z) = max (max x y) z
/\ (A /\ B /\ C /\ D /\ E /\ F /\ G /\ H /\ I /\ J /\ K /\ L /\ M /\ N
/\ O /\ P /\ Q /\ R /\ S /\ T /\ U /\ V /\ W /\ X /\ Y /\ Z
-> Z /\ Y /\ X /\ W /\ V /\ U /\ T /\ S /\ R /\ Q /\ P /\ O /\ N /\ M
/\ L /\ K /\ J /\ I /\ H /\ G /\ F /\ E /\ D /\ C /\ B /\ A).

Coq < Proof.

Coq < Set Ltac Profiling.

Coq < tac.
No more subgoals.
Coq < Show Ltac Profile.
total time: 1.142s
tactic local total calls max
────────────────────────────────────────┴──────┴──────┴───────┴───────
──┘
─tac ----------------------------------- 0.1% 100.0% 1 1.142s
─<Coq.Init.Tauto.with_uniform_flags> --- 0.0% 61.1% 26 0.056s
─<Coq.Init.Tauto.tauto_gen> ------------ 0.1% 61.1% 26 0.056s
─<Coq.Init.Tauto.tauto_intuitionistic> - 0.3% 61.0% 26 0.056s
─t_tauto_intuit ------------------------ 1.7% 60.8% 26 0.056s
─<Coq.Init.Tauto.simplif> -------------- 44.3% 58.8% 26 0.055s
─omega --------------------------------- 38.4% 38.4% 28 0.204s
─<Coq.Init.Tauto.is_conj> -------------- 5.4% 5.4% 28756 0.001s
─elim id ------------------------------- 5.3% 5.3% 650 0.001s
─intro --------------------------------- 2.0% 2.0% 1300 0.001s
tactic local total calls max
────────────────────────────────────────┴──────┴──────┴───────┴───────
──┘
─tac ----------------------------------- 0.1% 100.0% 1 1.142s
├─<Coq.Init.Tauto.with_uniform_flags> - 0.0% 61.1% 26 0.056s
│└<Coq.Init.Tauto.tauto_gen> ---------- 0.1% 61.1% 26 0.056s
│└<Coq.Init.Tauto.tauto_intuitionistic> 0.3% 61.0% 26 0.056s
│└t_tauto_intuit ---------------------- 1.7% 60.8% 26 0.056s
│└<Coq.Init.Tauto.simplif> ------------ 44.3% 58.8% 26 0.055s
│ ├─<Coq.Init.Tauto.is_conj> ---------- 5.4% 5.4% 28756 0.001s
│ ├─elim id --------------------------- 5.3% 5.3% 650 0.001s
│ └─intro ----------------------------- 2.0% 2.0% 1300 0.001s
└─omega ------------------------------- 38.4% 38.4% 28 0.204s

Coq < Show Ltac Profile "omega".
total time: 1.142s
tactic local total calls max
────────────────────────────────────────┴──────┴──────┴───────┴───────
──┘
─omega --------------------------------- 38.4% 38.4% 28 0.204s
tactic local total calls max
────────────────────────────────────────┴──────┴──────┴───────┴───────
──┘
Coq < Abort.

Coq < Unset Ltac Profiling.

The following two tactics behave like idtac but enable and disable the
profiling. They allow you to exclude parts of a proof script from
profiling.
start ltac profiling. stop ltac profiling.
You can also pass the -profile-ltac command line option to coqc, which
performs a Set Ltac Profiling at the beginning of each document, and a
Show Ltac Profile at the end.

Note that the profiler currently does not handle backtracking into
multi-success tactics, and issues a warning to this effect in many
cases when such backtracking occurs.



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


.. _2.9: :///home/steck/gallina-ext.html#SetPrintingAll
.. _Get Coq: :///download
.. _43: :///home/steck/biblio.html#Del00
.. _About Coq: :///about-coq
.. _CSS valid: http://jigsaw.w3.org/css-validator/
.. _Cover: :///home/steck/index.html
.. _Errors: :///home/steck/error-index.html
.. _9.3  Tactic toplevel definitions: :///home/steck/ltac.html#sec498
.. _8.2.3: :///home/steck/tactics.html#refine
.. _Table of contents: :///home/steck/toc.html
.. _Community: :///community
.. _10: :///home/steck/tactic-examples.html#Tactics-examples
.. _ tactics: :///home/steck/ltac.html#sec501
.. _9.2  Semantics: :///home/steck/ltac.html#sec466
.. _9.1  Syntax: :///home/steck/ltac.html#sec465
.. _1: :///home/steck/gallina.html#BNF-syntax
.. _Commands: :///home/steck/command-index.html
.. _xhtml valid: http://validator.w3.org/
.. _Tactics: :///home/steck/tactic-index.html
.. _General: :///home/steck/general-index.html
.. _Options: :///home/steck/option-index.html
.. _The Coq Proof Assistant: :///
.. _Documentation: :///documentation
.. _8: :///home/steck/tactics.html#Tactics
.. _webmaster: mailto:coq-www_@_inria.fr
.. _2.11: :///home/steck/gallina-ext.html#ExistentialVariables



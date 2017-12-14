

+ `Home`_
+ `About Coq`_
+ `Get Coq`_
+ `Documentation`_
+ `Community`_

` `_ `The Coq Proof Assistant`_


Chapter 5 The Module System
===========================


+ `5.1 Modules and module types`_
+ `5.2 Typing Modules`_


The module system extends the Calculus of Inductive Constructions
providing a convenient way to structure large developments as well as
a means of massive abstraction.


5.1 Modules and module types
----------------------------


Access path.
++++++++++++

It is denoted by p, it can be either a module variable X or, if p′ is
an access path and id an identifier, thenp′.id is an access path.


Structure element.
++++++++++++++++++

It is denoted by e and is either a definition of a constant, an
assumption, a definition of an inductive, a definition of a module, an
alias of module or a module type abbreviation.


Structure expression.
+++++++++++++++++++++

It is denoted by S and can be:


+ an access path p
+ a plain structure Struct e ; … ; e End
+ a functor Functor(X:S) S′, where X is a module variable,S and S′ are
  structure expression
+ an application S p, where S is a structure expression and p an
  access path
+ a refined structure S with p := p′ or S with p := t:T where S is a
  structure expression, p and p′ are access paths, t is a term and T is
  the type of t.



Module definition,
++++++++++++++++++

is written Mod(X:S [:=S′]) and consists of a module variable X, a
module typeS which can be any structure expression and optionally a
module implementation S′ which can be any structure expression except
a refined structure.


Module alias,
+++++++++++++

is written ModA(X==p) and consists of a module variable X and a module
path p.


Module type abbreviation,
+++++++++++++++++++++++++

is written ModType(Y:=S), whereY is an identifier and S is any
structure expression .


5.2 Typing Modules
------------------

In order to introduce the typing system we first slightly extend the
syntactic class of terms and environments given in section `4.1`_. The
environments, apart from definitions of constants and inductive types
now also hold any other structure elements. Terms, apart from
variables, constants and complex terms, include also access paths.

We also need additional typing judgments:


+ E[] ⊢ WF(S), denoting that a structure S is well-formed,
+ E[] ⊢ p : S, denoting that the module pointed by p has type S in
  environment E.
+ E[] ⊢ S —→ S, denoting that a structure S is evaluated to a
  structure S in weak head normal form.
+ E[] ⊢ S 1 <: S 2 , denoting that a structure S 1 is a subtype of a
  structure S 2 .
+ E[] ⊢ e 1 <: e 2 , denoting that a structure elemente 1 is more
  precise that a structure element e 2 .


The rules for forming structures are the following:

:WF-STR: WF(E;E′)[] E[] ⊢ WF( Struct E′ End)
:WF-FUN: E; Mod(X:S)[] ⊢ WF( S′ ) E[] ⊢ WF( Functor(X:S) S′)


Evaluation of structures to weak head normal form:

:WEVAL-APP: E[] ⊢ S —→ Functor(X:S 1 ) S 2 E[] ⊢ S 1 —→ S 1 E[] ⊢ p :
  S 3 E[] ⊢ S 3 <: S 1 E[] ⊢ S p —→ S 2 {p/X,t 1 /p 1 .c 1 ,…,t n /p n
  .c n }


In the last rule, {t 1 /p 1 .c 1 ,…,t n /p n .c n } is the resulting
substitution from the inlining mechanism. We substitute in S the
inlined fields p i .c i form Mod(X:S 1 ) by the corresponding delta-
reduced term t i in p.

:WEVAL-WITH-MOD: E[] ⊢ S —→ Struct e 1 ;…;e i ; Mod(X:S 1 );e i+2 ;…
  ;e n End E;e 1 ;…;e i [] ⊢ S 1 —→ S 1 E[] ⊢ p : S 2 E;e 1 ;…;e i [] ⊢
  S 2 <: S 1 E[] ⊢ S with x := p —→ Struct e 1 ;…;e i ; ModA(X==p);e i+2
  {p/X} ;…;e n {p/X} End
:WEVAL-WITH-MOD-REC: E[] ⊢ S —→ Struct e 1 ;…;e i ; Mod(X 1 :S 1 );e
  i+2 ;… ;e n End E;e 1 ;…;e i [] ⊢ S 1 with p := p 1 —→ S 2 E[] ⊢ S
  with X 1 .p := p 1 —→ Struct e 1 ;…;e i ; Mod(X:S 2 );e i+2 {p 1 /X 1
  .p} ;…;e n {p 1 /X 1 .p} End
:WEVAL-WITH-DEF: E[] ⊢ S —→ Struct e 1 ;…;e i ;Assum()(c:T 1 );e i+2
  ;… ;e n End E;e 1 ;…;e i [] ⊢ Def()(c:=t:T) <: Assum()(c:T 1 ) E[] ⊢ S
  with c := t:T —→ Struct e 1 ;…;e i ;Def()(c:=t:T);e i+2 ;… ;e n End
:WEVAL-WITH-DEF-REC: E[] ⊢ S —→ Struct e 1 ;…;e i ; Mod(X 1 :S 1 );e
  i+2 ;… ;e n End E;e 1 ;…;e i [] ⊢ S 1 with p := p 1 —→ S 2 E[] ⊢ S
  with X 1 .p := t:T —→ Struct e 1 ;…;e i ; Mod(X:S 2 );e i+2 ;… ;e n
  End
:WEVAL-PATH-MOD: E[] ⊢ p —→ Struct e 1 ;…;e i ; Mod(X:S [:=S 1 ]);e
  i+2 ;… ;e n End E;e 1 ;…;e i [] ⊢ S —→ S E[] ⊢ p.X —→ S WF(E)[]
  Mod(X:S [:=S 1 ])∈ E E[] ⊢ S —→ S E[] ⊢ X —→ S
:WEVAL-PATH-ALIAS: E[] ⊢ p —→ Struct e 1 ;…;e i ; ModA(X==p 1 );e i+2
  ;… ;e n End E;e 1 ;…;e i [] ⊢ p 1 —→ S E[] ⊢ p.X —→ S WF(E)[]
  ModA(X==p 1 )∈ E E[] ⊢ p 1 —→ S E[] ⊢ X —→ S
:WEVAL-PATH-TYPE: E[] ⊢ p —→ Struct e 1 ;…;e i ; ModType(Y:=S);e i+2
  ;… ;e n End E;e 1 ;…;e i [] ⊢ S —→ S E[] ⊢ p.Y —→ S
:WEVAL-PATH-TYPE: WF(E)[] ModType(Y:=S)∈ E E[] ⊢ S —→ S E[] ⊢ Y —→ S


Rules for typing module:

:MT-EVAL: E[] ⊢ p —→ S E[] ⊢ p : S
:MT-STR: E[] ⊢ p : S E[] ⊢ p : S/p


The last rule, called strengthening is used to make all module fields
manifestly equal to themselves. The notation S/p has the following
meaning:


+ if S—→ Struct e 1 ;…;e n End thenS/p= Struct e 1 /p;…;e n /p End
  where e/p is defined as follows:

    + Def()(c:=t:T)/p 1 = Def()(c:=t:T)
    + Assum()(c:U)/p = Def()(c:=p.c:U)
    + Mod(X:S)/p = ModA(X==p.X)
    + ModA(X==p′)/p = ModA(X==p′)
    + Ind[Γ P ](Γ C := Γ I )/p = Ind p ()[Γ P ]( Γ C :=Γ I )
    + Ind p′ ()[Γ P ]( Γ C :=Γ I )/p = Ind p′ ()[Γ P ]( Γ C :=Γ I )

+ if S—→ Functor(X:S′) S″ then S/p=S


The notation Ind p ()[Γ P ](
Γ C :=Γ I )
denotes an inductive definition that is definitionally equal to the
inductive definition in the module denoted by the path p. All rules
which haveInd[Γ P ](Γ C := Γ I ) as premises are also valid for Ind p
()[Γ P ](
Γ C :=Γ I )
. We give the formation rule for Ind p ()[Γ P ](
Γ C :=Γ I )
below as well as the equality rules on inductive types and
constructors.
The module subtyping rules:

:MSUB-STR: E;e 1 ;…;e n [] ⊢ e σ(i) <: e′ i for i=1..m σ : {1… m} →
  {1… n} injective E[] ⊢ Struct e 1 ;…;e n End <: Struct e′ 1 ;…;e′ m
  End
:MSUB-FUN: E[] ⊢ S 1 ′ <: S 1 E; Mod(X:S 1 ′)[] ⊢ S 2 <: S 2 ′ E[] ⊢
  Functor(X:S 1 ) S 2 <: Functor(X:S 1 ′) S 2 ′


Structure element subtyping rules:

:ASSUM-ASSUM: E[] ⊢ T 1 ≤ βδιζη T 2 E[] ⊢ Assum()(c:T 1 ) <:
  Assum()(c:T 2 )
:DEF-ASSUM: E[] ⊢ T 1 ≤ βδιζη T 2 E[] ⊢ Def()(c:=t:T 1 ) <:
  Assum()(c:T 2 )
:ASSUM-DEF: E[] ⊢ T 1 ≤ βδιζη T 2 E[] ⊢ c = βδιζη t 2 E[] ⊢
  Assum()(c:T 1 ) <: Def()(c:=t 2 :T 2 )
:DEF-DEF: E[] ⊢ T 1 ≤ βδιζη T 2 E[] ⊢ t 1 = βδιζη t 2 E[] ⊢ Def()(c:=t
  1 :T 1 ) <: Def()(c:=t 2 :T 2 )
:IND-IND: E[] ⊢ Γ P = βδιζη Γ P ′ E[Γ P ] ⊢ Γ C = βδιζη Γ C ′ E[Γ P ;Γ
  C ] ⊢ Γ I = βδιζη Γ I ′ E[] ⊢ Ind[Γ P ](Γ C := Γ I ) <: Ind[Γ P ′](Γ C
  ′ := Γ I ′)
:INDP-IND: E[] ⊢ Γ P = βδιζη Γ P ′ E[Γ P ] ⊢ Γ C = βδιζη Γ C ′ E[Γ P
  ;Γ C ] ⊢ Γ I = βδιζη Γ I ′ E[] ⊢ Ind p ()[Γ P ]( Γ C :=Γ I ) <: Ind[Γ
  P ′](Γ C ′ := Γ I ′)
:INDP-INDP: E[] ⊢ Γ P = βδιζη Γ P ′ E[Γ P ] ⊢ Γ C = βδιζη Γ C ′ E[Γ P
  ;Γ C ] ⊢ Γ I = βδιζη Γ I ′ E[] ⊢ p = βδιζη p′ E[] ⊢ Ind p ()[Γ P ]( Γ
  C :=Γ I ) <: Ind p′ ()[Γ P ′]( Γ C ′:=Γ I ′ )
:MOD-MOD: E[] ⊢ S 1 <: S 2 E[] ⊢ Mod(X:S 1 ) <: Mod(X:S 2 )
:ALIAS-MOD: E[] ⊢ p : S 1 E[] ⊢ S 1 <: S 2 E[] ⊢ ModA(X==p) <: Mod(X:S
  2 )
:MOD-ALIAS: E[] ⊢ p : S 2 E[] ⊢ S 1 <: S 2 E[] ⊢ X = βδιζη p E[] ⊢
  Mod(X:S 1 ) <: ModA(X==p)
:ALIAS-ALIAS: E[] ⊢ p 1 = βδιζη p 2 E[] ⊢ ModA(X==p 1 ) <: ModA(X==p 2
  )
:MODTYPE-MODTYPE: E[] ⊢ S 1 <: S 2 E[] ⊢ S 2 <: S 1 E[] ⊢ ModType(Y:=S
  1 ) <: ModType(Y:=S 2 )


New environment formation rules

:WF-MOD: WF(E)[] E[] ⊢ WF(S) WF(E; Mod(X:S))[]
:WF-MOD: E[] ⊢ S 2 <: S 1 WF(E)[] E[] ⊢ WF(S 1 ) E[] ⊢ WF(S 2 ) WF(E;
  Mod(X:S 1 [:=S 2 ]))[]
:WF-ALIAS: WF(E)[] E[] ⊢ p : S WF(E, ModA(X==p))[]
:WF-MODTYPE: WF(E)[] E[] ⊢ WF(S) WF(E, ModType(Y:=S))[]
:WF-IND: WF(E;Ind[Γ P ](Γ C := Γ I ))[] E[] ⊢ p: Struct e 1 ;…;e n
  ;Ind[Γ P ′](Γ C ′ := Γ I ′);… End : E[] ⊢ Ind[Γ P ′](Γ C ′ := Γ I ′)
  <: Ind[Γ P ](Γ C := Γ I ) WF(E; Ind p ()[Γ P ]( Γ C :=Γ I ) )[]


Component access rules

:ACC-TYPE: E[Γ] ⊢ p : Struct e 1 ;…;e i ;Assum()(c:T);… End E[Γ] ⊢ p.c
  : T E[Γ] ⊢ p : Struct e 1 ;…;e i ;Def()(c:=t:T);… End E[Γ] ⊢ p.c : T
:ACC-DELTA: Notice that the following rule extends the delta rule
  defined in section `4.3`_ E[Γ] ⊢ p : Struct e 1 ;…;e i
  ;Def()(c:=t:U);… End E[Γ] ⊢ p.c ▷ δ t In the rules below we assume Γ P
  is [p 1 :P 1 ;…;p r :P r ], Γ I is [I 1 :A 1 ;…;I k :A k ], and Γ C is
  [c 1 :C 1 ;…;c n :C n ]
:ACC-IND: E[Γ] ⊢ p : Struct e 1 ;…;e i ;Ind[Γ P ](Γ C := Γ I );… End
  E[Γ] ⊢ p.I j : (p 1 :P 1 )…(p r :P r )A j E[Γ] ⊢ p : Struct e 1 ;…;e i
  ;Ind[Γ P ](Γ C := Γ I );… End E[Γ] ⊢ p.c m : (p 1 :P 1 )…(p r :P r )C
  m I j (I j p 1 …p r ) j=1… k
:ACC-INDP: E[] ⊢ p : Struct e 1 ;…;e i ; Ind p′ ()[Γ P ]( Γ C :=Γ I )
  ;… End E[] ⊢ p.I i ▷ δ p′.I i E[] ⊢ p : Struct e 1 ;…;e i ; Ind p′
  ()[Γ P ]( Γ C :=Γ I ) ;… End E[] ⊢ p.c i ▷ δ p′.c i




:1: Opaque definitions are processed as assumptions.




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
.. _5.1  Modules and module types: :///home/steck/modules.html#sec225
.. _Tactics: :///home/steck/tactic-index.html
.. _About Coq: :///about-coq
.. _4.3: :///home/steck/cic.html#delta
.. _CSS valid: http://jigsaw.w3.org/css-validator/
.. _The Coq Proof Assistant: :///
.. _Errors: :///home/steck/error-index.html
.. _General: :///home/steck/general-index.html
.. _Cover: :///home/steck/index.html
.. _5.2  Typing Modules: :///home/steck/modules.html#sec232
.. _Documentation: :///documentation
.. _Options: :///home/steck/option-index.html
.. _xhtml valid: http://validator.w3.org/
.. _Table of contents: :///home/steck/toc.html
.. _Community: :///community
.. _webmaster: mailto:coq-www_@_inria.fr
.. _4.1: :///home/steck/cic.html#Terms



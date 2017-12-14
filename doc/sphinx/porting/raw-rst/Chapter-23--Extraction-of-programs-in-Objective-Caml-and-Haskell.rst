

+ `Home`_
+ `About Coq`_
+ `Get Coq`_
+ `Documentation`_
+ `Community`_

` `_ `The Coq Proof Assistant`_


Chapter 23 Extraction of programs in Objective Caml and Haskell
===============================================================


+ `23.1 Generating ML code`_
+ `23.2 Extraction options`_
+ `23.3 Differences between Coq and ML type systems`_
+ `23.4 Some examples`_


Jean-Christophe Filliâtre and Pierre Letouzey



We present here the Coq extraction commands, used to build certified
and relatively efficient functional programs, extracting them from
either Coq functions or Coq proofs of specifications. The functional
languages available as output are currently Objective Caml,Haskell and
Scheme. In the following, “ML” will be used (abusively) to refer to
any of the three.

Before using any of the commands or options described in this chapter,
the extraction framework should first be loaded explicitly via Require
Extraction, or via the more robustFrom Coq Require Extraction. Note
that in earlier versions of Coq, these commands and options were
directly available without any preliminary Require.
Coq < Require Extraction.
[Loading ML file extraction_plugin.cmxs ... done]



23.1 Generating ML code
-----------------------



The next two commands are meant to be used for rapid preview of
extraction. They both display extracted term(s) inside Coq.

:: Extraction qualid. Extraction of a constant or module in the Coq
  toplevel.
:: Recursive Extraction qualid 1 … qualid n . Recursive extraction of
  all the globals (or modules) qualid 1 … qualid n and all their
  dependencies in the Coq toplevel.


All the following commands produce real ML files. User can choose to
produce one monolithic file or one file per Coq library.

:: Extraction " *file*" qualid 1 … qualid n . Recursive extraction of
  all the globals (or modules) qualid 1 … qualid n and all their
  dependencies in one monolithic file *file*. Global and local
  identifiers are renamed according to the chosen ML language to fulfill
  its syntactic conventions, keeping original names as much as possible.
:: Extraction Library ident. Extraction of the whole Coq library
  ident.v to an ML moduleident.ml. In case of name clash, identifiers
  are here renamed using prefixes `coq_` or `Coq_` to ensure a session-
  independent renaming.
:: Recursive Extraction Library ident. Extraction of the Coq library
  ident.v and all other modules ident.v depends on.
:: Separate Extractionqualid 1 … qualid n . Recursive extraction of
  all the globals (or modules) qualid 1 … qualid n and all their
  dependencies, just as Extraction " *file*", but instead of producing
  one monolithic file, this command splits the produced code in separate
  ML files, one per corresponding Coq .v file. This command is hence
  quite similar to Recursive Extraction Library, except that only the
  needed parts of Coq libraries are extracted instead of the whole. The
  naming convention in case of name clash is the same one asExtraction
  Library: identifiers are here renamed using prefixes `coq_` or `Coq_`.


The following command is meant to help automatic testing of the
extraction, see for instance the test-suite directory in the Coq
sources.

:: Extraction TestCompile qualid 1 … qualid n . All the globals (or
  modules) qualid 1 … qualid n and all their dependencies are extracted
  to a temporary Ocaml file, just as inExtraction " *file*". Then this
  temporary file and its signature are compiled with the same Ocaml
  compiler used to builtCoq. This command succeeds only if the
  extraction and the Ocaml compilation succeed (and it fails if the
  current target language of the extraction is not Ocaml).



23.2 Extraction options
-----------------------


23.2.1 Setting the target language
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~



The ability to fix target language is the first and more important of
the extraction options. Default is Ocaml.

:: Extraction Language Ocaml.
:: Extraction Language Haskell.
:: Extraction Language Scheme.



23.2.2 Inlining and optimizations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Since Objective Caml is a strict language, the extracted code has to
be optimized in order to be efficient (for instance, when using
induction principles we do not want to compute all the recursive calls
but only the needed ones). So the extraction mechanism provides an
automatic optimization routine that will be called each time the user
want to generate Ocaml programs. The optimizations can be split in two
groups: the type-preserving ones – essentially constant inlining and
reductions – and the non type-preserving ones – some function
abstractions of dummy types are removed when it is deemed safe in
order to have more elegant types. Therefore some constants may not
appear in the resulting monolithic Ocaml program. In the case of
modular extraction, even if some inlining is done, the inlined
constant are nevertheless printed, to ensure session-independent
programs.

Concerning Haskell, type-preserving optimizations are less useful
because of laziness. We still make some optimizations, for example in
order to produce more readable code.

The type-preserving optimizations are controlled by the following Coq
options:

:: Unset Extraction Optimize.Default is Set. This controls all type-
  preserving optimizations made on the ML terms (mostly reduction of
  dummy beta/iota redexes, but also simplifications on Cases, etc). Put
  this option to Unset if you want a ML term as close as possible to the
  Coq term.
:: Set Extraction Conservative Types.Default is Unset. This controls
  the non type-preserving optimizations made on ML terms (which try to
  avoid function abstraction of dummy types). Turn this option to Set to
  make sure that e:t implies that e’:t’ where e’ and t’ are the
  extracted code of e and t respectively.
:: Set Extraction KeepSingleton.Default is Unset. Normally, when the
  extraction of an inductive type produces a singleton type (i.e. a type
  with only one constructor, and only one argument to this constructor),
  the inductive structure is removed and this type is seen as an alias
  to the inner type. The typical example is sig. This option allows
  disabling this optimization when one wishes to preserve the inductive
  structure of types.
:: Unset Extraction AutoInline.Default is Set. The extraction
  mechanism inlines the bodies of some defined constants, according to
  some heuristics like size of bodies, uselessness of some arguments,
  etc. Those heuristics are not always perfect; if you want to disable
  this feature, do it by Unset.
:: Extraction [Inline|NoInline] qualid 1 … qualid n .In addition to
  the automatic inline feature, you can tell to inline some more
  constants by the Extraction Inline command. Conversely, you can forbid
  the automatic inlining of some specific constants by the Extraction
  NoInline command. Those two commands enable a precise control of what
  is inlined and what is not.
:: Print Extraction Inline. Prints the current state of the table
  recording the custom inlinings declared by the two previous commands.
:: Reset Extraction Inline. Puts the table recording the custom
  inlinings back to empty.



Inlining and printing of a constant declaration.
++++++++++++++++++++++++++++++++++++++++++++++++

A user can explicitly ask for a constant to be extracted by two means:


+ by mentioning it on the extraction command line
+ by extracting the whole Coq module of this constant.


In both cases, the declaration of this constant will be present in the
produced file. But this same constant may or may not be inlined in the
following terms, depending on the automatic/custom inlining mechanism.

For the constants non-explicitly required but needed for dependency
reasons, there are two cases:


+ If an inlining decision is taken, whether automatically or not, all
  occurrences of this constant are replaced by its extracted body, and
  this constant is not declared in the generated file.
+ If no inlining decision is taken, the constant is normally declared
  in the produced file.



23.2.3 Extra elimination of useless arguments
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The following command provides some extra manual control on the code
elimination performed during extraction, in a way which is independent
but complementary to the main elimination principles of extraction
(logical parts and types).

:: Extraction Implicit qualid [ ident 1 … ident n ].This experimental
  command allows declaring some arguments ofqualid as implicit, i.e.
  useless in extracted code and hence to be removed by extraction. Here
  qualid can be any function or inductive constructor, and ident i are
  the names of the concerned arguments. In fact, an argument can also be
  referred by a number indicating its position, starting from 1.


When an actual extraction takes place, an error is normally raised if
theExtraction Implicit declarations cannot be honored, that is if any
of the implicited variables still occurs in the final code. This
behavior can be relaxed via the following option:

:: Unset Extraction SafeImplicits.Default is Set. When this option is
  Unset, a warning is emitted instead of an error if some implicited
  variables still occur in the final code of an extraction. This way,
  the extracted code may be obtained nonetheless and reviewed manually
  to locate the source of the issue (in the code, some comments mark the
  location of these remaining implicited variables). Note that this
  extracted code might not compile or run properly, depending of the use
  of these remaining implicited variables.



23.2.4 Realizing axioms
~~~~~~~~~~~~~~~~~~~~~~~



Extraction will fail if it encounters an informative axiom not
realized (see Section 23.2.4). A warning will be issued if it
encounters a logical axiom, to remind the user that inconsistent
logical axioms may lead to incorrect or non-terminating extracted
terms.

It is possible to assume some axioms while developing a proof. Since
these axioms can be any kind of proposition or object or type, they
may perfectly well have some computational content. But a program must
be a closed term, and of course the system cannot guess the program
which realizes an axiom. Therefore, it is possible to tell the system
what ML term corresponds to a given axiom.



:: Extract Constant qualid => string. Give an ML extraction for the
  given constant. The string may be an identifier or a quoted string.
:: Extract Inlined Constant qualid => string. Same as the previous
  one, except that the given ML terms will be inlined everywhere instead
  of being declared via a let.


Note that the Extract Inlined Constant command is sugar for an Extract
Constant followed by a Extraction Inline. Hence a Reset Extraction
Inline will have an effect on the realized and inlined axiom.

Of course, it is the responsibility of the user to ensure that the ML
terms given to realize the axioms do have the expected types. In fact,
the strings containing realizing code are just copied to the extracted
files. The extraction recognizes whether the realized axiom should
become a ML type constant or a ML object declaration.


Example:
Coq < Axiom X:Set.

Coq < Axiom x:X.

Coq < Extract Constant X => "int".

Coq < Extract Constant x => "0".

Notice that in the case of type scheme axiom (i.e. whose type is an
arity, that is a sequence of product finished by a sort), then some
type variables have to be given. The syntax is then:

:: Extract Constant qualid string 1 … string n => string.


The number of type variables is checked by the system.


Example:
Coq < Axiom Y : Set -> Set -> Set.

Coq < Extract Constant Y "'a" "'b" => " 'a*'b ".

Realizing an axiom via Extract Constant is only useful in the case of
an informative axiom (of sort Type or Set). A logical axiom have no
computational content and hence will not appears in extracted terms.
But a warning is nonetheless issued if extraction encounters a logical
axiom. This warning reminds user that inconsistent logical axioms may
lead to incorrect or non-terminating extracted terms.

If an informative axiom has not been realized before an extraction, a
warning is also issued and the definition of the axiom is filled with
an exception labeled AXIOM TO BE REALIZED. The user must then search
these exceptions inside the extracted file and replace them by real
code.



The system also provides a mechanism to specify ML terms for inductive
types and constructors. For instance, the user may want to use the ML
native boolean type instead of Coq one. The syntax is the following:

:: Extract Inductive qualid => string [ string … string ]
  optstring.Give an ML extraction for the given inductive type. You must
  specify extractions for the type itself (first string) and all its
  constructors (between square brackets). If given, the final optional
  string should contain a function emulating pattern-matching over this
  inductive type. If this optional string is not given, the ML
  extraction must be an ML inductive datatype, and the native pattern-
  matching of the language will be used.


For an inductive type with k constructor, the function used to emulate
the match should expect (k+1) arguments, first the k branches in
functional form, and then the inductive element to destruct. For
instance, the match branch `| S n => foo` gives the functional form
`(fun n -> foo)`. Note that a constructor with no argument is
considered to have one unit argument, in order to block early
evaluation of the branch: `| O => bar` leads to the functional form
`(fun () -> bar)`. For instance, when extracting nat into int, the
code to provide has type:(unit->’a)->(int->’a)->int->’a.

As for Extract Inductive, this command should be used with care:


+ The ML code provided by the user is currently *not* checked at all
  by extraction, even for syntax errors.
+ Extracting an inductive type to a pre-existing ML inductive type is
  quite sound. But extracting to a general type (by providing an ad-hoc
  pattern-matching) will often *not* be fully rigorously correct. For
  instance, when extracting nat to Ocaml’s int, it is theoretically
  possible to build nat values that are larger than Ocaml’s max_int. It
  is the user’s responsibility to be sure that no overflow or other bad
  events occur in practice.
+ Translating an inductive type to an ML type does *not* magically
  improve the asymptotic complexity of functions, even if the ML type is
  an efficient representation. For instance, when extractingnat to
  Ocaml’s int, the function mult stays quadratic. It might be
  interesting to associate this translation with some specific Extract
  Constant when primitive counterparts exist.



Example: Typical examples are the following:
Coq < Extract Inductive unit => "unit" [ "()" ].

Coq < Extract Inductive bool => "bool" [ "true" "false" ].

Coq < Extract Inductive sumbool => "bool" [ "true" "false" ].

If an inductive constructor or type has arity 2 and the corresponding
string is enclosed by parenthesis, then the rest of the string is used
as infix constructor or type.
Coq < Extract Inductive list => "list" [ "[]" "(::)" ].

Coq < Extract Inductive prod => "(*)" [ "(,)" ].

As an example of translation to a non-inductive datatype, let’s
turnnat into Ocaml’s int (see caveat above):
Coq < Extract Inductive nat => int [ "0" "succ" ]
"(fun fO fS n -> if n=0 then fO () else fS (n-1))".



23.2.5 Avoiding conflicts with existing filenames
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~



When using Extraction Library, the names of the extracted files
directly depends from the names of the Coq files. It may happen that
these filenames are in conflict with already existing files, either in
the standard library of the target language or in other code that is
meant to be linked with the extracted code. For instance the module
List exists both in Coq and in Ocaml. It is possible to instruct the
extraction not to use particular filenames.

:: Extraction Blacklist ident … ident. Instruct the extraction to
  avoid using these names as filenames for extracted code.
:: Print Extraction Blacklist. Show the current list of filenames the
  extraction should avoid.
:: Reset Extraction Blacklist. Allow the extraction to use any
  filename.


For Ocaml, a typical use of these commands isExtraction Blacklist
String List.


23.3 Differences between Coq and ML type systems
------------------------------------------------

Due to differences between Coq and ML type systems, some extracted
programs are not directly typable in ML. We now solve this problem (at
least in Ocaml) by adding when needed some unsafe casting Obj.magic,
which give a generic type ’a to any term.

For example, here are two kinds of problem that can occur:


+ If some part of the program is *very* polymorphic, there may be no
  ML type for it. In that case the extraction to ML works alright but
  the generated code may be refused by the ML type-checker. A very well
  known example is the *distr-pair* function:

::

    Definition dp := 
     fun (A B:Set)(x:A)(y:B)(f:forall C:Set, C->C) => (f A x, f B y).

  In Ocaml, for instance, the direct extracted term would be

::

    let dp x y f = Pair((f () x),(f () y))

  and would have type

::

    dp : 'a -> 'a -> (unit -> 'a -> 'b) -> ('b,'b) prod

  which is not its original type, but a restriction.We now produce the
  following correct version:

::

    let dp x y f = Pair ((Obj.magic f () x), (Obj.magic f () y))


+ Some definitions of Coq may have no counterpart in ML. This happens
  when there is a quantification over types inside the type of a
  constructor; for example:

::

    Inductive anything : Type := dummy : forall A:Set, A -> anything.

  which corresponds to the definition of an ML dynamic type. In Ocaml,
  we must cast any argument of the constructor dummy.


Even with those unsafe castings, you should never get error like
“segmentation fault”. In fact even if your program may seem ill-typed
to the Ocaml type-checker, it can’t go wrong: it comes from a Coq
well-typed terms, so for example inductives will always have the
correct number of arguments, etc.

More details about the correctness of the extracted programs can be
found in [`99`_].

We have to say, though, that in most “realistic” programs, these
problems do not occur. For example all the programs of Coq library are
accepted by Caml type-checker without any Obj.magic (see examples
below).


23.4 Some examples
------------------

We present here two examples of extractions, taken from the Coq
Standard Library. We choose Objective Caml as target language, but all
can be done in the other dialects with slight modifications. We then
indicate where to find other examples and tests of Extraction.


23.4.1 A detailed example: Euclidean division
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The file Euclid contains the proof of Euclidean division (theorem
eucl_dev). The natural numbers defined in the example files are unary
integers defined by two constructors O and S:
Coq < Inductive nat : Set :=
| O : nat
| S : nat -> nat.

This module contains a theorem eucl_dev, whose type is

::

    forall b:nat, b > 0 -> forall a:nat, diveucl a b


where diveucl is a type for the pair of the quotient and the modulo,
plus some logical assertions that disappear during extraction. We can
now extract this program to Objective Caml:
Coq < Require Extraction.

Coq < Require Import Euclid Wf_nat.

Coq < Extraction Inline gt_wf_rec lt_wf_rec induction_ltof2.

Coq < Recursive Extraction eucl_dev.
type nat =
| O
| S of nat
type sumbool =
| Left
| Right
(** val sub : nat -> nat -> nat **)
let rec sub n m =
match n with
| O -> n
| S k -> (match m with
| O -> n
| S l -> sub k l)
(** val le_lt_dec : nat -> nat -> sumbool **)
let rec le_lt_dec n m =
match n with
| O -> Left
| S n0 -> (match m with
| O -> Right
| S m0 -> le_lt_dec n0 m0)
(** val le_gt_dec : nat -> nat -> sumbool **)
let le_gt_dec =
le_lt_dec
type diveucl =
| Divex of nat * nat
(** val eucl_dev : nat -> nat -> diveucl **)
let rec eucl_dev n m =
let s = le_gt_dec n m in
(match s with
| Left ->
let d = let y = sub m n in eucl_dev n y in
let Divex (q, r) = d in Divex ((S q), r)
| Right -> Divex (O, m))

The inlining of gt_wf_rec and others is not mandatory. It only
enhances readability of extracted code. You can then copy-paste the
output to a file euclid.ml or let Coq do it for you with the following
command:

::

    Extraction "euclid" eucl_dev.


Let us play the resulting program:

::

    # #use "euclid.ml";;
    type nat = O | S of nat
    type sumbool = Left | Right
    val minus : nat -> nat -> nat = <fun>
    val le_lt_dec : nat -> nat -> sumbool = <fun>
    val le_gt_dec : nat -> nat -> sumbool = <fun>
    type diveucl = Divex of nat * nat
    val eucl_dev : nat -> nat -> diveucl = <fun>
    # eucl_dev (S (S O)) (S (S (S (S (S O)))));;
    - : diveucl = Divex (S (S O), S O)


It is easier to test on Objective Caml integers:

::

    # let rec nat_of_int = function 0 -> O | n -> S (nat_of_int (n-1));;
    val nat_of_int : int -> nat = <fun>
    # let rec int_of_nat = function O -> 0 | S p -> 1+(int_of_nat p);;
    val int_of_nat : nat -> int = <fun>
    # let div a b = 
         let Divex (q,r) = eucl_dev (nat_of_int b) (nat_of_int a)
         in (int_of_nat q, int_of_nat r);;
    val div : int -> int -> int * int = <fun>
    # div 173 15;;
    - : int * int = (11, 8)


Note that these nat_of_int and int_of_nat are now available via a mere
Require Import ExtrOcamlIntConv and then adding these functions to the
list of functions to extract. This fileExtrOcamlIntConv.v and some
others in plugins/extraction/ are meant to help building concrete
program via extraction.


23.4.2 Extraction’s horror museum
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Some pathological examples of extraction are grouped in the file
test-suite/success/extraction.v of the sources of Coq.


23.4.3 Users’ Contributions
~~~~~~~~~~~~~~~~~~~~~~~~~~~

Several of the Coq Users’ Contributions use extraction to produce
certified programs. In particular the following ones have an automatic
extraction test:


+ additions
+ bdds
+ canon-bdds
+ chinese
+ continuations
+ coq-in-coq
+ exceptions
+ firing-squad
+ founify
+ graphs
+ higman-cf
+ higman-nw
+ hardware
+ multiplier
+ search-trees
+ stalmarck


continuations and multiplier are a bit particular. They are examples
of developments where Obj.magic are needed. This is probably due to an
heavy use of impredicativity. After compilation, those two examples
run nonetheless, thanks to the correction of the extraction [`99`_].



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
.. _Tactics: :///home/steck/tactic-index.html
.. _Options: :///home/steck/option-index.html
.. _23.2  Extraction options: :///home/steck/extraction.html#sec815
.. _About Coq: :///about-coq
.. _CSS valid: http://jigsaw.w3.org/css-validator/
.. _The Coq Proof Assistant: :///
.. _Errors: :///home/steck/error-index.html
.. _23.4  Some examples: :///home/steck/extraction.html#sec823
.. _Cover: :///home/steck/index.html
.. _General: :///home/steck/general-index.html
.. _99: :///home/steck/biblio.html#Let02
.. _Documentation: :///documentation
.. _xhtml valid: http://validator.w3.org/
.. _ and ML type systems: :///home/steck/extraction.html#sec822
.. _23.1  Generating ML code: :///home/steck/extraction.html#sec814
.. _Community: :///community
.. _webmaster: mailto:coq-www_@_inria.fr
.. _Table of contents: :///home/steck/toc.html



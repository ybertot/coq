

+ `Home`_
+ `About Coq`_
+ `Get Coq`_
+ `Documentation`_
+ `Community`_

` `_ `The Coq Proof Assistant`_


Chapter 6 Vernacular commands
=============================


+ `6.1 Displaying`_
+ `6.2 Flags, Options and Tables`_
+ `6.3 Requests to the environment`_
+ `6.4 Loading files`_
+ `6.5 Compiled files`_
+ `6.6 Loadpath`_
+ `6.7 Backtracking`_
+ `6.8 Quitting and debugging`_
+ `6.9 Controlling display`_
+ `6.10 Controlling the reduction strategies and the conversion
  algorithm`_
+ `6.11 Controlling the locality of commands`_




6.1 Displaying
--------------


6.1.1 Print qualid.
~~~~~~~~~~~~~~~~~~~

This command displays on the screen information about the declared or
defined object referred by qualid.


Error messages:


#. qualid not a defined object



Variants:


#. Print Term qualid. This is a synonym to Print qualid when qualid
   denotes a global constant.
#. About qualid. This displays various information about the object
   denoted by qualid: its kind (module, constant, assumption, inductive,
   constructor, abbreviation, …), long name, type, implicit arguments and
   argument scopes. It does not print the body of definitions or proofs.



6.1.2 Print All.
~~~~~~~~~~~~~~~~

This command displays information about the current state of the
environment, including sections and modules.


Variants:


#. Inspect num. This command displays the num last objects of the
   current environment, including sections and modules.
#. Print Section ident. should correspond to a currently open section,
   this command displays the objects defined since the beginning of this
   section.



6.2 Flags, Options and Tables
-----------------------------

Coq configurability is based on flags (e.g. Set Printing All in
Section `2.9`_), options (e.g. Set Printing Widthinteger in Section
6.9.6), or tables (e.g. Add Printing Record ident, in Section
`2.2.4`_). The names of flags, options and tables are made of non-
empty sequences of identifiers (conventionally with capital initial
letter). The general commands handling flags, options and tables are
given below.


6.2.1 Set flag.
~~~~~~~~~~~~~~~

This command switches flag on. The original state offlag is restored
when the current module ends.


Variants:


#. Local Set flag. This command switches flag on. The original state
   offlag is restored when the current *section* ends.
#. Global Set flag. This command switches flag on. The original state
   offlag is *not* restored at the end of the module. Additionally, if
   set in a file, flag is switched on when the file isRequire-d.



6.2.2 Unset flag.
~~~~~~~~~~~~~~~~~

This command switches flag off. The original state of flag is restored
when the current module ends.


Variants:


#. Local Unset flag. This command switches flag off. The original
   state of flag is restored when the current *section* ends.
#. Global Unset flag. This command switches flag off. The original
   state offlag is *not* restored at the end of the module. Additionally,
   if set in a file, flag is switched off when the file isRequire-d.



6.2.3 Test flag.
~~~~~~~~~~~~~~~~

This command prints whether flag is on or off.


6.2.4 Set option value.
~~~~~~~~~~~~~~~~~~~~~~~

This command sets option to value. The original value ofoption is
restored when the current module ends.


Variants:


#. Local Set option value. This command sets option to value. The
   original value ofoption is restored at the end of the module.
#. Global Set option value. This command sets option to value. The
   original value ofoption is *not* restored at the end of the module.
   Additionally, if set in a file, option is set to value when the file
   isRequire-d.



6.2.5 Unset option.
~~~~~~~~~~~~~~~~~~~

This command resets option to its default value.


Variants:


#. Local Unset option. This command resets option to its default
   value. The original state of option is restored when the current
   *section* ends.
#. Global Unset option. This command resets option to its default
   value. The original state ofoption is *not* restored at the end of the
   module. Additionally, if unset in a file, option is reset to its
   default value when the file isRequire-d.



6.2.6 Test option.
~~~~~~~~~~~~~~~~~~

This command prints the current value of option.


6.2.7 Tables
~~~~~~~~~~~~

The general commands for tables are Add table value, Remove table
value, Testtable, Test table for value andPrint Table table.


6.2.8 Print Options.
~~~~~~~~~~~~~~~~~~~~

This command lists all available flags, options and tables.


Variants:


#. Print Tables. This is a synonymous of Print Options.



6.3 Requests to the environment
-------------------------------


6.3.1 Check term.
~~~~~~~~~~~~~~~~~

This command displays the type of term. When called in proof mode, the
term is checked in the local context of the current subgoal.


Variants:


#. selector: Check term. specifies on which subgoal to perform typing
   (see Section `8.1`_).



6.3.2 Eval convtactic in term.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command performs the specified reduction on term, and displays
the resulting term with its type. The term to be reduced may depend on
hypothesis introduced in the first subgoal (if a proof is in
progress).


See also: Section `8.7`_.


6.3.3 Compute term.
~~~~~~~~~~~~~~~~~~~

This command performs a call-by-value evaluation of term by using the
bytecode-based virtual machine. It is a shortcut forEval vm_compute in
term.


See also: Section `8.7`_.


6.3.4 Extraction term.
~~~~~~~~~~~~~~~~~~~~~~

This command displays the extracted term fromterm. The extraction is
processed according to the distinction between Set and Prop; that is
to say, between logical and computational content (see Section
`4.1.1`_). The extracted term is displayed in Objective Caml syntax,
where global identifiers are still displayed as in Coq terms.


Variants:


#. Recursive Extraction qualid 1 … qualid n . Recursively extracts all
   the material needed for the extraction of global qualid 1 , …, qualid
   n .



See also: Chapter `23`_.


6.3.5 Print Assumptions qualid.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~



This commands display all the assumptions (axioms, parameters and
variables) a theorem or definition depends on. Especially, it informs
on the assumptions with respect to which the validity of a theorem
relies.


Variants:


#. Print Opaque Dependencies qualid. Displays the set of opaque
   constants qualid relies on in addition to the assumptions.
#. Print Transparent Dependencies qualid. Displays the set of
   transparent constants qualid relies on in addition to the assumptions.
#. Print All Dependencies qualid. Displays all assumptions and
   constants qualid relies on.



6.3.6 Search qualid.
~~~~~~~~~~~~~~~~~~~~

This command displays the name and type of all objects (hypothesis of
the current goal, theorems, axioms, etc) of the current context whose
statement contains qualid. This command is useful to remind the user
of the name of library lemmas.


Error messages:


#. The reference qualid was not found in the current environment There
   is no constant in the environment named qualid.



Variants:


#. Search string.If string is a valid identifier, this command
   displays the name and type of all objects (theorems, axioms, etc) of
   the current context whose name contains string. If string is a
   notation’s string denoting some reference qualid (referred to by its
   main symbol as in `"+"` or by its notation’s string as in `"_ + _"` or
   `"_ 'U' _"`, see Section `12.1`_), the command works like
   Searchqualid.
#. Search string%key.The string string must be a notation or the main
   symbol of a notation which is then interpreted in the scope bound to
   the delimiting keykey (see Section `12.2.2`_).
#. Search term_pattern.This searches for all statements or types of
   definition that contains a subterm that matches the pattern
   term_pattern (holes of the pattern are either denoted by “_” or by
   “?ident” when non linear patterns are expected).
#. Search [-]term_pattern-string … [-]term_pattern-string. where
   term_pattern-string is aterm_pattern or a string, or a string followed
   by a scope delimiting key %key.This generalization of Search searches
   for all objects whose statement or type contains a subterm matching
   term_pattern (orqualid if string is the notation for a reference
   qualid) and whose name contains all string of the request that
   correspond to valid identifiers. If a term_pattern or a string is
   prefixed by “-”, the search excludes the objects that mention that
   term_pattern or thatstring.
#. Search term_pattern-string … term_pattern-stringinside module 1 …
   module n .This restricts the search to constructions defined in
   modulesmodule 1 … module n .
#. Search term_pattern-string … term_pattern-string outside module 1
   ...module n .This restricts the search to constructions not defined in
   modulesmodule 1 … module n .
#. selector: Search [-]term_pattern-string … [-]term_pattern-
   string.This specifies the goal on which to search hypothesis (see
   Section `8.1`_). By default the 1st goal is searched. This variant can
   be combined with other variants presented here.



Examples:
Coq < Require Import ZArith.

Coq < Search Z.mul Z.add "distr".
Z.mul_add_distr_l:
forall n m p : Z, (n * (m + p))%Z = (n * m + n * p)%Z
Z.mul_add_distr_r:
forall n m p : Z, ((n + m) * p)%Z = (n * p + m * p)%Z
fast_Zmult_plus_distr_l:
forall (n m p : Z) (P : Z -> Prop),
P (n * p + m * p)%Z -> P ((n + m) * p)%Z

Coq < Search "+"%Z "*"%Z "distr" -positive -Prop.
Z.mul_add_distr_l:
forall n m p : Z, (n * (m + p))%Z = (n * m + n * p)%Z
Z.mul_add_distr_r:
forall n m p : Z, ((n + m) * p)%Z = (n * p + m * p)%Z

Coq < Search (?x * _ + ?x * _)%Z outside OmegaLemmas.
Z.mul_add_distr_l:
forall n m p : Z, (n * (m + p))%Z = (n * m + n * p)%Z


Warning: Up to Coq version 8.4, Search had the behavior of current
SearchHead and the behavior of current Search was obtained with
command SearchAbout. For compatibility, the deprecated name
SearchAbout can still be used as a synonym of Search. For
compatibility, the list of objects to search when using SearchAbout
may also be enclosed by optional[ ] delimiters.


6.3.7 SearchHead term.
~~~~~~~~~~~~~~~~~~~~~~

This command displays the name and type of all hypothesis of the
current goal (if any) and theorems of the current context whose
statement’s conclusion has the form (term t1 .. tn). This command is
useful to remind the user of the name of library lemmas.
Coq < SearchHead le.
le_n: forall n : nat, n <= n
le_0_n: forall n : nat, 0 <= n
le_S: forall n m : nat, n <= m -> n <= S m
le_pred: forall n m : nat, n <= m -> Nat.pred n <= Nat.pred m
le_n_S: forall n m : nat, n <= m -> S n <= S m
le_S_n: forall n m : nat, S n <= S m -> n <= m

Coq < SearchHead (@eq bool).
andb_true_intro:
forall b1 b2 : bool, b1 = true /\ b2 = true -> (b1 && b2)%bool = true


Variants:


#. SearchHead term inside module 1 … module n .This restricts the
   search to constructions defined in modulesmodule 1 … module n .
#. SearchHead term outside module 1 … module n .This restricts the
   search to constructions not defined in modulesmodule 1 … module n .
   Error messages:

    #. Module/section module not found No module module has been required
       (see Section 6.5.1).

#. selector: SearchHead term.This specifies the goal on which to
   search hypothesis (see Section `8.1`_). By default the 1st goal is
   searched. This variant can be combined with other variants presented
   here.



Warning: Up to Coq version 8.4, SearchHead was named Search.


6.3.8 SearchPattern term.
~~~~~~~~~~~~~~~~~~~~~~~~~

This command displays the name and type of all hypothesis of the
current goal (if any) and theorems of the current context whose
statement’s conclusion or last hypothesis and conclusion matches the
expressionterm where holes in the latter are denoted by “_”. It is a
variant of Searchterm_pattern that does not look for subterms but
searches for statements whose conclusion has exactly the expected
form, or whose statement finishes by the given series of
hypothesis/conclusion.
Coq < Require Import Arith.

Coq < SearchPattern (_ + _ = _ + _).
Nat.add_comm: forall n m : nat, n + m = m + n
plus_Snm_nSm: forall n m : nat, S n + m = n + S m
Nat.add_succ_comm: forall n m : nat, S n + m = n + S m
Nat.add_shuffle3: forall n m p : nat, n + (m + p) = m + (n + p)
plus_assoc_reverse: forall n m p : nat, n + m + p = n + (m + p)
Nat.add_assoc: forall n m p : nat, n + (m + p) = n + m + p
Nat.add_shuffle0: forall n m p : nat, n + m + p = n + p + m
f_equal2_plus:
forall x1 y1 x2 y2 : nat, x1 = y1 -> x2 = y2 -> x1 + x2 = y1 + y2
Nat.add_shuffle2: forall n m p q : nat, n + m + (p + q) = n + q + (m +
p)
Nat.add_shuffle1: forall n m p q : nat, n + m + (p + q) = n + p + (m +
q)

Coq < SearchPattern (nat -> bool).
Nat.odd: nat -> bool
Init.Nat.odd: nat -> bool
Nat.even: nat -> bool
Init.Nat.even: nat -> bool
Init.Nat.testbit: nat -> nat -> bool
Nat.leb: nat -> nat -> bool
Nat.eqb: nat -> nat -> bool
Init.Nat.eqb: nat -> nat -> bool
Nat.ltb: nat -> nat -> bool
Nat.testbit: nat -> nat -> bool
Init.Nat.leb: nat -> nat -> bool
Init.Nat.ltb: nat -> nat -> bool
BinNat.N.testbit_nat: BinNums.N -> nat -> bool
BinPosDef.Pos.testbit_nat: BinNums.positive -> nat -> bool
BinPos.Pos.testbit_nat: BinNums.positive -> nat -> bool
BinNatDef.N.testbit_nat: BinNums.N -> nat -> bool

Coq < SearchPattern (forall l : list _, _ l l).
List.incl_refl: forall (A : Type) (l : list A), List.incl l l
List.lel_refl: forall (A : Type) (l : list A), List.lel l l

Patterns need not be linear: you can express that the same expression
must occur in two places by using pattern variables ‘?ident”.
Coq < SearchPattern (?X1 + _ = _ + ?X1).
Nat.add_comm: forall n m : nat, n + m = m + n


Variants:


#. SearchPattern term insidemodule 1 … module n .This restricts the
   search to constructions defined in modulesmodule 1 … module n .
#. SearchPattern term outside module 1 … module n .This restricts the
   search to constructions not defined in modulesmodule 1 … module n .
#. selector: SearchPattern term.This specifies the goal on which to
   search hypothesis (see Section `8.1`_). By default the 1st goal is
   searched. This variant can be combined with other variants presented
   here.



6.3.9 SearchRewrite term.
~~~~~~~~~~~~~~~~~~~~~~~~~

This command displays the name and type of all hypothesis of the
current goal (if any) and theorems of the current context whose
statement’s conclusion is an equality of which one side matches the
expression term. Holes in term are denoted by “_”.
Coq < Require Import Arith.

Coq < SearchRewrite (_ + _ + _).
Nat.add_shuffle0: forall n m p : nat, n + m + p = n + p + m
plus_assoc_reverse: forall n m p : nat, n + m + p = n + (m + p)
Nat.add_assoc: forall n m p : nat, n + (m + p) = n + m + p
Nat.add_shuffle1: forall n m p q : nat, n + m + (p + q) = n + p + (m +
q)
Nat.add_shuffle2: forall n m p q : nat, n + m + (p + q) = n + q + (m +
p)
Nat.add_carry_div2:
forall (a b : nat) (c0 : bool),
(a + b + Nat.b2n c0) / 2 =
a / 2 + b / 2 +
Nat.b2n
(Nat.testbit a 0 && Nat.testbit b 0
|| c0 && (Nat.testbit a 0 || Nat.testbit b 0))


Variants:


#. SearchRewrite term insidemodule 1 … module n .This restricts the
   search to constructions defined in modulesmodule 1 … module n .
#. SearchRewrite term outside module 1 … module n .This restricts the
   search to constructions not defined in modulesmodule 1 … module n .
#. selector: SearchRewrite term.This specifies the goal on which to
   search hypothesis (see Section `8.1`_). By default the 1st goal is
   searched. This variant can be combined with other variants presented
   here.



Nota Bene:
``````````

For the Search, SearchHead, SearchPattern andSearchRewrite queries, it
is possible to globally filter the search results via the commandAdd
Search Blacklist "substring1". A lemma whose fully-qualified name
contains any of the declared substrings will be removed from the
search results. The default blacklisted substrings are "_subproof"
"Private_". The command Remove Search Blacklist ... allows expunging
this blacklist.


6.3.10 Locate qualid.
~~~~~~~~~~~~~~~~~~~~~

This command displays the full name of objects whose name is a prefix
of the qualified identifier qualid, and consequently the Coq module in
which they are defined. It searches for objects from the different
qualified name spaces ofCoq: terms, modules, Ltac, etc.
Coq < Locate nat.
Inductive Coq.Init.Datatypes.nat

Coq < Locate Datatypes.O.
Constructor Coq.Init.Datatypes.O
(shorter name to refer to it in current context is O)

Coq < Locate Init.Datatypes.O.
Constructor Coq.Init.Datatypes.O
(shorter name to refer to it in current context is O)

Coq < Locate Coq.Init.Datatypes.O.
Constructor Coq.Init.Datatypes.O
(shorter name to refer to it in current context is O)

Coq < Locate I.Dont.Exist.
No object of suffix I.Dont.Exist


Variants:


#. Locate Term qualid. As Locate but restricted to terms.
#. Locate Module qualid. As Locate but restricted to modules.
#. Locate Ltac qualid. As Locate but restricted to tactics.



See also: Section `12.1.10`_


6.4 Loading files
-----------------

Coq offers the possibility of loading different parts of a whole
development stored in separate files. Their contents will be loaded as
if they were entered from the keyboard. This means that the loaded
files are ASCII files containing sequences of commands for Coq’s
toplevel. This kind of file is called a *script* forCoq. The standard
(and default) extension ofCoq’s script files is .v.


6.4.1 Load ident.
~~~~~~~~~~~~~~~~~

This command loads the file named ident.v, searching successively in
each of the directories specified in the *loadpath*. (see Section
`2.6.3`_)


Variants:


#. Load string. Loads the file denoted by the string string, where
   string is any complete filename. Then the `~` and .. abbreviations are
   allowed as well as shell variables. If no extension is specified, Coq
   will use the default extension .v
#. Load Verbose ident., Load Verbose string Display, while loading,
   the answers of Coq to each command (including tactics) contained in
   the loaded file See also: Section 6.9.1



Error messages:


#. Can’t find file ident on loadpath



6.5 Compiled files
------------------

This section describes the commands used to load compiled files (see
Chapter `14`_ for documentation on how to compile a file). A compiled
file is a particular case of module called *library file*.


6.5.1 Require qualid.
~~~~~~~~~~~~~~~~~~~~~

This command looks in the loadpath for a file containing module qualid
and adds the corresponding module to the environment of Coq. As
library files have dependencies in other library files, the command
Require qualid recursively requires all library files the module
qualid depends on and adds the corresponding modules to the
environment of Coq too. Coq assumes that the compiled files have been
produced by a valid Coq compiler and their contents are then not
replayed nor rechecked.

To locate the file in the file system, qualid is decomposed under the
form dirpath.ident and the file ident.vo is searched in the physical
directory of the file system that is mapped in Coq loadpath to the
logical path dirpath (see Section `2.6.3`_). The mapping between
physical directories and logical names at the time of requiring the
file must be consistent with the mapping used to compile the file. If
several files match, one of them is picked in an unspecified fashion.


Variants:


#. Require Import qualid. This loads and declares the module qualid
   and its dependencies then imports the contents of qualid as described
   in Section `2.5.8`_.It does not import the modules on which qualid
   depends unless these modules were itself required in module qualid
   using Require Export, as described below, or recursively required
   through a sequence of Require Export.If the module required has
   already been loaded, Require Importqualid simply imports it, as Import
   qualid would.
#. Require Export qualid.This command acts as Require Import qualid,
   but if a further module, say A, contains a command Require Export B,
   then the command Require Import A also imports the module B.
#. Require [Import | Export] qualid 1 … qualid n .This loads the
   modules qualid 1 , …, qualid n and their recursive dependencies. If
   Import or Export is given, it also imports qualid 1 , …, qualid n and
   all the recursive dependencies that were marked or transitively marked
   as Export.
#. From dirpath Require qualid.This command acts as Require, but picks
   any library whose absolute name is of the form dirpath.dirpath’.qualid
   for some dirpath’. This is useful to ensure that the qualid library
   comes from a given package by making explicit its absolute root.



Error messages:


#. Cannot load qualid: no physical path bound to dirpath
#. Cannot find library foo in loadpathThe command did not find the
   file foo.vo. Either foo.v exists but is not compiled or foo.vo is in a
   directory which is not in your LoadPath (see Section `2.6.3`_).
#. Compiled library ident.vo makes inconsistent assumptions over
   library qualidThe command tried to load library file ident.vo that
   depends on some specific version of library qualid which is not the
   one already loaded in the current Coq session. Probably ident.v was
   not properly recompiled with the last version of the file containing
   module qualid.
#. Bad magic number The file ident.vo was found but either it is not a
   Coq compiled module, or it was compiled with an older and incompatible
   version of Coq.
#. The file ident.vo contains library dirpath and not library
   dirpath’The library file dirpath’ is indirectly required by the
   Require command but it is bound in the current loadpath to the
   fileident.vo which was bound to a different library name dirpath at
   the time it was compiled.
#. Require is not allowed inside a module or a module typeThis command
   is not allowed inside a module or a module type being defined. It is
   meant to describe a dependency between compilation units. Note however
   that the commands Import and Export alone can be used inside modules
   (see Section `2.5.8`_).



See also: Chapter `14`_


6.5.2 Print Libraries.
~~~~~~~~~~~~~~~~~~~~~~

This command displays the list of library files loaded in the
currentCoq session. For each of these libraries, it also tells if it
is imported.


6.5.3 Declare ML Module string 1 .. string n .
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This commands loads the Objective Caml compiled files string 1 …string
n (dynamic link). It is mainly used to load tactics dynamically. The
files are searched into the current Objective Caml loadpath (see the
command Add ML Path in the Section `2.6.3`_). Loading of Objective
Caml files is only possible under the bytecode version of coqtop (i.e.
coqtop.byte, see chapter `14`_), or when Coq has been compiled with a
version ofObjective Caml that supports native Dynlink (≥ 3.11).


Variants:


#. Local Declare ML Module string 1 .. string n . This variant is not
   exported to the modules that import the module where they occur, even
   if outside a section.



Error messages:


#. File not found on loadpath : string
#. Loading of ML object file forbidden in a native Coq



6.5.4 Print ML Modules.
~~~~~~~~~~~~~~~~~~~~~~~

This print the name of all Objective Caml modules loaded with Declare
ML Module. To know from where these module were loaded, the user
should use the command Locate File (see Section 6.6.10)


6.6 Loadpath
------------

Loadpaths are preferably managed using Coq command line options (see
Section `2.6.3`_) but there remain vernacular commands to manage them
for practical purposes. Such commands are only meant to be issued in
the toplevel, and using them in source files is discouraged.


6.6.1 Pwd.
~~~~~~~~~~

This command displays the current working directory.


6.6.2 Cd string.
~~~~~~~~~~~~~~~~

This command changes the current directory according to string which
can be any valid path.


Variants:


#. Cd. Is equivalent to Pwd.



6.6.3 Add LoadPath string as dirpath.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command is equivalent to the command line option -Q
stringdirpath. It adds the physical directory string to the current
Coq loadpath and maps it to the logical directory dirpath.


Variants:


#. Add LoadPath string. Performs as Add LoadPath string as dirpath but
   for the empty directory path.



6.6.4 Add Rec LoadPath string as dirpath.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command is equivalent to the command line option -R
stringdirpath. It adds the physical directory string and all its
subdirectories to the current Coq loadpath.


Variants:


#. Add Rec LoadPath string. Works as Add Rec LoadPath string as
   dirpath but for the empty logical directory path.



6.6.5 Remove LoadPath string.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command removes the path string from the current Coq loadpath.


6.6.6 Print LoadPath.
~~~~~~~~~~~~~~~~~~~~~

This command displays the current Coq loadpath.


Variants:


#. Print LoadPath dirpath. Works as Print LoadPath but displays only
   the paths that extend the dirpath prefix.



6.6.7 Add ML Path string.
~~~~~~~~~~~~~~~~~~~~~~~~~

This command adds the path string to the current Objective Caml
loadpath (see the command Declare ML Module in the Section 6.5).


6.6.8 Add Rec ML Path string.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command adds the directory string and all its subdirectories to
the current Objective Caml loadpath (see the command Declare ML Module
in the Section 6.5).


6.6.9 Print ML Path string.
~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command displays the current Objective Caml loadpath. This
command makes sense only under the bytecode version of coqtop, i.e.
coqtop.byte (see the command Declare ML Module in the section6.5).


6.6.10 Locate File string.
~~~~~~~~~~~~~~~~~~~~~~~~~~

This command displays the location of file string in the current
loadpath. Typically, string is a .cmo or .vo or .v file.


6.6.11 Locate Library dirpath.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command gives the status of the Coq module dirpath. It tells if
the module is loaded and if not searches in the load path for a module
of logical name dirpath.


6.7 Backtracking
----------------

The backtracking commands described in this section can only be used
interactively, they cannot be part of a vernacular file loaded viaLoad
or compiled by coqc.


6.7.1 Reset ident.
~~~~~~~~~~~~~~~~~~

This command removes all the objects in the environment since ident
was introduced, including ident. ident may be the name of a defined or
declared object as well as the name of a section. One cannot reset
over the name of a module or of an object inside a module.


Error messages:


#. ident: no such entry



Variants:


#. Reset Initial. Goes back to the initial state, just after the start
   of the interactive session.



6.7.2 Back.
~~~~~~~~~~~

This commands undoes all the effects of the last vernacular command.
Commands read from a vernacular file via a Load are considered as a
single command. Proof management commands are also handled by this
command (see Chapter `7`_). For that, Back may have to undo more than
one command in order to reach a state where the proof management
information is available. For instance, when the last command is a
Qed, the management information about the closed proof has been
discarded. In this case,Back will then undo all the proof steps up to
the statement of this proof.


Variants:


#. Back n Undoes n vernacular commands. As for Back, some extra
   commands may be undone in order to reach an adequate state. For
   instance Back n will not re-enter a closed proof, but rather go just
   before that proof.



Error messages:


#. Invalid backtrack The user wants to undo more commands than
   available in the history.



6.7.3 BackTo num.
~~~~~~~~~~~~~~~~~



This command brings back the system to the state labeled num,
forgetting the effect of all commands executed after this state. The
state label is an integer which grows after each successful command.
It is displayed in the prompt when in -emacs mode. Just as Back (see
above), the BackTo command now handles proof states. For that, it may
have to undo some extra commands and end on a state num′ ≤ num if
necessary.


Variants:


#. Backtrack num 1 num 2 num 3 . Backtrack is a *deprecated* form of
   BackTo which allows explicitly manipulating the proof environment. The
   three numbers num 1 , num 2 and num 3 represent the following:

    + num 3 : Number of Abort to perform, i.e. the number of currently
      opened nested proofs that must be canceled (see Chapter `7`_).
    + num 2 : *Proof state number* to unbury once aborts have been done.
      Coq will compute the number of Undo to perform (see Chapter `7`_).
    + num 1 : State label to reach, as for BackTo.




Error messages:


#. Invalid backtrack The destination state label is unknown.



6.8 Quitting and debugging
--------------------------


6.8.1 Quit.
~~~~~~~~~~~

This command permits to quit Coq.


6.8.2 Drop.
~~~~~~~~~~~

This is used mostly as a debug facility by Coq’s implementors and does
not concern the casual user. This command permits to leave Coq
temporarily and enter theObjective Caml toplevel. The Objective Caml
command:


::

    #use "include";;


add the right loadpaths and loads some toplevel printers for all
abstract types of Coq- section_path, identifiers, terms, judgments, ….
You can also use the file base_include instead, that loads only the
pretty-printers for section_paths and identifiers. You can return back
to Coq with the command:


::

    go();;



Warnings:


#. It only works with the bytecode version of Coq (i.e. coqtop called
   with option -byte, see the contents of Section `14.1`_).
#. You must have compiled Coq from the source package and set the
   environment variable COQTOP to the root of your copy of the sources
   (see Section `14.3.2`_).



6.8.3 Time command.
~~~~~~~~~~~~~~~~~~~

This command executes the vernacular command command and display the
time needed to execute it.


6.8.4 Redirect "file" command.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command executes the vernacular command command, redirecting its
output to “file.out”.


6.8.5 Timeout int command.
~~~~~~~~~~~~~~~~~~~~~~~~~~

This command executes the vernacular command command. If the command
has not terminated after the time specified by the integer (time
expressed in seconds), then it is interrupted and an error message is
displayed.


6.8.6 Set Default Timeout int.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

After using this command, all subsequent commands behave as if they
were passed to a Timeout command. Commands already starting by a
Timeout are unaffected.


6.8.7 Unset Default Timeout.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command turns off the use of a default timeout.


6.8.8 Test Default Timeout.
~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command displays whether some default timeout has be set or not.


6.9 Controlling display
-----------------------


6.9.1 Set Silent.
~~~~~~~~~~~~~~~~~

This command turns off the normal displaying.


6.9.2 Unset Silent.
~~~~~~~~~~~~~~~~~~~

This command turns the normal display on.


6.9.3 Set Warnings ‘‘(w 1 ,…,w n )’’.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command configures the display of warnings. It is experimental,
and expects, between quotes, a comma-separated list of warning names
or categories. Adding - in front of a warning or category disables it,
adding + makes it an error. It is possible to use the special
categories all and default, the latter containing the warnings enabled
by default. The flags are interpreted from left to right, so in case
of an overlap, the flags on the right have higher priority, meaning
thatA,-A is equivalent to -A.


6.9.4 Set Search Output Name Only.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command restricts the output of search commands to identifier
names; turning it on causes invocations of Search, SearchHead,
SearchPattern, SearchRewrite etc. to omit types from their output,
printing only identifiers.


6.9.5 Unset Search Output Name Only.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command turns type display in search results back on.


6.9.6 Set Printing Width integer.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command sets which left-aligned part of the width of the screen
is used for display.


6.9.7 Unset Printing Width.
~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command resets the width of the screen used for display to its
default value (which is 78 at the time of writing this documentation).


6.9.8 Test Printing Width.
~~~~~~~~~~~~~~~~~~~~~~~~~~

This command displays the current screen width used for display.


6.9.9 Set Printing Depth integer.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command sets the nesting depth of the formatter used for pretty-
printing. Beyond this depth, display of subterms is replaced by dots.


6.9.10 Unset Printing Depth.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command resets the nesting depth of the formatter used for
pretty-printing to its default value (at the time of writing this
documentation, the default value is 50).


6.9.11 Test Printing Depth.
~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command displays the current nesting depth used for display.


6.9.12 Unset Printing Compact Contexts.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command resets the displaying of goals contexts to non compact
mode (default at the time of writing this documentation). Non compact
means that consecutive variables of different types are printed on
different lines.


6.9.13 Set Printing Compact Contexts.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command sets the displaying of goals contexts to compact mode.
The printer tries to reduce the vertical size of goals contexts by
putting several variables (even if of different types) on the same
line provided it does not exceed the printing width (See Set Printing
Width above).


6.9.14 Test Printing Compact Contexts.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command displays the current state of compaction of goal.


6.9.15 Unset Printing Unfocused.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command resets the displaying of goals to focused goals only
(default). Unfocused goals are created by focusing other goals with
bullets(see `7.2.7`_) or curly braces (see `7.2.6`_).


6.9.16 Set Printing Unfocused.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command enables the displaying of unfocused goals. The goals are
displayed after the focused ones and are distinguished by a separator.


6.9.17 Test Printing Unfocused.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command displays the current state of unfocused goals display.


6.9.18 Set Printing Dependent Evars Line.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command enables the printing of the “(dependent evars: …)” line
when -emacs is passed.


6.9.19 Unset Printing Dependent Evars Line.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command disables the printing of the “(dependent evars: …)” line
when -emacs is passed.


6.10 Controlling the reduction strategies and the conversion algorithm
----------------------------------------------------------------------



Coq provides reduction strategies that the tactics can invoke and two
different algorithms to check the convertibility of types. The first
conversion algorithm lazily compares applicative terms while the other
is a brute-force but efficient algorithm that first normalizes the
terms before comparing them. The second algorithm is based on a
bytecode representation of terms similar to the bytecode
representation used in the ZINC virtual machine [`98`_]. It is
especially useful for intensive computation of algebraic values, such
as numbers, and for reflection-based tactics. The commands to fine-
tune the reduction strategies and the lazy conversion algorithm are
described first.


6.10.1 Opaque qualid 1 … qualid n .
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command has an effect on unfoldable constants, i.e. on constants
defined by Definition or Let (with an explicit body), or by a command
assimilated to a definition such as Fixpoint, Program Definition, etc,
or by a proof ended by Defined. The command tells not to unfold the
constants qualid 1 … qualid n in tactics using δ-conversion (unfolding
a constant is replacing it by its definition).

Opaque has also an effect on the conversion algorithm of Coq, telling
it to delay the unfolding of a constant as much as possible whenCoq
has to check the conversion (see Section `4.3`_) of two distinct
applied constants.

The scope of Opaque is limited to the current section, or current
file, unless the variant Global Opaque qualid 1 …qualid n is used.


See also: sections `8.7`_, `8.16`_,`7.1`_


Error messages:


#. The reference qualid was not found in the current environment There
   is no constant referred by qualid in the environment. Nevertheless, if
   you asked Opaque foo bar and if bar does not exist, foo is set opaque.



6.10.2 Transparent qualid 1 … qualid n .
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command is the converse of Opaque and it applies on unfoldable
constants to restore their unfoldability after an Opaque command.

Note in particular that constants defined by a proof ended by Qed are
not unfoldable and Transparent has no effect on them. This is to keep
with the usual mathematical practice of *proof irrelevance*: what
matters in a mathematical development is the sequence of lemma
statements, not their actual proofs. This distinguishes lemmas from
the usual defined constants, whose actual values are of course
relevant in general.

The scope of Transparent is limited to the current section, or current
file, unless the variant Global Transparent qualid 1 … qualid n is
used.


Error messages:


#. The reference qualid was not found in the current environment There
   is no constant referred by qualid in the environment.



See also: sections `8.7`_, `8.16`_,`7.1`_


6.10.3 Strategy level [ qualid 1 … qualid n ].
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command generalizes the behavior of Opaque and Transparent
commands. It is used to fine-tune the strategy for unfolding
constants, both at the tactic level and at the kernel level. This
command associates a level to qualid 1 …qualid n . Whenever two
expressions with two distinct head constants are compared (for
instance, this comparison can be triggered by a type cast), the one
with lower level is expanded first. In case of a tie, the second one
(appearing in the cast type) is expanded.

Levels can be one of the following (higher to lower):

:opaque: : level of opaque constants. They cannot be expanded by
  tactics (behaves like +∞, see next item).
:num: : levels indexed by an integer. Level 0 corresponds to the
  default behavior, which corresponds to transparent constants. This
  level can also be referred to as transparent. Negative levels
  correspond to constants to be expanded before normal transparent
  constants, while positive levels correspond to constants to be
  expanded after normal transparent constants.
:expand: : level of constants that should be expanded first (behaves
  like −∞)


These directives survive section and module closure, unless the
command is prefixed by Local. In the latter case, the behavior
regarding sections and modules is the same as for the Transparent and
Opaque commands.


6.10.4 Print Strategy qualid.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command prints the strategy currently associated to qualid. It
fails ifqualid is not an unfoldable reference, that is, neither a
variable nor a constant.


Error messages:


#. The reference is not unfoldable.



Variants:


#. Print Strategies Print all the currently non-transparent
   strategies.



6.10.5 Declare Reduction ident := convtactic.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command allows giving a short name to a reduction expression, for
instance lazy beta delta [foo bar]. This short name can then be used
in Eval ident in ... or eval directives. This command accepts the
Local modifier, for discarding this reduction name at the end of the
file or module. For the moment the name cannot be qualified. In
particular declaring the same name in several modules or in several
functor applications will be refused if these declarations are not
local. The name ident cannot be used directly as an Ltac tactic, but
nothing prevent the user to also perform a Ltac ident := convtactic.


See also: sections `8.7`_


6.11 Controlling the locality of commands
-----------------------------------------


6.11.1 Local, Global
~~~~~~~~~~~~~~~~~~~~

Some commands support a Local or Global prefix modifier to control the
scope of their effect. There are four kinds of commands:


+ Commands whose default is to extend their effect both outside the
  section and the module or library file they occur in.For these
  commands, the Local modifier limits the effect of the command to the
  current section or module it occurs in.As an example, the Coercion
  (see Section `2.8`_) and Strategy (see Section 6.10.3) commands belong
  to this category.
+ Commands whose default behavior is to stop their effect at the end
  of the section they occur in but to extent their effect outside the
  module or library file they occur in.For these commands, the Local
  modifier limits the effect of the command to the current module if the
  command does not occur in a section and the Global modifier extends
  the effect outside the current sections and current module if the
  command occurs in a section.As an example, the Implicit Arguments (see
  Section `2.7`_), Ltac (see Chapter `9`_) or Notation (see Section
  `12.1`_) commands belong to this category.Notice that a subclass of
  these commands do not support extension of their scope outside
  sections at all and the Global is not applicable to them.
+ Commands whose default behavior is to stop their effect at the end
  of the section or module they occur in.For these commands, the Global
  modifier extends their effect outside the sections and modules they
  occurs in.The Transparent and Opaque (see Section 6.10) commands
  belong to this category.
+ Commands whose default behavior is to extend their effect outside
  sections but not outside modules when they occur in a section and to
  extend their effect outside the module or library file they occur in
  when no section contains them.For these commands, the Local modifier
  limits the effect to the current section or module while the Global
  modifier extends the effect outside the module even when the command
  occurs in a section.The Set and Unset commands belong to this
  category.




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
.. _6.11  Controlling the locality of commands: :///home/steck/vernacular.html#sec317
.. _About Coq: :///about-coq
.. _6.5  Compiled files: :///home/steck/vernacular.html#compiled
.. _CSS valid: http://jigsaw.w3.org/css-validator/
.. _7.2.6: :///home/steck/proof-handling.html#curlybacket
.. _Cover: :///home/steck/index.html
.. _Errors: :///home/steck/error-index.html
.. _14.3.2: :///home/steck/commands.html#EnvVariables
.. _4.3: :///home/steck/cic.html#conv-rules
.. _6.8  Quitting and debugging: :///home/steck/vernacular.html#sec282
.. _14.1: :///home/steck/commands.html#binary-images
.. _Table of contents: :///home/steck/toc.html
.. _Community: :///community
.. _8.1: :///home/steck/tactics.html#tactic-syntax
.. _6.7  Backtracking: :///home/steck/vernacular.html#sec278
.. _23: :///home/steck/extraction.html#Extraction
.. _12.1.10: :///home/steck/syntax-extensions.html#LocateSymbol
.. _6.9  Controlling display: :///home/steck/vernacular.html#sec291
.. _6.10  Controlling the reduction strategies and the conversion algorithm: :///home/steck/vernacular.html#sec311
.. _6.4  Loading files: :///home/steck/vernacular.html#sec259
.. _6.2  Flags, Options and Tables: :///home/steck/vernacular.html#sec238
.. _Options: :///home/steck/option-index.html
.. _6.1  Displaying: :///home/steck/vernacular.html#sec235
.. _webmaster: mailto:coq-www_@_inria.fr
.. _Commands: :///home/steck/command-index.html
.. _7.2.7: :///home/steck/proof-handling.html#bullets
.. _2.7: :///home/steck/gallina-ext.html#Implicit%20Arguments
.. _8.16: :///home/steck/tactics.html#Automatizing
.. _12.2.2: :///home/steck/syntax-extensions.html#scopechange
.. _4.1.1: :///home/steck/cic.html#Sorts
.. _xhtml valid: http://validator.w3.org/
.. _Tactics: :///home/steck/tactic-index.html
.. _7: :///home/steck/proof-handling.html#Proof-handling
.. _7.1: :///home/steck/proof-handling.html#Theorem
.. _9: :///home/steck/ltac.html#TacticLanguage
.. _6.6  Loadpath: :///home/steck/vernacular.html#sec266
.. _General: :///home/steck/general-index.html
.. _14: :///home/steck/commands.html#Addoc-coqc
.. _2.5.8: :///home/steck/gallina-ext.html#Import
.. _8.7: :///home/steck/tactics.html#Conversion-tactics
.. _The Coq Proof Assistant: :///
.. _2.2.4: :///home/steck/gallina-ext.html#AddPrintingLet
.. _Documentation: :///documentation
.. _2.8: :///home/steck/gallina-ext.html#Coercions
.. _12.1: :///home/steck/syntax-extensions.html#Notation
.. _98: :///home/steck/biblio.html#Leroy90
.. _6.3  Requests to the environment: :///home/steck/vernacular.html#sec247
.. _2.6.3: :///home/steck/gallina-ext.html#loadpath



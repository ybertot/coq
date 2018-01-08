.. _coqintegrateddevelopmentenvironment:

----------------------------------------
 Coq Integrated Development Environment
----------------------------------------

:Source: https://coq.inria.fr/distrib/current/refman/coqide.html
:Converted by: Paul Steckler

The Coq Integrated Development Environment is a graphical tool, to be
used as a user-friendly replacement to `coqtop`. Its main purpose is to
allow the user to navigate forward and backward into a Coq vernacular
file, executing corresponding commands or undoing them respectively.

CoqIDE is run by typing the command `coqide` on the command line.
Without argument, the main screen is displayed with an “unnamed
buffer”, and with a file name as argument, another buffer displaying
the contents of that file. Additionally, `coqide` accepts the same
options as `coqtop`, given in :ref:`thecoqcommands`, the ones having obviously
no meaning for CoqIDE being ignored. Additionally, `coqide` accepts
the option `-enable-geoproof` to enable the support for *GeoProof* [#]_.

.. _coqide_mainscreen:

  .. image:: ../_static/coqide.png
     :alt: CoqIDE main screen

A sample CoqIDE main screen, while navigating into a file `Fermat.v`,
is shown in the figure :ref:`CoqIDE main screen <coqide_mainscreen>`.
At the top is a menu bar, and a tool bar
below it. The large window on the left is displaying the various
*script buffers*. The upper right window is the *goal window*, where
goals to prove are displayed. The lower right window is the *message
window*, where various messages resulting from commands are displayed.
At the bottom is the status bar.

Managing files and buffers, basic editing
----------------------------------------------

In the script window, you may open arbitrarily many buffers to edit.
The *File* menu allows you to open files or create some, save them,
print or export them into various formats. Among all these buffers,
there is always one which is the current *running buffer*, whose name
is displayed on a green background, which is the one where Coq
commands are currently executed.

Buffers may be edited as in any text editor, and classical basic
editing commands (Copy/Paste, …) are available in the *Edit* menu.
CoqIDE offers only basic editing commands, so if you need more complex
editing commands, you may launch your favorite text editor on the
current buffer, using the *Edit/External Editor* menu.

Interactive navigation into Coq scripts
--------------------------------------------

The running buffer is the one where navigation takes place. The
toolbar proposes five basic commands for this. The first one,
represented by a down arrow icon, is for going forward executing one
command. If that command is successful, the part of the script that
has been executed is displayed on a green background. If that command
fails, the error message is displayed in the message window, and the
location of the error is emphasized by a red underline.

In the figure :ref:`CoqIDE main screen <coqide_mainscreen>`,
the running buffer is `Fermat.v`, all commands until
the ``Theorem`` have been already executed, and the user tried to go
forward executing ``Induction n``. That command failed because no such
tactic exists (tactics are now in lowercase…), and the wrong word is
underlined.

Notice that the green part of the running buffer is not editable. If
you ever want to modify something you have to go backward using the up
arrow tool, or even better, put the cursor where you want to go back
and use the goto button. Unlike with `coqtop`, you should never use
``Undo`` to go backward.

Two additional tool buttons exist, one to go directly to the end and
one to go back to the beginning. If you try to go to the end, or in
general to run several commands using the goto button, the execution
will stop whenever an error is found.

If you ever try to execute a command which happens to run during a
long time, and would like to abort it before its termination, you may
use the interrupt button (the white cross on a red circle).

Finally, notice that these navigation buttons are also available in
the menu, where their keyboard shortcuts are given.

.. _try-tactics-automatically:

Trying tactics automatically
------------------------------

The menu Try Tactics provides some features for automatically trying
to solve the current goal using simple tactics. If such a tactic
succeeds in solving the goal, then its text is automatically inserted
into the script. There is finally a combination of these tactics,
called the *proof wizard* which will try each of them in turn. This
wizard is also available as a tool button (the light bulb). The set of
tactics tried by the wizard is customizable in the preferences.

These tactics are general ones, in particular they do not refer to
particular hypotheses. You may also try specific tactics related to
the goal or one of the hypotheses, by clicking with the right mouse
button on the goal or the considered hypothesis. This is the
“contextual menu on goals” feature, that may be disabled in the
preferences if undesirable.


Proof folding
------------------

As your script grows bigger and bigger, it might be useful to hide the
proofs of your theorems and lemmas.

This feature is toggled via the Hide entry of the Navigation menu. The
proof shall be enclosed between ``Proof.`` and ``Qed.``, both with their final
dots. The proof that shall be hidden or revealed is the first one
whose beginning statement (such as ``Theorem``) precedes the insertion
cursor.


Vernacular commands, templates
-----------------------------------

The Templates menu allows using shortcuts to insert vernacular
commands. This is a nice way to proceed if you are not sure of the
spelling of the command you want.

Moreover, this menu offers some *templates* which will automatic
insert a complex command like ``Fixpoint`` with a convenient shape for its
arguments.

Queries
------------

.. _coqide_querywindow:

.. image:: ../_static/coqide-queries.png
   :alt: CoqIDE queries

We call *query* any vernacular command that does not change the current
state, such as ``Check``, ``Search``, *etc*. Those commands are of course
useless during compilation of a file, hence should not be included in
scripts. To run such commands without writing them in the script,
CoqIDE offers another input window called the *query window*. This
window can be displayed on demand, either by using the Window menu, or
directly using shortcuts given in the Queries menu. Indeed, with
CoqIDE the simplest way to perform a Search on some identifier is to
select it using the mouse, and pressing `F2`. This will both make
appear the query window and run the Search in it, displaying the
result. Shortcuts `F3` and `F4` are for ``Check`` and ``Print``
respectively. The figure :ref:`CoqIDE query window <coqide_querywindow>`
displays the query window after selection of the word “mult” in the
script windows, and pressing `F4` to print its definition.

Compilation
----------------

The `Compile` menu offers direct commands to:

+ compile the current buffer
+ run a compilation using `make`
+ go to the last compilation error
+ create a `Makefile` using `coq_makefile`.

Customizations
-------------------

You may customize your environment using menu Edit/Preferences. A new
window will be displayed, with several customization sections
presented as a notebook.

The first section is for selecting the text font used for scripts,
goal and message windows.

The second section is devoted to file management: you may configure
automatic saving of files, by periodically saving the contents into
files named `#f#` for each opened file `f`. You may also activate the
*revert* feature: in case a opened file is modified on the disk by a
third party, CoqIDE may read it again for you. Note that in the case
you edited that same file, you will be prompt to choose to either
discard your changes or not. The File charset encoding choice is
described below in :ref:`character-encoding-saved-files`.

The `Externals` section allows customizing the external commands for
compilation, printing, web browsing. In the browser command, you may
use `%s` to denote the URL to open, for example:
`firefox -remote "OpenURL(%s)"`.

The `Tactics Wizard` section allows defining the set of tactics that
should be tried, in sequence, to solve the current goal.

The last section is for miscellaneous boolean settings, such as the
“contextual menu on goals” feature presented in the section
:ref:`Try tactics automatically <try-tactics-automatically>`.

Notice that these settings are saved in the file `.coqiderc` of your
home directory.

A Gtk2 accelerator keymap is saved under the name `.coqide.keys`. It
is not recommanded to edit this file manually: to modify a given menu
shortcut, go to the corresponding menu item without releasing the
mouse button, press the key you want for the new shortcut, and release
the mouse button afterwards. If your system does not allow it, you may
still edit this configuration file by hand, but this is more involved.


Using Unicode symbols
--------------------------

CoqIDE is based on GTK+ and inherits from it support for Unicode in
its text windows. Consequently a large set of symbols is available for
notations.


Displaying Unicode symbols
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

You just need to define suitable notations as described in the chapter
:ref:`syntaxextensionsandinterpretationscopes`. For example, to use the
mathematical symbols ∀ and ∃, you may define:

.. coqtop:: in

  Notation "∀ x : T, P" :=
  (forall x : T, P) (at level 200, x ident).
  Notation "∃ x : T, P" :=
  (exists x : T, P) (at level 200, x ident).

There exists a small set of such notations already defined, in the
file `utf8.v` of Coq library, so you may enable them just by
``Require utf8`` inside CoqIDE, or equivalently, by starting CoqIDE with
``coqide -l utf8``.

However, there are some issues when using such Unicode symbols: you of
course need to use a character font which supports them. In the Fonts
section of the preferences, the Preview line displays some Unicode
symbols, so you could figure out if the selected font is OK. Related
to this, one thing you may need to do is choose whether GTK+ should
use antialiased fonts or not, by setting the environment variable
`GDK_USE_XFT` to 1 or 0 respectively.

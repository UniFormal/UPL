This README documents the tests for the UPL to Isabelle/HOL compilers.

The tests are contained in the folders `tests`, `basics` and `negative-test`.
The folder `targets` contains Isabelle code files that correspond to
targeted compilation output of some of the UPL test files.
R
The folder `tests` contains a test suite of small test that are helpful for development and debugging.
A single test file can be run with <br>
`--isabelle test/isabelle/tests/test000.p` <br>
and the whole folder with <br>
`--isabelle test/isabelle/tests`

The following table summarizes the content of these test files.

| Tests | Content |
| :--- | :--- |
| **test00-09** | some initial tests |
| **test20-29** | collection type, kinds and values |
| **test30-39** | traverser |
| **test40-49** | axioms outside of theories |
| **test50-59** | operators (problems with min, max, in, snoc) |
| **test60-69** | polymorphism, type variables, any type, type declarations |
| **test70-79** | tuples |
| **test80-89** | arithmetic operators |
| **test100** | locales |
| **test200** | checker merges declarations with same name |
| **test300** | functions |

Another test suite is within the folder `basics` and can be run with
`--isabelle test/isabelle/basics/`. It is taken from the UPL example 
`basics.p`. Since the compiler only translates part of UPL, there is 
a file `basics-part.p` that comments out all the parts that currently 
don't compile.

The folder `targets` contains Isabelle/HOL target code. During 
implementation these files were used as an aim for compiling some of 
the test files.

The folder `negative-tests` contains tests that fail for various 
reasons. These include nesting of modules, object-oriented programming 
features, interval types, (mutual) recursion, subtyping, and 
theories/locales.
These failing tests reflect the issues and challenges for translation: <br>
No direct correspondence between UPL module and Isabelle theory,
No while and for loops,
(mutual) recursion (need Analyzer to prevent stack overflow and use appropriate
Isabelle/HOL command `fun`, `primrec`, etc.,
no empty type, no interval types, no snoc,
no exceptions, no imperative program blocks, mutable variable assignment.
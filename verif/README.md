This directory contains a Coq verification of cspgen's core translation for a
toy imperative language.  Roughly, we prove that, for any execution of a program
in the operational semantics of the imperative language, there is a
corresponding trace of its translated CSP process.  The imperative language is
similar to the one that appears in the "Imp" chapter of Software Foundations,
which it itself based on Winskel's classic book.

There are four files:

- `CSP_Syntax.v`, which contains the CSP AST.

- `CSP_OpSem.v`, which contains the CSP operational semantics.

- `While_Definitions.v`, which contains the imperative syntax and operational
  semantics.

- `Translation.v`, which contains the translation and proof of correctness.

You can run "make all" to build everything.  This is all known to compile with
Coq 8.5pl2.  The scripts are not very clean, so future versions of Coq may break
them (changes in name generation often break this kind of proof).

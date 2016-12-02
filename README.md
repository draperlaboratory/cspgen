cspgen is a command line tool for creating models of software in the
Communicating Sequential Processes (CSP) process calculus.  The tool accepts
both C programs and LLVM IR as input, and writes a corresponding .csp file to
disk.  The output is compatible with FDR3, the Oxford CSP model checker.  FDR
may be used to check the model for for general properties, like deadlock
freedom, divergence freedom and determinism, or may be compared with
specifications written in CSP using refinement.  cspgen aims to model the
high-level communication behavior of the input code and to abstract data as much
as possible to reduce model-checking time.  It supports a subset of the pthreads
library for multithreading and mutex primitives.

This is prototype, research software.


## Usage

```
Usage: cspgen [OPTIONS] FILE
  -o FILE    --output=FILE      Output destination
  -l         --llvm             Take in LLVM IR rather than C
  -d         --dump             Dump the AST representation of the C-Flat code
  -c         --emit-c           Output the parsed C code
  -e FILE    --externals=FILE   External function specifications
  -r FILE    --runtime=FILE     Runtime file
  -p STRING  --cpp-opts=STRING  Options to be passed to cpp
  -t         --test             Run test files
  -w         --warn             Hide warnings
  -i         --intermediate     Show intermediate results
```

Note: By default, the input is assumed to be a C program.  Use the -l flag if
supplying LLVM IR instead.

## Installation

Cspgen is written in Haskell and can be built with cabal, the Haskell package
manager.  If you already have cabal installed, simply run `cabal install` from
the top-level `specgen` directory.  The build depends on LLVM 3.4, which may be
available from your operating systems package manager.  The `cspgen` binary will
be installed to `~/.cabal/bin`.  You can add this directory to your path or move
the binary elsewhere.

## Examples and Organization

The `examples` directory contains a variety of C and C++ files we use as test
cases and examples.  The tests can be run with `cabal test` or with `cspgen -t`,
which provides more information.  Note that some of the LLVM tests are currently
known to fail.

For information about the organization of the source code, see the ORGANIZATION
file in this directory.

## Documention

Someday there may be some.

## Credit

Cspgen has been developed primarly by Chris Casinghino and Chinedu Okongwu.


## Contact
-------

Cspgen is developed by Draper Labs.  Contact Chris Casinghino
(ccasinghino@draper.com) for additional information.

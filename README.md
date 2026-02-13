# Pacing Types

This artifact contains the Rocq development accompanying the paper "Pacing Types for Asynchronous Stream Equations", accepted at [FM 2026]().
This development includes a formal semantics of micro-RTLola -- a subset of the [RTlola](https://rtlola.cispa.de) specification language
with support for pacing annotations -- and a formalization of two type systems for checking the consistency of these annotations.
The development also includes machine-checkable proofs that the type systems are sound for *consistency* of micro-RTLola equations.

## Structure

+ `theories/lang.v` syntax of stream equations with pacing annotations
+ `theories/sem.v` semantics of stream equations with pacing annotations
+ `theories/typ.v` basic type system for checking consistency of pacing annotations
+ `theories/typ_soundness.v` soundness proof of the basic type system
+ `theories/typ_ext.v` extended type system (with support for self-references and reordering of equations)
+ `theories/typ_ext_soundness.v` soundness proof of the extended type system

## Installation

In order to evaluate the artifact, you will need a working installation of the
the Rocq proof assistant.
More specifically, the artifact was built with Rocq 9.0.1 (but should work with any Rocq `9.*`).

Instructions on how to install Rocq for you system can be found on the official Rocq website:

<div style="text-align:center">
  <a href="https://rocq-prover.org/install">https://rocq-prover.org/install</a>
</div>

## HTML Documentation

To have a closer look at the content of the development, we recommend browsing the precompiled HTML documentation of the Rocq sources.
To get started, open the file `doc/toc.html` in a browser.

## Evaluation Instruction

To check that all claims of the paper are correctly proved in Rocq, you can start by re-compiling all Rocq files using `make`. The output should resemble the following:

```
ROCQ DEP VFILES
ROCQ compile theories/lang.v
ROCQ compile theories/opt.v
ROCQ compile theories/sem.v
ROCQ compile theories/typ.v
ROCQ compile theories/typ_soundness.v
ROCQ compile theories/typ_ext.v
ROCQ compile theories/typ_ext_soundness.v
```

If the compilation ends without any error, this indicates that all proofs
have been successfully compiled and checked.

To make sure that no proof is relying on unreasonable axioms or admitted lemmas,
one can type `make validate`. The expected output should resemble the following:

```
CONTEXT SUMMARY
===============

* Theory: Set is predicative
  
* Theory: Rewrite rules are not allowed
  
* Axioms:
    minilola.typ.bat_lvl
    minilola.lang.IN_dec
    minilola.lang.value
    minilola.lang.OUT
    minilola.lang.IN
    minilola.typ.drain
    minilola.typ.dft
    minilola.typ.f
    Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep
    minilola.lang.OUT_dec
  
* Constants/Inductives relying on type-in-type: <none>
  
* Constants/Inductives relying on unsafe (co)fixpoints: <none>
  
* Inductives whose positivity is assumed: <none>
```
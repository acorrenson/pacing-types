# Pacing Types

This repository contains a Rocq formalization of the system of pacing annotations used in [RTlola](https://rtlola.cispa.de), a stream-based language for runtime verification.

## Structure

+ `theories/lang.v` syntax of stream equations with pacing annotations
+ `theories/sem.v` semantics of stream equations with pacing annotations
+ `theories/typ.v` basic type system for checking consistency of pacing annotations
+ `theories/typ_soundness.v` soundness proof of the basic type system
+ `theories/typ_ext.v` extended type system (with support for self-references and reordering of equations)
+ `theories/typ_ext_soundness.v` soundness proof of the extended type system
---
rg: 2
id: reverse-kleene-involutive-nonmf-proof
kind: route
title: Diagonalize against mark triviality and apply the sign-twist wrapper
target: reverse-kleene-involutive-compiler-gives-non-mf
requires: []
---

Given index `e`, enumerate van Kampen consequences of its compiled finite
presentation and halt exactly upon finding `w_e=1`.  Kleene's recursion
theorem supplies a fixed index `e_*`.  If it halted, the proof found would
contradict the compiler's halting clause `w_(e_*)!=1`; hence it does not halt.
Completeness of van Kampen enumeration also gives `w_(e_*)!=1`, while the
nonhalting collapse clause now applies to this same instance.

Adjoin a central involution `z` and stable letter `a` with

```text
a w_(e_*) a^-1=z w_(e_*).
```

The sign-twist HNN normal form embeds the base and keeps `z` nontrivial.  In
every norm-matrix-corona representation, the HS-collapse estimate on the
involutive mark forces the sign-twist trace comparison to kill `z`.
Therefore the finitely presented wrapper cannot embed into a norm matrix
corona and is not operator-MF.

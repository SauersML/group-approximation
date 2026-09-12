---
rg: 2
id: exact-code-prefix-ultraproduct-proof
kind: route
title: Diagonalize exact prefix tuples through a free matrix ultrafilter
target: exact-code-prefixes-have-matrix-ultraproduct-model
requires: []
---

Enumerate generators so that every generator appearing in `R_n` or `w` has
been assigned by `U_n`; assign identity to temporarily missing generators.
Choose a free ultrafilter and send each generator to the class of its matrix
sequence `(U_n(s))_n`.

Every fixed relation belongs to `R_N` for some `N` and is exactly one for all
`n>=N`.  Its ultraproduct class is one.  Thus the assignment represents the
full relation system in a tracial matrix ultraproduct.  Normalized
Hilbert--Schmidt norm passes to the ultralimit, and `(ECP1)` gives

```text
||w(U)-1||_2=lim_U ||w(U_n)-1||_2 >= alpha.
```

No local-testability estimate enters: exact satisfiability of every prefix
already defeats mark collapse in the limiting matrix semantics.


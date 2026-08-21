---
rg: 2
id: pauli-carrier-membership-decoder
kind: claim
title: Decode the transported Pauli carrier inside the raw binary algebra
distinct_from:
  finite-window-decoder: This asks only for one binary-algebra membership estimate on the fixed Pauli carrier; the other reconstructs the four finite-window endomorphisms.
  outer-pvm-synchronization: This is the coefficient-space membership endpoint after the common carrier is selected; the other constructs a joint transition PVM.
---

In every asymptotically multiplicative normalized-HS model of the fixed
Leavitt atlas packet, recover the trace-`1/8` raw Pauli projection `E` and
the trace-`1/4` transported projection `F` in common finite multiplicity
coordinates and prove

```text
dist_2(F, W*(E)) -> 0.
```

This is the shortest remaining fixed-packet synchronization statement.  It
must use the mixed compressor/root relations: finite subgroup moments alone
admit exact Pauli countermodels.

Do not identify this transported branch-transfer projection with the common
quarter corner in `transported-coefficient-corners-share-flat-quarter-carrier`.
Exact prefix arithmetic proves that they are distinct and have overlap
`1/16`, exactly the product of their traces.  Their second overlap is `3/64`,
so their projection reflections have commutator energy `1/2`.  Any bridge
between them is part of the decoder, not a finite-packet identity; the
noncommutative angle is the alternative holonomy certificate.

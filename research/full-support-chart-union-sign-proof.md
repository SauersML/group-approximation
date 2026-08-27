---
rg: 2
id: full-support-chart-union-sign-proof
kind: route
title: Close the full support-chart union and compute its relative semidirect sign
target: full-support-chart-union-retains-relative-sign
requires:
  - support-return-gives-gauged-native-loop
  - support-return-charts-meet-in-two-pauli-pairs
---

Represent every coefficient in the faithful binary-prefix replacement
normal form, where

```text
(u,v)=(u0,v0)+(u1,v1).
```

Use exact seven-by-seven elementary matrices over that normal form.  Reduce
sibling prefix pairs after every multiplication; this gives a canonical key
compatible with the exact equality test rather than a syntactic key at a
chosen refinement depth.

Conjugate the six generators of `E` by `W_1` and `W_2`.  Breadth-first
closure under the resulting twelve involutions terminates with exactly
`1024` elements.  Testing commutation with the twelve generators finds
exactly four central elements.  Directly evaluating all thirty-six cross
commutators gives `(FUS3)`; the element `d` is represented, for example, by

```text
[W_1A_1W_1,W_2B_1W_2].
```

It is central, nonidentity, and distinct from `c`.  This calculation retains
precisely the cross-relations omitted by the earlier chart-groupoid model.

The nested-support identity gives

```text
S=W_1W_2=W_79(e_0+e_000,e_0+e_000),       S^2=1.
```

Conjugating the twelve generators by `S` permutes the closed set `G`, so
`S` normalizes `G`.  Exact membership testing gives `S notin G`.  Comparing
the conjugation signature of `S` with those of all `1024` elements of `G`
finds no implementer, proving outerness.  Conjugating the four central
elements fixes each one.

Finally close the thirteen involutions consisting of the twelve chart
generators and `S`.  The closure has `2048` elements.  Equivalently,
normality, `S^2=1`, and `S notin G` already identify it with the index-two
semidirect product in `(FUS5)`.  The quotient map to `H/G` is the character
`(FUS6)`.  Since tensoring by a one-dimensional character preserves every
conjugation equation, it supplies the claimed exact relative-sign gauge
model.

---
rg: 2
id: exact-code-prefixes-have-matrix-ultraproduct-model
kind: claim
title: Exact finite code prefixes diagonalize to a matrix-ultraproduct model
distinct_from:
  stabilizer-checks-either-have-logical-shears-or-erase-payload: that gives a finite stabilizer normalizer obstruction; this is a general compactness fence for any increasing family of exactly satisfiable finite code checks.
  robust-locally-satisfiable-relator-code: that asks local checks to amplify an independently supplied semantic obstruction; this proves why exact prefix satisfiability cannot itself supply that obstruction.
---

**ESTABLISHED.**  Let `R_1 subset R_2 subset ...` be finite prefixes of a
countable unitary relation system, and let `w` be a fixed word.  If for every
`n` there is a finite-dimensional tuple `U_n` satisfying `R_n` exactly and

```text
||w(U_n)-1||_2 >= alpha>0,                               (ECP1)
```

then the full relation system has a tracial matrix-ultraproduct model in
which the image of `w` remains at distance at least `alpha` from one.

Consequently a QLTC or fault-tolerant code family whose every finite prefix
has an exact finite-dimensional live-mark code space cannot, by check
soundness alone, force that mark to collapse in matrix ultraproducts.  Such a
code can amplify or synchronize a semantic non-CE/predicate obstruction that
is already coupled to the payload, but cannot manufacture the separation
merely from local testability, distance, or recursion through exact prefixes.

The live-mark hypothesis is essential.  If every exact prefix model erases
the distinguished mark, the diagonal construction says nothing about a
marked obstruction.  This theorem produces one marked tracial model, not a
faithful hyperlinear embedding of the entire presented group.


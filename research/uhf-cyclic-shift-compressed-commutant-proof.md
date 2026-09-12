---
rg: 2
id: uhf-cyclic-shift-compressed-commutant-proof
kind: route
title: Put the one-sided tensor shift and the escaping last-site Pauli in one norm corona
target: uhf-cyclic-shift-has-strict-compressed-commutant
requires: []
---

The formula `(UCS2)` is compatible with the unital inclusions
`M_(2^k)->M_(2^(k+1))`, because two representatives of the same UHF element
agree at every sufficiently large coordinate.  It is isometric, since tensor
amplification preserves operator norm.

For a word supported on the first `k` sites, `(UCS3)` sends it to the same
word on sites `2,...,k+1` once `n>k`.  This proves `(UCS4)`.  The image misses
every non-scalar operator on site one, so the inclusion is proper.

From `cLc^*<=L`, commutants reverse inclusion:

```text
L' intersect Q <= (cLc^*)' intersect Q=c(L' intersect Q)c^*.
```

Conjugating by `c^*` gives `(UCS5)`.  For each fixed `l in L`, the supports
of `l_n` and `v_n` are disjoint for all large `n`, proving `v in B`.
Finally `v_n` and `c_n^*X_1c_n=X_n` anticommute exactly, so their commutator
has norm two at every coordinate.  Thus `v` does not commute with
`c^*X_1c`, proving `(UCS7)--(UCS8)`.

---
rg: 2
id: summed-reynolds-kernel-corner-proof
kind: route
title: Cut the sum of the Reynolds defect Laplacians and polar-correct every word
target: summed-reynolds-cut-synchronizes-kernel-corners
requires:
  - reynolds-defect-cut-gives-regular-relator-corner
---

Conjugation by `rho(H)` permutes the summands of `Delta`, so `Delta` and `q`
commute with `rho(H)`.  Also `tr(Delta)=E`; Markov's spectral inequality
proves `(SRC2)`.

For each `a`, the identity-conjugate summand gives

```text
(Y_a-I)^*(Y_a-I)<=|H|Delta.                            (SRC8)
```

Since `qDelta q<=sq`, the proof of `(RDC8)--(RDC10)` applies verbatim to
every `Y_a` on the same `q`.  It gives `(SRC3)` and `(SRC5)`.  The triangle
inequality gives

```text
||B_a-q||_(2,q)
 <=||B_a-C_a||_(2,q)+||C_a-q||_(2,q)
 <=2sqrt(|H|s),
```

and applying it once more proves the pairwise bound `(SRC4)`.

Set `s=sqrt(E)` to obtain `(SRC6)`.  Finally `(RDC7)` applied to this common
`H`-invariant projection, together with `1-beta<=E/s`, gives `(SRC7)`.

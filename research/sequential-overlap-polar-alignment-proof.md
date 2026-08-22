---
rg: 2
id: sequential-overlap-polar-alignment-proof
kind: route
title: Threshold the full product and polar-correct every prefix
target: sequential-overlap-polar-aligns-carriers-not-contexts
requires:
  - fano-maximal-cap-overlap-has-positive-sequential-mass
  - finite-product-selected-type-mark-does-not-align-carriers
  - common-source-partial-isometries-decode-one-game-state
  - canonical-types-extend-every-finite-bass-serre-actor
  - polar-correction-preserves-povm-covariance
---

Since `0<=X^*X<=1`, spectral splitting at `a/2` gives

```text
a<=tau(X^*X)
 <=(a/2)(1-tau(P))+tau(P).
```

Rearranging proves `(SPA4)`.  On `P`, `(SPA3)` gives
`||XP xi||>=sqrt(a/2)||P xi||`.  For every `c`, the suffix
`q_m...q_(c+1)` is a contraction and

```text
XP=(q_m...q_(c+1))Y_c.
```

Therefore `||Y_c xi||>=||XP xi||`, proving `(SPA6)`.  Functional calculus
on the invertible positive operator `Y_c^*Y_c` in `PMP` proves `(SPA7)` and
`(SPA8)`; the range is below `q_c` because `Y_c=q_cY_c`.

For the firewall, the swap involution in `(SPA9)` maps the whole range of
`q_1` isometrically onto the orthogonal equal-rank space `H_1`.  Thus
`(1-q_1)Aq_1=Aq_1` has squared normalized Hilbert--Schmidt norm `mu`.
The two off-diagonal blocks of `[A,q_1]` have the same squared norm, proving
`(SPA11)`.

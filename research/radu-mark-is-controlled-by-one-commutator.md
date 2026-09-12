---
rg: 2
id: radu-mark-is-controlled-by-one-commutator
kind: claim
title: In Radu's BMW lattice the mark (xz)^4 is linearly controlled by one commutator and the six square defects
distinct_from:
  titz-witzel-sandwich-matchings-need-macroscopic-noncommutation: that bounds the Titz--Witzel mark by a commutator of derived involutions in the building gate; this is the quantitative form of Radu's Lemma 3.5 inside the product-of-trees sublattice.
  titz-witzel-two-generator-gate-forces-macroscopic-noncommutation: that controls the mark u^8 of the two-generator building gate; this controls the Radu mark (xz)^4 with explicit constants and no property (T).
artifacts:
  - research/artifacts/titz-witzel-radu-sublattice-2026-09-11.md
  - research/artifacts/titz-witzel-radu-robust-lemma-check.py
  - research/artifacts/titz-witzel-radu-projections-output-2026-09-11.txt
---

**ESTABLISHED.**  Let `a,b,c,x,y,z` be involutions in a group with a
bi-invariant metric `d`, and let `e1,...,e6` be the defects `d(w,1)` of
`axax, ayay, azbz, bxbx, bycy, cxcz`.  Put `delta = xz`, `u = y delta^2 y`,
`kappa1 = d(u delta, delta u)` and `kappa2 = d(u delta b, delta b u)`.  Then

```text
d(delta^4,1) <= 2 kappa1 + 3e1 + 2e2 + 4e3 + e4 + 2e5 + 4e6,           (RL1)
|kappa1 - kappa2| <= 3e1 + 2e2 + 4e3 + e4,                              (RL2)
d(delta^4,1) <= 2 kappa2 + 9e1 + 6e2 + 12e3 + 3e4 + 2e5 + 4e6.         (RL3)
```

Consequences.

* Titz Mite--Witzel Lemma 3.5 (every finite quotient kills `(xz)^4` once one
  of the two commutators of Proposition 3.4(4) dies) holds with explicit
  linear constants in normalized Hamming distance, for arbitrary almost
  actions.
* A marked approximate solution of `Gamma_R`, with `limsup d_H((xz)^4,1) = epsilon > 0`
  and square defects tending to zero, has
  `limsup d_H([y(xz)^2y, xz],1) >= epsilon/2`.  In any sofic approximation
  both commutators of Proposition 3.4(4) are macroscopic.
* The negative horn reduces to `radu-commutator-collapse`.  Every
  exact-quotient step of Radu's non-residual-finiteness proof except
  Proposition 3.4(4) is now quantitative.

A randomized check (2000 involution tuples on 8 to 128 points) found no
violation.

DERIVATION
radu-mark-is-controlled-by-one-commutator-proof

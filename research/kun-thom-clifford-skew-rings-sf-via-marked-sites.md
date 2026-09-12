---
rg: 2
id: kun-thom-clifford-skew-rings-sf-via-marked-sites
kind: route
title: Separate the Clifford skew rings by marked-site crossed products, as for the Kun--Thom wreath
target: kun-thom-clifford-skew-rings-are-stably-finite
requires:
  - rf-lamps-preserve-stable-finiteness-for-arbitrary-actions
  - residual-lamp-quotients-handle-monomial-actions
artifacts:
  - research/artifacts/clifford-skew-ring-matrix-lamp-wreath-2026-09-12.md
---

**DEAD.** Invalidated by `nondegenerate-clifford-skew-rings-have-no-finite-dim-reps`.

The plan was to copy the proof of the untwisted theorem:
- detect each element of `A_S` by unital maps into `(C^(tensor r)) semidirect G`, where `C` is a
  unitized sum of site algebras;
- induct through stabilizer corners.

Those maps need a character of the lamp algebra (evaluation at infinity). The Clifford lamp algebra of a
nondegenerate form is simple and infinite-dimensional, so every marked-site ring over a residually finite
base is out of reach of any unital map from `A_S`. That is Corollary 2.3 of the artifact.

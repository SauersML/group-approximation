---
rg: 2
id: titz-witzel-central-square-lifts-collapse-mark
kind: claim
title: Central-square lifts of the two-generator Titz gate collapse the mark
distinct_from:
  titz-witzel-two-generator-gate-forces-macroscopic-noncommutation: That forces the original generators `e,u` to be macroscopically noncommuting; this separately forces `e` to fail to commute with the square `u^2`, and therefore excludes flip-over-abelian-fibre voltage lifts even when `e,u` themselves are far from commuting.
  titz-witzel-cyclic-normalizer-ansatz-collapses-mark: That uses the last three gate relators under a cyclic-normalizer hypothesis; this uses only the first derived square and an approximate central-square hypothesis.
artifacts:
  - research/artifacts/titz-witzel-involution-sandwich-check.py
---

**THEOREM.**  Use the words in `(TW2G1)`.  Let `e,u` lie in any group with
a bi-invariant metric `d`, assume `e^2=1`, and put

```text
eta=d(u^2 e,e u^2),                 delta=d(c^2,1).
```

Then

```text
d(u^8,1) <= delta+6 eta.                                (TWCS1)
```

Consequently a positive solution of the two-generator finite-permutation
gate must have

```text
limsup d_H(u_n^2 e_n,e_n u_n^2)>0.                       (TWCS2)
```

Quantitatively, if the mark has limsup `epsilon` and the `c^2` defect tends
to zero, the limsup in `(TWCS2)` is at least `epsilon/6`.

This rules out, in particular, the standard abelian voltage lift of the
exact `C_2` quotient: on `A x C_2`, let both generators flip the second
coordinate and allow arbitrary translations in an abelian fibre `A`.  The
square of `u` is then a uniform fibre translation, hence commutes with `e`,
so `(TWCS1)` says directly that the first gate defect dominates the mark.

---

### Proof

titz-witzel-central-square-lifts-proof

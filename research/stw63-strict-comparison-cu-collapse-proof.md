---
rg: 2
id: stw63-strict-comparison-cu-collapse-proof
kind: route
title: Collapse every soft Jiang--Su class by all quasitraces and invoke Robert
target: stw63-strict-comparison-sr1-uniqueness
requires:
  - stw63-sr1-return-is-cu-equality
artifacts:
  - research/artifacts/stw63-z-embedding-audit-2026-08-30.md
---

Let `phi,psi:Z->B` be unital embeddings.  Robert computes in Section 6.3

```text
Cu(Z) = N disjointUnion (0,infinity],                    (1)
```

where the first summand consists of compact classes and the second of soft
classes.  Unitality forces both `Cu(phi)` and `Cu(psi)` to send the compact
class `n` to `n[1_B]`.

Fix a soft class `r in (0,infinity]`.  For every
`tau in QT_1(B)`, both compositions `tau phi` and `tau psi` are normalized
2-quasitraces on `Z`, hence equal its unique normalized trace.  Therefore

```text
d_tau(Cu(phi)(s))=s=d_tau(Cu(psi)(s))                  (2)
```

for every soft `s`.  Choose an increasing sequence of soft real numbers
`r_k<r` with supremum `r` (finite `r_k` if `r=infinity`).  Equations (2) and
strict comparison give

```text
Cu(phi)(r_k) <= Cu(psi)(r)       for every k.
```

Cu-morphisms preserve increasing suprema, so
`Cu(phi)(r)<=Cu(psi)(r)`.  Interchanging the maps gives equality.  This
handles every soft class, including the soft copy of an integer, without an
equal-rank use of strict comparison: the strict gap is inserted first at
`r_k<r`, and only then is the supremum taken.  Thus the two `Cu` maps agree
on all of (1), and the stable-rank-one Cu return theorem gives approximate
unitary equivalence.

Robert's Proposition 6.3.1 states a narrower application assuming a unique
2-quasitrace because it also computes the target semigroup.  The argument
above only compares two already existing embeddings and shows exactly why
quasitrace uniqueness is unnecessary for that comparison.

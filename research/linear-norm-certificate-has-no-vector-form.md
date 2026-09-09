---
rg: 2
id: linear-norm-certificate-has-no-vector-form
kind: claim
title: The linear relator certificate fails in vector form, for every finite relator set
distinct_from:
  mf-radical-words-have-linear-certificates: that is the operator-norm certificate itself, bounding a radical word by the largest relator error on the whole space; this shows the same bound is false when both sides are evaluated at a single vector, so the certificate does not upgrade to a positive-operator inequality.
  full-mf-radical-linear-relator-inequality: that is the generator-tuple form of the same certificate for a group with full MF radical; this refutes the vector strengthening of both, and applies to every nontrivial presented group, including MF ones.
  commuting-repair-forces-half-dimension-rank: that obstructs repairing an almost commuting pair to a commuting one; this obstructs treating a common fixed vector of a finite relator set as a finite-dimensional quotient representation, and the obstruction is that the compressions are not unitary.
artifacts:
  - research/artifacts/linear-certificate-has-no-vector-form-2026-09-08.md
---

**ESTABLISHED.**  Let `G = F/R` be a nontrivial group with `F` free, let `w`
in `F` have nonidentity image in `G`, and let `S` be **any** finite subset of
`R` — in particular any prescribed finite collection of conjugates of a
finite presentation's defining relators.  Then there exist a
finite-dimensional unitary tuple `U` and a unit vector `xi` with

```text
(s(U) - I) xi = 0   for every s in S,
||(w(U) - I) xi|| = sqrt 2.                                        (VF1)
```

Consequently no finite `S` and constant `C` satisfy

```text
||(w(U)-I)xi|| <= C ( sum_(s in S) ||(s(U)-I)xi||^2 )^(1/2)        (VF2)
```
for all finite-dimensional unitary tuples and all vectors.  So the operator
certificate of `mf-radical-words-have-linear-certificates` does **not** imply
the positive-operator inequality obtained by squaring it.

**There is no conflict with that certificate.**  It bounds `w` by the largest
relator error **on the whole space**, and in the witness below the `s(U)` are
far from `I` away from `xi`.  Only the vector form fails, and it fails for
every nontrivial `G` — including MF ones, where the certificate itself is
vacuous.

**The methodological consequence.**  Writing `P` for the rank-one projection
onto `xi`, one has `(s(U) - I)P = 0` for every selected relator while
`||(w(U) - I)P|| = sqrt 2`, yet the compressions `P U_x P` are **not
unitary**.  A common fixed vector for a finite relator set therefore cannot be
treated as a finite-dimensional quotient representation, so compression is not
a repair for a descent argument.

DERIVATION
vector-form-relator-certificate-counterexample-proof

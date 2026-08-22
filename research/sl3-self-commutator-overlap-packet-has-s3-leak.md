---
rg: 2
id: sl3-self-commutator-overlap-packet-has-s3-leak
kind: claim
title: The rank-one self-commutator and overlap-power packet alone has an exact S3 leak
distinct_from:
  sl3-rank-one-denominator-self-commutator-removes-target-phase: that derives a useful identity from the full arithmetic assignment; this shows that the derived identity together with its two immediate overlap-power consequences cannot force the trace-square energy to vanish.
  one-root-p3-denominator-fragment-has-finite-regular-leaks: that builds finite quotients of a Baumslag--Solitar root-scaling fragment; this is a six-dimensional regular model of the bounded self-commutator packet at the target commutator itself.
  overlap-hecke-coboundaries-have-canonical-finite-matrix-models: that realizes the whole one-overlap Gram kernel by Bernoulli coordinates; this is the smaller nonabelian algebraic calibration of the new rank-one identity.
---

The bounded consequences

```text
W=X[W,Z]X^(-1),     [W,Z^4]=1,     [W,X^2]=1           (S3L1)
```

do not imply `|tr(W)|=1`, even in exact finite matrices.  There are exact
permutation matrices of dimension six satisfying `(S3L1)` with

```text
tr(W)=0.                                                (S3L2)
```

Thus the self-commutator identity removes a scalar phase only **after**
projective energy is known to be small.  It cannot be reversed into a
trace-square transfer inequality using just the immediate fourth-power and
second-power overlap centralities.  A direct rank-one proof still needs
additional arithmetic relations coupling `X` and `Z` to the same lattice
microstate; the three displayed relations alone have a maximal exact leak.


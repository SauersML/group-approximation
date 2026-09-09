---
rg: 2
id: jacobson-positive-root-gluing-misses-laurent-coherence
kind: claim
title: Two complete finite packets sharing only the positive root can satisfy both mixed cells and violate Laurent coherence
distinct_from:
  jacobson-full-boundary-packets-have-compatible-regular-models: that glues the prescribed full intersection but does not impose all mixed relators; this satisfies both quotient mixed cells exactly while omitting only the opposite-root identification between the two finite factors.
  jacobson-shift-finite-core-actions-are-locally-inner: that realizes finite core covariance without actor multiplication identities; this is one explicit finite permutation model of two full actor packets and their selected multiplication cells.
artifacts:
  - research/artifacts/jacobson-missing-laurent-coherence-word-and-finite-cell-countermodel-2026-09-08.md
---

There are two exact faithful representations of `GL_3(F_2)` on
one set of 168 points, with first packet `(C,K,Q)` corresponding
to `(x_13,x_31,w_23)` and second packet `(C',K',H)` corresponding
to `(x_13,x_31,w_12)`, such that, on putting

```text
C'=C,
R=x_23 in the first packet,
U=[H C' H,K'],
```

both mixed relations hold exactly:

```text
(H Q)^3=I,
[U,H R H]=R.
```

Nevertheless

```text
Q H U H Q H R H != I,
K' != K.
```

The explicit permutation implementing the first inequality sends
the label `q=w_23` to `q h`, where `h=w_12`. Both finite
factor tables and the shared positive root are exact; their
shared opposite root is not identified.

This is not a countermodel to `Lambda` or `Theta_shift`, whose
presentation requires that opposite-root identification. It
proves that a derivation of the missing coherence word cannot
discard that part of the common finite subgroup.

DERIVATION
jacobson-168-point-coset-twist-countermodel-proof

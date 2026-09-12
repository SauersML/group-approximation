---
rg: 2
id: stw12-periodic-actions-over-af-embeddable-algebras
kind: claim
title: Outer-periodic integer actions on AF-embeddable algebras have AF-embeddable crossed products
distinct_from:
  stw99-problem-xii-ah-rr0-crossed-qd-afe: that asks about every automorphism of a real-rank-zero AH algebra once its crossed product is quasidiagonal; this theorem removes both hypotheses on the outer-periodic slice but assumes that some positive power of the automorphism is inner.
  pimsner-cyclic-transformation-af-equivalence: Pimsner treats commutative coefficients through a dynamical compression criterion; this theorem treats arbitrary AF-embeddable coefficients by an explicit matrix-valued Floquet embedding.
artifacts:
  - research/artifacts/stw12-periodic-action-af-embedding-audit-2026-08-30.md
---

Let `A` be an AF-embeddable C*-algebra and let `alpha in Aut(A)`.  If there
are `n>=1` and a unitary `v in M(A)` such that

```text
alpha^n = Ad(v),
```

then

```text
A rtimes_alpha Z
```

is AF-embeddable.  The assertion applies to nonunital algebras as well; the
canonical implementing unitary is then interpreted in the multiplier
algebra.

Consequently, if `A` is any separable AH algebra and the class of `alpha` has
finite order in `Out(A)`, then its integer crossed product is AF-embeddable.
In particular Problem XII has a positive answer for outer-periodic actions,
without using real rank zero or assuming the crossed product quasidiagonal.

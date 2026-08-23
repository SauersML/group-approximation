---
rg: 2
id: rowwise-shared-involution-forces-pairwise-marginal-closeness
kind: claim
title: A rowwise shared involution forces its masked context marginals to be canonically close
distinct_from:
  independent-row-masks-transfer-bcs-gap-to-ambient-identity: that transfers all masked verifier rows to the ambient BCS energy; this isolates the pairwise geometric price already imposed by one shared involution.
  common-meet-local-sectors-pay-one-deficit: that uses a common meet for all verifier rows; this forms only the meet of two masks belonging to one variable.
  finite-product-selected-type-mark-does-not-align-carriers: that shows scalar overlap data do not identify multiplicity coordinates; this is a direct operator-distance consequence of exact agreement with the same involution.
---

Let `(M,tau)` be a finite tracial von Neumann algebra.  Let `A_i,A_j,B` be
self-adjoint unitaries and `q_i,q_j` projections satisfying

```text
(A_i-B)q_i=0,             (A_j-B)q_j=0.                (PIC1)
```

Then

```text
(1/4)||A_i-A_j||_2^2
 <=tau(1-q_i)+tau(1-q_j).                               (PIC2)
```

Consequently rowwise masks do not permit independently placed context
marginals to be glued at arbitrarily small deficit.  The marginals incident
to one variable must already form a canonically tight `L2` cluster.

In particular, suppose `A_i` and `A_j` lie in distinct free factors of a
tracial free product and have real traces `m_i,m_j`.  Freeness gives

```text
(1/4)||A_i-A_j||_2^2=(1/2)(1-m_i m_j),                 (PIC3)
```

so every shared-involution interpolation obeys

```text
tau(1-q_i)+tau(1-q_j)>=(1/2)(1-m_i m_j).               (PIC4)
```

For two unbiased occurrences the pairwise deficit floor is `1/2`.  Thus
separate affine Frobenius packets placed as free factors cannot be the
high-density input to the rowwise Hecke CRT; the construction must correlate
their marginal involutions before, or as part of, the finite-support overlap
relations.

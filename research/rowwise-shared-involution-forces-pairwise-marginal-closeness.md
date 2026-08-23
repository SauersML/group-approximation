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

For the explicit Fourier masks of
`affine-frobenius-packets-solve-local-row-mask-storage`, this obstruction
rounds all the way to a classical assignment.  Suppose distinct context
packets remain free factors, every incidence mask has complement trace
`1/p`, and `p>8`.  For two occurrences of one variable, write

```text
alpha=tau(A_(c,x)),        gamma=tau(A_(d,x)).          (PIC8)
```

Then shared interpolation implies

```text
alpha gamma>=1-8/p.                                   (PIC9)
```

Hence the two traces have one common sign `s_x`, each has absolute value at
least `1-8/p`, and

```text
||A_(c,x)-s_x I||_2<=4/sqrt(p).                        (PIC10)
```

Let `nu_c(a)=tau(P_(c,a))`.  Then

```text
nu_c(a_x!=s_x)<=4/p,
nu_c(a=s|_(U_c))>=1-4|U_c|/p.                         (PIC11)
```

If the Fourier labelling puts all forbidden mass in the zero atom, then
`nu_c(forbidden)<=1/p`.  Therefore, whenever

```text
p>4|U_c|+1                                             (PIC12)
```

for every context, the sign tuple `s|_(U_c)` is allowed.  The shared signs
form a global classical satisfying assignment.  Thus free placement does
not merely fail to prove the non-CE certificate: at sufficiently high
density it forces the opposite conclusion.

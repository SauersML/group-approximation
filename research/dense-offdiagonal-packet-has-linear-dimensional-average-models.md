---
rg: 2
id: dense-offdiagonal-packet-has-linear-dimensional-average-models
kind: claim
title: The dense off-diagonal packet has linear-dimensional models with vanishing average Weyl defect
distinct_from:
  packet-kazhdan-commutant-placement-decouples: that tensor-decouples a finite packet from an old Kazhdan action; this collapses the growing complementary Weyl table itself while preserving its basic canonical moments.
  dirac-average-is-a-sharp-near-extra-clifford-generator: that gives inverse-square-root pairwise Clifford defects; this has exact off-diagonal Weyl relations and confines all error to a one-over-D diagonal set.
---

**ESTABLISHED.**

Let `D=2^n`.  There are unitary involutions

```text
X_1,...,X_D, Y_1,...,Y_D,J in U(8D)
```

such that

```text
J^2=1,                 tr(J)=0,
[X_alpha,X_beta]=[Y_alpha,Y_beta]=1,
tr(X_alpha)=tr(Y_beta)=0,
tr(X_alpha^*X_beta)=tr(Y_alpha^*Y_beta)=delta_(alpha,beta),
tr(X_alpha^*Y_beta)=0,                                  (DOA1)
```

and

```text
[X_alpha,Y_beta]=J^(1+delta_(alpha,beta))
```

for every unequal pair.  Only the `D` equal pairs fail.  Consequently the
uniform mean squared normalized-HS defect of the `D^2` complementary Weyl
relations is exactly `2/D` (with the balanced construction below), although
`J` remains a fixed distance from the identity and the labels retain the
displayed canonical first and second moments.

Therefore the positive phase density and bounded average prefix area in
`dense-offdiagonal-leavitt-heisenberg-packet` do not robustly retain its
rank-`D` symplectic dimension obstruction.  Deleting the rare diagonal turns
`I+11^T` into the rank-one all-ones table.  Any live use of the dense packet
must authenticate the diagonal/rank by a separate constant-loss test (for
example a genuinely robust high-rank comparison kernel); average cross
consistency alone admits `O(D)`-dimensional canonical-moment models instead
of forcing dimension `2^D`.


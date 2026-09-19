---
rg: 2
id: ordinary-green-triangle-curl-has-a-linear-code-tangent
kind: claim
title: Ordinary Green triangle curl has a linear code tangent
distinct_from:
  low-odd-square-removes-pairwise-green-stationarity: that proves every individual low-odd edge has a strong skew signal; this shows those signals can have first-order ordinary triangle curl.
  tangent-commutator-covariance-bypasses-code-riesz-endpoint: that uses the support-weighted code coboundary at an exact character block; this refutes replacing that weighted complex by the ordinary complete-graph curl.
  clifford-packets-are-stationary-for-intrinsic-green-step: that obstructs descent at the high endpoint `R=I`; this obstruction occurs with `R=O(t^2)` arbitrarily small.
---

ESTABLISHED NO-GO.  Let an exact diagonal code representation contain two
characters whose difference codeword has support `T` with
`2<=|T|<L`.  Choose distinct `i,j in T` and `k notin T`.  After harmless
sign changes take

```text
 S_i=S_j=Z,        S_k=I
```

on their two-dimensional character block.  Rotate only coordinate `i`:

```text
 Q_i(t)=cos(2t)Z+sin(2t)X,
 Q_l(t)=S_l for l!=i.                                  (OGC1)
```

For the intrinsic skew edge signal `(LOS1)`, direct Pauli calculus gives

```text
 omega_ij(t)=(i/2)sin(4t)Y=2itY+O(t^3),
 omega_jk(t)=omega_ki(t)=0.                            (OGC2)
```

Hence the ordinary triangle curl

```text
 omega_ij+omega_jk+omega_ki
```

is `Theta(t)`, not quadratic in pair defects.  Meanwhile

```text
 R_ij=sin^2(2t)I=O(t^2)I,                              (OGC3)
```

so the example lies in every fixed pointwise low-odd-square sector for
small enough `t`.

Therefore no estimate of the form

```text
 avg_(i,j,k)||omega_ij+omega_jk+omega_ki||_2^2
 <=C s avg_(i,j)||omega_ij||_2^2                       (OGC4)
```

can follow from `R_ij<=sI` alone.  For a family with a positive-density
support and complement, averaging the rotated coordinate over its support
makes both sides' unweighted energy densities comparable except for the
false factor `s`.

The linear curl is exactly a sparse-code syndrome: the perturbation changes
one coordinate inside the difference support without the coordinated
changes demanded by the local dual faces.  Thus the surviving coercivity
target must charge ordinary curl by the parity/equality residual row square,
or retain the support-weighted code complex of `(CRM1)`.  A pair-only
quadratic curl lemma is false.

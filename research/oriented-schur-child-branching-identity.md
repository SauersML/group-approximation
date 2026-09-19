---
rg: 2
id: oriented-schur-child-branching-identity
kind: claim
title: One Schur child carries the predicate as an exact doubling of total branch multiplicity
distinct_from:
  oriented-schur-restriction-mass-identity: that restricts all the way to the full-matrix baseline `A_f`; this retains one child generator and exposes the doubled copies as two inequivalent branch labels.
  schur-child-toeplitz-morita-wire: that computes both transverse child commutants and their Toeplitz actuation; this is the scalar weighted-multiplicity identity for one compressed child.
---

Let `B_f^Q=<A_f,q_(N+1)>`. In selector sector `x`, every irreducible
`B_f`-module `T_x` restricts to `B_f^Q` as follows:

```text
f(x)=0: one child simple, once;
f(x)=1: two inequivalent child simples, once each.              (OCB1)
```

Thus if `m_B(x)` is full-packet multiplicity and `m_Q(x)` denotes the sum of
all child-simple multiplicities above `x`, then

```text
m_Q(x)=2^f(x)m_B(x).                                           (OCB2)
```

For normalized weighted sums

```text
a_B=(D/d)sum_x m_B(x),       a_Q=(D/d)sum_x m_Q(x),
b=(D/d)sum_(f(x)=0)m_B(x),
```

one has the exact oriented identity

```text
a_B=(1/2)a_Q+(1/2)b.                                          (OCB3)
```

Unlike restriction to `A_f`, the two active copies in `(OCB1)` remain
canonically distinguished by the eigenvalue of `q_(N+1)`. Since this child is
the subgroup placed in the compressed Toeplitz tail, those branch labels can
be carried into the next cell without scalarizing the nonlinear predicate.


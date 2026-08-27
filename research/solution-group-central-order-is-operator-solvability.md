---
rg: 2
id: solution-group-central-order-is-operator-solvability
kind: claim
title: Full central phase order is equivalent to an operator solution
distinct_from:
  slofstra-zhang-high-girth-phase-survival: that proves the required order by planar picture curvature; this identifies the representation-theoretic meaning of that order and does not prove it for any particular system.
  perfect-decoding-does-not-imply-quantum-value-gap: that separates exact solvability from robust finite-dimensional soundness; this is only an exact equivalence and supplies no approximation modulus.
---

Let `2<=p<infinity`, and let `Gamma_p(A,b)` be the solution group of an
integer linear system, with distinguished central element `J` of order
dividing `p`.  Then `Ax=b` has a possibly infinite-dimensional operator
solution over `Z_p` if and only if

```text
order_(Gamma_p(A,b))(J)=p.                              (SCO1)
```

One implication is immediate: an operator solution is a unitary
representation sending `J` to `omega_p I`, so the order of `J` is at least
`p`, and the presentation already gives `J^p=1`.

Conversely, suppose `J` has order `p`.  In the left regular representation
`lambda` of the solution group, the central spectral idempotent

```text
e_omega=(1/p) sum_(r=0)^(p-1) omega_p^(-r) lambda(J)^r
```

is nonzero.  Centrality of `J` makes its range invariant under the whole
group, and the compressed regular representation sends `J` to
`omega_p I`.  The defining solution-group relations then give an operator
solution.

This is the exact bridge used in Slofstra--Zhang, *Operator solutions of
linear systems and small cancellation*, arXiv:2412.10305v2.  It deliberately
says **possibly infinite-dimensional**.  Full order of `J` alone gives no
finite-dimensional realization and no normalized-Hilbert--Schmidt stability.

---
rg: 2
id: rank-one-lift-perturbation-gap-no-go
kind: claim
title: Exact algebraic centralizer capture does not control finite-level adjoint gaps
invalidates: [kazhdan-centralizer-capture-forces-most-block-gaps-proof]
---

There is a Kazhdan group `Gamma`, a finite generating set `S`, an ultraproduct
representation `pi : Gamma -> U(M_omega)`, and unitary generator lifts
`g_(s,n) in U(d_n)` with `d_n -> infinity` such that

```text
pi(Gamma)' cap M_omega = C
                       = prod_omega {g_(s,n):s in S}',
```

but the adjoint Poincare constant of the **only** minimal projection of the
finite-level exact centralizer tends to zero.

Thus exact-centralizer capture in the tracial algebra ultraproduct, even in
its strongest scalar form, does not imply the finite-level block-gap clause
needed by `hs-expander-block-decomposition`.  Vanishing-rank almost-invariant
corners are invisible to the algebra ultraproduct but become unit vectors
after `L2` normalization.

Consequently Alekseev--Thom Open Problem 6.2(b), by itself, cannot supply the
normalized-HS Kun block decomposition.  A usable strengthening must control
the Hilbert-space `L2` ultraproduct / uniform integrability of almost-central
vectors, or impose a finite-level spectral-gap statement in addition to
algebraic centralizer capture.

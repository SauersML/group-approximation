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

**Scope (2026-09-11).**  The previous paragraph is about the per-block gap
inequality for *arbitrary* self-adjoint witnesses, which is how the block
clauses were then written.  Every consumer of those clauses feeds them only
operator-bounded observables, in block-summed form: see the bounded-witness
section of `hs-one-level-expander-block-decomposition` and step 2 of
`transported-gap-masa-kills-leavitt-hs-models-proof`.  For that bounded,
summed inequality exact-centralizer capture does suffice, and this no-go does
not obstruct it.  Its spiky witnesses have diverging operator norm.  The
theorem above is unaffected.

---
rg: 2
id: commutator-defect-survives-standard-amplification
kind: claim
title: Standard amplification cannot repair a missing commutator relation
distinct_from:
  commuting-sofic-actions-need-not-combine: that gives global counterexamples to combining action models; this is a finite quantitative identity showing why the usual amplification operations cannot reduce the particular commutator defect.
  mihailova-left-right-local-models-do-not-see-q: that concerns quotient-blind local metric patches; this concerns the actor relation needed before any common color chart can exist.
---

For permutations `p,q in Sym(A)`, write

```text
delta=d_Ham([p,q],1).
```

On the coordinatewise diagonal action on `A^k`, let `p^[k]` and
`q^[k]` act by `p` and `q` in every coordinate.  Then

```text
d_Ham([p^[k],q^[k]],1)=1-(1-delta)^k >= delta.          (CAS1)
```

On the disjoint union of `k` identical copies of `A`, the commutator
defect remains exactly `delta`.  More generally, a product with an
auxiliary pair that commutes exactly also leaves the original defect
unchanged.

Consequently, if separately constructed left and right finite models have
a commutator defect bounded away from zero, neither ordinary tensor or
configuration-power amplification, disjoint-union amplification, nor the
addition of a perfectly commuting auxiliary factor can turn them into the
asymptotically commuting maps required for an action of `F_m x F_m`.

For the Mikhailova left-right problem, this rules out the standard
amplification repair after building the two free-factor charts
independently.  A successful model must arrange the cross-commutators to
be small in the original joint construction; amplification cannot create
that compatibility.

DERIVATION
[[commutator-defect-standard-amplification-proof]]

---
rg: 2
id: monotracial-mf-trace-selection-proof
kind: route
title: Pull a matrix ultralimit trace through an MF embedding and diagonalize
target: monotracial-mf-algebra-has-mf-trace
requires: []
---

Choose a unital embedding

```text
Phi:A -> prod_n M_(d_n) / directSum_n M_(d_n).
```

Let `q:prod_n M_(d_n)->prod_n M_(d_n)/directSum_n M_(d_n)` be the quotient.
A norm-controlled homogeneous section of `q` may be chosen with

```text
q o s = id,                 ||s(x)|| <= 2||x||.
```

Put `phi_n(a)=(s(Phi(a)))_n`.  Equality after applying `q` makes these maps
asymptotically linear, star preserving, and multiplicative in operator norm,
while the section bound gives the uniform estimate

```text
||phi_n(a)|| <= 2||a||                                      (MMT0)
```

for every `a` and `n`.  Exact unitality is unnecessary; since `Phi` is
unital, `||phi_n(1)-I||->0`.

Fix a free ultrafilter `omega`.  The normalized matrix traces define a
tracial state on the norm matrix quotient after passage to their scalar
ultralimit.  Its pullback through `Phi` is a tracial state on `A`, hence is
`tau` by monotraciality.  Thus

```text
lim_(n->omega) tr_(d_n)(phi_n(a)) = tau(a)                 (MMT1)
```

for every `a in A`.

Choose a countable dense star-subalgebra of `A`.  Successive finite
intersections of the `omega`-large sets in `(MMT1)` give a strictly increasing
ordinary subsequence on which the normalized traces converge to `tau` on
that subalgebra.  For arbitrary `a,b`, approximate linearity and `(MMT0)` give

```text
limsup_n ||phi_n(a)-phi_n(b)|| <= 2||a-b||.
```

This asymptotic equicontinuity, together with continuity of `tau`, extends
trace convergence from the dense subalgebra to every `a in A`.  The three
operator-norm defect limits survive passage to a subsequence, so these
coordinates are exactly an MF-trace model for `tau`.

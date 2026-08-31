---
rg: 2
id: stw85-integral-heisenberg-irrep-quotients-are-torus-powers
kind: claim
title: Infinite-dimensional irreducible quotients of every integral Heisenberg group are tensor powers of an irrational rotation algebra
distinct_from:
  stw99-problem-lxxxv-polynomial-growth-invariants: that problem asks for all polynomial-growth groups; this theorem closes the full standard integral Heisenberg tower but makes no claim for higher-step nilpotent groups.
artifacts:
  - research/artifacts/stw85-integral-heisenberg-invariant-audit-2026-08-31.md
---

For `n>=1`, use the presentation

```text
H_(2n+1)(Z)=<x_1,y_1,...,x_n,y_n,z |
 z central, y_j x_j=z x_j y_j,
 [x_i,x_j]=[y_i,y_j]=[x_i,y_j]=1 for i!=j>.
```

Let `pi` be an irreducible unitary representation and write

```text
pi(z)=exp(2 pi i theta)1,       theta in R/Z.
```

Then `pi` is infinite-dimensional exactly when `theta` is irrational.
In that case

```text
C*_pi(H_(2n+1)(Z)) isomorphic to A_theta^(tensor n),
A_theta=C*(U,V | VU=exp(2 pi i theta)UV).               (H85-1)
```

The tensor product is spatial.  At the sharp excluded boundary, if
`theta=p/q` in lowest terms, every irreducible representation with that
central character has dimension `q^n` and its generated C-star algebra
is `M_(q^n)`.  This is a statement about irreducible fibres of the
rational rotation algebra, not an identification `A_(p/q)=M_q`.

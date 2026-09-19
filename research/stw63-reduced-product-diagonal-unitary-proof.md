---
rg: 2
id: stw63-reduced-product-diagonal-unitary-proof
kind: route
title: Diagonalize coordinate conjugacies so their errors vanish in the quotient ideal
target: stw63-liftable-reduced-product-pairs-are-exactly-conjugate
requires: []
---

Fix a dense sequence `(z_k)` in the unit ball of `Z`.  Write

```text
Phi_n=pr_n Phi,             Psi_n=pr_n Psi.
```

These coordinate maps are unital, hence injective because `Z` is simple.
For each `n`, approximate uniqueness in `B_n` supplies a unitary `u_n in B_n`
such that

```text
max_(k<=n) ||u_n Phi_n(z_k)u_n* - Psi_n(z_k)|| < 1/n. (2)
```

The element `U=(u_n)_n` is a unitary in `product_n B_n`.  Fix `k`.  For all
`n>=k`, (2) bounds the `n`th coordinate of

```text
U Phi(z_k)U* - Psi(z_k)
```

by `1/n`.  Its coordinate norms therefore tend to zero, so this difference
belongs to `directSum_n B_n`, and hence to `J`.  If `pi:product_n B_n->Q`
is the quotient map and `u=pi(U)`, then

```text
u phi(z_k)u*=psi(z_k)
```

for every `k`.  Density and contractivity extend the equality to every
`z in Z`, proving (1).

If all embeddings into `Q` lift, apply the argument to any pair.  For the
contrapositive, if both members of a counterexample pair lifted, the unitary
just constructed would exactly conjugate them, which is stronger than the
approximate equivalence they were assumed not to have.

**Trust boundary.**  The unitary lies in the norm quotient `Q`; no bidual,
von Neumann closure, Cuntz-semigroup reflection, or unitary-lifting theorem is
used.  Homomorphic liftability is an explicit hypothesis and is not inferred
from nuclearity of `Z`.

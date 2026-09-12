---
rg: 2
id: finite-group-intertwiner-laplacian-gap-proof
kind: route
title: Reduce the Laplacian to finitely many irreducible-pair blocks
target: finite-group-intertwiner-laplacian-gap
requires: []
---

Choose one representative `S_lambda` of every irreducible complex unitary
representation of the finite group `H`.  There are only finitely many.  Write

```text
V = directSum_mu S_mu tensor C^(m_mu),
W = directSum_lambda S_lambda tensor C^(n_lambda).
```

Then

```text
Hom(V,W)
 = directSum_(lambda,mu)
   Hom(S_mu,S_lambda) tensor
   Hom(C^(m_mu),C^(n_lambda)).                         (1)
```

On the `(lambda,mu)` block, `(FIL1)` acts as the fixed positive operator
associated to

```text
q_(lambda,mu)(A)
 = sum_(s in S)
   ||S_lambda(s)A-A S_mu(s)||^2                       (2)
```

on the finite-dimensional space `Hom(S_mu,S_lambda)`, tensored with the
identity on the multiplicity matrix factor.  Therefore changing the
multiplicities only repeats eigenvalues; it creates no new ones.

The kernel of `(2)` is `Hom_H(S_mu,S_lambda)`.  By Schur's lemma it is zero
when `lambda!=mu` and one-dimensional when `lambda=mu`.  Because `S`
generates `H`, vanishing of every summand in `(2)` is exactly intertwining the
whole group, so there is no larger kernel.

For each irreducible pair, take the smallest strictly positive eigenvalue of
`(2)` on the orthogonal complement of its kernel.  Each such number is
positive.  There are finitely many pairs, so their minimum

```text
kappa(H,S)>0                                             (3)
```

is positive.  Orthogonal decomposition `(1)` now gives `(FIL2)` for arbitrary
multiplicities.  The kernel over all blocks is exactly `Hom_H(V,W)`.

Finally, no eigenvalue lies strictly between `0` and `kappa(H,S)`, so every
spectral cutoff `a<kappa(H,S)` has low-energy space equal to the exact
intertwiner kernel.

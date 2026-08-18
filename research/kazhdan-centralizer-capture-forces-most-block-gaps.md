---
rg: 2
id: kazhdan-centralizer-capture-forces-most-block-gaps
kind: claim
title: Exact centralizer capture forces a uniform adjoint gap on almost all minimal commutant blocks
artifacts:
  - research/hs-expander-block-decomposition.md
---

Fix a Kazhdan group `Gamma`, a finite symmetric generating set `S`, and a
Kazhdan constant `kappa` in the squared-sum form

```text
sum_(s in S) ||sigma(s)xi-xi||^2 >= kappa^2 ||xi||^2
```

for every unitary representation `sigma` and every `xi` orthogonal to its
fixed vectors.

Let `g_(s,n) in U(d_n)` be lifts whose tracial-ultraproduct classes define a
homomorphism `pi : Gamma -> U(M_omega)`, and put

```text
A_n = {g_(s,n) : s in S}' subset M_(d_n).
```

Assume the exact finite-level centralizers capture the whole relative
commutant,

```text
pi(Gamma)' cap M_omega = prod_omega A_n.
```

For each `n`, choose any orthogonal family of minimal projections
`p_(n,j) in A_n` summing to `1`.  Call `p_(n,j)` bad if its compressed
adjoint Poincare constant is smaller than `kappa/2`, i.e. if some self-adjoint
`x in p_(n,j) M_(d_n) p_(n,j)` with normalized corner trace zero satisfies

```text
sum_(s in S) ||g_(s,n) x - x g_(s,n)||_(2,p_(n,j))^2
  < (kappa^2/4) ||x||_(2,p_(n,j))^2.
```

Then the total normalized trace of the bad minimal projections tends to zero
along `omega`.

Hence exact-centralizer capture already gives the one-level block/gap part of
a normalized-HS Kun decomposition: after discarding `o_omega(1)` trace, the
**minimal projections of the commutant** commute exactly with the chosen
lifts and every surviving block has adjoint spectral gap at least `kappa/2`.
Central/isotypic projections are in general too coarse when multiplicities
occur.

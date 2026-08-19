---
rg: 2
id: regular-subgroup-branching-hall-proof
kind: route
title: Restriction-support Hall inequalities are the marginals of the Plancherel coupling
requires:
  - plancherel-restriction-coupling
target: regular-subgroup-branching-is-hall-balanced
---

Let `S` be any set of `G`-irreducibles and let `N(S)` be its restriction
neighbor set in `Irr(H)`.  The coupling `pi_GH` from
`plancherel-restriction-coupling` has no mass from `S` outside `N(S)`.  Therefore

```text
Pl_G(S)
 = pi_GH(S x N(S))
 <= pi_GH(Irr(G) x N(S))
 = Pl_H(N(S)).                                         (HB1)
```

Expanding the two Plancherel measures is exactly

```text
sum_(sigma in S) d_sigma^2/|G|
 <= sum_(theta in N(S)) d_theta^2/|H|,
```

which is `(RBH1)`.  The same argument after any number of subgroup-restriction
steps uses the coherent composed coupling, so inserting intermediate type
layers cannot manufacture a Hall deficit either.

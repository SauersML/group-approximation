---
rg: 2
id: plancherel-restriction-coupling-proof
kind: route
title: Dimension identities and Frobenius reciprocity give the branching transport
requires: []
target: plancherel-restriction-coupling
---

Fix `H<=G` and write `m_(sigma,theta)` for the restriction multiplicities.
For a fixed `sigma`, dimension of the restricted representation gives

```text
sum_theta d_theta m_(sigma,theta)=d_sigma.
```

Hence the first marginal of `(PRC1)` is

```text
sum_theta pi_GH(sigma,theta)
 = d_sigma/|G| sum_theta d_theta m_(sigma,theta)
 = d_sigma^2/|G|=Pl_G(sigma).                         (P1)
```

For the second marginal, Frobenius reciprocity gives

```text
m_(sigma,theta)
 = dim Hom_G(sigma, Ind^G_H theta).
```

Decomposing `Ind^G_H theta` into `G`-irreducibles and taking dimensions yields

```text
sum_sigma d_sigma m_(sigma,theta)
 = dim Ind^G_H theta
 = [G:H] d_theta.
```

Therefore

```text
sum_sigma pi_GH(sigma,theta)
 = d_theta [G:H] d_theta / |G|
 = d_theta^2/|H|=Pl_H(theta).                         (P2)
```

So `(PRC1)` is the asserted coupling, supported exactly where the branching
multiplicity is nonzero.

For coherence, let `K<=H<=G`.  Transitivity of restriction gives

```text
m^GK_(sigma,kappa)
 = sum_theta m^GH_(sigma,theta) m^HK_(theta,kappa).
```

Substitute this identity into the product of the kernels `(PRC3)`:

```text
sum_theta K_GH(theta|sigma) K_HK(kappa|theta)
 = sum_theta
   (d_theta m^GH_(sigma,theta)/d_sigma)
   (d_kappa m^HK_(theta,kappa)/d_theta)
 = d_kappa m^GK_(sigma,kappa)/d_sigma
 = K_GK(kappa|sigma).
```

This proves `(PRC4)` and finishes the claim.

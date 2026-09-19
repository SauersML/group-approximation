---
rg: 2
id: plancherel-restriction-coupling
kind: claim
title: Finite-group restriction carries a canonical Plancherel coupling, coherent down subgroup chains
---

Let `H<=G` be finite groups.  For irreducibles `sigma in Irr(G)` and
`theta in Irr(H)`, write

```text
m_(sigma,theta)=dim Hom_H(theta, Res^G_H sigma).
```

Define

```text
pi_GH(sigma,theta)
  = d_sigma d_theta m_(sigma,theta) / |G|.             (PRC1)
```

Then `pi_GH` is a probability coupling of the Plancherel measures

```text
Pl_G(sigma)=d_sigma^2/|G|,
Pl_H(theta)=d_theta^2/|H|,                             (PRC2)
```

and its support is exactly the ordinary restriction-incidence graph.
Equivalently, the Markov kernel

```text
K_GH(theta | sigma)=d_theta m_(sigma,theta)/d_sigma    (PRC3)
```

pushes `Pl_G` to `Pl_H`.

Moreover these kernels are coherent along subgroup chains: if
`K<=H<=G`, then

```text
K_GK(kappa | sigma)
 = sum_theta K_GH(theta | sigma) K_HK(kappa | theta). (PRC4)
```

Thus any finite construction which remembers only irreducible restriction
types along a subgroup chain inherits an exact feasible transport of the
regular-chart weights.  Such type-only data cannot by itself create a weighted
Hall deficit; a successful atlas obstruction must delete transport edges by
relation-sensitive coefficient identities, multiplicity-arrow equations, or
some other information finer than restriction support.

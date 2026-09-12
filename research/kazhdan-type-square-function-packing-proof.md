---
rg: 2
id: kazhdan-type-square-function-packing-proof
kind: route
title: Project the twisted Kazhdan gap onto off-isotypic blocks
target: kazhdan-type-blocks-pack-a-square-function
requires: []
---

Let `Gamma` act on the Hilbert--Schmidt space `Hom(H_0,H_1)` by

```text
g.X=pi_1(g) X pi_0(g)^*.
```

Its invariant space `F_01` is the space of intertwiners.  Schur's lemma puts
every intertwiner in the same-type block space

```text
B=direct_sum_theta P_theta^1 Hom(H_0,H_1) P_theta^0,
F_01 subset B.
```

The orthogonal complement of `B` consists exactly of the blocks
`P_sigma^1 X P_theta^0` with `sigma!=theta`.  Hence

```text
||P_(B^perp)X||_HS <= dist_HS(X,F_01),
```

and the squared-sum Kazhdan inequality therefore yields

```text
sum_(sigma!=theta) ||P_sigma^1 X P_theta^0||_HS^2
 <= kappa^(-2) sum_(g in S)
      ||pi_1(g)X-X pi_0(g)||_HS^2.                      (1)
```

Distinct type pairs have orthogonal left or right supports, hence are
pairwise Hilbert--Schmidt orthogonal.  For any finite or countable
partition of the off-diagonal pairs into layers `L_n`, Tonelli's theorem
and orthogonality give

```text
sum_n sum_((sigma,theta) in L_n)
  ||P_sigma^1 X P_theta^0||_HS^2
=sum_(sigma!=theta)||P_sigma^1 X P_theta^0||_HS^2.      (2)
```

Combining `(1)` and `(2)` proves the claimed square-function packing with
no factor depending on the number of layers, types, dimensions, or
multiplicities.  Rescaling the Hilbert--Schmidt inner product by one common
normalization rescales both sides equally.

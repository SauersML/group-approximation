---
rg: 2
id: surviving-leavitt-corona-character-orbit-proof
kind: route
title: Make one root orbit infinite using the Leavitt module dimension equation
target: surviving-leavitt-corona-character-has-infinite-parabolic-orbit
requires: []
---

For `h in H`, conjugating `(PCO1)` shows that

```text
P_h=rho(h)P rho(h)^(-1)
```

is a global `N`-character projection for

```text
(h chi)(v)=chi(h^(-1) v h).                            (PCP1)
```

Two nonzero projections carrying distinct characters are orthogonal.  Choose
`v in N` on which the two signs differ.  The two projections are spectral
subprojections of the opposite eigenspaces of the same involution `rho(v)`.
Also one nonzero projection cannot carry two distinct characters.  Therefore
the projection orbit and the character orbit have the same cardinality.

Write a character of `N=(L,+)^(n-1)` as

```text
chi(v_1,...,v_(n-1))=product_i chi_i(v_i).              (PCP2)
```

Choose `i` for which `chi_i` is nontrivial and choose `j!=i`.  For `r in L`,
the upper-left transvection `u_r=x_ij(r)` performs the elementary column
shear

```text
(v_i,v_j) |-> (v_i+r v_j,v_j)                           (PCP3)
```

up to the immaterial characteristic-two inverse convention.  Therefore the
`j`th coordinate of `u_r chi` differs from that of `chi` by

```text
a |-> chi_i(r a).                                       (PCP4)
```

The kernel of the additive map

```text
L -> dual(L,+),       r |-> (a |-> chi_i(r a))          (PCP5)
```

is the right ideal

```text
K={r:chi_i(r a)=1 for every a in L}.                    (PCP6)
```

It is proper because `chi_i` is nontrivial.  If the image in `(PCP5)` were
finite, `L/K` would be a nonzero finite-dimensional right `L`-module over
`F_2`.  If `R_a` denotes right multiplication by `a`, put
`S_i=R_(t_i)` and `T_i=R_(s_i)`.  Since composition reverses coefficient
order, these endomorphisms satisfy

```text
T_i S_j=delta_(ij)I,          S_0T_0+S_1T_1=I.         (PCP7)
```

The two maps `S_i` are injective with disjoint ranges whose direct sum is the
whole module.  Hence

```text
dim(L/K)=2 dim(L/K),                                  (PCP8)
```

forcing `L/K=0`, a contradiction.  Thus `(PCP5)` has infinite image, so the
single root subgroup `{u_r:r in L}` already gives infinitely many character
translates and, by the first paragraph, infinitely many pairwise orthogonal
conjugates of `P`.

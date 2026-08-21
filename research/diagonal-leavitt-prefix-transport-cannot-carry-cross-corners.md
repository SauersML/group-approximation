---
rg: 2
id: diagonal-leavitt-prefix-transport-cannot-carry-cross-corners
kind: claim
title: Diagonal Leavitt prefix compression cannot recursively transport the cross-corners of a Carmichael cycle
distinct_from:
  leavitt-whitehead-20x20-compression-cell: that constructs a stabilized inner implementation of the multiplicative diagonal corner map a |-> s_0 a t_0; this proves why the analogous off-diagonal map needed for prefix permutations is not a ring homomorphism and cannot be substituted into that construction.
  leavitt-cylinder-swaps-generate-thompson-in-el: that factors every cylinder swap into elementary roots, with length allowed to grow under refinement; this isolates why diagonal self-similarity does not make those growing cross-root factorizations uniformly bounded-area.
  thompson-v-r5-uniform-common-pivot-centralizers: that asks for bounded Bleak--Quick filling area inside V; this is a coefficient-algebra obstruction to obtaining such a bound solely from the diagonal Whitehead transport in a larger Steinberg group.
---

In `R=L_2(F_2)`, write `e_u=s_u t_u` for a binary prefix word `u`.  The
diagonal prefix map

```text
alpha_u(a)=s_u a t_u                                      (DPC1)
```

is additive and multiplicative and lands in `e_u R e_u`.  It therefore acts
rootwise on a Steinberg group and is the kind of map implemented by the
rank-20 Whitehead cell.

For two incomparable words `u!=v`, the rectangular prefix map

```text
beta_(u,v)(a)=s_u a t_v in e_u R e_v                      (DPC2)
```

is square-zero under composition with itself:

```text
beta_(u,v)(a) beta_(u,v)(b)
 =s_u a (t_v s_u) b t_v=0,                                (DPC3)
```

whereas `beta_(u,v)(ab)` is generally nonzero.  Hence `beta_(u,v)` is not a
ring homomorphism and the assignment

```text
x_ij(a) |-> x_ij(beta_(u,v)(a))                            (DPC4)
```

does not preserve the Steinberg product commutator.

Every nontrivial permutation of three pairwise orthogonal prefix cylinders
has nonzero off-diagonal entries in at least one corner `e_u R e_v`; a
common-pivot three-cycle has four such cross-corners involving its two pivots
and its variable leaf.  Therefore iterating the existing diagonal Whitehead
compressors cannot by itself give coherent recursive names, or uniformly
bounded Steinberg-presentation certificates, for the Carmichael packet.

This is not a no-go for a genuinely stabilized **rectangular Morita cell**
acting on a larger matrix algebra.  It proves that such a new cell is
necessary: first-divergence identities cannot be compressed merely by
reusing the already constructed rootwise diagonal endomorphisms.

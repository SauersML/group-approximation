---
rg: 2
id: ssa-self-kunneth-exact-k-theory-criterion-proof
kind: route
title: Factor the first-factor K-isomorphism through the external product
target: ssa-self-kunneth-exact-k-theory-criterion
requires: []
---

Let `iota_1:D -> D tensor D` be `d |-> d tensor 1`. Strong
self-absorption gives an isomorphism approximately unitarily equivalent to
`iota_1`, so

```text
(iota_1)_*:G -> K_*(D tensor D)                         (1)
```

is an isomorphism. Naturality of the external product gives

```text
(iota_1)_* = alpha o j,       j(x)=x tensor u.          (2)
```

Consequently `alpha` is split-surjective without a UCT or Kunneth hypothesis:
`j o (iota_1)_*^(-1)` is a right inverse.
After identifying the target with `G` by `(1)`, write

```text
m=(iota_1)_*^(-1) o alpha:G tensor G -> G.
```

Equation `(2)` says `m o j=id_G`, so `m` is a split epimorphism and `j` is
always split-injective.

The Kunneth short exact sequence for `(D,D)` says that `alpha` is injective
and that its cokernel is the indicated graded `Tor(G,G)` term. Since `alpha`
is already surjective, this is equivalent to

```text
alpha is an isomorphism       and       Tor(G,G)=0.     (3)
```

By `(2)`, `alpha` is an isomorphism if and only if `j` is: if `alpha` is an
isomorphism then `j=alpha^(-1)(iota_1)_*`; if `j` is an isomorphism then
`m=j^(-1)` and hence `alpha=(iota_1)_* m` is an isomorphism.

The odd part of `G tensor G` is

```text
(G_0 tensor G_1) (+) (G_1 tensor G_0).
```

The map `j` sends `G_1` only into the second summand. If `j` is surjective,
then `G_0 tensor G_1=0`; symmetry also gives `G_1 tensor G_0=0`. Hence
`j|_(G_1)=0`, and injectivity forces `G_1=0`. The even part is therefore

```text
G_0 -> G_0 tensor G_0,       x |-> x tensor u,
```

and is an isomorphism. Its inverse is the tensor multiplication `m`; the
remaining graded Tor condition is `Tor(G_0,G_0)=0`.

For completeness, an abelian group `A` has `Tor(A,A)=0` exactly when it is
torsion-free. One direction is flatness of torsion-free `Z`-modules. For the
other, if `C_n <= A` is a nonzero cyclic torsion subgroup, the global
dimension one of `Z` makes `Tor_1` left-exact on subgroup inclusions in each
variable; hence

```text
C_n ~= Tor(C_n,C_n) -> Tor(A,A)
```

is injective. Thus self-Tor cannot vanish in the presence of torsion. Since
`j` is inverse to tensor multiplication, the criterion is equivalently
`K_1(D)=0` and `K_0(D)` a torsion-free solid ring. QED

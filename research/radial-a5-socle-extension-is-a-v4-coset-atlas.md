---
rg: 2
id: radial-a5-socle-extension-is-a-v4-coset-atlas
kind: claim
title: The first A5-socle radial escape is exactly a V4-coset atlas
distinct_from:
  radial-simplex-excludes-partitioned-involution-targets: that rules out a direct A5 target because its involutions have disjoint elementary-abelian carriers; the factor-swap extension here has carriers which overlap in one involution.
  atlas-a4-packet-collision-quotient-audit: that is a matrix-packet quotient fork built from two A8 charts and a collision word; this is an exact finite-group reduction intrinsic to the radial simplex presentation.
---

Let

```text
G=(A5 x A5) semidirect <tau>,
tau(g,h)tau=(h,g).                                      (RWA1)
```

Its socle is `A5 x A5`, the quotient by the socle is `C2`, and the socle is
minimal normal because `tau` exchanges its two simple factors.  Thus `(RWA1)`
is the first genuine wreath-style architecture not covered by the direct
`A5` no-go.

Every involution in the nontrivial `tau`-coset has a unique expression

```text
r_a=(a,a^(-1))tau,       a in A5.                       (RWA2)
```

For a radial presentation in which every coordinate has nontrivial image in
the top `C2`, homomorphisms `Gamma_rad -> G` are in bijection with labelings

```text
a:K^* -> A5                                                (RWA3)
```

having the following property.  For each radial set
`P_x={x,alpha x,gamma x,delta x}`, there are a Klein four subgroup `E_x<A5`
and `c_x in A5` such that

```text
{a_y:y in P_x} subset E_x c_x,
a_y=d_y c_x,          product_(y in P_x) d_y=1 in E_x. (RWA4)
```

The image is abelian exactly when all labels in `(RWA3)` lie in one global
coset `E c`.  Consequently this constant-top `A5^2`-socle case has a
nonabelian radial image **if and only if** the radial hypergraph admits a
non-global `V4`-coset atlas `(RWA4)`.

The calculation is elementary.  Two swap-coset involutions commute precisely
when, after choosing one of them as `r_c`, the other is `r_(d c)` for an
involution `d`; a pairwise commuting family is therefore contained in

```text
R_(E,c)={r_(d c):d in E}                                (RWA5)
```

for one Klein four group `E`.  Moreover

```text
r_(d1 c) r_(d2 c)
  =(d1 d2, c^(-1)d1 d2 c),

product_(j=1)^4 r_(dj c)=1
  iff product_(j=1)^4 d_j=1.                            (RWA6)
```

Equations `(RWA5)--(RWA6)` prove both directions of the atlas equivalence.

This also pinpoints why the previous support-connectivity proof stops.  A
single `r_c` lies in the five carriers `R_(E,c)` as `E` ranges over the five
Klein four subgroups of `A5`.  Distinct carriers can therefore meet in one
reflection.  The commuting graph on the `r_a` is connected: adjacency is
equivalent to `a b^(-1)` being an involution, and the conjugacy class of
involutions generates the simple group `A5`.  Hence contexts joined through
one coordinate can rotate their `V4` carrier without violating any local
relation.

This claim does not assert that a non-global atlas `(RWA4)` exists for the
chosen radial parameters.  It reduces the smallest semisimple-extension gate
to that explicit finite incidence problem and proves that affine support
connectivity alone cannot settle it.  Any no-go must control carrier holonomy
around cycles of contexts (or use overlaps of at least two distinct labels),
not merely connectivity of the coordinate support.

---
rg: 2
id: stw22-bare-cone-projectivity-does-not-supply-ilr
kind: claim
title: Bare matrix-cone projectivity cannot supply intrinsic local replication
distinct_from:
  stw22-intrinsic-local-replication-colouring-reduction: that reduction assumes only mutually orthogonal replication ranges; a prescribed-corner cone lift also forces every range to be orthogonal to the source support and is strictly stronger.
  stw22-zero-dimensional-factor-bundles-have-uniform-traces: that theorem constructs weighted copies intrinsically by correction and clopen gluing; this no-go shows why lifting an unrestricted projective cone does not replace its prescribed-source step.
artifacts:
  - research/artifacts/stw22-relative-cone-lifting-no-go-audit-2026-08-30.md
---

# Bare matrix-cone projectivity cannot supply intrinsic local replication

Fix `m>=1` and put

```text
D_(m+1)=C_0((0,1]) tensor M_(m+1).
```

A star-homomorphism `Theta:D_(m+1)->B` satisfying

```text
Theta(iota tensor e_00)=a
```

does produce `m` weighted copies of `a`, but it imposes an extra relation:
their range supports are orthogonal not only to one another but also to
`supp(a)`. Thus relative lifting with the `e_00` corner prescribed is
strictly stronger than the intrinsic local replication property used in the
XXII colouring reduction.

Equivalently, this is a c.p.c. order-zero map
`phi:M_(m+1)->B` with `phi(e_00)=a`, under the standard correspondence
`phi(z)=Theta(iota tensor z)` between order-zero maps and cone
homomorphisms.

This strictness already occurs over a trivial one-dimensional matrix field.
Let

```text
N=2m+1,
B=C([0,1],M_N),
a(s)=diag(1,s,0,...,0).
```

With normalized matrix traces,

```text
sup_s tau(supp(a(s))) = 2/(2m+1) < 1/m.
```

There are global contractions `w_1,...,w_m in B` such that

```text
w_j^*w_j=a,
(w_iw_i^*)(w_jw_j^*)=0                  (i!=j).
```

Hence this section satisfies the strongest possible version of ILR: one
tuple works on the whole interval.

At `s=0`, there is a star-homomorphism

```text
theta_0:D_(m+1)->M_N,
theta_0(iota tensor e_00)=a(0),
```

and `theta_0` even has an explicit global lift to `B` with constant values.
Nevertheless, no neighborhood `O` of zero admits a star-homomorphism

```text
Theta_O:D_(m+1)->C_b(O,M_N)
```

whose prescribed corner is `a|O`. At every `s>0`, that corner has support
rank two, while a representation of the matrix cone forces all `m+1`
diagonal support projections to be mutually orthogonal and to have equal
rank. This would require

```text
2(m+1) <= N=2m+1,
```

which is impossible.

Therefore ordinary projectivity of `D_(m+1)` lifts a fibre map with some
corner section agreeing with `a` at the chosen fibre, but cannot force that
corner section to equal `a` nearby. A prescribed-corner relative lifting
theorem would contain genuinely new selection/comparison input and cannot
be substituted for ILR as a formal consequence of cone projectivity.

## The rank-efficient cone formulation

The correct cone size for `m` copies is `M_m`, not `M_(m+1)`: count the
source itself as the first range. More precisely, a local cone homomorphism

```text
Theta:C_0((0,1]) tensor M_m -> M|O,
Theta(iota tensor e_00)=a|O
```

gives an ILR tuple by

```text
w_0=a^(1/2),
w_j=Theta(iota^(1/2) tensor e_j0)       (1<=j<m).
```

Conversely, an ILR tuple normalized so that its first member is
`a^(1/2)` defines the associated order-zero map on `M_m`, hence the cone
homomorphism. Thus prescribed-corner lifting for the `m`-matrix cone is
exactly an **anchored ILR** property. This removes the wasteful extra support
copy, but it does not remove the relative lifting problem: projectivity by
itself still lifts the fibre cone map with an uncontrolled corner section.

---
rg: 2
id: stw22-relative-cone-lifting-rank-jump-proof
kind: route
title: Separate unrestricted and prescribed-corner cone lifts by one rank jump
target: stw22-bare-cone-projectivity-does-not-supply-ilr
requires: []
artifacts:
  - research/artifacts/stw22-relative-cone-lifting-no-go-audit-2026-08-30.md
---

# Separate unrestricted and prescribed-corner cone lifts by one rank jump

We use interchangeably a cone homomorphism `Theta` and its associated
c.p.c. order-zero map `z -> Theta(iota tensor z)`.

Fix `m>=1`, set `N=2m+1`, and let

```text
p=e_11+e_22 in M_N,
a(s)=e_11+s e_22.
```

## 1. Global ILR holds

Choose pairwise orthogonal rank-two projections `q_1,...,q_m` in `M_N`.
For each `j`, choose a partial isometry `u_j` with

```text
u_j^*u_j=p,          u_ju_j^*=q_j.
```

Define

```text
w_j(s)=u_j a(s)^(1/2).
```

These are norm-continuous contractions in `B=C([0,1],M_N)`, and

```text
w_j(s)^*w_j(s)=a(s).
```

The range of `w_j(s)` is contained in `q_j`, so the range positive elements
for distinct `j` are orthogonal. Since `a(0)` has rank one and `a(s)` has
rank two for `s>0`, normalized traces give

```text
sup_s tau(supp(a(s)))=2/(2m+1)<1/m.
```

Thus the ILR hypothesis and conclusion both hold globally.

## 2. The unrestricted fibre cone map lifts

Let `iota` be the coordinate function on `(0,1]`. Identify `M_(m+1)` with a
rank-`(m+1)` corner `qM_Nq` whose first diagonal matrix unit is `e_11`, and
use the nonunital corner inclusion `qM_Nq subset M_N`. Let

```text
theta_0(f tensor z)=f(1)z.
```

Then `theta_0(iota tensor e_00)=e_11=a(0)`. The constant function with value
`theta_0(d)` gives a star-homomorphic lift

```text
D_(m+1) -> C([0,1],M_N)
```

through evaluation at zero. Its `e_00` corner is the constant section
`e_11`, not the prescribed section `a`.

## 3. A prescribed-corner local lift is impossible

Suppose a neighborhood `O` of zero and a star-homomorphism `Theta_O` with

```text
Theta_O(iota tensor e_00)=a|O
```

existed. Choose `s in O` with `s>0` and evaluate there. In any
finite-dimensional representation of `D_(m+1)`, the support projections of

```text
Theta_s(iota tensor e_00),...,
Theta_s(iota tensor e_mm)
```

are mutually orthogonal and have equal rank. The first is `supp(a(s))`, of
rank two. Consequently `M_N` would contain `m+1` mutually orthogonal
rank-two projections, forcing `2(m+1)<=2m+1`, a contradiction.

Equivalently, setting

```text
v_j=Theta_O(iota^(1/2) tensor e_j0)
```

would give `v_j^*v_j=a`, mutually orthogonal ranges, and ranges orthogonal
to `supp(a)`. The last relation is the extra condition absent from ILR and
is precisely what fails in this example.

## 4. The rank-efficient relative cone is anchored ILR

For `m` desired trace copies, a cone on `M_m` can count the prescribed
source as its zeroth range. If `Theta(iota tensor e_00)=a`, then

```text
w_0=Theta(iota^(1/2) tensor e_00)=a^(1/2),
w_j=Theta(iota^(1/2) tensor e_j0)
```

form `m` copies with mutually orthogonal ranges. Conversely, if an ILR
tuple has first member `a^(1/2)`, the matrix

```text
phi(e_ij)=w_iw_j^*
```

defines a c.p.c. order-zero map with `phi(e_00)=a`, and therefore a cone
homomorphism. This identifies the rank-efficient relative cone property
with anchored ILR. It remains a prescribed-corner problem; unrestricted
projectivity does not impose `phi(e_00)=a` off the base fibre.

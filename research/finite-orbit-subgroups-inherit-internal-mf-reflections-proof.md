---
rg: 2
id: finite-orbit-subgroups-inherit-internal-mf-reflections-proof
kind: route
title: Restrict the visible actor and count its coordinate orbits
target: finite-orbit-subgroups-inherit-internal-mf-reflections
requires:
  - leavitt-unit-internal-all-virtually-free-reflections
  - finite-product-lift-of-internal-mf-reflections
---

The product reflection embeds `P` in `U` and has split quotient `P->R` with
kernel `B`.  Restrict its actor section to `S`; its preimage is exactly the
internal semidirect product `(FOS2)`.

Every homomorphism from `K_S` to an MF group kills each coordinate copy of
`U`, hence kills `B` and factors uniquely through `S`.  Conversely every map
from `S` pulls back.  This proves `(FOS4)`.  Since `S` is a subgroup of a
product of residually finite groups, it is residually finite and therefore
MF.  Intersecting kernels proves `(FOS3)`, and repeating the intersection
over maps killing `N` gives `(FOS5)`.  Finite quotients of `S` separate its
points and have faithful permutation representations over every field, so
the same argument gives all the other residual and completion statements.

The actor `S` acts on the coordinate set `Q_i` through its projection `S_i`
by left translation.  Its orbits are the left cosets of `S_i`, so their
number is `[Q_i:S_i]`.  Choose one coordinate in every orbit and put a finite
generating set of `U` there.  Conjugation by lifts of generators of `S`
reaches every coordinate in the orbit.  Under `(FOS6)`, these finitely many
base generators together with generators of `S` generate `K_S`.

A fixed involution `d` normally generates the nonabelian simple group `U`.
Choose an orbit representative `x_O` for every `S`-orbit and put

```text
delta_S=product_O d_(x_O).
```

The factors have disjoint support, so they commute and `delta_S` is an
involution.  For one orbit `O`, choose `h in U_(x_O)` with `[d,h]!=1`; such an
`h` exists because the center of `U` is trivial.  Commuting `delta_S` with
`h` cancels every other coordinate and gives

```text
[delta_S,h]=[d_(x_O),h]!=1
```

inside the single coordinate group `U_(x_O)`.  Simplicity makes the normal
closure of this commutator contain that whole coordinate group.  Conjugation
by `S` reaches every coordinate in `O`.  Repeating this isolation for each
orbit proves `(FOS7)`.

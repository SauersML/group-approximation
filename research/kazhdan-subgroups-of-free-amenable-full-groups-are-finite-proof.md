---
rg: 2
id: kazhdan-subgroups-of-free-amenable-full-groups-are-finite-proof
kind: route
title: "The invariant measure makes almost every orbit finite; full support makes those free finite orbits dense; the uniform orbit bound then makes K finite"
target: kazhdan-subgroups-of-free-amenable-full-groups-are-finite
requires:
  - kazhdan-subgroups-of-amenable-orbit-full-groups-are-rf
  - dense-finite-free-orbits-force-finite-kazhdan-subgroups
---

Notation as in the target. `K ≤ [[P ⋉ X]]` has property (T).

## Step 1. K lies in the measured full group

`(X, μ)` is a standard probability space, since `X` is compact metrizable. `P` acts by
Borel automorphisms, which preserve `μ` by hypothesis. The action is essentially free:
`X_free = X \ ∪_{p ≠ 1} Fix(p)` is a `G_δ` set of measure `1`.

Every `g ∈ K` is a homeomorphism, hence a Borel bijection. Its `c_g` is continuous from
a compact space to a discrete one, hence Borel of finite range. So
`K ≤ W(P ↷ X)` in the sense of `kazhdan-subgroups-of-amenable-orbit-full-groups-are-rf`.

## Step 2. Almost every orbit is finite

Apply the theorem of `kazhdan-subgroups-of-amenable-orbit-full-groups-are-rf` to the
inclusion `ρ : K → W(P ↷ X)`. It gives: `μ`-almost every point has a finite `K`-orbit.
Intersecting with `X_free`, the set `G = {x ∈ X_free : Kx finite}` contains a conull
set.

## Step 3. Density, and conclusion

`μ` has full support, so every nonempty open `U ⊂ X` has `μ(U) > 0`. Hence `U` meets
every conull set, and so meets `G`. So `G` is dense.

Now `P` is amenable. Take `A = P` and `d = 0`, so `P = A × F_0`. The hypothesis of
`dense-finite-free-orbits-force-finite-kazhdan-subgroups` holds, and that theorem gives:
all `K`-orbits are bounded by `M`, and `K` is finite. ∎

## Consequence 1 (free minimal actions)

Amenability of `P` gives an invariant Borel probability measure on compact metrizable
`X`. The standard argument: take weak-* limit points of Følner averages of a point
mass, and use compactness of the probability measures. Its support is closed, nonempty
and `P`-invariant, so by minimality it is `X`. A free action is essentially free for
every measure. The statement then applies.

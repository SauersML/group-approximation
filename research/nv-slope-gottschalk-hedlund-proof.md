---
rg: 2
id: nv-slope-gottschalk-hedlund-proof
kind: route
title: A bounded orbit of the slope skew product has a minimal subset that is a graph, and the graph is a continuous potential whose deep bricks are permuted canonically
target: bounded-slope-at-one-point-puts-nv-minimal-set-in-u-k
requires: []
artifacts:
  - research/artifacts/kazhdan-nv-displacement-gap-2026-09-17.md
---

Direct establishment; complete proof is artifact Section C. `requires: []` is a proof
commitment; only the brick calculus (well-defined locally constant slope, cocycle
identity, depth `D_g`, canonical image of a deep brick) is used, as recorded in Section 0
of `research/artifacts/kazhdan-nv-measure-criterion-2026-09-17.md`.

1. `K` acts on `Z x Z^n` by `g(y,m) = (gy, m + s(g,y))`, commuting with fibre translations.
2. The orbit closure of `(x,0)` is compact and contains a minimal `M` projecting onto `Z`.
3. Two points of `M` in one fibre differing by `t ≠ 0` make `M + t = M` (two minimal sets
   meeting), contradicting compactness, so `M` is the graph of a continuous, hence locally
   constant, `φ` with `φ(gy) = φ(y) + s(g,y)`.
4. With `F = -φ` and `c` beyond the depths of a finite generating set and the constancy
   scale of `F`, the bricks of shape `c·1 + F(y)` containing `y ∈ Z` form a finite family,
   disjoint on `Z`, mapped canonically `B(y) -> B(hy)` by each generator.
5. The kernel of the permutation action has finite index and is the identity on the open
   union of the family, which contains `Z`; so `Z ⊆ U_K`, and points of `U_K` have finite
   orbits.

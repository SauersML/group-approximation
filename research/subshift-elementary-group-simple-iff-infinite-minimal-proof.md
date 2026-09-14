---
rg: 2
id: subshift-elementary-group-simple-iff-infinite-minimal-proof
kind: route
title: If direction from Steinberg simplicity; only-if direction by passing an ideal to a noncentral proper normal subgroup
target: subshift-elementary-group-simple-iff-infinite-minimal
requires: [steinberg-elementary-groups-are-simple-mod-centre]
---

**If.** For an infinite minimal subshift, `T` has no periodic points. So the transformation groupoid `X ⋊ Z` is a Hausdorff ample groupoid with compact infinite unit space, and it is minimal and effective. Its Steinberg algebra is `R_X`. So `G/Z(G)` is simple by `steinberg-elementary-groups-are-simple-mod-centre`. For `k = F_q` and `n = 3` this is also the reviewed `simple-kazhdan-lef-group-from-minimal-subshift`.

**Only if.** Suppose `X` is not both infinite and minimal. Then `X` is not minimal, or `X` is minimal and finite. In the second case every point is periodic and `X` is a single orbit of some size `p`.

*A nonzero proper ideal.*
- *`X` not minimal.* Choose a closed invariant `∅ ≠ Y ⊊ X`, and let `ρ: R_X → R_Y` be `Σ f_j u^j ↦ Σ (f_j|_Y) u^j`. It is a ring homomorphism, because restriction commutes with composition by `T^(−i)` on the invariant set `Y`. It is surjective, because every clopen subset of `Y` is the trace of a clopen subset of `X`. Its kernel contains `e_U ≠ 0` for any clopen `U ≠ ∅` disjoint from `Y`, and `R_Y ≠ 0`.
- *`X` a finite orbit of size `p`.* Let `σ: R_X → End_k(k^X)` send `f` to multiplication by `f` and `u` to `δ_y ↦ δ_(Ty)`. It is a ring homomorphism: `σ(u)σ(f)σ(u)^(-1) δ_(Ty) = f(y) δ_(Ty) = σ(f∘T^(-1)) δ_(Ty)`. Its kernel contains `u^p − 1`, which is nonzero because `u^p` and `1` have different degrees. Its image is nonzero.

*From an ideal to a normal subgroup.* Let `φ: R_X → S` be one of these surjections, with `S ≠ 0` and `0 ≠ r ∈ ker φ`. Then `EL_n(φ): G → EL_n(S)` is surjective, since it maps elementary generators onto elementary generators. Let `K` be its kernel.
- `K ∋ e_12(r)`, and `e_12(r)` does not commute with `e_21(1)`: the `(1,1)` entries of `e_12(r) e_21(1)` and `e_21(1) e_12(r)` are `1 + r` and `1`. So `K ⊄ Z(G)`.
- If `K Z(G) = G`, then `EL_n(S) = φ(Z(G))` would be abelian. But `e_12(1)` and `e_21(1)` do not commute in `EL_n(S)` for `S ≠ 0`.

So `K Z(G)/Z(G)` is a nontrivial proper normal subgroup of `G/Z(G)`.

**Model tests.**
- `X = {a^∞}`: `φ` = reduction mod `u − 1`, `S = k`, `EL_n(S) = SL_n(k)`, and `e_12(u − 1) ∈ K`. This is the finite-orbit case with `p = 1`.
- The Fibonacci subshift is infinite and minimal, so it lies on the simple side.

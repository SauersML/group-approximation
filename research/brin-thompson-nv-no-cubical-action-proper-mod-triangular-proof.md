---
rg: 2
id: brin-thompson-nv-no-cubical-action-proper-mod-triangular-proof
kind: route
title: "The Callard--Salo element has sublinear wall count, hence bounded; its powers leave every finite union of undistorted cosets"
target: brin-thompson-nv-no-cubical-action-proper-mod-triangular
requires:
  - cubical-coset-proper-actions-capture-distorted-elements
  - brin-thompson-triangular-subgroup-is-undistorted
  - brin-thompson-mv-contains-a-distortion-element
---

Notation is as in the target.

**Step 1 (the distorted element).** By `brin-thompson-mv-contains-a-distortion-element` with
`m = n ≥ 2`, `nV` contains an infinite-order `f` and a finitely generated `L ≤ nV` containing `f`
with `|f^N|_L = O(log^4 N)`. In particular `f` is distorted.

**Step 2 (item 1).** By hypothesis on `H`, its infinite-order elements are undistorted in every
finitely generated subgroup containing them. For `H` inside a conjugate or coordinate permutation
of `T_n`, this is item 3 of `brin-thompson-triangular-subgroup-is-undistorted`, since undistortion
passes to subgroups (it is a property of the element and of `L`). Item 3 of
`cubical-coset-proper-actions-capture-distorted-elements` then says that no commensurating action
of `nV` is proper modulo `H`.

The cube complex and wall space versions are the special case where `X` is the set of half-spaces
and `A` is the set of half-spaces containing a vertex `v`: then `|gA Δ A|` counts the walls
separating `v` from `gv`, which is the combinatorial distance.

**Step 3 (item 2).**
- *Distinct cosets.* If `f^a H = f^b H` with `a < b`, then `f^{b−a} ∈ H`. It has infinite order,
  and it is distorted in `L`, as in Step 3 of the proof of
  `cubical-coset-proper-actions-capture-distorted-elements`. This contradicts the hypothesis on `H`.
- *Bounded wall counts.* `ℓ(f^N) ≤ K|f^N|_L = o(N)`, so `ℓ(f^N)` is bounded by item 1 of
  `cubical-coset-proper-actions-capture-distorted-elements`.
- *Growth of `ψ_1`.* A sublevel set `{ψ_1 ≤ R}` lies in finitely many cosets, so it contains only
  finitely many `f^N`, by distinctness. Hence `ψ_1(f^N) → ∞`. And `√ψ_1` is subadditive: writing
  `ψ_1 = ‖b‖²` for a cocycle, `b(gh) = b(g) + π(g)b(h)` gives `‖b(gh)‖ ≤ ‖b(g)‖ + ‖b(h)‖`. So `√ψ_1(g) ≤ K'|g|_L` with
  `K' = max_S √ψ_1`. So `ψ_1(f^N) ≤ K'^2 |f^N|_L^2 = O(log^8 N)`.
- A finite sum of wall counts is again a wall count (disjoint union of the sets `X`, and of the
  sets `A`), so it is bounded on `⟨f⟩`, and cannot be proper modulo `H`. ∎

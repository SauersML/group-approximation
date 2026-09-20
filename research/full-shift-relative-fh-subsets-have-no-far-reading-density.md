---
rg: 2
id: full-shift-relative-fh-subsets-have-no-far-reading-density
kind: claim
title: "Diagonal-pair test: a subset of the full-shift full group whose local rules read far-away coordinates at a positive density of positions is unbounded for some cnd function on [[X]]; so an infinite Boolean subgroup of B_1 has no relative (T), while the w16 involutions g_m and a run-length Boolean group survive"
distinct_from:
  full-shift-topological-full-group-is-a-t-menable: that is the open Haagerup claim; this is a class kill for its relative-FH refutations, not a proof of it, and the functions built here are not proper
---

**ESTABLISHED (unreviewed).** Route: `full-shift-far-reading-density-diagonal-pair-proof`.
Imports: only that `g ↦ ‖π(g)ξ − ξ‖²` is cnd for a unitary representation `π`, and that
pointwise limits of cnd functions are cnd. Lane proof by swarm-0917-w21-w21-nv-follow. No priority
claimed.

**Near neighbours (wave-20/21 nodes on the swarm branch, not in this checkout).**
- `wobbling-relative-fh-subsets-lie-in-displacement-balls` uses cut-space vectors on one orbit to
  confine relative-FH subsets to one ball `B_K`. This node uses Følner vectors on pairs of
  different orbits and kills subsets inside `B_1` itself.
- `wobbling-group-cnd-functions-are-bounded-on-displacement-balls` shows that cnd functions on
  `W(Y)` are bounded on `B_1`. The functions here are unbounded on an infinite subgroup of `B_1`,
  so they do not come from any `W(Y)`.
- `full-shift-full-group-local-cocycles-are-displacement-bounded` shows that local covariant
  cocycles are bounded on `B_1`. The functions here are therefore non-local.

## Setting

- `X = {0,1}^Z`, `(σx)_n = x_{n+1}`. `[[X]]` is the topological full group, `g(x) = σ^{k_g(x)} x`
  with `k_g: X → Z` continuous. The **window** `w(g)` is the least `w` such that `k_g(x)` depends
  only on `x_{[−w,w]}`. `B_K = {g : ‖k_g‖_∞ ≤ K}`.
- A subset `Y` of a group `Γ` has **relative FH** in `Γ` if every cnd function on `Γ` is bounded on
  `Y`. For a subgroup this is relative (T) of `(Γ, Y)`.
- **Far-reading density.** For `q ∈ [[X]]`, `M ≥ 0` and `η > 0`, let `θ_{M,η}(q)` be the supremum of
  `#{a ∈ J : k_q(σ^a x) ≠ k_q(σ^a x')} / |J|` over all intervals `J ⊆ Z` with `|J| ≥ 1/η` and
  all `x, x' ∈ X` such that
  `#{a ∈ J : x_{[a−M, a+M]} ≠ x'_{[a−M, a+M]}} ≤ η|J|`.
  For `Y ⊆ [[X]]` put `Θ(Y) = inf_{M ≥ 0, η > 0} sup_{q ∈ Y} θ_{M,η}(q)`.
- In words: `x` and `x'` look the same through every window of radius `M` centred in `J`, except at
  an `η` fraction of centres. `θ` asks at what fraction of `J` the rule `k_q` still tells them
  apart, so `q` must read coordinates that radius-`M` rules cannot see from `J`.

## Statement

1. **(Diagonal-pair test.)** Let `Y ⊆ [[X]]` with `Θ(Y) > 0`. Then there is a cnd function `ψ` on
   `[[X]]` with `sup_Y ψ = ∞`. Hence for every subgroup `Γ ≤ [[X]]` containing `Y`, the set `Y`
   does not have relative FH in `Γ`.
2. **(An infinite Boolean subgroup of `B_1` with no relative (T).)** Let
   `E = {y : y_{−1} = 1, y_0 = 0}`, so `E ∩ σE = ∅`. For `M ≥ 1` let `U_M = E ∩ {y : y_M = 0}`, and
   let `q_M = s_{U_M}` be the involution that swaps `y ↔ σy` for `y ∈ U_M` and fixes everything
   else. The `q_M` commute and generate an infinite elementary abelian 2-group `H_E ≤ B_1`. For
   every infinite `Λ ⊆ N`, `Θ({q_M : M ∈ Λ}) ≥ 1/2`. So no `Γ ≤ [[X]]` has relative (T) with
   respect to `H_E`, or relative FH with respect to any infinite subset of `{q_M}`.
3. **(The test is blind to sparse and run-length families.)**
   - *w16 involutions.* Let `z` be aperiodic, `E_m = {y : y_{[−m,m]} = z_{[−m,m]}}` and
     `g_m = s_{E_m}`, defined once `E_m ∩ σE_m = ∅`. Then `Θ({g_m}) = 0`.
   - *Run-length group.* For `i ≥ 0` let `R_i = E ∩ {y : y_1 = … = y_i = 0, y_{i+1} = 1}`, which
     are pairwise disjoint. The involutions `s_{R_i}` generate an infinite elementary abelian
     2-group `H_run ≤ B_1`, and `Θ(H_run) = 0`.

## What it kills (for refutations of `full-shift-topological-full-group-is-a-t-menable`)

- **Class.** Relative-FH witnesses `Y` (subsets or subgroups, normal or not, inside any
  `Γ ≤ [[X]]`) with positive far-reading density. With
  `wobbling-relative-fh-subsets-lie-in-displacement-balls`, a surviving witness must lie in one
  ball `B_K`, have bounded exponent if it is a subgroup, **and** have `Θ(Y) = 0`.
- **Invariant.** `Θ`, the density of positions along an orbit at which `k_q` distinguishes two
  points that no bounded-radius rule centred there can distinguish.
- **Where every member dies.** The vector `|J|^{-1/2} 1_{D}` in `ℓ²(X × X)`, with
  `D = {(σ^a x, σ^a x') : a ∈ J}`. Radius-`M` elements move it along the diagonal. An element
  that sees `x` and `x'` differently at `a` sends `(σ^a x, σ^a x')` off the diagonal, which is
  fatal: a `θ` fraction of such positions moves the vector by `√(2θ)`.

## Why it matters

- **A separation from `W(Y)`.** By `wobbling-group-cnd-functions-are-bounded-on-displacement-balls`,
  every cnd function on an orbit wobbling group is bounded on `B_1`. By
  `full-shift-full-group-local-cocycles-are-displacement-bounded`, so is every local covariant
  cocycle. Item 2 gives the first cnd functions on `[[X]]` that are unbounded on an infinite subset
  of `B_1`. They realize the survivor that w20 named: a sum over infinitely many orbit pairs whose
  convergence comes from the continuity of `k_g` across orbits.
- **Where the problem now sits.** Item 3 shows exactly what the diagonal mechanism cannot reach:
  - elements with sparse support, like the w16 involutions `g_m` on which the invariant-measure
    walls died;
  - elements that read far only at `O(1)` positions of each interval, like `H_run`.
  A proper cnd function on `[[X]]` has to be unbounded on both families. A relative-(T) refutation
  has to be built from such families. The w16 obstruction is therefore not a density phenomenon.
  It is a sparsity phenomenon.

## Next falsifiable steps

- Decide whether `{g_m}` (or `H_run`) has relative FH in `[[X]]`. The diagonal-pair test would
  need Følner sets concentrated where `g_m` acts. Along an orbit those points have density at
  most `2/π_m`, where `π_m` is the least period of `z_{[−m,m]}`.
- Test whether an influence-weighted variant can do this, using many-point configurations in
  `X^k` in place of pairs. The route explains why plain `k`-tuples give no gain: the ratio of
  `q`-sensitivity to generator defect per disagreement site does not change.

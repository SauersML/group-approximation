---
rg: 2
id: nv-cnd-functions-grow-at-most-linearly-along-fibre-elements
kind: claim
title: "Every cnd function on nV grows at most linearly along every element that fixes one coordinate; on C(C,Z) ⋊ V, ψ(k·1_C) = O(k)"
distinct_from:
  brin-thompson-nv-fibre-elements-are-cubically-elliptic: that shows the same fibre elements are bounded in every commensurating (cubical) action; this bounds every conditionally negative definite function, cubical or not, but only by a linear function
  brin-thompson-mv-contains-a-distortion-element: that gives O(log^8) growth along one distorted element through word length; the elements here are undistorted, so word length only gives O(k^2)
  cantor-integer-maps-pair-lacks-relative-property-t: that constructs almost invariant vectors moving unbounded-depth subsets of C(C,Z); this is an inequality every almost invariant vector satisfies along the centre, and kills the positive-drift characters for the centre
---

**ESTABLISHED** by `nv-cnd-linear-growth-along-fibre-elements-proof`.

## Statement

Let `C = {0,1}^N`, `A = C(C,Z)`, `G = A ⋊ V` with `(h·f)(x) = f(h^{-1}x)`, and
`z = 1_C` (central). Fix `h_1, h_2, h_3 ∈ V` with `h_1[0] = [1]`, `h_2[0] = [00]`,
`h_3[0] = [01]` as sets.

1. **Paradox inequality.** For every unitary representation `π` of `G`, every
   `M ∈ Z` and every unit vector `ξ`,
   `|Im⟨π(M·1_C)ξ, ξ⟩| ≤ 28 (‖π(M·1_{[0]})ξ − ξ‖² + max_i ‖π(h_i)ξ − ξ‖²)`.
   For `G = Z` and `π = e^{iθ}` the left side is `≈ θ` and the right side `≈ θ²`, so this
   is a genuine constraint: the centre is "first-order invisible" to almost invariant
   vectors.
2. **Linear growth.** For every cnd function `ψ` on `G` and `k ≥ 1`,
   `ψ(k·1_C) ≤ 2ψ(1_C) + 28π² k (ψ(1_{[0]}) + ψ(h_1) + ψ(h_2) + ψ(h_3))`.
3. **Transfer to nV.** Let `n ≥ 2`. For every cnd function `ψ` on `nV` and every
   `g ∈ nV` that acts as the identity on some coordinate and as an element of `(n−1)V` on
   the remaining ones (`g = σ(id × s)σ^{-1}`, `s ∈ (n−1)V`, `σ` a coordinate permutation), or
   that is a product of boundedly many pairwise commuting such elements (e.g. every element
   of `V^n = V × ... × V`), `ψ(g^k) = O(k)`.
4. **Positive-drift characters are dead for the centre.** Let `Y_+ ⊆ Â` be the
   characters `χ = e^{2πiτ}` with `τ` a nonnegative finitely additive measure on the
   clopen sets and `0 < τ(C) < 1/2`; `Y_-` the conjugates. Every probability measure
   `μ` on `Y_+` (or `Y_-`) has `max_i ‖(h_i)_*μ − μ‖_TV ≥ 1/5`. Consequently, if
   `‖π(h_i)ξ − ξ‖ ≤ ε` for a unit vector `ξ`, its spectral measure on `Â` gives mass
   `≤ 10ε` to each of `Y_+`, `Y_-`. So spectral measures of almost invariant vectors
   (witnesses of failure of relative (T) of `(G, Z·1_C)`) give vanishing mass to `Y_+ ∪ Y_-`.

## What this changes

- Any proof of `cantor-integer-maps-by-v-have-haagerup-property` or of
  `brin-thompson-nv-cnd-proper-on-triangular-subgroup` must produce a cnd function that
  is proper along `k·1_C` (resp. `id × s`) yet grows at most linearly there. Word length
  only gives `O(k²)`, and the quadratic part vanishes for the easy reason that `z` is
  central in a perfect group. The linear bound is the new part.
- **Invariant:** the `V`-paradoxicality of `C` (`[0] ~ [00] ~ [01] ~ [1]`), which is
  `K_0(O_2) = 0`. It forces the first-order (imaginary) part `U ↦ Im⟨π(1_U)ξ, ξ⟩` of
  every almost invariant vector state to be a finitely additive, almost `V`-invariant
  functional of total mass `sin θ`, hence `O(ε)`.
- **Class killed (item 4):** characters whose angles are a nonnegative drift, i.e.
  weighted point configurations with positive weights and any number of atoms,
  empirical measures `(θ/N)Σδ_{x_i}`, and nonnegative non-atomic densities. This
  extends §3(g) of the artifact (boundedly many atoms, arbitrary weights) to unboundedly
  many atoms and non-atomic characters, at the price of a sign condition. The step where
  every member dies is exact: `τ/τ(C)` is a `V`-equivariant finitely additive
  probability measure, and the three elements `h_i` make it paradoxical.
- **Not ruled out:** signed drifts whose positive and negative parts cancel to first
  order. Item 1 says a witness of non-rigidity of the centre on the angle shell
  `θ ≈ 2^{-j}` needs defect `ε ≳ 2^{-j}`; it does not forbid it. Relative (T) of
  `(G, Z·1_C)` (equivalently `brin-thompson-2v-is-not-a-t-menable` through `G`) stays
  open; a spectral gap would need an inequality with `ε^α`, `α → ∞`, on shells, which
  second-order terms in item 1 show this argument cannot give.

---
rg: 2
id: finite-cd-groups-have-no-micro-supported-line-action-proof
kind: route
title: Disjointly supported nontrivial elements generate a free abelian group of full rank
target: finite-cd-groups-have-no-micro-supported-line-action
requires: []
---

**Imported facts (statement level).** From K. S. Brown, *Cohomology of Groups*,
Chapter VIII, §2:

- a group of finite cohomological dimension is torsion-free;
- `cd H ≤ cd G` for every subgroup `H ≤ G`;
- `cd Z^k = k`.

**Proof of item 1.** Choose `g_j ∈ G_{I_j}` with `g_j ≠ 1`, for `j = 1, …, k`.

- Since `cd G < ∞`, `G` is torsion-free, so each `g_j` has infinite order.
- For `i ≠ j` the homeomorphisms `ρ(g_i)` and `ρ(g_j)` have disjoint supports, so they
  commute. Since `ρ` is injective, `g_i` and `g_j` commute. So `H = ⟨g_1, …, g_k⟩` is
  abelian, and `φ : Z^k → H`, `(a_1, …, a_k) ↦ g_1^{a_1} ⋯ g_k^{a_k}`, is a surjective
  homomorphism.
- `φ` is injective. Suppose `g_1^{a_1} ⋯ g_k^{a_k} = 1`. Fix `j`. On `I_j` every factor
  except `g_j^{a_j}` acts as the identity, so `ρ(g_j^{a_j})` is the identity on `I_j`. It is
  also the identity off `I_j`, because `g_j ∈ G_{I_j}`. So `ρ(g_j^{a_j}) = id`, hence
  `g_j^{a_j} = 1` by injectivity, hence `a_j = 0` because `g_j` has infinite order.
- So `Z^k ≅ H ≤ G`, and `k = cd Z^k ≤ cd G = d`.

**Proof of item 2.** `R` contains `d + 1` pairwise disjoint nonempty open intervals.
If `ρ` were micro-supported, each of them would have a nontrivial rigid stabilizer,
contradicting item 1.

**Proof of item 3.** If `K(G,1)` is a finite CW complex of dimension `n`, then its
cellular chain complex gives a projective resolution of `Z` over `ZG` of length `n`, so
`cd G ≤ n < ∞`. Apply item 2.

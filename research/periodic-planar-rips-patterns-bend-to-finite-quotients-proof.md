---
rg: 2
id: periodic-planar-rips-patterns-bend-to-finite-quotients-proof
kind: route
title: "Proof: wrap the strip around a circle of circumference N|v|; near pairs keep their distances up to O(1/N), far pairs stay far, and flag complexes of the quotient graph are quotients of flag complexes"
target: periodic-planar-rips-patterns-bend-to-finite-quotients
requires: []
---

**Coordinates.** Rotate so that `v = (ℓ, 0)` with `ℓ > 0`. Write points as
`(x, y)`, and let `w = max_{m ∈ M} |y(m)|`; every point of `Y` has `|y| ≤ w`.
Put `D = 2r`, `L = Nℓ`, `ρ = L/2π`, and

  `β(x, y) = ((ρ + y) cos(x/ρ), (ρ + y) sin(x/ρ))`.

`τ^N` adds `L = 2πρ` to `x`, so `β` factors through `Y/⟨τ^N⟩`. Assume
`ρ > 2w`. For `p = (x_1, y_1)`, `q = (x_2, y_2)` and `θ = (x_1 − x_2)/ρ`, the
law of cosines gives

  `(*)  |βp − βq|^2 = (y_1 − y_2)^2 + 2(ρ + y_1)(ρ + y_2)(1 − cos θ)`.

**Two constants.** Consider pairs `p ≠ q` in `Y` with `|x_1 − x_2| ≤ D`.
Up to `τ` there are finitely many such pairs, because `M` is finite and
`|x_1 − x_2| ≤ D` bounds the shift. So

  `μ = min |d(p,q)^2 − r^2| > 0` (genericity) and
  `δ = min d(p,q)^2 > 0` (distinct points),

both over these pairs, are attained and positive.

**Step 1: near pairs.** Let `|x_1 − x_2| ≤ D`. By `(*)`,
`|βp − βq|^2 − (y_1 − y_2)^2 = (x_1 − x_2)^2 · g`, where

  `g = [2(1 − cos θ)/θ^2] · [(ρ + y_1)(ρ + y_2)/ρ^2]`.

Since `1 − θ^2/12 ≤ 2(1 − cos θ)/θ^2 ≤ 1` and `|θ| ≤ D/ρ`,

  `(1 − D^2/(12ρ^2))(1 − w/ρ)^2 ≤ g ≤ (1 + w/ρ)^2`.

So `| |βp − βq|^2 − d(p,q)^2 | ≤ D^2 ε(ρ)`, with `ε(ρ) → 0` as `ρ → ∞`.
Choose `ρ` with `D^2 ε(ρ) < min(μ, δ)`. For every such pair this gives
`βp ≠ βq`, and `|βp − βq| ≤ r ⟺ d(p, q) ≤ r`.

**Step 2: far pairs.** Take two distinct classes `p̄ ≠ q̄`. Choose lifts with
`x`-difference `Δ ∈ [−L/2, L/2]`. Every other pair of lifts has `x`-difference
`Δ + jL` with `|Δ + jL| ≥ |Δ|`. Suppose `|Δ| > D`. The planar distance of every
lift pair is then `> D = 2r > r`, so no lifts are adjacent in `G`. On the
circle side, both points have radius `≥ ρ − w` and angular separation
`φ ∈ (D/ρ, π]`. From `(*)`, `|βp − βq|^2 ≥ 2(ρ − w)^2(1 − cos φ) =
(2(ρ − w) sin(φ/2))^2`. Since `sin(φ/2) ≥ φ/π` on `[0, π]`,

  `|βp − βq| ≥ (2/π)(ρ − w) φ > (2/π)(1 − w/ρ) D = (4/π)(1 − w/ρ) r > r`

once `w/ρ < 1 − π/4`. So `βp̄ ≠ βq̄`, and the images are not adjacent.

**Step 3: conclusion (1).** Assume also `L > 4r`. Suppose `|Δ| ≤ D`. The
chosen lift pair `(p, q)` is the unique one, up to applying `τ^N` to both,
with `x`-difference in `[−D, D]`. Every other lift pair has
`|Δ + jL| ≥ L − D > 2r > r`, so it is not adjacent. By Step 1,
`βp̄ ≠ βq̄`, and `|βp̄ − βq̄| ≤ r` exactly when `d(p, q) ≤ r`. With Step 2
this proves (1) and the injectivity of `β_N`. Take `N_0` to be the least `N`
for which `L = Nℓ > 4r`, `ρ = Nℓ/2π > w/(1 − π/4)` (this also gives
`ρ > 2w`) and `D^2 ε(ρ) < min(μ, δ)` all hold. Each condition is monotone in
`N`.

**Step 4: flag complexes, conclusions (2) and (3).** Let `Γ = ⟨τ^N⟩`. It acts
freely on the vertices of `G`. An edge path of length `≤ 2` changes `x` by
at most `2r < L`, and `τ^{Nj}` with `j ≠ 0` changes `x` by `|j| L`. So every
non-trivial element of `Γ` moves every vertex to combinatorial distance
`≥ 3`. Under this standard condition:

- the quotient `Flag(G)/Γ` is a simplicial complex whose simplices are the
  images of cliques of `G`;
- the quotient map is a covering map with deck group `Γ`.

It remains to show that `Flag(G)/Γ = Flag(G/Γ)`, i.e. that every clique
`σ̄` of `G/Γ` lifts to a clique of `G`. Fix `ā ∈ σ̄` and a lift `a`. By (1),
each `b̄ ∈ σ̄ ∖ {ā}` has a unique lift `b` adjacent to `a`, and
`|x_b − x_a| ≤ r`. Take two such lifts `b, c`. Some pair `b, τ^{Nj} c` is
adjacent, so `|x_b − x_c − jL| ≤ r`, while `|x_b − x_c| ≤ 2r`. Hence
`|j| L ≤ 3r < L`, so `j = 0` and `b ∼ c`. The lifts form a clique mapping
bijectively onto `σ̄`. By (1), `R_r(X_N) = Flag(G/Γ)`, which proves (2).

For (3): if `G` is connected, so is its image `G/Γ`. The total space of the
covering is `R_r(Y)`, which is connected, so the covering is connected. ∎

**Remark (equivariant reduction).** Suppose a vertex `(i, 0)` is dominated
by a vertex `(i', s)` of a different orbit, `N[(i, 0)] ⊆ N[(i', s)]`. The map
`f` sending `(i, j) ↦ (i', s + j)` for all `j`, and fixing every other vertex,
is simplicial on `Flag(G)`:

- two vertices `(i, j), (i, j')` of one clique `σ` go to adjacent or equal
  vertices, because `(i', s + j) ∈ N[(i, j')] ⊆ N[(i', s + j')]`;
- every other vertex of `σ` lies in `N[(i, j)] ⊆ N[(i', s + j)]`.

The same inclusions show that `σ ∪ f(σ)` is a clique. So `f` is contiguous to
the identity, and it is a `τ`-equivariant retraction onto the complex with
the orbit of `i` removed. Removing a dominated orbit is therefore an
equivariant homotopy equivalence, and it preserves the `k[t^{±1}]`-module
`H_*(R_r(Y); k)`. The scripts in
`experiments/planar-rips-periodic-strip-2026-09-17/` use this reduction.

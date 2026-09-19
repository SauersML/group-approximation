---
rg: 2
id: full-shift-full-group-kazhdan-finite-proof
kind: route
title: "Aperiodic orbits of a full-shift full group are subsets of a line with bounded jumps; half-line cuts bound Kazhdan orbits, and faithfulness on the dense aperiodic set gives finiteness"
target: full-shift-full-group-kazhdan-subgroups-are-finite
requires: []
---

Notation as in the target. A *Kazhdan pair* `(S, ε)` for `Γ` is a finite generating set `S`
and `ε > 0` such that every unitary representation of `Γ` with a unit vector `ξ` satisfying
`max_{s∈S} ‖sξ − ξ‖ < ε` has a nonzero invariant vector. Every group with property (T) is
finitely generated and has a Kazhdan pair (standard). Apply the definition to the orthogonal
complement `W` of the invariant vectors, which is a subrepresentation with no nonzero invariant
vector. It gives: **for every `ξ ∈ W` there is `s ∈ S` with `‖sξ − ξ‖ ≥ ε‖ξ‖`.**

Each `k_s` is continuous on the compact space `X` with values in `Z`, so it is bounded. So `r` is
finite.

**Step 1 (orbits are subsets of a line with bounded jumps).** Let `x` be aperiodic. Then
`j ↦ σ^j x` is injective, and every `f ∈ [[X]]` maps `σ^j x` to `σ^{j + k_f(σ^j x)} x`. So the
orbit `O = Γx` is `{σ^j x : j ∈ P}` for a set `P ⊆ Z`, and each `s ∈ S` moves each point of `O`
by at most `r` positions: `s(σ^j x) = σ^{j'} x` with `|j' − j| ≤ r`. Write `pos(σ^j x) = j`.

**Step 2 (half-line cuts).** Let `t ∈ Z` and `A = {y ∈ O : pos(y) ≤ t}`. For `s ∈ S`, a point of
`sA \ A` is `s(y)` with `pos(y) ≤ t < pos(s(y)) ≤ pos(y) + r`. So `y` is one of the at most `r`
points of `O` with position in `(t − r, t]`, and `|sA \ A| ≤ r`. The same argument applied to
`s^{-1}`, which also moves points by at most `r` positions because it undoes `s`, gives
`|A \ sA| = |s^{-1}A \ A| ≤ r`. So `|sA Δ A| ≤ 2r`. The same count applied to a two-sided window
`F = {y ∈ O : a ≤ pos(y) ≤ b}` gives `|sF Δ F| ≤ 4r`.

**Step 3 (aperiodic orbits are finite).** Suppose `O` is infinite, and consider the permutation
representation of `Γ` on `ℓ²(O)`. `Γ` is transitive on `O`, so an invariant vector is constant, and
hence `0` because `O` is infinite. But `P` is infinite, so windows `F` as in Step 2 exist with `|F|`
arbitrarily large. The unit vectors `ξ = |F|^{−1/2} 1_F` satisfy
`‖sξ − ξ‖² = |sF Δ F|/|F| ≤ 4r/|F|`, which is `< ε²` once `|F| > 4r/ε²`. This contradicts the
Kazhdan pair. So `O` is finite.

**Step 4 (uniform bound).** Let `|O| = N ≥ 2`, list `O` in increasing position, and let `A` be the
first `m = ⌊N/2⌋` points, which is a half-line cut. Put `ξ = 1_A − (m/N) 1_O`. The invariant
vectors of `ℓ²(O)` are the constants, and `ξ ⊥ 1_O`, so `ξ ∈ W`. For each `s`,
`sξ − ξ = 1_{sA} − 1_A`, so `‖sξ − ξ‖² = |sA Δ A| ≤ 2r` by Step 2. Also
`‖ξ‖² = m(N − m)/N ≥ (N − 1)/4`: for even `N` it equals `N/4`, and for odd `N` it equals
`(N² − 1)/(4N) ≥ (N − 1)/4`. The Kazhdan inequality gives `ε² (N − 1)/4 ≤ 2r`, that is,
`N ≤ 1 + 8r/ε²`. Put `N_0 = ⌊1 + 8r/ε²⌋`. This proves item 1.

**Step 5 (faithfulness on the aperiodic set).** Aperiodic points are dense in `X`: a cylinder fixes
finitely many coordinates, and filling the rest with a sequence that is not eventually periodic
in the positive direction gives an aperiodic point. If `γ ∈ Γ` is not the identity, then
`γ(x) ≠ x` for some `x`, hence on an open neighbourhood of `x`, which contains an aperiodic point.
So `Γ` acts faithfully on the set `X_ap` of aperiodic points.

**Step 6 (finiteness).** For each aperiodic orbit `O`, the kernel `L_O` of the action on `O` is a
subgroup of index at most `N_0!`, because `Γ/L_O` embeds in `Sym(O)`. A finitely generated group has
only finitely many subgroups of index at most `N_0!`: each is the kernel of the action on the cosets
of a subgroup of index at most `N_0!`, and that action is determined by the images of the finitely
many generators in a symmetric group of degree at most `N_0!`. So the groups `L_O` take only
finitely many values, and `L = ⋂_O L_O` is a finite intersection of finite-index subgroups. So `L`
has finite index. `L` fixes every aperiodic point, so `L = {id}` by Step 5. Hence `Γ` is finite.

For the last sentence of the target: the image of a Kazhdan group under a homomorphism has
property (T), so it is a Kazhdan subgroup of `[[X]]`, and it is finite.

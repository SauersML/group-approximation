---
rg: 2
id: wobbling-normal-relative-t-locally-finite-proof
kind: route
title: "Normality gives a quantitative relative-Kazhdan projection; interval vectors in l2(Z) then bound H-orbits in windows, and bounded jumps turn a large orbit of a finitely generated subgroup into many bad points of one window"
target: wobbling-normal-relative-t-subgroups-are-locally-finite
requires: []
---

Notation as in the target. `Γ ≤ W(Z)` and `H ⊴ Γ`, with `(Γ, H)` relative (T). For a unitary
representation `(π, V)` of `Γ`, `V^H` is the space of `H`-invariant vectors and `P` is the
orthogonal projection onto it.

**Step 0 (normality makes `P` equivariant).** If `v ∈ V^H`, `g ∈ Γ` and `h ∈ H`, then
`π(h)π(g)v = π(g)π(g^{-1}hg)v = π(g)v`, because `g^{-1}hg ∈ H`. So `V^H` is `Γ`-invariant. Since `π`
is unitary, so is its orthogonal complement. Hence `P` commutes with every `π(g)`, and
`‖π(g)(1−P)ξ − (1−P)ξ‖ = ‖(1−P)(π(g)ξ − ξ)‖ ≤ ‖π(g)ξ − ξ‖`.

**Step 1 (quantitative projection).** *For every `δ ∈ (0,1)` there are a finite `Q ⊂ Γ` and
`ε > 0` such that, for every unitary representation and every unit vector `ξ` with
`max_{g∈Q} ‖π(g)ξ − ξ‖ ≤ ε`, we have `‖ξ − Pξ‖ ≤ δ`.*

Suppose not, for some `δ`. Then for each index `j = (Q, k)`, with `Q ⊂ Γ` finite and `k ≥ 1`, there
are `(π_j, V_j)` and a unit vector `ξ_j` with `max_{g∈Q} ‖π_j(g)ξ_j − ξ_j‖ ≤ 1/k` and
`‖(1−P_j)ξ_j‖ > δ`. Put `η_j = (1−P_j)ξ_j / ‖(1−P_j)ξ_j‖`, a unit vector of `(1−P_j)V_j`. By
Step 0, `‖π_j(g)η_j − η_j‖ ≤ 1/(kδ)` for `g ∈ Q`.

Let `ρ = ⊕_j (1−P_j)π_j`, a unitary representation of `Γ` by Step 0. It has almost invariant
vectors: given finite `Q` and `ε > 0`, take `k > 1/(εδ)`, and the copy of `η_{(Q,k)}` works.
If `v = (v_j)` is `H`-invariant, then each `v_j` is an `H`-invariant vector of `(1−P_j)V_j`, hence
`0`. So `ρ` has no nonzero `H`-invariant vector. This contradicts relative (T).

**Step 2 (projection in `ℓ²(Z)`).** `Γ` acts on `ℓ²(Z)` by `(gf)(n) = f(g^{-1}n)`. A vector is
`H`-invariant iff it is constant on `H`-orbits. Being square-summable, it vanishes on infinite
orbits. So `{|O|^{-1/2} 1_O : O a finite H-orbit}` is an orthonormal basis of `V^H`, and
`‖Pf‖² = Σ_{O finite} |⟨f, 1_O⟩|² / |O|`.

**Step 3 (window bound, item 1).** Fix `δ`, take `Q, ε` from Step 1, and put `r = r(Q)` and
`L_0 = max(1, ⌈4r/ε²⌉)`. Let `I = [a, b] ⊂ Z` with `L = |I| ≥ L_0`, and `ξ = L^{-1/2} 1_I`.

- For `g ∈ Q`, a point `n ∈ I` with `g(n) ∉ I` lies within `r` of an endpoint of `I`. So
  `|gI \ I| ≤ 2r`, and `|I \ gI| = |gI \ I|` because `|gI| = |I|`. So `|gI Δ I| ≤ 4r`, and
  `‖gξ − ξ‖² = |gI Δ I|/L ≤ 4r/L ≤ ε²`.
- Step 1 gives `‖ξ − Pξ‖ ≤ δ`. Since `ξ − Pξ ⊥ Pξ`, we get `‖Pξ‖² ≥ 1 − δ²`.
- Let `B ⊂ I` be the set of points whose `H`-orbit is infinite or has more than `2L` points.
  By Step 2, `L‖Pξ‖² = Σ_{O finite} |I ∩ O|²/|O|`. Split this sum three ways:
  - an orbit with `|O| ≤ 2L` contributes at most `|I ∩ O|`;
  - a finite orbit with `|O| > 2L` contributes `|I ∩ O| · |I ∩ O|/|O| ≤ |I ∩ O| · L/(2L)`;
  - infinite orbits contribute `0`.
- So `L(1 − δ²) ≤ L‖Pξ‖² ≤ (L − |B|) + |B|/2`, which gives `|B| ≤ 2δ² L`.

**Step 4 (orbits of finitely generated subgroups, item 2).**
- Let `H' = ⟨S'⟩ ≤ H` with `S'` finite and `c = max(1, r(S'))`. Each `s ∈ S'` and each `s^{-1}` moves
  every integer by at most `c`. The inverse does too: `|s^{-1}(n) − n| = |m − s(m)|` with
  `m = s^{-1}(n)`.
- Let `O'` be an `H'`-orbit. It is connected in the Schreier graph, whose edges `n — s^{±1}(n)`
  have length at most `c`. So two consecutive points of `O'` (in the order of `Z`) are at distance
  at most `c`. Otherwise no edge crosses the gap. Hence every `c` consecutive integers inside
  `[inf O', sup O']` contain a point of `O'`.
- Take `δ` with `2δ² < 1/(2c)`, and `Q, ε, L_0` from Step 3. Put `L = max(L_0, 2c)`. Suppose
  `|O'| > 2L`, where infinite is allowed.
  - Then `O'` spans at least `2L ≥ L` consecutive integers, so it contains in its span an interval
    `I` with `|I| = L`.
  - `I` contains `⌊L/c⌋` disjoint runs of `c` consecutive integers, so
    `|I ∩ O'| ≥ ⌊L/c⌋ ≥ L/c − 1 ≥ L/(2c)`, using `L ≥ 2c`.
  - Every `z ∈ I ∩ O'` has `Hz ⊇ H'z = O'`, which is infinite or has more than `2L` points. So
    `z ∈ B`, and `|B| ≥ L/(2c) > 2δ² L`.
  - This contradicts Step 3, since `L ≥ L_0`. So every `H'`-orbit has at most `2L` points.

**Step 5 (finiteness, item 3).**
- Let `N = 2L` from Step 4. `H'` acts faithfully on `Z`, because it is a group of bijections of
  `Z`. For each orbit `O`, the restriction `ρ_O: H' → Sym(O)` has target of order at most `N!`.
- After numbering `O` as `{1, …, |O|}`, `ρ_O` is determined by the images of the finitely many
  generators in some `S_k` with `k ≤ N`. So the kernels `ker ρ_O` take at most
  `Σ_{k≤N} (k!)^{|S'|}` values, each of finite index.
- Faithfulness gives `⋂_O ker ρ_O = {1}`. This is a finite intersection of finite-index subgroups,
  so `{1}` has finite index in `H'`, and `H'` is finite.
- Applied to `H' = ⟨h⟩`, every element of `H` has finite order.

**Step 6 (the corollary for `[[X]]`).**
- Let `x*` have a dense `σ`-orbit, which exists in the full shift (concatenate all finite words),
  and identify `Z` with the orbit by `j ↦ σ^j x*`. The point `x*` is aperiodic, since its orbit is
  infinite.
- Each `f ∈ [[X]]` maps `σ^j x*` to `σ^{j + k_f(σ^j x*)} x*`. Since `k_f` is continuous on the
  compact space `X`, it is bounded, so `f` acts on the orbit by a bijection of bounded displacement.
- The map `[[X]] → W(Z)` is a homomorphism. It is injective: if `f` fixes the orbit pointwise, then
  `f` is the identity on a dense set, hence everywhere by continuity.
- Relative (T) and normality pass to the isomorphic image of `Γ`. So items 1–3 hold for
  `Γ ≤ [[X]]`.

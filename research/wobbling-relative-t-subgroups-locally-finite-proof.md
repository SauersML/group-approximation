---
rg: 2
id: wobbling-relative-t-subgroups-locally-finite-proof
kind: route
title: "The uniform relative-(T) projection replaces normality; interval vectors in l2(Z) then bound H-orbits in windows, and bounded jumps turn a large orbit of a finitely generated subgroup into many bad points of one window"
target: wobbling-relative-t-subgroups-are-locally-finite
requires:
  - relative-t-subgroup-pairs-have-uniform-invariant-projection
---

Notation as in the target. `Γ ≤ W(Z)` is countable, `H ≤ Γ`, and `(Γ, H)` has relative (T). For a
unitary representation `(π, V)`, `P` is the orthogonal projection onto `V^H`.

This is the argument of `wobbling-normal-relative-t-locally-finite-proof` with its Steps 0–1
replaced by the prerequisite. Steps 2–5 are repeated so that this route stands alone. We checked
that none of them uses normality.

**Step 1 (quantitative projection, no normality).** By
`relative-t-subgroup-pairs-have-uniform-invariant-projection`, for every `δ ∈ (0,1)` there are a
finite `Q ⊂ Γ` and `ε > 0` such that every `(Q, ε)`-invariant unit vector `ξ` of every unitary
representation has `‖ξ − Pξ‖ < δ`. Countability of `Γ` is used here and nowhere else.

**Step 2 (invariant vectors of `ℓ²(Z)`).** `Γ` acts on `ℓ²(Z)` by `(gf)(n) = f(g^{-1}n)`.
- A vector is `H`-invariant iff it is constant on `H`-orbits. Being square-summable, it vanishes on
  infinite orbits.
- So `{|O|^{-1/2} 1_O : O a finite H-orbit}` is an orthonormal basis of `V^H`, and
  `‖Pf‖² = Σ_{O finite} |⟨f, 1_O⟩|²/|O|`.
- Only the `H`-action on `Z` enters, not how `H` sits in `Γ`.

**Step 3 (window bound, item 1).** Fix `δ` and take `Q, ε` from Step 1. Put `r = r(Q)` and
`L_0 = max(1, ⌈4r/ε²⌉)`. Let `I ⊂ Z` be an interval with `L = |I| ≥ L_0`, and `ξ = L^{-1/2} 1_I`.
- For `g ∈ Q`, a point of `I` that `g` maps out of `I` is within `r` of an endpoint of `I`. So
  `|gI \ I| ≤ 2r`. Also `|I \ gI| = |gI \ I|`, since `|gI| = |I|`.
- Hence `‖gξ − ξ‖² = |gI Δ I|/L ≤ 4r/L ≤ ε²`, and Step 1 gives `‖Pξ‖² = 1 − ‖ξ − Pξ‖² > 1 − δ²`.
- Let `B ⊂ I` be the points whose `H`-orbit is infinite or has more than `2L` points. By Step 2,
  `L‖Pξ‖² = Σ_{O finite} |I ∩ O|²/|O|`. An orbit with `|O| ≤ 2L` contributes at most `|I ∩ O|`. A
  finite orbit with `|O| > 2L` contributes at most `|I ∩ O| · L/(2L)`. Infinite orbits contribute
  `0`.
- So `L(1 − δ²) < (L − |B|) + |B|/2`, which gives `|B| < 2δ²L`.

**Step 4 (orbits of finitely generated subgroups, item 2).**
- Let `H' = ⟨S'⟩ ≤ H` with `S'` finite and `c = max(1, r(S'))`. Each `s^{±1}`, `s ∈ S'`, moves
  every integer by at most `c`: indeed `|s^{-1}(n) − n| = |m − s(m)|` with `m = s^{-1}(n)`.
- An `H'`-orbit `O'` is connected in the Schreier graph, whose edges have length at most `c`. So
  consecutive points of `O'` in the order of `Z` are at distance at most `c`, since otherwise no
  edge crosses the gap. Hence every `c` consecutive integers in `[inf O', sup O']` meet `O'`.
- Take `δ` with `2δ² < 1/(2c)`, and `Q, ε, L_0` from Step 3. Put `L = max(L_0, 2c)`. Suppose
  `|O'| > 2L`, where infinite is allowed.
  - Then the span of `O'` contains an interval `I` with `|I| = L`.
  - `|I ∩ O'| ≥ ⌊L/c⌋ ≥ L/(2c)`, since `L ≥ 2c`.
  - Each `z ∈ I ∩ O'` has `Hz ⊇ O'`, so `z ∈ B`. Thus `|B| ≥ L/(2c) > 2δ²L`, contradicting Step 3.
- So every `H'`-orbit has at most `N = 2 max(L_0, 2c)` points.

**Step 5 (finiteness, item 3).**
- For each `H'`-orbit `O`, `ρ_O: H' → Sym(O)` lands in a group of order at most `N!`. After
  numbering `O`, `ρ_O` is determined by the images of the finitely many generators in some `S_k`
  with `k ≤ N`.
- So `ker ρ_O` takes at most `Σ_{k≤N} (k!)^{|S'|}` values, each of finite index.
- `H'` acts faithfully on `Z`, so `⋂_O ker ρ_O = {1}` is a finite intersection of finite-index
  subgroups. Hence `H'` is finite. Taking `H' = ⟨h⟩` shows every element of `H` has finite order.

**Step 6 (subset witnesses, item 4).** Let `X ⊂ Γ` have every cnd function bounded on it. The first
bullet of the prerequisite, which holds for such subsets, gives finite `Q` and `ε` with
`sup_{x∈X} ‖xξ − ξ‖ < δ` for every `(Q, ε)`-invariant unit `ξ`. For `ξ = L^{-1/2} 1_I` with
`L ≥ ⌈4r(Q)/ε²⌉`, Step 3 shows `ξ` is `(Q, ε)`-invariant, and `‖xξ − ξ‖² = |xI Δ I|/L`.

**Step 7 (corollary for `[[X]]`).**
- `[[X]]` is countable: each element is given by a continuous `k_f: X → Z`, hence by a finite
  cylinder partition and finitely many integers.
- Fix `x*` with dense `σ`-orbit, obtained by concatenating all finite words. It is aperiodic.
  Then `f ↦ (j ↦ j + k_f(σ^j x*))` is an injective homomorphism `[[X]] → W(Z)`. Injectivity holds
  because an element fixing a dense orbit pointwise is the identity.
- Every subgroup of `[[X]]` is therefore a countable subgroup of `W(Z)`, and items 1–4 apply. □

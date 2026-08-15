---
rg: 2
id: normal-closure-fixes-gamma-fixed-algebra-proof
kind: route
title: Double the model, read invariance off the normalized centralizer, conjugate pointwise
target: normal-closure-fixes-gamma-fixed-algebra
requires: [kun-thom-nonsofic-wreath]
---

# Double the model, read invariance off the normalized centralizer, conjugate pointwise

**Item 1 (invariance).**  Projections generate `D_𝒰^{σ(Γ)}`, and its
projections are the classes `1_E` of `Γ`-invariant sets, so it suffices to
show: `E` `Γ`-invariant `⟹ σ(g)E` `Γ`-invariant.  Double the model:
replace each `A_n` by `A_n × {1,2}` with `σ` acting diagonally.  Doubling
multiplies no distances — each `σ(g)`'s moved fraction is unchanged — so
the doubled `σ` is again a sofic representation, and `Γ` is still
infranormal in `G` with both Kazhdan; Theorem 4.1 of the in-repo artifact
`research/artifacts/kun-thom-2608-06222-verified.md` applies to it:
`C_{S_𝒰}(σ(Γ))` is normalized by `σ(G)`.

For a set `E`, let `π_E` be the involution swapping `(s,1) ↔ (s,2)` for
`s ∈ E` and fixing everything else.  In the ultraproduct,
`σ(g)π_Eσ(g)^{-1} = π_{σ(g)E}`, and

```text
π_E ∈ C_{S_𝒰}(σ(Γ))   ⟺   σ(γ)Eσ(γ)^{-1}-swap = E-swap for all γ   ⟺   E is Γ-invariant,
```

since `σ(γ)π_Eσ(γ)^{-1} = π_{σ(γ)E}` and `π_F = π_E` exactly when
`F △ E` is null.  So `E` `Γ`-invariant `⟹ π_E ∈ C ⟹
σ(g)π_Eσ(g)^{-1} = π_{σ(g)E} ∈ C ⟹ σ(g)E` `Γ`-invariant.  Item 1 holds.

**Item 2 (pointwise triviality).**  Let `b ∈ D_𝒰^{σ(Γ)}`, `γ ∈ Γ`,
`u ∈ G`.  By item 1, `σ(u)^{-1}b ∈ D_𝒰^{σ(Γ)}`, so
`σ(γ)σ(u)^{-1}b = σ(u)^{-1}b`, hence

```text
σ(uγu^{-1})b = σ(u)σ(γ)σ(u)^{-1}b = σ(u)σ(u)^{-1}b = b.
```

Every conjugate of every element of `Γ` acts trivially on
`D_𝒰^{σ(Γ)}`; the set of elements acting trivially is a subgroup; hence
all of `⟨⟨Γ⟩⟩_G` acts trivially.

**The Theorem E computation.**  `⟨⟨Γ⟩⟩_G ⊆ EL_r(R)` because `EL_r(R)` is
normal in `G = EL_r(R) ⋊ SL_d(ℤ)` and contains `Γ`; conversely monomial
substitutions carry `e_{ij}(x^a)`, `a ∈ ℕ^d`, to `e_{ij}(x^c)` for every
`c ∈ ℤ^d` (every vector is an `SL_d(ℤ)`-image of a vector in `ℕ^d` — e.g.
of a positive multiple of a primitive vector — and entries add), and these
generate `EL_r(R)`.  So `⟨⟨Γ⟩⟩_G = EL_r(R)`.  An element with nontrivial
`SL_d(ℤ)`-component lies outside it, and
`compressor-coset-two-point-exact` shows the fixed algebra genuinely sees
such elements — the dichotomy is sharp on both sides.

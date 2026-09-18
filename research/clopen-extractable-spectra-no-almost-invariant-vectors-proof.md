---
rg: 2
id: clopen-extractable-spectra-no-almost-invariant-vectors-proof
kind: route
title: "Shallow clopens are rare, the leaf-uniform Lebesgue map commutes with h_1, h_2, h_3 on deep clopens, and the three-move paradox kills the averaged measure on C"
target: clopen-extractable-spectra-carry-no-almost-invariant-vectors
requires:
  - extractable-character-spectra-carry-no-almost-invariant-vectors
---

**Notation.**
- `a = h_1`, `b = h_2`, `s = h_3`, as in the target.
- `‖·‖` is the total-variation norm, so `|μ(S) − ν(S)| ≤ ‖μ − ν‖` for every set `S`.
- `η ∈ Prob(𝒞)` satisfies `‖g_*η − η‖ ≤ ε` for `g ∈ {a, b, s}`.
- The sets `{U : U ⊆ W}` are written `(U ⊆ W)`.

Throughout we use `g_*η(U ⊆ W) = η(U ⊆ g^{-1}W)`.

## Step 1: shallow clopens are rare

**Depth 1.**
- `a[0] = [00]` and `b[0] = [01]`. So `η(U ⊆ [00]) ≥ η(U ⊆ [0]) − ε` and
  `η(U ⊆ [01]) ≥ η(U ⊆ [0]) − ε`.
- These two events are disjoint, since `U ≠ ∅`, and both lie in `(U ⊆ [0])`. Hence
  `η(U ⊆ [0]) ≤ 2ε`.
- The move `s` gives `η(U ⊆ [1]) ≤ 3ε`.

**Depth 2.**
- `a^{-1}([01] ∪ [1]) = [1]`, so `η(U ⊆ [00]^c) ≤ 3ε + ε = 4ε`.
- `b^{-1}([00] ∪ [1]) = [1]`, so `η(U ⊆ [01]^c) ≤ 4ε`.
- `s^{-1}([00]^c) = [10]^c` and `s^{-1}([01]^c) = [11]^c`. So `η(U ⊆ [10]^c)` and
  `η(U ⊆ [11]^c)` are each `≤ 5ε`.

So `η(some cylinder of depth 1 or 2 misses U) ≤ 2 + 3 + 4 + 4 + 5 + 5 = 23ε`.

**Complements.** Complementation `c : 𝒞 → 𝒞` is a bijection commuting with `V`. So `c_*η` satisfies
the same hypothesis. Since `[w] ⊆ U` iff `[w]` misses `U^c`, we get
`η(some cylinder of depth ≤ 2 lies in U) ≤ 23ε`.

Call `U` *pure at* `[w]` if `[w] ⊆ U` or `[w] ∩ U = ∅`. Call `U` *deep* if it is pure at no cylinder
of depth `1` or `2`, and let `D` be the set of deep clopens. Then `η(D^c) ≤ 46ε`.

## Step 2: the leaf map is equivariant on deep clopens

**Leaves.**
- For `U ∈ 𝒞`, the pure cylinders along any point form a tail of its prefixes, since a sub-cylinder
  of a pure cylinder is pure. Clopenness makes this tail nonempty.
- The *leaves* of `U` are the maximal pure cylinders. They are pairwise disjoint, since two cylinders
  are nested or disjoint. They cover `C`, and by compactness there are finitely many.
- A pure cylinder is a leaf iff its parent is not pure, since any larger cylinder contains the parent.
- If `U` is deep, every leaf has depth `≥ 3`.

**Equivariance.**
- Each `g ∈ {a, b, s}` acts on cylinders of depth `≥ 2` by prefix replacement:
  `g[u] = [u']` with `|u'| ≥ 1`. It maps normalized Lebesgue measure `λ_[u]` to `λ_[u']`.
- For `|u| ≥ 3` the parent of `u` has depth `≥ 2`. The parent of `g[u]` is `g[parent(u)]`: check the
  prefixes `0`, `10`, `11` for `a` and `b`, and `0`, `1` for `s`.
- `g` is a bijection, so `U` is pure at `[p]` iff `gU` is pure at `g[p]`.
- So for deep `U`, `g(leaves(U))` is a partition of `C` into cylinders that are pure for `gU` and
  have impure parents. That is, each piece is a leaf of `gU`. Two leaves are nested or disjoint, and
  maximality then forces equality, so `leaves(gU) = g(leaves(U))`.

**The averaged measure.**
- Put `ρ(U) = (1/#leaves(U)) Σ_(ℓ ∈ leaves(U)) λ_ℓ ∈ Prob(C)`. Then `g_*ρ(U) = ρ(gU)` for deep `U` and
  `g ∈ {a, b, s}`.
- Let `m = ∫_D ρ(U) dη(U)`, with mass `|m| = η(D) ≥ 1 − 46ε`. Then
  `g_*m = ∫_D ρ(gU) dη(U) = ∫_(gD) ρ d(g_*η)`.
- Hence
  `‖g_*m − m‖ ≤ ‖g_*η − η‖ + η(gD Δ D) ≤ ε + η(D^c) + η(g(D^c))`.
- Also `η(g(D^c)) = (g^{-1})_*η(D^c) ≤ 46ε + ε`.
- So `‖g_*m − m‖ ≤ 94ε`, and `m' = m/|m|` satisfies `‖g_*m' − m'‖ ≤ δ := 94ε/(1 − 46ε)`.

## Step 3: the three-move paradox (proof of Theorem L)

- `m'` is a probability on `C`. `a_*m'[00] = m'[0] = b_*m'[01]`, so `m'[00]` and `m'[01]` are each
  `≥ m'[0] − δ`. Since they sum to `m'[0]`, we get `m'[0] ≤ 2δ`.
- `s` gives `m'[1] ≤ 3δ`, so `1 ≤ 5δ`.
- If `ε < 1/516`, then `470ε < 1 − 46ε`, that is `δ < 1/5`: a contradiction.

## Step 4: spectral transfer (proof of Theorem M)

- `X` is `V`-invariant, so `E(X)` commutes with `π(V)`. Put `ζ = E(X)ξ`; then
  `‖π(g)ζ − ζ‖ ≤ ε` for `g ∈ {a, b, s}`.
- The spectral law of `π(g)ζ` is `g_*μ_ζ`, where `μ_ζ` is carried by `X`.
- For each Borel partition `(S_i)`, Cauchy–Schwarz gives
  `Σ_i |⟨E(S_i)ζ',ζ'⟩ − ⟨E(S_i)ζ,ζ⟩| ≤ ‖ζ' − ζ‖(‖ζ'‖ + ‖ζ‖)`. So
  `‖g_*μ_ζ − μ_ζ‖ ≤ 2ε‖ζ‖`.
- Put `η = ‖ζ‖^{-2} ∫_X Φ dμ_ζ ∈ Prob(𝒞)`. Equivariance of `Φ` gives
  `g_*η = ‖ζ‖^{-2} ∫ Φ d(g_*μ_ζ)`, so `‖g_*η − η‖ ≤ 2ε/‖ζ‖`.
- Theorem L then gives `2ε/‖ζ‖ ≥ 1/516`, that is `‖ζ‖ ≤ 1032ε`. (If `ζ = 0` there is nothing to
  prove.)

**Families.** Atoms of a partition with at least two pieces, and nonempty level sets of a nonconstant
function, are proper nonempty clopens. The uniform law on them is equivariant because `V` permutes
them.

## Step 5: Haar extensions (proof of the Corollary)

**Pairwise singularity.**
- `A/A_B` is torsion-free: if `nf` is constant on the atoms of `B`, so is `f`.
- So for `f ∉ A_B`, evaluation at `f` is a nontrivial character of `A_B^⊥ = (A/A_B)^`. Hence
  `χ'(f)` is Haar-distributed on `T` under `μ_(B,χ)`.
- Take `(B, χ) ≠ (B', χ'')`.
  - If `B ≠ B'`, pick, by symmetry, `U ∈ B ∖ B'`. The event `{χ'(1_U) = χ(1_U)}` has
    `μ_(B,χ)`-measure `1` and `μ_(B',χ'')`-measure `0`.
  - If `B = B'`, then `χ ≠ χ''` differ at some `1_U` with `U ∈ B`, and the same event separates the
    two laws.

**Equivariant disjoint supports.**
- `v_*μ_(B,χ) = μ_(vB, χ∘v^{-1})`. So we may replace `Ω` by its `V`-orbit, which is still countable
  and consists of nontrivial `B`.
- A countable pairwise singular family has pairwise disjoint Borel sets `X_ω` with `μ_ω(X_ω) = 1`.
  Intersect the separating sets over pairs, then remove the earlier ones.
- Put `X'_ω = ∩_(v ∈ V) v^{-1} X_(vω)`. It is a countable intersection of `μ_ω`-conull sets, so
  `μ_ω(X'_ω) = 1`. It satisfies `u X'_ω = X'_(uω)` and `X'_ω ⊆ X_ω`.
- Let `X = ⊔_ω X'_ω`, and on `X'_(B,χ)` let `Φ` be the uniform law on the atoms of `B`. This `Φ` is
  Borel and equivariant, and every atom lies in `𝒞` because `B` is nontrivial.
- A vector whose spectral law is `≪ Σ μ_ω` has its `X^c` part equal to `0`. So Theorem M gives the
  bound.

## Remark (why Theorem K does not already apply)

- Suppose `Ψ : Prob(𝒞) → Prob(C)` were `V`-equivariant. Then `Ψ(δ_U)` would be a
  `Stab_V(U)`-invariant probability on `C = U ⊔ U^c`.
- `Stab_V(U)` contains `V_U × V_(U^c)`, each factor acting on its piece as `V` acts on `C`. So the
  halving paradox forbids an invariant probability on either piece.
- Hence Theorem M does not follow by composing `Φ` with an equivariant map to `Prob(C)`. The
  approximate equivariance of `ρ`, for three elements on deep clopens, is what replaces such a map.
- Whether the Haar-extension sets carry some other equivariant Borel map to `Prob(C)` is not decided
  here. The kill above does not need that question answered.

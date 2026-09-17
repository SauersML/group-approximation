---
rg: 2
id: commensurating-loxodromics-split-their-centralizers-proof
kind: route
title: "Only finitely many z-orbits carry a one-ended trace of A; the centralizer permutes them and translates each"
target: commensurating-loxodromics-split-their-centralizers
requires: []
---

Notation is as in the target.

**Step 1 (orbit decomposition).** Split `X` into `⟨z⟩`-orbits `O`, and write `B_O = A ∩ O`.
Then `z^N A Δ A` is the disjoint union of the sets `z^N B_O Δ B_O`, so
`ℓ(z^N) = Σ_O |z^N B_O Δ B_O|`. Let `F` be the set of orbits with `z B_O ≠ B_O`. Each such
orbit contributes at least `1` to `ℓ(z)`, so `F` is finite. For `O ∉ F` the set `B_O` is
`z`-invariant and contributes `0` to every `ℓ(z^N)`.

**Step 2 (types of orbits in `F`).**
- If `O` is finite, its contribution is at most `|O|`.
- If `O` is infinite, identify `O ≅ Z` with `z` acting as `+1`. Then `(B_O + 1) Δ B_O` is finite,
  so `B_O` has finite symmetric difference with one of `∅`, `Z`, `[0,∞)` or `(−∞,0]`.
  - If `B_O` is finite or cofinite, then `|(B_O+N) Δ B_O| ≤ 2 min(|B_O|, |Z∖B_O|)`, which is
    bounded in `N`.
  - If `B_O` is *one-ended*, meaning finite symmetric difference with `[0,∞)` or `(−∞,0]`, then
    `|(B_O+N) Δ B_O| ≥ |N| − 2|B_O Δ H|`, where `H` is the half-line. Indeed `(H+N) Δ H` has `|N|`
    elements, and changing `B_O` by `k` points changes the count by at most `2k`.

Let `T` be the set of infinite orbits with one-ended `B_O`, so `T ⊆ F` is finite. Then `ℓ(z^N)`
is unbounded if and only if `T ≠ ∅`. By hypothesis, `T ≠ ∅`.

**Step 3 (the centralizer permutes `T`).** Let `g ∈ C_G(z)`. Since `gz = zg`, `g` maps
`⟨z⟩`-orbits to `⟨z⟩`-orbits `z`-equivariantly. Let `O ∈ T` and put `O' = gO`, an infinite orbit.
Then `g B_O = gA ∩ O'`, which differs from `A ∩ O' = B_{O'}` by a subset of the finite set
`gA Δ A`. Transport by the equivariant bijection `g : O → O'` preserves one-endedness, so
`O' ∈ T`. Hence `C_G(z)` acts on the finite set `T`. Let `C'` be the kernel of this action. It
has finite index in `C_G(z)`, and `z ∈ C'` because `z` preserves each of its own orbits.

**Step 4 (the character).** Fix `O ∈ T` and identify `O ≅ Z` with `z = +1`. Each `g ∈ C'`
restricts to a bijection of `O` commuting with `+1`, which is translation by some integer
`φ(g)`: put `φ(g) = g(0)`, and then `g(m) = g(z^m 0) = z^m g(0) = m + φ(g)`. Composition of
translations adds, so `φ : C' → Z` is a homomorphism, and `φ(z) = 1`. This proves item 1.

**Step 5 (item 2).** Suppose `z` were not elliptic, and take `C'` and `φ` from item 1. The
subgroup `S ∩ C'` has finite index in `S`, so it equals `S`. Thus `φ|_S : S → Z` is a
homomorphism with `φ(z) = 1`. It factors through `S/[S,S]`, where `z` has finite order `k`. So
`k = φ(z^k) = 0`, a contradiction. The case of a central element of a perfect group is `k = 1`
with `S ≤ C_G(z)`.

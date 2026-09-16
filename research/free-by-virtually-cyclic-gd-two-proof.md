---
rg: 2
id: free-by-virtually-cyclic-gd-two-proof
kind: route
title: Free stabilizers by Serre and Stallings-Swan, then a graph of free groups
target: free-by-virtually-cyclic-torsion-free-groups-have-gd-two
requires: []
artifacts:
  - research/artifacts/eg-special-case-virtually-free-by-cyclic-2026-09-16.md
---

## Proof

The full proof is Theorem A, Lemma L and Corollary A1 in the cited artifact. The imports are
standard textbook results: Serre's cd theorem, Stallings--Swan, Bass--Serre, Scott--Wall
Proposition 3.6 and Karrass--Pietrowski--Solitar. They were recalled, not fetched this session.

Setting: `G` is torsion-free, `N ⊲ G` is free, and `Γ = G/N` acts on a tree `T` without
inversions and with finite vertex stabilizers.

1. **Free stabilizers.** `G` acts on `T` through `G → Γ`. A stabilizer `G_x` contains `N` with
   index `|Γ_x| < ∞`. `G_x` is torsion-free, so `cd G_x = cd N ≤ 1` by Serre. Stallings--Swan
   makes `G_x` free.
2. **Graph of groups.** By Bass--Serre, `G` is the fundamental group of a graph of free groups
   with injective edge maps.
3. **Graph of spaces.**
   - Realize each vertex and edge group by a wedge of circles, and each edge monomorphism by a
     based cellular map.
   - Glue edge cylinders `X_e × [0,1]` to the vertex spaces. The result is a CW complex of
     dimension at most 2.
   - By Scott--Wall it is aspherical with fundamental group `G`, so `gd G ≤ 2`.
   - If `cd G ≤ 1`, then `G` is free, so `gd G = cd G`.
4. **Virtually cyclic quotients.** If `Γ` is virtually infinite cyclic, it acts on the
   simplicial line `(1/2)Z` as the hypothesis requires.
   - Let `C_0 ≅ Z` be a normal finite-index subgroup, and `Γ_+` the centralizer of `C_0`, of
     index at most 2.
   - Restriction `H^1(Γ_+;Q) → H^1(C_0;Q)` is onto, which gives `τ: Γ_+ → Z` with finite
     kernel.
   - An element `s ∉ Γ_+` satisfies `τ(sxs^{-1}) = −τ(x)` and `τ(s^2) = 0`.
   - Hence `x ↦ (t ↦ t + τ(x))` and `xs ↦ (t ↦ −t + τ(x))` is a homomorphism into integer
     translations and integer reflections. It inverts no edge of `(1/2)Z`, and its vertex
     stabilizers have order at most `2|ker τ|`.
   - If `Γ` is finite, it fixes a point.

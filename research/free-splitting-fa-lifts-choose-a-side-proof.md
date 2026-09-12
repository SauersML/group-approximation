---
rg: 2
id: free-splitting-fa-lifts-choose-a-side-proof
kind: route
title: FA gives a fixed vertex, and finite abelianization makes a fixed cyclic vertex standard
target: free-splitting-fa-lifts-choose-a-side
requires: []
artifacts:
  - research/artifacts/bh-aut-out-virtual-section-2026-09-12.md
---

Full argument: Section 2 of the artifact.

1. **Injectivity of `J_B`.** If `id ∗ β = ι_x`, then `x` centralizes `p` and
   normalizes `B`. So `x ∈ ⟨p⟩ ∩ B = 1`, and `β = id`.
2. **Action on `T`.** Write `φ = ι_y (id ∗ β) ∈ π^{-1}(J_B)`. It acts on `T`
   by `x⟨p⟩ ↦ φ(x) y⟨p⟩` and `xB ↦ φ(x) yB`, and on edges by `x ↦ φ(x) y`.
   - This is well defined because `φ(p^m) = y p^m y^{-1}` and
     `φ(b) = y β(b) y^{-1}`.
   - It preserves vertex types, so it has no inversions.
3. **Fixed vertex.** `Λ` has FA, so `s(Λ)` fixes a vertex.
4. **A fixed `⟨p⟩`-vertex gives (S).** If `x⟨p⟩` is fixed, conjugate by `ι_x`
   so that `⟨p⟩` is fixed.
   - Then `y(λ) ∈ ⟨p⟩`, and `λ ↦ y(λ)` is a homomorphism to `⟨p⟩ ≅ Z`.
   - Finite abelianization makes it trivial, so `s(λ) = id ∗ β_λ`.
   - The fixed tree of the standard lift is the star of `⟨p⟩`. The fixed
     `⟨p⟩`-vertices `x⟨p⟩` need `(id ∗ β)(x) ∈ x⟨p⟩` for all `β` in a
     finite-index subgroup of `Aut(B)`, `rank B ≥ 2`, which forces
     `x ∈ ⟨p⟩`. The fixed `B`-vertices are its neighbours `p^m B`.
5. **Otherwise (N).** If no `⟨p⟩`-vertex is fixed, the fixed tree contains no
   edge, so it is a single `B`-vertex.
   - Conjugating it to `B` gives `y(λ) ∈ B`.
   - `y` is a cocycle because `s` is a homomorphism.
   - `ι_{y(λ)} β_λ` restricted to `B` is the homomorphism `ρ`.

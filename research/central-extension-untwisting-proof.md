---
rg: 2
id: central-extension-untwisting-proof
kind: route
title: Continuous cocycles splitting the constant extension, their restriction to stabilizers, the retract through a unit, and the square complex count
target: central-extension-untwisting-over-boundaries
requires: [tree-lattice-kgraph-power-phase-proof]
---

**Item 1.** Such an action is exactly a continuous map `κ : C x Y -> A` with
`κ(γ̃δ̃, y) = κ(γ̃, δ̄y) + κ(δ̃, y)` and `κ(z, y) = z`.
- **Existence gives a splitting.** Fix a set-theoretic section `s : C̄ -> C`. Then
  `f(γ̄)(y) = κ(s(γ̄), y)` is a 1-cochain with values in `C(Y, A)`. Its coboundary is
  the image of the 2-cocycle `(γ̄, δ̄) ↦ s(γ̄)s(δ̄)s(γ̄δ̄)^(-1) ∈ A`.
- **A splitting gives existence.** Conversely, a 1-cochain `f` with that coboundary
  defines `κ(s(γ̄) z, y) = f(γ̄)(y) + z`, and the cocycle identity follows from the
  coboundary equation.
- **Freeness and faithfulness.** `A` acts by translation on the second coordinate,
  hence freely. If `γ̃` acts trivially, then `γ̄` acts trivially on `Y`, so `γ̃ ∈ A`,
  and then `γ̃ = 0`.

**Item 2.** For `γ̃, δ̃ ∈ Stab_C(y)`, `κ(γ̃δ̃, y) = κ(γ̃, y) + κ(δ̃, y)`. So `κ(·, y)` is
a homomorphism `Stab_C(y) -> A` that is the identity on `A`, and the extension splits
over `Stab_(C̄)(y)`.

**Item 3.** Continuous cochains pull back along continuous groupoid homomorphisms.
`ι(g) = (g, t_0)` and `pr(g, k) = g` satisfy `pr ∘ ι = id`, so
`ι^* pr^* = id` on `H^*(𝒢; A)`. A twist `Σ` pulls back to `pr^*Σ`, and
`ι^* pr^* [Σ] = [Σ]`. For the pitfall: `Hom(C_c(W, Z), A)` assigns an element of `A`
to each compact open set additively. It is a measure, and it equals a continuous
function only after fixing a reference measure. Matui's chain complex
`C_c(𝒢^(n), Z)` therefore dualizes to measure cochains, not to the continuous
cochains that classify twists.

**Item 4.** `g` and `h` translate the lines `L_1` and `L_2`, so they fix the ends of
both lines and hence the points of `∂T_1 x ∂T_2` spanned by them. The commutator of
lifts `[g̃, h̃] ∈ A` is the value of `ω` on the generator of `H_2(Z²)`, the torus
class. By item 2 it is `0`. With phases, `γ` moves the phase of a fixed `ξ` by its
Busemann lag mod `N` (Step 5 of the phase route), so the stabilizer of `(ξ, r)` in
`Z²` is the lattice of elements whose lag is `0 mod N`.

**Item 5.** `K` has one vertex, `m + n` edges and `mn` squares (the link is
`K_(2m,2n)`, and each square gives four corners), so `χ(K) = 1 - (m+n) + mn`. `K` is
aspherical, with `π_1 = Λ` simple, so `b_1 = 0`, and `H_2(K)` is free (top dimension)
of rank `χ - 1`. For perfect `Λ`, universal coefficients give
`H²(Λ; A) = Hom(H_2(Λ), A)`, and the extension is perfect iff `ω` is onto (standard).

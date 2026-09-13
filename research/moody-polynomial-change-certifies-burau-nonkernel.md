---
rg: 2
id: moody-polynomial-change-certifies-burau-nonkernel
kind: claim
title: "Moody's criterion: if a braid changes the Moody polynomial of some arc configuration, it is not in the Burau kernel"
artifacts:
  - research/artifacts/zp-burau-four-strand-mechanism-2026-09-13.md
---

Let `n ≥ 3`. In `D_n`, let `α` be the arc from `p_1` to `p_2`, and `β_*^3` the arc from the boundary
point `p_*` to `p_3`. For `Γ ∈ B_n` write `𝕄_Γ = 𝕄(α, (β_*^3)Γ)`, where
`𝕄(α, β) = Σ_ℓ (t^ℓ α̃, β̃) t^ℓ` is the equivariant algebraic intersection number of lifts to the
infinite cyclic cover.

Claim: if `𝕄_{Ψ·Γ} ≠ 𝕄_Γ` for some `Γ ∈ B_n`, then `Ψ ∉ ker ρ_n`.

This is Theorem 2.3 of arXiv:2607.05283v1, attributed there to Moody (J. A. Moody, "The Burau
representation of the braid group B_n is unfaithful for large n", Bull. Amer. Math. Soc. 25
(1991)). The convention `𝕄_Γ = 𝕄(α, (β_*^3)Γ)` comes from the HTML render and has not yet been
checked against the PDF.

## Attempts

- 2026-09-13 (lane z3-05-burau-theory), artifact §2.6: the direction is consistent. The cover is
  invariant under all boundary-fixing mapping classes, so `𝕄((x)g, (y)g) = 𝕄(x, y)`. If the
  pairing factors through relative homology classes on which `B_n` acts through the unreduced
  Burau representation, then `Ψ ∈ ker ρ_n` gives `𝕄_{Ψ·Γ} = 𝕄((α)Γ^{-1}, (β_*^3)Ψ) = 𝕄_Γ`.
- Still to do before establishing: (a) name the relative homology module in which arcs from
  `p_*` to a puncture define classes, and prove that `ker ρ_n` acts trivially on it. Unreduced
  Burau is the action on `H_1` of the cover relative to the fiber over `p_*`, and the arcs end at
  punctures, which needs a locally finite or truncated version. (b) Read Moody 1991, or
  Long–Paton 1993, for the exact published statement.

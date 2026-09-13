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
(1991)).

## Attempts

- 2026-09-13 (lane z3-05-burau-theory), artifact §2.6: the direction is consistent. The cover is
  invariant under all boundary-fixing mapping classes, so `𝕄((x)g, (y)g) = 𝕄(x, y)`. If the
  pairing factors through classes on which `B_n` acts through the unreduced Burau representation,
  then `Ψ ∈ ker ρ_n` gives `𝕄_{Ψ·Γ} = 𝕄((α)Γ^{-1}, (β_*^3)Ψ) = 𝕄_Γ`.
- 2026-09-13 (check owner z3-05-burau-search, artifact
  `zp-burau-n4-verification-2026-09-13-part1.md`, landed 5c5c59481a): Moody's criterion checked
  OK.
  - The preprint pairs `α` with the class, in `H_1(D̃, p̃_*)`, of the loop bounding a neighborhood
    of the arc. `B_n` acts on `H_1(D̃, p̃_*)` through the unreduced Burau representation.
  - That pairing equals `(1 − t)·𝕄` up to a unit. `Z[t, t^{-1}]` is a domain, so a change of one is
    a change of the other.
  - The convention `𝕄_Γ = 𝕄(α, (β_*^3)Γ)` matches the preprint's tex source.
- Still to do before establishing: write the resulting proof as a `-proof` route (the loop class,
  the Burau action on `H_1(D̃, p̃_*)`, and the `(1 − t)` factor), then have it reviewed. Nothing
  about the open core (G1–G5 of the check) depends on this claim's route.

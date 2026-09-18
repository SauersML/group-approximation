---
rg: 2
id: long-reid-specializations-k-and-minus-one-minus-k-are-conjugate
kind: claim
title: The Long–Reid specializations rho_k and rho_{-1-k} of the figure-eight knot group have SL_3(Z)-conjugate images, fibre to fibre
distinct_from:
  sl3z-contains-cd2-group-with-fg-nonfree-normal-subgroup: that hole records the Long–Reid strategy for a Bieri witness; this is an exact symmetry of the parameter k that halves the set of integer specializations the strategy must examine
  sl3z-normal-f2-subgroups-have-virtually-cyclic-quotients: that claim constrains groups with a normal F_2; this is a matrix identity inside one explicit family, saying nothing about kernels beyond an automorphism of F
artifacts:
  - experiments/sl3z-long-reid-census-2026-09-17/lr_conjugacy.py
  - experiments/sl3z-long-reid-census-2026-09-17/lr_conjugacy.out
  - experiments/sl3z-long-reid-census-2026-09-17/lr_conjugacy_gamma.py
  - experiments/sl3z-long-reid-census-2026-09-17/lr_conjugacy_gamma.out
---

**Setting** (Long–Reid, Exp. Math. 20(4) (2011) 412–425, Prop. 2.1). Let
`Γ = <x, y, z | z x z^-1 = x y, z y z^-1 = y x y>` be the figure-eight knot
group, with fibre `F = <x, y>`. For an integer `k`, `ρ_k: Γ -> SL_3(Z)` sends
`x, y, z` to

- `X_k = [[1, -2, 3], [0, k, -1-2k], [0, 1, -2]]`,
- `Y_k = [[-2-k, -1, 1], [-2-k, -2, 3], [-1, -1, 2]]`,
- `Z_k = [[0, 0, 1], [1, 0, -k], [0, 1, -1-k]]`.

**Claim.** Put `C = [[0, 1, -2], [1, 1, -1], [1, 0, 0]]`, so `det C = 1`. For
every integer `k` (indeed as polynomial identities in `k`):

1. `C X_{-1-k} C^-1 = Y_k`;
2. `C Y_{-1-k} C^-1 = X_k^-1`;
3. `C Z_{-1-k} C^-1 = Z_k^-1 Y_k^-1`.

**Consequences.**

- `C ρ_{-1-k}(F) C^-1 = <Y_k, X_k^-1> = ρ_k(F)`, and
  `C ρ_{-1-k}(Γ) C^-1 = <Y_k, X_k^-1, Z_k^-1 Y_k^-1> = ρ_k(Γ)`.
- `ρ_{-1-k}|F = Ad(C^-1) ∘ ρ_k|F ∘ s`, where `s ∈ Aut(F)` is `s(x) = y`,
  `s(y) = x^-1`. So `ρ_{-1-k}` is injective on `F` iff `ρ_k` is.
- Every conjugation-invariant property of the pair `(ρ_k(Γ), ρ_k(F))` is shared
  by `k` and `-1-k`. This covers finite index, thinness, whether `Z_k` powers
  into `ρ_k(F)` (Long–Reid Question 4.3), cohomological dimension, type FP,
  Euler characteristic, and the fibration `ρ_k(Γ) -> ρ_k(Γ)/ρ_k(F)`.
- Long–Reid Theorem 4.1 gives finite index for `k = 0, 2, 3, 4, 5`. So finite
  index also holds for `k = -1, -3, -4, -5, -6`.
- The integer specializations whose index is unknown come in conjugate pairs:
  `{1, -2}` and `{k, -1-k}` for `k >= 6`. Any search over the family (finite
  index, Question 4.3, incoherence witnesses) needs only `k = 1` and `k >= 6`.

The proof is the route
`long-reid-k-minus-one-minus-k-conjugacy-proof`.

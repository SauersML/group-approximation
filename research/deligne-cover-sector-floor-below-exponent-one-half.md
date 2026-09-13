---
rg: 2
id: deligne-cover-sector-floor-below-exponent-one-half
kind: claim
title: At genus g >= 3 every nontrivial-sector tuple of a finite Deligne cover has normalized relator defect at least c d^(-b) for some b < 1/2
artifacts:
  - research/artifacts/deligne-hs-metric-ladder-2026-09-13.md
distinct_from:
  deligne-symplectic-covers-are-not-schatten-approximated: that proves the floor with exponent b = 1/2 from Frobenius stability; this asks for any exponent strictly below 1/2, which needs an input beyond dimension-free Frobenius stability.
  deligne-stable-triple-cover-is-not-hyperlinear: that is the floor with exponent b = 0 (a dimension-free normalized gap) at some genus; this asks only for a polynomial floor with a better exponent than the Frobenius one, and does not decide hyperlinearity.
  maslov-bounded-block-sector-gap: that gives a dimension-uniform gap on the mass carried by bounded blocks; this concerns all tuples, including irreducible ones of unbounded dimension.
---

**OPEN.** Notation of `deligne-symplectic-covers-are-not-schatten-approximated`: `g >= 3`,
`n >= 3`, `Gamma_n` the preimage of `Sp_(2g)(Z)` in the connected `n`-fold cover of
`Sp_(2g)(R)`, a finite presentation `<S cup {z} | R>`, and normalized Hilbert--Schmidt norm
`||A||_HS = d^(-1/2) tr(A^*A)^(1/2)` on `M_d(C)`.

**Claim.** There are `b < 1/2` and `c > 0` such that for every `d >= 1`, every `zeta` with
`zeta^n = 1` and `zeta^2 != 1`, and every `rho : S cup {z} -> U(d)` with `rho(z) = zeta I`,

```text
max_(r in R) ||rho(r) - I||_HS >= c d^(-b).                         (SF1)
```

Equivalently, the least unnormalized Frobenius sector defect `F(d) = d^(1/2) sigma(d)` grows at
least like `d^(1/2 - b)`. The established floor is `F(d) >= delta_n`.

**Where it sits.**
- `b = 1/2` is `(SG1)` of `deligne-symplectic-covers-are-not-schatten-approximated`.
- `b = 0` at genus `g` is non-hyperlinearity of `Gamma_n` at that genus, by the sector-gap
  equivalence (genus-independent commentary in `deligne-stable-triple-cover-is-not-hyperlinear`).
- Even `F(d) -> infinity` with no rate would be new and is not implied by `(SG1)`.
- **Reduction to g = 3.** A genus-`g` tuple restricts, through the block embedding of
  `deligne-cover-hyperlinearity-is-monotone-in-genus`, to a genus-3 tuple of the same dimension
  whose relator defects are at most a constant times the genus-`g` defects. So `(SF1)` at `g = 3`
  implies it at every `g >= 3` with the same exponent.

**Monotone profile.** Put `sigma(d)` for the least left side of `(SF1)` in dimension `d`.
Tensoring with `1_m` gives `sigma(dm) <= sigma(d)`. Direct sums with a remainder block give
`sigma(D)^2 <= sigma(d)^2 + 4d/D`. So `sigma` is essentially non-increasing, `liminf sigma = 0`
iff `lim sigma = 0`, and `(SF1)` is a statement about the *rate* at which hypothetical
microstates could improve.

## Attempts

- **Linear-rate Frobenius stability does not move the exponent.** Assume `dist_F <= K def_F`
  whenever `def_F <= delta_0`. A sector tuple with Frobenius defect `eta d^(1/2) <= delta_0` then
  has `eta >= |1 - zeta^2| / (2K)`. Above the threshold nothing is said. The floor stays
  `min(delta_0, c) d^(-1/2)`: every rate statement that only applies below a fixed Frobenius
  threshold dies here.
- **DGLT iteration in the normalized norm with the trivial operator bound.** The quadratic error is
  `||b||_op ||b||_HS <= d^(1/2) ||b||_HS^2 <= d^(1/2) K^2 eta^2`. It contracts only when
  `eta < c d^(-1/2)`. Exponent 1/2 again.
- **Tensor and exterior powers.** `rho^(tensor k)` and `Lambda^k rho` multiply the dimension by a
  power while the normalized defect grows by a factor up to `k`; every such amplification worsens
  the exponent. The determinant `Lambda^d` is one-dimensional with defect about `d eta`, so it gives
  at best a floor of order `1/d`, and nothing for the dimensions where the scalar class is exactly
  realizable.
- **Operator-norm sector emptiness would not suffice.** Even the open
  `deligne-nontrivial-maslov-opnorm-sectors-are-empty` (at this genus) gives one singular value of
  size `tau_0`, which is consistent with bounded Frobenius defect.

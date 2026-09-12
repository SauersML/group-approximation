---
rg: 2
id: atlas-defect-gap-limit-proof
kind: route
title: Compactness for positivity, direct sums for subadditivity, Fekete for the limit
target: atlas-defect-gap-limit
requires: [atlas-steinberg-rank-five-translation, atlas-relator-central-sufficiency]
artifacts:
  - research/artifacts/hyperlinear-q34-audit-2026-08-16.md
---

# Compactness, direct sums, Fekete

**1. Attained, and positive.**  `U ↦ max_{s ∈ T_St} ‖π_U(s) − I‖₂` is
continuous on the compact group `U(20160k)`, so the minimum is attained at some
`U₀`.  If `d_k = 0` then every relator holds exactly at `U₀`, so `π_{U₀}` is a
genuine `20160k`-dimensional unitary representation of
`E = P̄/⟨⟨T_St⟩⟩ ≅ St₅(L_{F₂}(1,2))`, and it is nontrivial because the first
chart is `λ ⊗ I_k`.  Minimal almost periodicity of `E` (the corpus fact carried
by `leavitt-steinberg-hs-stability-fork`, `notes/ATLAS_HS_CRITERION.md`) forbids
this.

An independent derivation, not needing minimal almost periodicity as an input:
by `atlas-relator-central-sufficiency`, `E` is a perfect central extension of
the infinite simple `Q`, and `π_{U₀}(E)` would be a finitely generated linear
group, hence residually finite (Malcev); but every finite quotient of a
perfect central extension of an infinite simple group is trivial — a
finite-index normal subgroup surjects onto `Q`, so the quotient is a quotient
of the centre, hence abelian, hence trivial by perfectness.  Residual
finiteness then forces `π_{U₀}(E) = 1`, contradicting nontriviality on the
first chart.

**2. Subadditivity.**  Let `U ∈ U(20160k)` and `V ∈ U(20160ℓ)`.  The basis
permutation identifying `(λ ⊗ I_k) ⊕ (λ ⊗ I_ℓ)` with `λ ⊗ I_{k+ℓ}` conjugates
both charts alike, so `U ⊕ V` (transported through it) is a legitimate
competitor at multiplicity `k + ℓ`, with

```text
‖π_{U⊕V}(s) − I‖₂² = ( k‖π_U(s) − I‖₂² + ℓ‖π_V(s) − I‖₂² ) / (k + ℓ)
```

because the normalized trace of the sum is the multiplicity-weighted average
of the two.  Taking the max over `s` and bounding each summand by its own
maximum,

```text
(k + ℓ) d_{k+ℓ}² ≤ k d_k² + ℓ d_ℓ² .
```

**3. Fekete.**  `a_k = k d_k²` is subadditive and nonnegative, so
`lim_k a_k/k = inf_k a_k/k`, i.e. `lim_k d_k² = inf_k d_k²`. ∎

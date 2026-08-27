---
rg: 2
id: atlas-stabilizer-slice-stationary-proof
kind: route
title: Exact integer differentiation of the atlas traces along the stabilizer slice
target: atlas-stabilizer-slice-stationary
requires: [atlas-steinberg-rank-five-translation, atlas-true-criterion-baseline]
artifacts:
  - research/artifacts/hyperlinear-q34-audit-2026-08-16.md
---

# Exact integer differentiation of the atlas traces along the stabilizer slice

The usable list `T_St` and its active subset are the inputs: by
`atlas-steinberg-rank-five-translation` the relators are explicit words in the
twelve atlas generators, and by `atlas-true-criterion-baseline` the objective
at `J` is supported on exactly the 72 relators escaping
`ker(P̄ ↠ A₈ × A₈)`, the other 4,564 being exactly zero and serving as the
control slice.

**1. Tangent.**  With `D_t = I_{ℓ²(M)} ⊗ e^{tK}` and `U_t = D_t J`, the first
chart is constant in `t` and a second-chart letter `b` contributes
`D_t R_b D_t*`, whose derivative at `0` is `[K, R_b]`.

**2. Cyclicity.**  For a word `w`, `π_{U_t}(w)` is a product of first-chart
left translations and conjugated right translations, so `f_w'(0)` is a finite
sum, one term per second-chart occurrence, of
`Tr(K R_b Q P) − Tr(K Q P R_b)` where `P` and `Q` collect the left/right
regular permutations to either side of that occurrence.

**3. Integrality.**  `K = I_{ℓ²(M)} ⊗ k` with `k` an arbitrary skew-Hermitian
`15 × 15` matrix, and every `R`, `L`, `P`, `Q` is a permutation of the regular
basis.  Each term is therefore `⟨k, G⟩` for an integer `15 × 15` matrix `G`
counting coset transitions, and `f_w'(0) = ⟨k, G_w⟩` with `G_w` the signed sum
over the occurrences.  Vanishing for *every* `K` is thus equivalent to
`G_w = 0`, a finite integer identity — decidable exactly, with no numerical
tolerance.

**4. Enumeration.**  Over the 72 active relators there are 1,052 second-chart
insertion sites falling into 40 distinct transition-coefficient cases, and
`G_w = 0` for all 72.

**5. Defects.**  Each `π_{U_t}(w)` is unitary, so
`‖π_{U_t}(w) − I‖₂² = 2 − 2 Re tr π_{U_t}(w)`, and the squared defect inherits
the vanishing derivative. ∎

The computation was performed with an exact integer checker
(`atlas_stabilizer_stationarity_check.py` in the audit's sandbox, not landed
here); its inputs are the same relator JSON the committed Stage-1 script
consumes, and `atlas-stabilizer-commutant-no-go` independently rules the whole
family out, so re-running it is a consistency check rather than a dependency.

---
rg: 2
id: atlas-stabilizer-slice-stationary
kind: claim
title: The index-15 stabilizer slice is exactly first-order stationary at the tensor flip
distinct_from:
  atlas-true-criterion-baseline: that is the exact value of the objective at the classical warm starts; this is the exact derivative of the objective at one of them, along the index-15 slice, and it is what makes the flat Stage-1 pilot structural rather than numerical.
  atlas-stabilizer-commutant-no-go: that is a uniform positive lower bound over the whole commutant family at every multiplicity; this is a vanishing first derivative in one slice at one point, and neither implies the other.
artifacts:
  - research/artifacts/hyperlinear-q34-audit-2026-08-16.md
  - research/artifacts/atlas-true-criterion-probe-2026-08-15.md
  - experiments/atlas_true_criterion_stage1.py
---

For the Stage-1 family of `atlas-true-criterion-baseline` §(d) —
`U_t = (I_{ℓ²(M)} ⊗ e^{tK}) J` with `M < A₈` the index-15 stabilizer of a
nonzero vector under `A₈ ≅ GL₄(𝔽₂)` and `K` skew-Hermitian in `M₁₅(ℂ)` — every
active relator's normalized trace is stationary at `t = 0`:

```text
d/dt|₀ tr π_{U_t}(w) = 0    for every skew-Hermitian K and every active w,
```

and hence, by `‖W − I‖₂² = 2 − 2 Re tr W` for unitary `W`, so is every squared
normalized-HS defect.  The statement is relator-by-relator, not an average over
the loss, and it is exact: the derivative reduces to an integer pairing.

**The reduction.**  At `t = 0` a second-chart letter `b` acts as the right
translation `R_b`, and `d/dt|₀ (D_t R_b D_t*) = [K, R_b]` for
`D_t = I_{ℓ²(M)} ⊗ e^{tK}`.  Differentiating `f_w(t) = tr π_{U_t}(w)` gives a
sum over the second-chart occurrences in `w`, each term reduced by cyclicity to
`Tr(K R_b Q P) − Tr(K Q P R_b)` with `P, Q` products of left/right regular
permutations.  Because `K = I_{ℓ²(M)} ⊗ k`, each trace is an exact integer
pairing of the free `15 × 15` matrix `k` against a `15 × 15` transition-count
matrix — no floating-point step anywhere.

**The computation.**  Over the 72 active relators (the cartesian escapees
identified in `atlas-true-criterion-baseline`), 1,052 second-chart derivative
insertion sites, and 40 distinct transition-coefficient cases: **zero relators
have a nonzero trace derivative**.

**What it explains.**  The MSI Stage-1 pilot (job 15868462, 60 Adam iterations
at lr `3e-3`) moved the total loss by `~1.1e-4` and was recorded as "locally
flat".  That reading was correct but under-determined — a flat run can mean a
bad step size, a noisy estimator, or a bad seed.  It was none of those: the
gradient is exactly zero at the flip in every direction of the slice.  The
right conclusion was never "iterate longer", and the planned exact Stage-1b
engine would have swept a landscape whose interesting structure starts at
second order — and which `atlas-stabilizer-commutant-no-go` has since excluded
outright, at every multiplicity.

Stationarity alone would not have closed the lane: second-order movement, and
unrestricted `U(20160k)` movement, both remained open at this point.  Recorded
here because the reduction (exact integer differentiation of atlas traces
through cyclicity) is reusable for any other structured slice, and because it
is the honest reason the pilot saw nothing.

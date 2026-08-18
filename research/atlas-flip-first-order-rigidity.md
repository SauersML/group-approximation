---
rg: 2
id: atlas-flip-first-order-rigidity
kind: claim
title: The tensor flip is first-order rigid in the full unitary group, per word, at every multiplicity
distinct_from:
  atlas-stabilizer-slice-stationary: that is exact stationarity along the index-15 stabilizer slice at k = 1, established by machine pairing; this is stationarity in ALL of U(20160·k) for EVERY k, per relator, with a two-case analytic proof of which the slice result is a corollary.
  atlas-stabilizer-commutant-no-go: that is a positive lower bound killing one structured family of moves at all orders; this is the vanishing of the first derivative for ALL moves at one point, and neither implies the other.
  atlas-true-criterion-baseline: that is the exact value of the objective at the flip; this is its exact (zero) derivative there, turning the baseline from a data point into a critical point.
artifacts:
  - research/artifacts/atlas-flip-stationarity-2026-08-17.json
  - research/artifacts/atlas-true-criterion-probe-2026-08-15.md
  - experiments/atlas_flip_stationarity_exact.py
---

For the explicit criterion of `atlas-steinberg-rank-five-translation`
(single unitary `U ∈ U(20160·k)`, the `T_St` relators evaluated with the
first chart in the left regular representation of `A₈` and the second
chart `U`-conjugated), the canonical warm start — the tensor flip
`J ⊗ I_k`, at which second-chart letters act as right translations
`R_h ⊗ I_k` — is a critical point of every defect built from `T_St`:

**Theorem.** For every word `w ∈ T_St`, every multiplicity `k ≥ 1`, and
every tangent direction `X ∈ u(20160·k)`,

```text
d/dt|₀ tr π_{e^{tX}·(J ⊗ I_k)}(w) = 0.
```

The statement is per relator, not an average: every weighting of every
subset of `T_St` has vanishing Riemannian gradient at the flip.  The
same holds at every point of the manifold `{J ⊗ V : V ∈ U(k)}`, since
each such point presents the second chart by the same operators
`R_h ⊗ I_k`.

**Why (two structural cases, no computation about `A₈` used).**  The
differential is a signed sum, over second-chart letters `h` of `w`, of
two-sided translations `L_a(R_{hb} − R_{bh})` with `a` a conjugate of
the first-factor projection `p₁(w)` and both `hb`, `bh` conjugates of
the second-factor projection `p₂(w)`.  Every `T_St` word has `p₁ = I`
or `p₂ = I` (the exact split is 36 + 36 escapees plus 4,564 doubly
trivial — no word escapes in both factors, `atlas-true-criterion-baseline`),
and each case kills the sum identically: `p₂ = I` forces `b = h⁻¹`
site-by-site, and `p₁ = I` makes the sum telescope cyclically.  Details
and the exact-integer machine verification (which confirms the stronger
pair-level vanishing of the unsymmetrized differential) are in
`atlas-flip-first-order-rigidity-proof`.

**What it changes.**

1. **There is no gradient route off the flip — anywhere, at any
   multiplicity.**  The slice pilots' flatness was not bad seeds or
   step sizes and not a property of the tested slices: the full
   landscape is first-order flat at the flip.  Any hyperlinear-side
   construction through this criterion must either start at a genuinely
   different basepoint or exploit second-order/global structure;
   raising `k` alone changes nothing at first order.
2. **The unrestricted-deformation probe became a Hessian probe, and it
   found nothing to escape through.**  Stage 2's clean run (V100 job
   16010744, resampled probes, Newton–Schulz retraction, 100 unbiased
   SGD iterations, completed 2026-08-18) recorded ZERO descent:
   best loss stayed at iteration 0's value, the dynamics equilibrated
   in a `‖W − I‖ ≈ 0.05` noise ball with the objective strictly above
   baseline throughout, and the gradient norm sat at the estimator
   noise floor — empirically no accessible negative curvature at that
   radius and noise scale, consistent with a local minimum and proving
   nothing beyond that (see the probe artifact for the full record and
   the designated sharper instruments).
3. **The mechanism is model-independent.**  The proof uses only that
   each relator escapes in at most one factor of the two-chart
   presentation.  Any flip-type warm start for any two-chart criterion
   with single-factor-escaping relators is first-order rigid — a fence
   for every future ansatz of this shape, not just this one.

**Corollary (the classical sector is gradient-dead).**  An
automorphism fold `P_φ`, `φ ∈ Aut(A₈) ≅ S₈`, conjugates right
translations to right translations: `P_φ R_h P_φ* = R_{φ(h)}`.  So at
any of the 40,320 fold basepoints of `atlas-true-criterion-baseline`
the second chart again acts by right translations, the factor
projections become `(p₁, φ(p₂))`, and the single-factor-escape
dichotomy is `φ`-invariant — the same two cases kill the differential.
Every classical warm start (all folds, the whole flip manifold, at
every multiplicity) is first-order rigid.  The criterion has no
first-order entry point from anywhere in its classical sector; pure
thought, no new computation.

Evidence and structure only with respect to the branch question: this
selects between nothing.  It sharpens `leavitt-steinberg-hs-unstable`
by closing the entire first-order neighborhood of the one warm start
whose defect set is exactly the finite-quotient obstruction.

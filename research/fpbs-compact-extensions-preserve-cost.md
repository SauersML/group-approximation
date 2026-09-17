---
rg: 2
id: fpbs-compact-extensions-preserve-cost
kind: claim
title: Relatively compact extensions of free actions of a finitely generated group preserve cost
distinct_from:
  fpbs-finite-fiber-cost-bound: that bounds the source cost of a uniform finite-fiber extension from above by an affine function of the base cost; this asks for equality along every relatively compact extension, including isometric and non-ergodic ones.
  kazhdan-map-bernoulli-finite-extensions-are-trivial: that collapses finite-to-one extensions of a Bernoulli base over Kazhdan hosts; this concerns relatively compact extensions of arbitrary free bases.
artifacts:
  - research/artifacts/fpbs-furstenberg-zimmer-cost-tower-2026-09-17.md
  - research/artifacts/fpbs/docs/finite-fiber-cost-descent.md
---

**OPEN.** Let G be a finitely generated group, and let V -> W be a factor map of free p.m.p. G-actions that is a relatively compact extension. Relatively compact means L²(V) is the closure of its G-invariant finitely generated L^∞(W)-submodules, as in `relative-furstenberg-zimmer-dichotomy`. Prove C(V) = C(W).

This is half P_c of `fpbs-compact-weakly-mixing-tower-decomposes-cost-preservation`. It contains the finite-fiber extensions, and with them the finite-index questions encoded in Section 2 of the finite-fiber artifact. It also contains compact-group rotation extensions. Four of the explicit removal countermodels recorded for `fpbs-correlated-reuse-flags-removable` are extensions of this class (artifact Section 3). None of them changes cost. Each defeats a particular removal operation. No route establishes the claim.

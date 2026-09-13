---
rg: 2
id: rank-kill-makes-ternary-strict-deficit-vacuous
kind: route
title: If every Sylvester rank function kills one minus the central involution, the anti-central strict deficit holds vacuously
target: ternary-anti-central-disjoint-defects-have-a-strict-deficit
requires:
  - sylvester-rank-functions-on-ternary-leavitt-units-kill-minus-one
artifacts:
  - research/artifacts/matrix-state-deficit-item-two-2026-09-12.md
---

Artifact Theorem 2.2.1.

1. The requirement gives `N(1 - [z]) = 0` for every Sylvester matrix rank function on `F_3[G]`. Since
   `eps_- = 2(1 - [z])`, no `N` has `N(eps_-) = 1`, so `A_S = ∅`.
2. The target quantifies over `A_S`, so it holds vacuously, with any `theta`. QED

**Equivalence.** The route `ternary-rank-kill-via-anti-central-defect-deficit` runs the other way, by the minimizer
contradiction; its other requirements are the gap, descent and compression claims. Together the two routes give an
equivalence. So the deficit claim is a restatement of the kill claim, not a reduction. Its value is as the local,
quantitative form a proof would aim at. Section 4.1 of
`research/artifacts/sylvester-exact-globality-and-kernel-compression-2026-09-12.md` says the same of the binary claim.

*On paper, lane `w7-matrix-state-deficit` (2026-09-12). Verification requested from `w4-vf-linear-b`.*

*Verification by `w4-vf-linear-b` (2026-09-12), Section 43 of `research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`: PASS. Steps 1–2 re-derived on paper: `N(eps_-) = N(1 - [z])`, since 2 is a unit in `F_3`.*

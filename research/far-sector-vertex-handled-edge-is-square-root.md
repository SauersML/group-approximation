---
rg: 2
id: far-sector-vertex-handled-edge-is-square-root
kind: claim
title: SL2(Z) stability handles the vertex, reducing the far sector to the square-root gluing, so the de la Salle and Iwahori routes coincide
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
distinct_from:
  far-sector-length-control-extension-gap: that frames the far sector as an averaged length-control estimate; this shows that estimate reduces, via ESTABLISHED SL_2(Z) stability, to the square-root/edge compatibility, unifying it with the Iwahori question.
  iwahori-question-as-square-root-of-parabolic: that is the square-root presentation; this is the reduction OF the far sector TO it through the established stability of the vertex group.
---

`SL_2(Z)` is Hilbert--Schmidt stable (it is virtually free; Gerasimova--Shchepin
arXiv:2107.10032 prove virtually free groups are stable in every normalized
`p`-Schatten norm, `p = 2` giving HS).  Use this on a microstate `U` of
`SL_2(Z[1/2])`:

1. **Vertex (established).**  `U|_(SL_2(Z))` is an approximate representation
   of `SL_2(Z)`, so by its stability it is HS-close to an EXACT
   finite-dimensional representation `rho_0` of `SL_2(Z)` (after the flexible
   corner padding).  So the "vertex" data is exactified for free.

2. **Edge (the only remaining content).**  `SL_2(Z[1/2]) = <SL_2(Z), u^(1/2)>`
   with the half-parabolic `u^(1/2) = [[1,1/2],[0,1]]`, and `U(u^(1/2))` is an
   approximate SQUARE ROOT of `rho_0(u)` (`U(u^(1/2))^2 = U(u) approx
   rho_0(u)`) subject to the two half-parabolic relations of `(SR2)`.  The
   far sector is therefore exactly: correct the approximate square root to an
   exact one compatible with `rho_0`, i.e. extend `rho_0` to an exact
   representation of `SL_2(Z[1/2])`.

**Consequence: the routes coincide.**  Step 2 is the Iwahori local-global /
square-root gluing question (`iwahori-question-as-square-root-of-parabolic`,
`iwahori-local-global-defect-question`).  So the de la Salle promotion route
(`far-sector-from-length-control-extension`) and the Iwahori route are the
SAME open problem, both with the vertex handled by established `SL_2(Z)`
stability and only the edge open.  This also pins the exact role of each
established piece: `SL_2(Z)` stability = vertex; the near-sector
infinitesimal rigidity + Newton (`iwahori-newton-closes-near-sector`) = the
edge NEAR the compatible locus; the far edge = non-compatible square roots =
`iwahori-outlier-repair`, the single remaining hole.

The convergence is evidence, not coincidence: every honest reduction of the
`SL_2(Z[1/2])` far sector -- averaged length control, square-root gluing,
relative-commutant collapse restricted to the amalgam -- lands on the same
edge statement, which is why closing any one closes them all, and why it is
genuinely the frontier.

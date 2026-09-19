---
rg: 2
id: ct-p-z-mixed-ray-torsion-reduces-to-sweeping-orbits-proof
kind: route
title: "Bounded cocycle freezes a middle degree everywhere; trapped segments plus compactness bound all orbits; torsion germs make the cocycle an orbitwise coboundary; a drifting return has a hyperbolic fixed point"
target: ct-p-z-mixed-ray-torsion-reduces-to-sweeping-orbits
requires:
  - ct-p-z-mixed-ray-frozen-tails-force-finite-orbits
  - ct-p-z-is-a-one-vertex-k-graph-full-group
---

Lane proof (bh-free-58, 2026-09-19), not reviewed. The full argument is in the body of
`ct-p-z-mixed-ray-torsion-reduces-to-sweeping-orbits`.
- **Inputs.** The trapped-segment orbit bound (item 1 of
  `ct-p-z-mixed-ray-frozen-tails-force-finite-orbits`, applied at every point of `Ẑ`) and the
  k-graph description of `CT_P(Z)`.
- **Steps proved in the body.** The finite-index argument and the germ computation.
- **Item 3.** It uses only the product structure `Z(τ) = ∏ B_p` and the contraction principle
  in each `Z_p`.

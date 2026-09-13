---
rg: 2
id: bf-n-r-twist-detected-characters-lie-in-sigma-infinity-proof
kind: route
title: "Meinert's criterion on a band of the Skipper–Wu Stein space with full twists in every stabilizer"
target: bf-n-r-twist-detected-characters-lie-in-sigma-infinity
requires:
  - pure-braided-bht-braid-characters-dimension-n-n-minus-1
artifacts:
  - research/artifacts/zp-pure-braided-bht-sigma-2026-09-13.md
---

Artifact §2, Theorem 3. The required claim gives `tau_phi(k) != 0` for all
`k >= p`.

- Skipper–Wu (arXiv:2103.14589) give the Stein space: contractible, height =
  number of feet, cocompact sublevel sets, and descending links whose
  connectivity grows with height.
- Ascending links are simplices, so the band `X^{p <= f <= q}` is
  `(j-1)`-connected for `q >= np` large.
- Cube stabilizers are conjugates of the pure braid groups on the feet of the
  bottom vertex. Their central full twist has `chi`-value `tau_phi(f(x)) != 0`.
- The central-element criterion (Meier–Meinert–VanWyk, Theorem 2.1) puts
  every restriction in `Sigma^infinity`, and Meinert's cocompact-action criterion
  (Meier–Meinert–VanWyk, Theorem 2.4) gives `[chi]` in `Sigma^j` for every `j`.

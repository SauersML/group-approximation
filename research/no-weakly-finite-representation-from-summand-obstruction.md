---
rg: 2
id: no-weakly-finite-representation-from-summand-obstruction
kind: route
title: A nontrivial weakly finite representation cuts to a weakly finite image of the anti-central summand
target: ternary-leavitt-units-have-no-weakly-finite-representation
requires:
  - ternary-anti-central-summand-has-no-weakly-finite-image
  - ternary-weakly-finite-representations-give-anti-central-images
artifacts:
  - research/artifacts/weakly-finite-representations-of-ternary-leavitt-units-2026-09-12.md
---

By `ternary-weakly-finite-representations-give-anti-central-images`, a nontrivial weakly finite representation
of `G` gives a nonzero weakly finite image of `S_-`, through the corner cut along `iota`. The required
obstruction forbids that image.

This route forms an intended cycle with `summand-no-weakly-finite-image-from-no-representation`.

*Verification by `w4-vf-linear-b` (2026-09-12), Section 38.2 of `research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`: PASS as an implication, inheriting the simplicity condition of Theorem 3. `f = 2(1 - u)` is a nonzero idempotent commuting with `rho(iota(G))`, and `[z] -> -f`, so the image of `S_-` is a nonzero unital subring of the weakly finite corner `fWf`.*

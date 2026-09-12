---
rg: 2
id: surjectivity-descends-to-centralized-coset-quotients-proof
kind: route
title: Right translations by the centralized subgroup commute with the automaton, so preimages of invariant configurations stay invariant
target: surjectivity-descends-to-centralized-coset-quotients
requires: []
artifacts:
  - research/artifacts/simple-host-direct-attack-2026-09-12.md
---

Section 2 of the artifact.

1. `tau(R_b x)(g) = mu((x(gmb))_m) = mu((x(gbm))_m) = tau(x)(gb)`, because `mb = bm`.
2. On `Y_B` the formula `tau(x)(gB) = mu((x(gmB))_m)` is well defined. Along each free right
   `N_G(B)/B`-orbit it is the automaton over `N_G(B)/B` with memory `MB/B`.
3. The restriction to `Y_B` is the product over orbits of copies of `taubar`, so injectivity
   passes to `taubar`.
4. If `tau` is bijective and `y` is `B`-invariant, its unique preimage `x` satisfies
   `tau(R_b x) = R_b y = y`. So `R_b x = x`, and every factor is onto.

**Verified 2026-09-12** by gk-vf-positive, independent re-derivation: PASS (Section 13 of `research/artifacts/gk-vf-positive-verification-2026-09-12.md`).

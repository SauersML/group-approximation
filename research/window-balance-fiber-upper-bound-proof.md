---
rg: 2
id: window-balance-fiber-upper-bound-proof
kind: route
title: The fiber counts sum to the average times the number of patterns, so an upper bound at the average forces equality
target: window-balance-is-a-fiber-upper-bound
requires: []
artifacts:
  - research/artifacts/window-balance-mass-transport-2026-09-12.md
  - research/artifacts/w3-vf-positive-verification-2026-09-12.md
---

Section 2 of the artifact. The image measure of the cylinder `p` on `E` is `c_E(p) q^(-|EM|)`. The
`q^|E|` fiber counts sum to `q^(|EM|)`, so their average is `q^(|EM| - |E|)`. A finite family bounded
above by its average is constant, which is uniform on `E`. Marginals of a uniform law are uniform,
and cylinder values determine the measure.

**Verification.** `w3-vf-positive` passed this route (Section 5.1 of `research/artifacts/w3-vf-positive-verification-2026-09-12.md`).

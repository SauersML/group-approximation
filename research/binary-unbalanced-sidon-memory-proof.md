---
rg: 2
id: binary-unbalanced-sidon-memory-proof
kind: route
title: An unbalanced binary rule is blind in each coordinate somewhere, and Sidon memory lets one configuration show all those blind patterns around a site
target: binary-unbalanced-rules-on-sidon-memory-are-not-pre-injective
requires: []
artifacts:
  - research/artifacts/small-memory-balance-census-2026-09-12.md
  - research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md
---

Section 3 of the artifact.
- **Blind patterns exist.** If coordinate `m` is never blind, then `mu = x_m + f(rest)` mod 2, and
  `mu` is balanced. So an unbalanced rule has a blind pattern `r_m` for each coordinate `m`.
- **Place them.** Write `r_m` on the sites `h m^-1 m'`. The Sidon property makes these sites
  distinct from each other and from `h`.
- **The flip is invisible.** Every site that reads `x(h)` is some `h m^-1`, and it sees `r_m` on
  its other coordinates. So flipping `x(h)` changes no output.

**Verification (w3-vf-nonlinear, 2026-09-12): PASS.** Re-derived independently. The content equals Lemma 6
of `research/artifacts/unbalanced-design-memory-collisions-2026-09-12.md`
(`research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md`, Section 9.1).

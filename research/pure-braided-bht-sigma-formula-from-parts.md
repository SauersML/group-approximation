---
rg: 2
id: pure-braided-bht-sigma-formula-from-parts
kind: route
title: "Assemble the Sigma^m formula for bF_{n,r} from the character splitting and three membership cases"
target: pure-braided-bht-sigma-invariants-miss-only-endpoint-hull
requires:
  - pure-braided-bht-braid-characters-dimension-n-n-minus-1
  - bf-n-r-twist-detected-characters-lie-in-sigma-infinity
  - bf-n-r-twist-invisible-braid-characters-in-sigma-infinity
  - bf-n-r-pulled-back-characters-follow-endpoint-hull
---

Every character is `chi = pi^* psi + phi` with `phi` in `W`
(`pure-braided-bht-braid-characters-dimension-n-n-minus-1`). Three cases:

- `phi = 0`: `chi` is pulled back, and
  `bf-n-r-pulled-back-characters-follow-endpoint-hull` is exactly the formula on
  that subsphere.
- `phi` nonzero with `tau_phi` not identically zero for large `k`:
  `[chi]` is in `Sigma^infinity` by
  `bf-n-r-twist-detected-characters-lie-in-sigma-infinity`.
- `phi` nonzero in `W_0`: `[chi]` is in `Sigma^infinity` by
  `bf-n-r-twist-invisible-braid-characters-in-sigma-infinity`.

So the only holes are the pulled-back endpoint characters (`m = 1`) and their
nonnegative hull (`m >= 2`), which is the candidate answer.

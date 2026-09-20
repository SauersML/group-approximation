---
rg: 2
id: ct-z-bounded-transverse-drift-gives-kourovka-20-44-proof
kind: route
title: "Theorem C runs the orbit-local corner argument from the raised start (D+f)·1, absorbing the bounded transverse error; C1 bounds the drift by the transfer function"
target: ct-z-bounded-transverse-drift-gives-kourovka-20-44
requires:
  - ct-z-kourovka-20-44-is-graded-by-orbit-slope-groups
  - ct-z-frozen-tails-anywhere-give-kourovka-20-44
  - ct-p-z-ray-cocycle-subgroups-satisfy-kourovka-20-44
---

Lane proof (bh-2044-tc, 2026-09-19), not reviewed.
- **Theorem C.** Theorem A of `ct-z-kourovka-20-44-is-graded-by-orbit-slope-groups`, started at
  `(D + f)·1` instead of `D·1`, so that an error `‖e‖_∞ ≤ f` never makes a tail readable off the
  corner. The tracking facts are those of `ct-p-z-ray-cocycle-subgroups-satisfy-kourovka-20-44`.
- **Non-TC groups.** Handled by `ct-z-frozen-tails-anywhere-give-kourovka-20-44`.
- **Corollaries C1 and C2** use only the cocycle identity and compactness.

All details are in the target's body.

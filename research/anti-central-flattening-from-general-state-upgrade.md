---
rg: 2
id: anti-central-flattening-from-general-state-upgrade
kind: route
title: The general state upgrade, specialized to the anti-central summand and read through the certificate criterion
target: anti-central-triangular-certificates-flatten-to-minors
requires:
  - rank-condition-rings-carry-sylvester-rank-functions
  - sylvester-rank-functions-iff-no-triangular-certificate
artifacts:
  - research/artifacts/state-upgrade-kill-test-2026-09-12.md
---

Apply the general claim to `S_-`: the rank condition gives a Sylvester rank function. By the criterion,
the rank condition fails iff some minor certificate `I_(q+1) <~ I_q` exists, and no rank function exists
iff some triangular certificate `I_(q+1) <=_T I_q` exists. Take the contrapositive.

*Verification by `w4-vf-linear-b` (2026-09-12), Section 38.4 of `research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`: PASS as an implication. Part 2 of the criterion turns "no minor certificate" into the rank condition on `S_-`, the general claim gives a Sylvester rank function, and part 1 excludes every triangular certificate.*

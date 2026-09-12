---
rg: 2
id: steinberg-schur-divide-antidiagonal-recursion
kind: route
title: Pivot recursively through every corrected antidiagonal coefficient
target: steinberg-rank-one-schur-pivot-is-invertible
requires:
  - steinberg-schur-corrected-endpoint-reduction
---

**INVALIDATED NONRESONANT RECURSION.**  This proposed proof solves the
endpoint equations successively by dividing through
`2^(2j-1)-1`.  It is invalidated by
`steinberg-schur-antidiagonal-resonates`: already the `j=3` pivot vanishes at
`p=31`.  A uniform proof must tolerate cyclotomic resonance, for example by
extracting `Q'(-1)` from a global row combination rather than dividing row by
row.

---
rg: 2
id: npa-class-count-fixes-rank-nullity-dictionary-proof
kind: route
title: Rank-nullity against the imported class count
target: npa-class-count-fixes-rank-nullity-dictionary
requires:
  - pakhunov-critical-face-structural-laws
artifacts:
  - research/artifacts/npa-critical-face-dimension-law-audit-2026-08-23.md
---

The counting law supplies `C_k = (5k+2)(k+1)/2` as the dimension of the domain
of `Phi_k`, so `rank Phi_k + dim ker Phi_k = C_k` and `(N) <-> (R)` is
substitution:

```text
C_k - (2k+3) = (5k^2 + 7k + 2)/2 - (4k+6)/2 = (5k^2 + 3k - 4)/2.
```

For the increments, `C_k - C_(k-1) = [(5k+2)(k+1) - (5k-3)k]/2 = (10k+2)/2 = 5k+1`,
so `(I)` and `(S)` add to `5k+1` and each determines the other.  Given `(N)` at
`k-1`, `(S)` is `(N)` at `k`.

Degrees: the level-`k` basis words have length at most `k` per party, so a
product class has total degree at most `2k`, and the classes newly available at
level `k` are exactly those of degree `2k-1` and `2k`; their number is therefore
the difference `5k+1`.

Base values are arithmetic: `C_2 = 12 * 3/2 = 18`, `C_3 = 17 * 4/2 = 34`, and
`(5 * 4 + 6 - 4)/2 = 11`, `(45 + 9 - 4)/2 = 25`.

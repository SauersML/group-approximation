---
rg: 2
id: some-noncrossing-chain-satisfies-turning-face-conditions
kind: claim
title: At n = 8 a noncrossing chain and its dual both satisfy the four turning-face conditions
distinct_from:
  no-noncrossing-chain-satisfies-turning-face-conditions: that claim asserts no such chain exists for any n; this one is its negation, witnessed at n = 8
---

In `NCP_8` the chain `F = ({{1,8}} < {{1,8},{2,6}})` and its Kreweras dual
`F* = ({{1,6,7},{2,3,4,5}} < {{1,2,3,4,5,6,7}})` both satisfy conditions I, II, III', IV of
`research/artifacts/zp-braid-cat0-turning-face-reduction-2026-09-13.md`. So the turning-face search of Theorem R, with
condition IV as stated (matching one consecutive pair `(i, i ± 1)`), cannot certify that the diagonal link of
`|NCP_8|` is CAT(1). The case `n = 8`, the first open case of Zaremsky Problem 3.6, is exactly where the method of
Haettel–Kielak–Schwer and Jeong stops.

This says nothing about whether `B_8` is CAT(0). It rules out one proof strategy as it stands. The hand proof is in
`some-noncrossing-chain-satisfies-turning-face-conditions-proof`. The mechanical search (`nc_turning.py`, MSI,
2026-09-13) finds 22268 chains in `NCP_8` whose duals also satisfy all four conditions, and none for `n = 5, 6, 7`.
